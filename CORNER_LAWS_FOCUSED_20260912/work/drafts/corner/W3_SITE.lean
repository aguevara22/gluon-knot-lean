-- W3_Skeleton.lean — corner wave 3 (row 110 thm:C-S7), 2026-09-15: the four open declarations of Corner_Assembled.lean
-- (s7_sliding_law_at 8656-8668, s7_bigon_law_at 9816-9834, thm_C_S7_of / thm_C_S7_of_floor 10008-10039) VERBATIM on top of the
-- ported library (SM.CornerChainUnits = waves 1-2a, SM.CS7Sliding = wave 2b, SM.BigonDeletion = the moves toolkit,
-- SM.CarrierFloorRows = thm_floor), plus the row theorem. Units APPEND prefixed material and may replace ONLY the two `sorry`
-- bodies; statements, names and docstrings are frozen (audit A-110-1, AUTHOR_NOTES 20:46Z).
import SM.CornerChainUnits
import SM.CS7Sliding
import SM.BigonDeletion
import SM.CarrierFloorRows

namespace SM

open Link Carrier

attribute [local instance] Classical.propDecidable

noncomputable section

section VertexEdge

variable {n : ℕ} [NeZero n]

/-- The sliding branch (sm-4:300-406): relocation bijection `φ(x₋) = x₊`, the support bijection
eq. s7c:sliding-bijection with the halves, equal coefficient products eq. s7c:sliding-coefficients, and
the exact selector difference eq. s7c:sliding-selector-difference.  NO floor, NO singleton. -/
theorem s7_sliding_law_at (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n) (h : g.SlidingAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  sorry


/-! ### Unit S7-SITE (I-110; prefix `s7s_`; corner wave 3, audit A-110-1)

The wall bigon site of PLAN_FINAL §3.3 bigon (2) on the ported `SM.BigonDeletion`: on the positive lift
`D_H` of a carrier `q` of a decomposition `S` of the bigon-side polygon `P` that RETAINS the two contact
crossings `x = x_{M−1,a}`, `y = x_{a,M}` (the "full contact carrier" through the vertex `M`), the switch
of `D_H` at (the lift of) `x` carries a `BigonData` whose bigon is `{x, y}` and whose region is the closed
contact triangle `K = conv{x, P M, y}` (`s7s_core`, via `exists_bigonData_of_triangle`).  Pattern: the
landed site `work/drafts/moves/Site_174.lean` (`s174_core`), with the corner at a polygon VERTEX instead of
a selected crossing: the corner index is `j_in + 1` (`hjout`, `hcorner`), the two `a`-visits are adjacent
(`hadj_s`), the contact crossing signs alternate (`hsgn`), and the other carrier edges are clear of `K`
(`hclear`) — these carrier-form facts are the wall data of U110-A/B (window clauses of
`VertexLocalData`, the printed emptiness sm-4:618-620): `hsgn` is PROVED from planar geometry
(`s7s_contact_sign`), `hjout`/`hcorner` from the window clauses by the block argument (`s7s_jout_of_wall`,
`s7s_cornerPolygon_of_wall`), `hclear` for the non-local carrier edges (`s7s_carrier_data_of_wall`); the
black boxes are `s7s_clear_local` (the carrier edges on the three local `P`-edges) and the `P`-level wall
data `s7s_wallTriangleData_of_bigon` (U110-A/B).  Then `s7s_switch_value`: given the record
identification `hrec` (`s7s_hrec_prop`, stated), `P (D_H.switch x) = P D_L` through the proved glue
`s7_switch_value_of_bigon` — exactly the hypothesis of `s7g_switch_value_of_rii` / the input of
`s7g_cornerHomfly_skein`, delivered on the accepted `positiveLift` by `geoPositiveLift_eq_generic`. -/

section S7Site

open GeoCarrier RProof

/-! #### s7s.1 Generic helpers (site-174 pattern; `Shadow.positiveDiagram`, `Diagram.switch`) -/

omit [NeZero n] in
theorem s7s_pos_over_iff {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing) {s t : Γ.Strand}
    (hx : x.val = {s, t}) (hst : s ≠ t) :
    (Γ.positiveDiagram hΓ).overStrand x = s ↔ 0 < det (Γ.dir s) (Γ.dir t) := by
  have hpos : 0 < det (Γ.dir ((Γ.positiveDiagram hΓ).overStrand x))
      (Γ.dir ((Γ.positiveDiagram hΓ).underStrand x)) := Γ.positiveDiagram_det_pos hΓ x
  have hs : s ∈ x.val := by rw [hx]; exact Finset.mem_insert_self _ _
  have ht : t ∈ x.val := by rw [hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hmem : (Γ.positiveDiagram hΓ).overStrand x ∈ ({s, t} : Finset Γ.Strand) := by
    rw [← hx]; exact (Γ.positiveDiagram hΓ).over_mem x
  constructor
  · intro h
    have hu : (Γ.positiveDiagram hΓ).underStrand x = t :=
      ((Γ.positiveDiagram hΓ).eq_under_of_mem_of_ne x ht
        (fun heq => hst.symm (heq.trans h))).symm
    rw [h, hu] at hpos
    exact hpos
  · intro hdet
    rcases Finset.mem_insert.mp hmem with h | h
    · exact h
    · exfalso
      have h' : (Γ.positiveDiagram hΓ).overStrand x = t := Finset.mem_singleton.mp h
      have hu : (Γ.positiveDiagram hΓ).underStrand x = s :=
        ((Γ.positiveDiagram hΓ).eq_under_of_mem_of_ne x hs (fun heq => hst (heq.trans h'))).symm
      rw [h', hu, det_swap] at hpos
      linarith

omit [NeZero n] in
theorem s7s_switch_over_self_iff (D : Diagram) (x : D.Γ.Crossing) {s t : D.Γ.Strand}
    (hx : x.val = {s, t}) (hst : s ≠ t) :
    (D.switch x).overStrand x = s ↔ D.overStrand x = t := by
  have hs : s ∈ x.val := by rw [hx]; exact Finset.mem_insert_self _ _
  have ht : t ∈ x.val := by rw [hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [D.switch_overStrand_self]
  constructor
  · intro h
    exact (D.eq_over_of_mem_of_ne x ht (by rw [h]; exact hst.symm)).symm
  · intro h
    exact (D.eq_under_of_mem_of_ne x hs (by rw [h]; exact hst)).symm

omit [NeZero n] in
/-- the over strand is the second strand iff it is not the first -/
theorem s7s_over_other_iff (D : Diagram) (x : D.Γ.Crossing) {s t : D.Γ.Strand}
    (hx : x.val = {s, t}) (hst : s ≠ t) : D.overStrand x = t ↔ D.overStrand x ≠ s := by
  have hmem : D.overStrand x ∈ ({s, t} : Finset D.Γ.Strand) := by rw [← hx]; exact D.over_mem x
  constructor
  · intro h heq; exact hst (heq.symm.trans h)
  · intro h
    rcases Finset.mem_insert.mp hmem with h' | h'
    · exact absurd h' h
    · exact Finset.mem_singleton.mp h'

omit [NeZero n] in
theorem s7s_pos_iff_of_sign_eq {a b : ℝ} (h : SignType.sign a = SignType.sign b) :
    0 < a ↔ 0 < b := by
  rw [← sign_eq_one_iff, ← sign_eq_one_iff, h]

omit [NeZero n] in
theorem s7s_neg_pos_iff_of_sign_eq {a b : ℝ} (h : SignType.sign a = SignType.sign b) :
    0 < -a ↔ 0 < -b := by
  rw [neg_pos, neg_pos, ← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, h]

omit [NeZero n] in
theorem s7s_not_pos_iff {a : ℝ} (ha : a ≠ 0) : ¬ 0 < a ↔ 0 < -a := by
  rw [not_lt, neg_pos]
  exact ⟨fun h => lt_of_le_of_ne h ha, le_of_lt⟩

omit [NeZero n] in
theorem s7s_det_smul_pos_iff {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (u v : Plane) :
    0 < det (c • u) (d • v) ↔ 0 < det u v := by
  rw [gu2_det_smul_smul]
  exact ⟨fun h => pos_of_mul_pos_right h (mul_pos hc hd).le,
    fun h => mul_pos (mul_pos hc hd) h⟩

theorem s7s_adjacent_zmod3 (i j : ZMod 3) : adjacent i j := by
  unfold adjacent
  have hv : ((j - i).val : ZMod 3) = j - i := ZMod.natCast_zmod_val (j - i)
  have hlt : (j - i).val < 3 := ZMod.val_lt (j - i)
  rw [← hv]
  generalize (j - i).val = d at hlt
  interval_cases d
  · right; left; rfl
  · right; right; rfl
  · left; decide

theorem s7s_four_le {k : ℕ} (hk : 3 ≤ k) (h : ∃ i j : ZMod k, ¬ adjacent i j) : 4 ≤ k := by
  by_contra hlt
  have h3 : k = 3 := by omega
  subst h3
  obtain ⟨i, j, hij⟩ := h
  exact hij (s7s_adjacent_zmod3 i j)

omit [NeZero n] in
/-- two strands of a one-component shadow with non-adjacent labels are distinct -/
theorem s7s_strand_ne_of_not_adjacent {C : PolyComp} {j j' : ZMod C.k} (h : ¬ adjacent j j') :
    (⟨0, j⟩ : (Shadow.single C).Strand) ≠ ⟨0, j'⟩ := by
  intro heq
  apply h
  have hjj : j = j' := eq_of_heq (Sigma.mk.inj heq).2
  rw [hjj]
  exact Or.inr (Or.inl (sub_self _))

/-! #### s7s.2 The lifted crossings of a carrier (site-174 pattern on `geoCarrierCrossingEquiv`) -/

section S7SiteCore

variable {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CarrierGeometry P)
  {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)

/-- the crossing of the carrier shadow at a retained crossing `c` of the carrier `q` -/
noncomputable def s7s_lift (c : Crossing P) (hc : c ∈ geoCarrierCrossings hG.cg S q) :
    (geoCarrierShadow hn hG hS q).Crossing :=
  (geoCarrierCrossingEquiv hn hG hS q).symm ⟨c, hc⟩

theorem s7s_lift_crossingPoint (c : Crossing P) (hc : c ∈ geoCarrierCrossings hG.cg S q) :
    (geoCarrierShadow hn hG hS q).crossingPoint (s7s_lift hn hG hS q c hc) = crossingPoint c := by
  have h := crossingPoint_geoCarrierCrossingEquiv hn hG hS q (s7s_lift hn hG hS q c hc)
  rw [s7s_lift, Equiv.apply_symm_apply] at h
  exact h.symm

theorem s7s_lift_injective_pt {c c' : Crossing P} (hc : c ∈ geoCarrierCrossings hG.cg S q)
    (hc' : c' ∈ geoCarrierCrossings hG.cg S q) (hne : c ≠ c') :
    s7s_lift hn hG hS q c hc ≠ s7s_lift hn hG hS q c' hc' := by
  intro h
  apply hne
  have := congrArg (geoCarrierShadow hn hG hS q).crossingPoint h
  rw [s7s_lift_crossingPoint, s7s_lift_crossingPoint] at this
  exact crossingPoint_injective_of_geometry hG.cg this

/-- the strands of the lifted crossing are the two carrier edges of the visits of `v.1` -/
theorem s7s_lift_val (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg S q)
    (hv' : (visitTwin v).1 ∈ geoCarrierCrossings hG.cg S q) :
    (s7s_lift hn hG hS q v.1 hv).val =
      {(⟨0, G11_carrierEdge hn hG hS q v hv⟩ : (geoCarrierShadow hn hG hS q).Strand),
       ⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩} := by
  set Γ := geoCarrierShadow hn hG hS q with hΓ
  have hna : ¬ Γ.Adjacent ⟨0, G11_carrierEdge hn hG hS q v hv⟩
      ⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩ := by
    rw [Shadow.single_adjacent_iff]
    exact gu1_carrierEdge_remote hn hG hS q v hv hv'
  have hmem1 : crossingPoint v.1 ∈ Γ.seg ⟨0, G11_carrierEdge hn hG hS q v hv⟩ :=
    (G11_carrierEdge_spec hn hG hS q v hv).1
  have hmem2 : crossingPoint v.1 ∈ Γ.seg ⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩ := by
    have := (G11_carrierEdge_spec hn hG hS q (visitTwin v) hv').1
    rw [visitTwin_crossing] at this
    exact this
  let y₀ : Γ.Crossing := ⟨_, Γ.isCrossing_pair hna ⟨crossingPoint v.1, hmem1, hmem2⟩⟩
  have hpt : Γ.crossingPoint y₀ = crossingPoint v.1 := by
    symm
    apply (geoCarrierShadow_generic hn hG hS q).common_point_unique
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact hmem1
    · rw [Finset.mem_singleton.mp hs]; exact hmem2
  have heq : s7s_lift hn hG hS q v.1 hv = y₀ := by
    apply (geoCarrierShadow_generic hn hG hS q).crossingPoint_injective
    rw [s7s_lift_crossingPoint, hpt]
  rw [heq]

include hn hS in
theorem s7s_four_le_cornerCount (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg S q)
    (hv' : (visitTwin v).1 ∈ geoCarrierCrossings hG.cg S q) :
    4 ≤ geoCornerCount hG.cg S q :=
  s7s_four_le (three_le_geoCornerCount hn hG hS q)
    ⟨_, _, gu1_carrierEdge_remote hn hG hS q v hv hv'⟩

omit [NeZero n] in
theorem s7s_det_ne_zero_of_isCrossing (hP : CrossingGeometry P) {i j : ZMod n}
    (h : IsCrossing P {i, j}) : det (edge P i) (edge P j) ≠ 0 :=
  (hP.2.1 i j (gu2_remote_of_isCrossing h) _ (crossingPoint_mem (xPair h) i (mem_pair_left i j))
    (crossingPoint_mem (xPair h) j (mem_pair_right i j))).2.2

include hn hS in
/-- at a lifted crossing `⟨0, j⟩, ⟨0, j'⟩` of the positive lift, the strand `⟨0, j'⟩` is over iff
`det (edge P e') (edge P e) > 0` for the original edges `e, e'` of the two visits -/
theorem s7s_pos_over_lift_iff (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg S q)
    (hv' : (visitTwin v).1 ∈ geoCarrierCrossings hG.cg S q) :
    (geoPositiveLift hn hG hS q).overStrand (s7s_lift hn hG hS q v.1 hv) =
        (⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔
      0 < det (edge P (visitTwin v).2.val) (edge P v.2.val) := by
  have hval := s7s_lift_val hn hG hS q v hv hv'
  rw [Finset.pair_comm] at hval
  have hne : (⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩ : (geoCarrierShadow hn hG hS q).Strand) ≠
      ⟨0, G11_carrierEdge hn hG hS q v hv⟩ :=
    (geoCarrierShadow hn hG hS q).ne_of_not_adjacent
      (fun h => gu1_carrierEdge_remote hn hG hS q v hv hv'
        ((Shadow.single_adjacent_iff _ _ _).mp (Shadow.Adjacent.symm _ h)))
  refine (s7s_pos_over_iff (geoCarrierShadow_generic hn hG hS q) _ hval hne).trans ?_
  obtain ⟨-, c, hc, he⟩ := G11_carrierEdge_spec hn hG hS q v hv
  obtain ⟨-, c', hc', he'⟩ := G11_carrierEdge_spec hn hG hS q (visitTwin v) hv'
  show 0 < det (edge (geoCornerPolygon hG.cg S q) _) (edge (geoCornerPolygon hG.cg S q) _) ↔ _
  rw [he, he']
  exact s7s_det_smul_pos_iff hc' hc _ _

/-! #### s7s.3 The wall bigon site: the vertex–edge triangle `conv{x, P M, y}` -/

variable {M a : ZMod n} (hx : IsCrossing P {M - 1, a}) (hy : IsCrossing P {a, M})

omit [NeZero n] in
/-- the closed contact triangle `conv{x, M, y}` (sm-4:618-620 "the isolated contact disc") -/
abbrev s7s_K : Set Plane :=
  convexHull ℝ {crossingPoint (xPair hx), P M, crossingPoint (xPair hy)}

include hn in
/-- **The wall bigon site (I-110; row 110 bigon (2)).**  On the positive lift `D_H = geoPositiveLift` of a
carrier `q` (independent support `S`) of the bigon-side polygon `P` that retains the two contact crossings
`x = x_{M−1,a}` (the visit `G11_vef hx` on the edge `M−1`, its twin `G11_vfe hx` on `a`) and `y = x_{a,M}`
(`G11_vfg hy` on `a`, `G11_vgf hy` on `M`), the switch of `D_H` at (the lift of) `x` or `y` carries a
`BigonData` whose bigon is `{x, y}` and whose region is the closed contact triangle `conv{x, P M, y}`.
Wall data consumed in carrier form (U110-A/B; discharged by `s7s_carrier_data_of_wall`):
`hjout` — the carrier edge of `y`'s `M`-visit is the successor of that of `x`'s `(M−1)`-visit (the block of
`x`'s leg visit ends at the vertex corner `M`, `y`'s leg visit opens the next block); `hcorner` — that corner
is the vertex `P M`; `hadj_s` — no visit lies between the two `a`-visits (window clause); `hsgn` — the two
contact crossing signs alternate (`crossingSign P (M−1) a = crossingSign P a M`, the geometric fact that
`P M` lies on one side of `a` and `P (M−1)`, `P (M+1)` on the other; see `s7s_contact_sign`); `hclear` — every
other edge of the corner polygon misses the closed triangle. -/
theorem s7s_core
    (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q) (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q)
    (hjout : G11_carrierEdge hn hG hS q (G11_vgf hy) hyq = G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1)
    (hcorner : geoCornerPolygon hG.cg S q (G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1) = P M)
    (hadj_s : ∀ w : Visit P, w.2.val = a →
      ¬ (visitParameter (G11_vfe hx) < visitParameter w ∧ visitParameter w < visitParameter (G11_vfg hy)) ∧
      ¬ (visitParameter (G11_vfg hy) < visitParameter w ∧ visitParameter w < visitParameter (G11_vfe hx)))
    (hsgn : crossingSign P (M - 1) a = crossingSign P a M)
    (hclear : ∀ h : ZMod (geoCornerCount hG.cg S q), h ≠ G11_carrierEdge hn hG hS q (G11_vef hx) hxq →
      h ≠ G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1 → h ≠ G11_carrierEdge hn hG hS q (G11_vfe hx) hxq →
      Disjoint (edgeSegment (geoCornerPolygon hG.cg S q) h) (s7s_K hx hy))
    (xs : (geoCarrierShadow hn hG hS q).Crossing)
    (hxs : xs = s7s_lift hn hG hS q _ hxq ∨ xs = s7s_lift hn hG hS q _ hyq) :
    ∃ B : BigonData ((geoPositiveLift hn hG hS q).switch xs),
      B.i = ⟨0, Nat.one_pos⟩ ∧ B.y = s7s_lift hn hG hS q _ hxq ∧ B.z = s7s_lift hn hG hS q _ hyq := by
  have hne_in_s : M - 1 ≠ a := P1.ne_of_isCrossing_pair hx
  have hne_s_out : a ≠ M := P1.ne_of_isCrossing_pair hy
  -- the two `a`-visits are adjacent: equal carrier edges
  have hjs : G11_carrierEdge hn hG hS q (G11_vfg hy) hyq =
      G11_carrierEdge hn hG hS q (G11_vfe hx) hxq :=
    G11_carrierEdge_eq_of_adjacent hn hG hS q hyq hxq rfl
      (fun w hw => (hadj_s w hw).symm)
  set jy := G11_carrierEdge hn hG hS q (G11_vef hx) hxq with hjy_def
  set js := G11_carrierEdge hn hG hS q (G11_vfe hx) hxq with hjs_def
  set ys := s7s_lift hn hG hS q _ hxq with hys
  set zs := s7s_lift hn hG hS q _ hyq with hzs
  have htwz : visitTwin (G11_vgf hy) = G11_vfg hy :=
    SEL_visitTwin_visitOn (mem_pair_left a M) (mem_pair_right a M) hne_s_out
  -- the strands of the two lifted crossings
  have hyv : ys.val = {(⟨0, jy⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, js⟩} := by
    have h := s7s_lift_val hn hG hS q (G11_vef hx) hxq hxq
    rw [gu2_carrierEdge_congr hn hG hS q (gu2_visitTwin_vef hx) hxq hxq] at h
    exact h
  have hzv : zs.val = {(⟨0, jy + 1⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, js⟩} := by
    have h := s7s_lift_val hn hG hS q (G11_vgf hy) hyq hyq
    rw [gu2_carrierEdge_congr hn hG hS q htwz hyq hyq, hjs, hjout] at h
    exact h
  have hna_y : ¬ adjacent jy js := by
    have h := gu1_carrierEdge_remote hn hG hS q (G11_vef hx) hxq hxq
    rw [gu2_carrierEdge_congr hn hG hS q (gu2_visitTwin_vef hx) hxq hxq] at h
    exact h
  have hna_z : ¬ adjacent (jy + 1) js := by
    have h := gu1_carrierEdge_remote hn hG hS q (G11_vgf hy) hyq hyq
    rw [gu2_carrierEdge_congr hn hG hS q htwz hyq hyq, hjs, hjout] at h
    exact h
  have hne_y : (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ≠ ⟨0, jy⟩ :=
    s7s_strand_ne_of_not_adjacent (fun h => hna_y (by
      rcases h with h | h | h
      · exact Or.inr (Or.inr (by linear_combination -h))
      · exact Or.inr (Or.inl (by linear_combination -h))
      · exact Or.inl (by linear_combination -h)))
  have hne_z : (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ≠ ⟨0, jy + 1⟩ :=
    s7s_strand_ne_of_not_adjacent (fun h => hna_z (by
      rcases h with h | h | h
      · exact Or.inr (Or.inr (by linear_combination -h))
      · exact Or.inr (Or.inl (by linear_combination -h))
      · exact Or.inl (by linear_combination -h)))
  have hyv' : ys.val = {(⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, jy⟩} := by
    rw [hyv, Finset.pair_comm]
  have hzv' : zs.val = {(⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, jy + 1⟩} := by
    rw [hzv, Finset.pair_comm]
  -- the two contact crossings are distinct
  have hone : (1 : ZMod n) ≠ 0 := by
    intro h
    rw [ZMod.one_eq_zero_iff] at h
    omega
  have hyz_c : xPair hx ≠ xPair hy := by
    intro h
    have hmem : M - 1 ∈ (xPair hy).val := by rw [← h]; exact mem_pair_left _ _
    rcases Finset.mem_insert.mp hmem with h' | h'
    · exact hne_in_s h'
    · have h'' : M - 1 = M := Finset.mem_singleton.mp h'
      exact hone (by linear_combination -h'')
  have hyz : ys ≠ zs := s7s_lift_injective_pt hn hG hS q hxq hyq hyz_c
  -- the over strands of the positive lift at `x` and `y`
  have hA := s7s_det_ne_zero_of_isCrossing hG.cg hx
  have hB := s7s_det_ne_zero_of_isCrossing hG.cg hy
  have hoy : (geoPositiveLift hn hG hS q).overStrand ys =
      (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔ 0 < -det (edge P (M - 1)) (edge P a) := by
    have h := s7s_pos_over_lift_iff hn hG hS q (G11_vef hx) hxq hxq
    rw [gu2_carrierEdge_congr hn hG hS q (gu2_visitTwin_vef hx) hxq hxq, gu2_visitTwin_vef,
      det_swap] at h
    exact h
  have hoz : (geoPositiveLift hn hG hS q).overStrand zs =
      (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔ 0 < det (edge P a) (edge P M) := by
    have h := s7s_pos_over_lift_iff hn hG hS q (G11_vgf hy) hyq hyq
    rw [gu2_carrierEdge_congr hn hG hS q htwz hyq hyq, hjs, htwz] at h
    exact h
  have hsign : (0 < det (edge P (M - 1)) (edge P a) ↔ 0 < det (edge P a) (edge P M)) :=
    s7s_pos_iff_of_sign_eq hsgn
  have hsign' : (0 < -det (edge P (M - 1)) (edge P a) ↔ 0 < -det (edge P a) (edge P M)) :=
    s7s_neg_pos_iff_of_sign_eq hsgn
  -- `same_over` on the switched diagram
  have hsame : (((geoPositiveLift hn hG hS q).switch xs).overStrand ys =
        (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ∧
        ((geoPositiveLift hn hG hS q).switch xs).overStrand zs =
        (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand)) ∨
      (((geoPositiveLift hn hG hS q).switch xs).overStrand ys ≠
        (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ∧
        ((geoPositiveLift hn hG hS q).switch xs).overStrand zs ≠
        (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand)) := by
    rcases hxs with rfl | rfl
    · -- the switch is at `x`
      have e1 : ((geoPositiveLift hn hG hS q).switch ys).overStrand ys =
          (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔ 0 < det (edge P (M - 1)) (edge P a) := by
        refine (s7s_switch_over_self_iff (geoPositiveLift hn hG hS q) ys hyv' hne_y).trans ?_
        refine (s7s_over_other_iff (geoPositiveLift hn hG hS q) ys hyv' hne_y).trans ?_
        refine (not_congr hoy).trans ?_
        rw [s7s_not_pos_iff (neg_ne_zero.mpr hA), neg_neg]
      have e2 : ((geoPositiveLift hn hG hS q).switch ys).overStrand zs =
          (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔ 0 < det (edge P a) (edge P M) := by
        have h := Diagram.switch_overStrand_of_ne (geoPositiveLift hn hG hS q) hyz.symm
        rw [h]
        exact hoz
      by_cases hp : 0 < det (edge P (M - 1)) (edge P a)
      · exact Or.inl ⟨e1.mpr hp, e2.mpr (hsign.mp hp)⟩
      · exact Or.inr ⟨fun h => hp (e1.mp h), fun h => hp (hsign.mpr (e2.mp h))⟩
    · -- the switch is at `y`
      have e1 : ((geoPositiveLift hn hG hS q).switch zs).overStrand ys =
          (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔ 0 < -det (edge P (M - 1)) (edge P a) := by
        have h := Diagram.switch_overStrand_of_ne (geoPositiveLift hn hG hS q) hyz
        rw [h]
        exact hoy
      have e2 : ((geoPositiveLift hn hG hS q).switch zs).overStrand zs =
          (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔ 0 < -det (edge P a) (edge P M) := by
        refine (s7s_switch_over_self_iff (geoPositiveLift hn hG hS q) zs hzv' hne_z).trans ?_
        refine (s7s_over_other_iff (geoPositiveLift hn hG hS q) zs hzv' hne_z).trans ?_
        exact (not_congr hoz).trans (s7s_not_pos_iff hB)
      by_cases hp : 0 < -det (edge P (M - 1)) (edge P a)
      · exact Or.inl ⟨e1.mpr hp, e2.mpr (hsign'.mp hp)⟩
      · exact Or.inr ⟨fun h => hp (e1.mp h), fun h => hp (hsign'.mpr (e2.mp h))⟩
  -- clearance, read on strands
  have hclear' : ∀ u : (geoCarrierShadow hn hG hS q).Strand, u ≠ ⟨0, jy⟩ → u ≠ ⟨0, jy + 1⟩ →
      u ≠ ⟨0, js⟩ → Disjoint ((geoCarrierShadow hn hG hS q).seg u) (s7s_K hx hy) := by
    rintro ⟨i₀, h⟩ h1 h2 h3
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    have h1' : h ≠ jy := fun hh => h1 (by rw [hh])
    have h2' : h ≠ jy + 1 := fun hh => h2 (by rw [hh])
    have h3' : h ≠ js := fun hh => h3 (by rw [hh])
    exact hclear h h1' h2' h3'
  have hk : 4 ≤ geoCornerCount hG.cg S q := s7s_four_le_cornerCount hn hG hS q (G11_vef hx) hxq hxq
  have hpy : (geoCarrierShadow hn hG hS q).crossingPoint ys = crossingPoint (xPair hx) :=
    s7s_lift_crossingPoint hn hG hS q _ hxq
  have hpz : (geoCarrierShadow hn hG hS q).crossingPoint zs = crossingPoint (xPair hy) :=
    s7s_lift_crossingPoint hn hG hS q _ hyq
  have hK : convexHull ℝ {(geoCarrierShadow hn hG hS q).crossingPoint ys, geoCornerPolygon hG.cg S q (jy + 1),
      (geoCarrierShadow hn hG hS q).crossingPoint zs} = s7s_K hx hy := by
    rw [hpy, hpz, hcorner]
  -- the triangle builder
  obtain ⟨B, hBi, hBy, hBz⟩ := exists_bigonData_of_triangle ((geoPositiveLift hn hG hS q).switch xs)
    ⟨0, Nat.one_pos⟩ jy hk (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ys zs hyv hzv hsame (by
      intro u h1 h2 h3
      have hK' : convexHull ℝ {((geoPositiveLift hn hG hS q).switch xs).Γ.crossingPoint ys,
          (((geoPositiveLift hn hG hS q).switch xs).Γ.comp ⟨0, Nat.one_pos⟩).P
            ((jy + 1 : ZMod (geoCornerCount hG.cg S q))),
          ((geoPositiveLift hn hG hS q).switch xs).Γ.crossingPoint zs} = s7s_K hx hy := by
        rw [← hK]; rfl
      exact (hclear' u h1 h2 h3).mono_right (le_of_eq hK'))
  exact ⟨B, hBi, hBy, hBz⟩

end S7SiteCore

/-! #### s7s.4 Glue: the record identification `hrec` (stated), the R-II witnesses, `P (D_H^{sw}) = P D_L` -/

section S7SiteGlue

open GeoCarrier RProof

omit [NeZero n] in
/-- the reduced record of a bigon site with crossings `y₀, z₀`, written without the `BigonData` -/
def s7s_reducedRecordOf (D : Diagram) (y₀ z₀ : D.Γ.Crossing) : Record :=
  D.record.restrictCrossings
    {c | c ≠ D.record.crossingOf (D.overVisit y₀) ∧ c ≠ D.record.crossingOf (D.overVisit z₀)}

omit [NeZero n] in
theorem s7s_reducedRecord_eq {D : Diagram} (B : BigonData D) {y₀ z₀ : D.Γ.Crossing}
    (hBy : B.y = y₀) (hBz : B.z = z₀) : B.reducedRecord = s7s_reducedRecordOf D y₀ z₀ := by
  unfold BigonData.reducedRecord BigonData.keep s7s_reducedRecordOf
  rw [hBy, hBz]

variable {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CarrierGeometry P)
  {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)
  {M a : ZMod n} (hx : IsCrossing P {M - 1, a}) (hy : IsCrossing P {a, M})

/-- **The wall data in carrier form** (the hypotheses of `s7s_core`, bundled): what U110-A/B deliver
about the full contact carrier `q` on the bigon side — see `s7s_core` for the reading of each field. -/
structure s7s_SiteData (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q)
    (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) : Prop where
  jout : G11_carrierEdge hn hG hS q (G11_vgf hy) hyq = G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1
  corner : geoCornerPolygon hG.cg S q (G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1) = P M
  adj_s : ∀ w : Visit P, w.2.val = a →
    ¬ (visitParameter (G11_vfe hx) < visitParameter w ∧ visitParameter w < visitParameter (G11_vfg hy)) ∧
    ¬ (visitParameter (G11_vfg hy) < visitParameter w ∧ visitParameter w < visitParameter (G11_vfe hx))
  sgn : crossingSign P (M - 1) a = crossingSign P a M
  clear : ∀ h : ZMod (geoCornerCount hG.cg S q), h ≠ G11_carrierEdge hn hG hS q (G11_vef hx) hxq →
    h ≠ G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1 → h ≠ G11_carrierEdge hn hG hS q (G11_vfe hx) hxq →
    Disjoint (edgeSegment (geoCornerPolygon hG.cg S q) h) (s7s_K hx hy)

/-- the site, from the bundled data: the bigon `{x, y}` on `D_H.switch x` -/
theorem s7s_site (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q)
    (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) (W : s7s_SiteData hn hG hS q hx hy hxq hyq) :
    ∃ B : BigonData ((geoPositiveLift hn hG hS q).switch (s7s_lift hn hG hS q _ hxq)),
      B.i = ⟨0, Nat.one_pos⟩ ∧ B.y = s7s_lift hn hG hS q _ hxq ∧ B.z = s7s_lift hn hG hS q _ hyq :=
  s7s_core hn hG hS q hx hy hxq hyq W.jout W.corner W.adj_s W.sgn W.clear _ (Or.inl rfl)

/-- **`hrec` of PLAN_FINAL §3.3 bigon (2) — STATED, not proved.**  The record of `D_H.switch x` with the
four occurrences of `x, y` deleted is the record of the `L`-side lift `D_L` (the positive lift of the
transported carrier `e q` of `S` on `P_L`, `s7a_componentEquiv`): the retained crossings correspond
through `s7a_cross` (persistent crossings, `s7a_mem_carrierCrossings`), the cyclic order of the
persistent visits is carried (`VertexLocalData.visit_order`, `s7a_between_map`), the over bits agree
(`s7a_side_sgn` + `s7d_positiveOverBit_eq_of_crossingSign`; the switched bit sits on a DELETED
occurrence), and the switched restricted record is `Record.restrictCrossings_switch` (retained case) —
here the switched crossing `x` is deleted, so the needed form is the DELETED-case analogue (Site_174_REPORT
§3 item 1).  Cost estimate in W3_SITE_REPORT.md §3. -/
def s7s_hrec_prop (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q)
    (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) (DL : Diagram) : Prop :=
  Nonempty (RecordIso
    (s7s_reducedRecordOf ((geoPositiveLift hn hG hS q).switch (s7s_lift hn hG hS q _ hxq))
      (s7s_lift hn hG hS q _ hxq) (s7s_lift hn hG hS q _ hyq))
    DL.record)

/-- **The two hypotheses of the accepted glue `s7g_switch_value_of_rii`, PROVED from the site and
`hrec`** (`s7_rii_witnesses`, SM.BigonDeletion): an R-II witness `RII Dred (D_H.switch x)` on the actual
polygonal lifts together with `Dred.record ≅ D_L.record`. -/
theorem s7s_rii_witnesses (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q)
    (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) (W : s7s_SiteData hn hG hS q hx hy hxq hyq)
    (DL : Diagram) (hrec : s7s_hrec_prop hn hG hS q hx hy hxq hyq DL) :
    ∃ Dred : Diagram, RII Dred ((geoPositiveLift hn hG hS q).switch (s7s_lift hn hG hS q _ hxq)) ∧
      Nonempty (RecordIso Dred.record DL.record) := by
  obtain ⟨B, -, hBy, hBz⟩ := s7s_site hn hG hS q hx hy hxq hyq W
  refine s7_rii_witnesses _ _ B DL ?_
  rw [s7s_reducedRecord_eq B hBy hBz]
  exact hrec

/-- **sm-4:600-606 on the geo lift: `P (D_H.switch x) = P D_L`** (`s7g_switch_value_of_rii` with the
witnesses of `s7s_rii_witnesses`; equivalently `s7_switch_value_of_bigon`). -/
theorem s7s_switch_value (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q)
    (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) (W : s7s_SiteData hn hG hS q hx hy hxq hyq)
    (DL : Diagram) (hrec : s7s_hrec_prop hn hG hS q hx hy hxq hyq DL) :
    SM.P ((geoPositiveLift hn hG hS q).switch (s7s_lift hn hG hS q _ hxq)) = SM.P DL := by
  obtain ⟨Dred, hR, hrec'⟩ := s7s_rii_witnesses hn hG hS q hx hy hxq hyq W DL hrec
  exact s7g_switch_value_of_rii _ Dred DL _ hR hrec'

end S7SiteGlue

/-! #### s7s.5 Transport to the accepted `positiveLift` (`cornerHomfly`): `geoPositiveLift_eq_generic` -/

section S7SiteGeneric

open GeoCarrier RProof

omit [NeZero n] in
/-- a crossing carried along an equality of diagrams -/
def s7s_castCrossing {D D' : Diagram} (h : D = D') (x : D.Γ.Crossing) : D'.Γ.Crossing :=
  cast (by rw [h]) x

omit [NeZero n] in
theorem s7s_switch_castCrossing {D D' : Diagram} (h : D = D') (x : D.Γ.Crossing) :
    D'.switch (s7s_castCrossing h x) = D.switch x := by
  subst h; rfl

omit [NeZero n] in
theorem s7s_castCrossing_crossingPoint {D D' : Diagram} (h : D = D') (x : D.Γ.Crossing) :
    D'.Γ.crossingPoint (s7s_castCrossing h x) = D.Γ.crossingPoint x := by
  subst h; rfl

variable {P : LabelledTuple n} (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P))
  (hS : IsDecomposition hn hP S) (q : Component hn hP S)

/-- the tier-1 witness of an SM-generic polygon -/
abbrev s7s_cg : CarrierGeometry P := CarrierGeometry.ofGeneric hn hP

include hS in
/-- a decomposition is geo-independent (`geoIndependent_iff_isDecomposition`) -/
theorem s7s_geoIndependent : GeoIndependent (s7s_cg hn hP).cg S :=
  (geoIndependent_iff_isDecomposition hn hP S).mpr hS

/-- the geo carrier corresponding to the accepted carrier `q` -/
abbrev s7s_geoComp : GeoComponent (s7s_cg hn hP).cg S := (geoComponentEquivGeneric hn hP S).symm q

/-- the geo positive lift of `s7s_geoComp q` IS the accepted `positiveLift` of `q` -/
theorem s7s_geoPositiveLift_eq :
    geoPositiveLift hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) =
      positiveLift hn hP S q hS := by
  rw [geoPositiveLift_eq_generic hn hP S _ _ hS]
  simp only [s7s_geoComp, Equiv.apply_symm_apply]

variable {M a : ZMod n} (hx : IsCrossing P {M - 1, a}) (hy : IsCrossing P {a, M})

/-- the crossing of the accepted positive lift `positiveLift hn hP S q hS` at a retained crossing `c` -/
noncomputable def s7s_liftGen (c : Crossing P)
    (hc : c ∈ geoCarrierCrossings (s7s_cg hn hP).cg S (s7s_geoComp hn hP S q)) :
    (positiveLift hn hP S q hS).Γ.Crossing :=
  s7s_castCrossing (s7s_geoPositiveLift_eq hn hP S hS q)
    (s7s_lift hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) c hc)

theorem s7s_liftGen_crossingPoint (c : Crossing P)
    (hc : c ∈ geoCarrierCrossings (s7s_cg hn hP).cg S (s7s_geoComp hn hP S q)) :
    (positiveLift hn hP S q hS).Γ.crossingPoint (s7s_liftGen hn hP S hS q c hc) = crossingPoint c := by
  exact (s7s_castCrossing_crossingPoint (s7s_geoPositiveLift_eq hn hP S hS q)
    (s7s_lift hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) c hc)).trans
    (s7s_lift_crossingPoint hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) c hc)

/-- **sm-4:600-606 on the accepted lift: `P ((positiveLift q).switch x) = P D_L`.** -/
theorem s7s_switch_value_positiveLift
    (hxq : xPair hx ∈ geoCarrierCrossings (s7s_cg hn hP).cg S (s7s_geoComp hn hP S q))
    (hyq : xPair hy ∈ geoCarrierCrossings (s7s_cg hn hP).cg S (s7s_geoComp hn hP S q))
    (W : s7s_SiteData hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) hx hy hxq hyq)
    (DL : Diagram)
    (hrec : s7s_hrec_prop hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) hx hy hxq hyq DL) :
    SM.P ((positiveLift hn hP S q hS).switch (s7s_liftGen hn hP S hS q _ hxq)) = SM.P DL := by
  exact (congrArg SM.P (s7s_switch_castCrossing (s7s_geoPositiveLift_eq hn hP S hS q)
    (s7s_lift hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) _ hxq))).trans
    (s7s_switch_value hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) hx hy hxq hyq W DL hrec)

/-- **eq. s7c:universal-skein at the contact crossing with the R-II step done** — `s7g_cornerHomfly_skein`
with `P (D_H.switch x)` replaced by `P D_L`: `H⁺_Q = a⁻² P(D_L) + a⁻¹ z P(D_A)`, `D_A` the library
smoothing at `x` with record `D_H.record.smooth v`.  This is the input of U110-H/K (the two-component row
on `D_A`, `s7h_extraction_two_component`). -/
theorem s7s_cornerHomfly_skein
    (hxq : xPair hx ∈ geoCarrierCrossings (s7s_cg hn hP).cg S (s7s_geoComp hn hP S q))
    (hyq : xPair hy ∈ geoCarrierCrossings (s7s_cg hn hP).cg S (s7s_geoComp hn hP S q))
    (W : s7s_SiteData hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) hx hy hxq hyq)
    (DL : Diagram)
    (hrec : s7s_hrec_prop hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) hx hy hxq hyq DL)
    (v : (positiveLift hn hP S q hS).Γ.Visit) (hv : v.1 = s7s_liftGen hn hP S hS q _ hxq) :
    ∃ D₀ : Diagram, IsOrientedSmoothing (positiveLift hn hP S q hS) (s7s_liftGen hn hP S hS q _ hxq) D₀ ∧
      Nonempty (RecordIso D₀.record ((positiveLift hn hP S q hS).record.smooth v)) ∧
      cornerHomfly hn hP S q hS = R.aInv * R.aInv * SM.P DL + R.aInv * R.z * SM.P D₀ := by
  obtain ⟨D₀, -, hsm, hrec₀, hsk⟩ := s7g_cornerHomfly_skein hn hP S q hS _ v hv
  refine ⟨D₀, hsm, hrec₀, ?_⟩
  rw [hsk, s7s_switch_value_positiveLift hn hP S hS q hx hy hxq hyq W DL hrec]

end S7SiteGeneric

/-! #### s7s.7 Towards `hrec`: the record side (Site_174_REPORT §3 item 1) and the `carrierCrossings` reading -/

section S7SiteRecord

open GeoCarrier RProof

omit [NeZero n] in
/-- the bits of the restriction of a switched record agree with the unswitched ones when the switched
occurrence is DELETED (its crossing is not kept): `restrictCrossings` reads `isOver` only at retained
occurrences, none of which is `v` or `pair v` -/
theorem s7s_restrict_switch_deleted_bit (ρ : Record) (S : Set ρ.Crossing) (v : ρ.M)
    (hv : ¬ ρ.CrossKeep S v) (w : (ρ.restrictCrossings S).M) :
    (ρ.restrictCrossings S).isOver w = ((ρ.switch v).restrictCrossings S).isOver w := by
  have hw1 : w.1 ≠ v := fun h => hv (h ▸ w.2)
  have hw2 : w.1 ≠ ρ.pair v := fun h => by
    apply hv
    have h2 := w.2
    rw [h, ρ.crossKeep_pair_iff] at h2
    exact h2
  show ρ.isOver w.1 = (ρ.switch v).isOver w.1
  rw [Record.switch_isOver_of_ne ρ v hw1 hw2]

omit [NeZero n] in
theorem s7s_restrict_switch_deleted_sgn (ρ : Record) (S : Set ρ.Crossing) (v : ρ.M)
    (hv : ¬ ρ.CrossKeep S v) (w : (ρ.restrictCrossings S).M) :
    (ρ.restrictCrossings S).sgn w = ((ρ.switch v).restrictCrossings S).sgn w := by
  have hw1 : w.1 ≠ v := fun h => hv (h ▸ w.2)
  have hw2 : w.1 ≠ ρ.pair v := fun h => by
    apply hv
    have h2 := w.2
    rw [h, ρ.crossKeep_pair_iff] at h2
    exact h2
  show ρ.sgn w.1 = (ρ.switch v).sgn w.1
  rw [Record.switch_sgn_of_ne ρ v hw1 hw2]

omit [NeZero n] in
/-- **The DELETED-case companion of `Record.restrictCrossings_switch`** (Site_174_REPORT §3 item 1): when
the switched occurrence's crossing is not kept, restricting the switched record is restricting the
record — the switch of row 110 sits on the bigon crossing `x`, which the R-II deletion removes, so the
reduced record of `D_H.switch x` is the reduced record of `D_H` itself. -/
theorem s7s_restrictCrossings_switch_deleted (ρ : Record) (S : Set ρ.Crossing) (v : ρ.M)
    (hv : ¬ ρ.CrossKeep S v) :
    Nonempty (RecordIso ((ρ.switch v).restrictCrossings S) (ρ.restrictCrossings S)) :=
  ⟨RecordIso.mk (Equiv.refl _) (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun w => s7s_restrict_switch_deleted_bit ρ S v hv w)
    (fun w => s7s_restrict_switch_deleted_sgn ρ S v hv w)⟩

variable {P : LabelledTuple n} (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P))
  (hS : IsDecomposition hn hP S) (q : Component hn hP S)

/-- the site's membership hypotheses in the accepted `carrierCrossings` form -/
theorem s7s_mem_geoCarrierCrossings_iff (c : Crossing P) :
    c ∈ geoCarrierCrossings (s7s_cg hn hP).cg S (s7s_geoComp hn hP S q) ↔
      c ∈ carrierCrossings hn hP S q := by
  rw [geoCarrierCrossings_eq_generic hn hP S]
  simp only [s7s_geoComp, Equiv.apply_symm_apply]

include hS in
/-- the lifted crossing of the accepted lift IS the accepted `carrierCrossingEquiv` inverse at `c` -/
theorem s7s_liftGen_eq_carrierCrossingEquiv (c : Crossing P)
    (hc : c ∈ geoCarrierCrossings (s7s_cg hn hP).cg S (s7s_geoComp hn hP S q)) :
    s7s_liftGen hn hP S hS q c hc =
      (carrierCrossingEquiv hn hP S q hS).symm ⟨c, (s7s_mem_geoCarrierCrossings_iff hn hP S q c).mp hc⟩ := by
  apply (carrierShadow_generic hn hP S q hS).crossingPoint_injective
  refine (s7s_liftGen_crossingPoint hn hP S hS q c hc).trans ?_
  have h := crossingPoint_carrierCrossingEquiv hn hP S q hS
    ((carrierCrossingEquiv hn hP S q hS).symm ⟨c, (s7s_mem_geoCarrierCrossings_iff hn hP S q c).mp hc⟩)
  rw [Equiv.apply_symm_apply] at h
  exact h

end S7SiteRecord

/-! #### s7s.8 `hrec` reduced to the UNSWITCHED record: `D_H.record − {x, y} ≅ D_L.record` -/

section S7SiteHrec

open GeoCarrier RProof

omit [NeZero n] in
/-- the keep set "every crossing but `y₀, z₀`", read on the record of `D` itself -/
def s7s_keepOf (D : Diagram) (y₀ z₀ : D.Γ.Crossing) : Set D.record.Crossing :=
  {c | c ≠ D.record.crossingOf (D.overVisit y₀) ∧ c ≠ D.record.crossingOf (D.overVisit z₀)}

omit [NeZero n] in
/-- an occurrence has the record crossing of `x` iff it is a visit of `x` (U-M6's `key`) -/
theorem s7s_crossingOf_eq_iff_fst (D : Diagram) (x : D.Γ.Crossing) (w : D.Γ.Visit) :
    D.record.crossingOf w = D.record.crossingOf (D.overVisit x) ↔ w.1 = x := by
  rw [Record.crossingOf_eq_iff]
  show w ∈ ({D.overVisit x, D.record.pair (D.overVisit x)} : Finset D.Γ.Visit) ↔ _
  rw [D.record_pair_apply, D.mem_pair_twin_iff]
  rfl

omit [NeZero n] in
/-- **`hrec` needs only the UNSWITCHED identification.**  The reduced record of `D.switch x` (the four
occurrences of `x, y` deleted) is isomorphic to the record of `D` minus `{x, y}`: `Diagram.switchRecordIso`
(the identity on occurrences) transports `restrictCrossings` (`CB.restrictCrossings_iso_of_recordIso`),
and the switch sits on the DELETED crossing `x` (`s7s_restrictCrossings_switch_deleted`).  So the record
identification of row 110 is the persistent-visit transport `D_H.record − {x, y} ≅ D_L.record` of U110-A,
with no switch involved. -/
theorem s7s_hrec_of_unswitched (D : Diagram) (x y : D.Γ.Crossing) (v : D.Γ.Visit) (hv : v.1 = x)
    (DL : Diagram)
    (h : Nonempty (RecordIso (D.record.restrictCrossings (s7s_keepOf D x y)) DL.record)) :
    Nonempty (RecordIso (s7s_reducedRecordOf (D.switch x) x y) DL.record) := by
  obtain ⟨κ⟩ := h
  have hX : ∀ w : (D.switch x).record.M,
      (D.switch x).record.crossingOf w ∈
          ({c | c ≠ (D.switch x).record.crossingOf ((D.switch x).overVisit x) ∧
            c ≠ (D.switch x).record.crossingOf ((D.switch x).overVisit y)} : Set (D.switch x).record.Crossing) ↔
        (D.record.switch v).crossingOf ((Diagram.switchRecordIso D x v hv).Φ w) ∈
          (s7s_keepOf D x y : Set (D.record.switch v).Crossing) := by
    intro w
    show ((D.switch x).record.crossingOf w ≠ (D.switch x).record.crossingOf ((D.switch x).overVisit x) ∧
        (D.switch x).record.crossingOf w ≠ (D.switch x).record.crossingOf ((D.switch x).overVisit y)) ↔
      (D.record.crossingOf w ≠ D.record.crossingOf (D.overVisit x) ∧
        D.record.crossingOf w ≠ D.record.crossingOf (D.overVisit y))
    exact and_congr
      (not_congr ((s7s_crossingOf_eq_iff_fst (D.switch x) x w).trans
        (s7s_crossingOf_eq_iff_fst D x w).symm))
      (not_congr ((s7s_crossingOf_eq_iff_fst (D.switch x) y w).trans
        (s7s_crossingOf_eq_iff_fst D y w).symm))
  obtain ⟨ι₁⟩ := CB.restrictCrossings_iso_of_recordIso (Diagram.switchRecordIso D x v hv) _ _ hX
  have hv' : ¬ D.record.CrossKeep (s7s_keepOf D x y) v := by
    intro hk
    have hk' : D.record.crossingOf v ≠ D.record.crossingOf (D.overVisit x) ∧
        D.record.crossingOf v ≠ D.record.crossingOf (D.overVisit y) := hk
    exact hk'.1 ((s7s_crossingOf_eq_iff_fst D x v).mpr hv)
  obtain ⟨ι₂⟩ := s7s_restrictCrossings_switch_deleted D.record (s7s_keepOf D x y) v hv'
  exact ⟨ι₁.trans (ι₂.trans κ)⟩

variable {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CarrierGeometry P)
  {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)
  {M a : ZMod n} (hx : IsCrossing P {M - 1, a}) (hy : IsCrossing P {a, M})

/-- **`s7s_hrec_prop` from the unswitched identification** `D_H.record − {x, y} ≅ D_L.record`
(the U110-A persistent-visit transport, `s7a_cross` / `s7a_between_map` / `s7a_side_sgn` on the retained
crossings of the full contact carrier — the remaining content of `hrec`, W3_SITE_REPORT.md §3). -/
theorem s7s_hrec_prop_of_unswitched (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q)
    (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) (DL : Diagram)
    (h : Nonempty (RecordIso ((geoPositiveLift hn hG hS q).record.restrictCrossings
      (s7s_keepOf (geoPositiveLift hn hG hS q) (s7s_lift hn hG hS q _ hxq) (s7s_lift hn hG hS q _ hyq)))
      DL.record)) :
    s7s_hrec_prop hn hG hS q hx hy hxq hyq DL :=
  s7s_hrec_of_unswitched (geoPositiveLift hn hG hS q) _ _
    ((geoPositiveLift hn hG hS q).overVisit (s7s_lift hn hG hS q _ hxq))
    ((geoPositiveLift hn hG hS q).overVisit_fst _) DL h

end S7SiteHrec

/-! #### s7s.9 The `corner` field from window clause (2): the block of `x`'s leg visit ends at the vertex `M` -/

section S7SiteBlocks

open GeoCarrier RProof

variable {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CarrierGeometry P)
  {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)
  {M a : ZMod n} (hx : IsCrossing P {M - 1, a})

omit [NeZero n] in
/-- a visit is determined by its crossing and its edge -/
theorem s7s_visit_ext {v w : Visit P} (h1 : v.1 = w.1) (h2 : v.2.val = w.2.val) : v = w := by
  rcases v with ⟨c, i, hi⟩
  rcases w with ⟨c', i', hi'⟩
  change c = c' at h1
  subst h1
  change i = i' at h2
  subst h2
  rfl

/-- the smoothing successor of an UNSELECTED visit is its mark successor -/
theorem s7s_smoothingSuccessor_of_not_mem (hP : CrossingGeometry P) (v : Visit P) (hv : v.1 ∉ S) :
    geoSmoothingSuccessor hP S (Sum.inr v) = geoMarkSuccessor hP (Sum.inr v) := by
  rw [geoSmoothingSuccessor_apply, selectedMarkPerm_visit, selectedVisitTwin_of_not_mem S v hv]

include hn in
/-- the mark successor of the LAST visit on its edge is the next vertex
(`geoMarkSuccessor_position_cases`: the alternative "same edge, larger parameter" is excluded) -/
theorem s7s_markSuccessor_last (hP : CrossingGeometry P) (v : Visit P)
    (hlast : ∀ w : Visit P, w.2.val = v.2.val → w ≠ v → visitParameter w < visitParameter v) :
    geoMarkSuccessor hP (Sum.inr v) = Sum.inl (v.2.val + 1) := by
  rcases geoMarkSuccessor_position_cases hn hP (Sum.inr v) with ⟨hedge, hlt⟩ | h
  · exfalso
    rcases hsucc : geoMarkSuccessor hP (Sum.inr v) with j | w
    · rw [hsucc] at hlt
      have h0 : (geoMarkPosition hP (Sum.inl j)).2.val = 0 := rfl
      have hge : 0 ≤ (geoMarkPosition hP (Sum.inr v)).2.val :=
        (geoMarkPosition hP (Sum.inr v)).2.property.1
      rw [h0] at hlt
      linarith
    · rw [hsucc] at hedge hlt
      have hw_edge : w.2.val = v.2.val := hedge
      have hlt' : visitParameter v < visitParameter w := hlt
      have hwv : w ≠ v := by
        intro h
        subst h
        exact lt_irrefl _ hlt'
      have := hlast w hw_edge hwv
      linarith
  · exact h

include hn in
/-- **`corner` (mark form), PROVED from window clause (2)**: the corner after the carrier edge of `x`'s leg
visit is the vertex mark `inl M`.  The leg visit `v = G11_vef hx` (on `M−1`, unselected) is the `r`-th mark
of the block of its carrier edge `j` (`gu1_carrierEdge_block`); the block ends at the corner `j + 1` after
`m` steps (`geoCornerPolygon_block`); the smoothing successor of `v` is its mark successor
(`s7s_smoothingSuccessor_of_not_mem`), which is the vertex `inl M` because `v` is the last visit on `M−1`
(`s7s_markSuccessor_last`); a vertex is a true corner, so `r + 1 = m`. -/
theorem s7s_cornerMark_of_wall
    (h2 : ∀ w : Visit P, w.2.val = M - 1 → w.1 ≠ xPair hx → visitParameter w < visitParameter (G11_vef hx))
    (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q) :
    geoCornerMark hG.cg S q (G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1) = Sum.inl M := by
  have hvS : (G11_vef hx).1 ∉ S := ((mem_geoCarrierCrossings hG.cg S q (G11_vef hx).1).mp hxq).1
  obtain ⟨r, hr1, hρr, hbr, -, -⟩ := gu1_carrierEdge_block hn hG hS q (G11_vef hx) hxq
  obtain ⟨m, hm1, hρm, hint, -, -, -, -, -⟩ :=
    geoCornerPolygon_block hn hG.cg hS q (G11_carrierEdge hn hG hS q (G11_vef hx) hxq)
  have hsucc : geoSmoothingSuccessor hG.cg S (Sum.inr (G11_vef hx)) = Sum.inl M := by
    rw [s7s_smoothingSuccessor_of_not_mem hG.cg (G11_vef hx) hvS,
      s7s_markSuccessor_last hn hG.cg (G11_vef hx) ?_]
    · show Sum.inl (M - 1 + 1) = Sum.inl M
      rw [sub_add_cancel]
    · intro w hw hwv
      refine h2 w hw ?_
      intro hw1
      exact hwv (s7s_visit_ext hw1 hw)
  have hρr1 : (geoSmoothingSuccessor hG.cg S ^ (r + 1))
      (geoCornerMark hG.cg S q (G11_carrierEdge hn hG hS q (G11_vef hx) hxq)) = Sum.inl M := by
    rw [pow_succ', Equiv.Perm.mul_apply, hρr, hsucc]
  have hrm : r < m := by
    by_contra hle
    obtain ⟨w, hw, hwS, -⟩ := hbr m hm1 (not_lt.mp hle)
    have hc := isTrueCorner_geoCornerMark hG.cg S q (G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1)
    rw [← hρm, hw] at hc
    exact hwS ((isTrueCorner_visit S w).mp hc)
  have hr1m : r + 1 = m := by
    by_contra hne
    have hlt : r + 1 < m := by omega
    obtain ⟨w, hw, -, -⟩ := hint (r + 1) (by omega) hlt
    rw [hρr1] at hw
    exact Sum.inl_ne_inr hw
  rw [← hρm, ← hr1m, hρr1]

include hn in
/-- **`corner` of `s7s_SiteData`, PROVED**: `geoCornerPolygon (j_in + 1) = P M`. -/
theorem s7s_cornerPolygon_of_wall
    (h2 : ∀ w : Visit P, w.2.val = M - 1 → w.1 ≠ xPair hx → visitParameter w < visitParameter (G11_vef hx))
    (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q) :
    geoCornerPolygon hG.cg S q (G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1) = P M := by
  rw [geoCornerPolygon_apply, s7s_cornerMark_of_wall hn hG hS q hx h2 hxq,
    geoMarkPosition_evaluation_vertex]

include hn in
/-- **window clause (3) ⇒ the mark successor of the vertex `M` is `y`'s `M`-visit.**  By
`geoMarkSuccessor_position_cases` the successor is a visit `u` on `M` with parameter `> 0` or the vertex
`M + 1`; in either case, if it is not `y`'s visit `w`, then `w` (parameter in `(0, 1)`, and `< param u`
by (3)) lies strictly between `inl M` and the successor in the traversal order — against
`geoMarkSuccessor_no_mark_between` (key arithmetic, including the wrap `(M+1).val = 0`). -/
theorem s7s_markSuccessor_vertex_first (hy : IsCrossing P {a, M})
    (h3 : ∀ w : Visit P, w.2.val = M → w.1 ≠ xPair hy →
      visitParameter (G11_vgf hy) < visitParameter w) :
    geoMarkSuccessor hG.cg (Sum.inl M) = Sum.inr (G11_vgf hy) := by
  have hw0 : 0 < visitParameter (G11_vgf hy) :=
    (crossingParameter_interior_of_geometry hG.cg (xPair hy) M (mem_pair_right a M)).1
  have hw1 : visitParameter (G11_vgf hy) < 1 :=
    (crossingParameter_interior_of_geometry hG.cg (xPair hy) M (mem_pair_right a M)).2
  have hnb := geoMarkSuccessor_no_mark_between hG.cg (Sum.inl M) (Sum.inr (G11_vgf hy))
  have k0 : traversalKey (geoMarkPosition hG.cg (Sum.inl M)) = (M.val : ℝ) := by
    show ((M.val : ℕ) : ℝ) + 0 = _
    rw [add_zero]
  have kw : traversalKey (geoMarkPosition hG.cg (Sum.inr (G11_vgf hy))) =
      (M.val : ℝ) + visitParameter (G11_vgf hy) := rfl
  rcases geoMarkSuccessor_position_cases hn hG.cg (Sum.inl M) with ⟨hedge, hlt⟩ | h
  · rcases hsucc : geoMarkSuccessor hG.cg (Sum.inl M) with j | u
    · exfalso
      rw [hsucc] at hlt
      have h0 : (geoMarkPosition hG.cg (Sum.inl j)).2.val = 0 := rfl
      have h0' : (geoMarkPosition hG.cg (Sum.inl M)).2.val = 0 := rfl
      rw [h0, h0'] at hlt
      exact lt_irrefl _ hlt
    · rw [hsucc] at hedge hlt hnb
      have hu_edge : u.2.val = M := hedge
      have hu_pos : 0 < visitParameter u := hlt
      by_contra hne
      have hne' : u ≠ G11_vgf hy := fun h => hne (by rw [h])
      have hu1 : u.1 ≠ xPair hy := fun h => hne' (s7s_visit_ext h hu_edge)
      have hlt3 := h3 u hu_edge hu1
      have ku : traversalKey (geoMarkPosition hG.cg (Sum.inr u)) = (M.val : ℝ) + visitParameter u := by
        show ((u.2.val.val : ℕ) : ℝ) + visitParameter u = _
        rw [hu_edge]
      apply hnb
      have hpr : traversalKey (geoMarkPosition hG.cg (Sum.inl M)) <
          traversalKey (geoMarkPosition hG.cg (Sum.inr u)) := by
        rw [k0, ku]; linarith
      rw [traversalBetween_of_key_lt hpr, k0, kw, ku]
      constructor <;> linarith
  · exfalso
    have hM1 : (geoMarkPosition hG.cg (Sum.inl M)).1 = M := rfl
    rw [h, hM1] at hnb
    apply hnb
    have : Fact (1 < n) := ⟨by omega⟩
    have hval : (M + 1).val = (M.val + 1) % n := by rw [ZMod.val_add, ZMod.val_one]
    have hMlt : M.val < n := ZMod.val_lt M
    have k1 : traversalKey (geoMarkPosition hG.cg (Sum.inl (M + 1))) = (((M + 1).val : ℕ) : ℝ) := by
      show (((M + 1).val : ℕ) : ℝ) + 0 = _
      rw [add_zero]
    unfold traversalBetween
    rw [k0, kw, k1]
    by_cases hlt : M.val + 1 < n
    · rw [hval, Nat.mod_eq_of_lt hlt]
      left
      constructor
      · linarith
      · push_cast; linarith
    · have hn' : M.val + 1 = n := by omega
      rw [hval, hn', Nat.mod_self]
      right; right
      have h2M : 2 ≤ M.val := by omega
      have h2M' : (2 : ℝ) ≤ (M.val : ℝ) := by exact_mod_cast h2M
      constructor
      · push_cast; linarith
      · linarith

include hn in
/-- **`jout` of `s7s_SiteData`, PROVED from window clauses (2), (3)**: the carrier edge of `y`'s `M`-visit
is the successor of that of `x`'s `(M−1)`-visit.  The block opening at the corner `j_in + 1 = inl M`
(`s7s_cornerMark_of_wall`) has `y`'s `M`-visit as its first mark (`s7s_markSuccessor_vertex_first`,
unselected, on the out-slot edge `M`), so `GeoBlockInterior (j_in + 1) 1`; block uniqueness
`geo_block_mark_eq` against `gu1_carrierEdge_block` at `y`'s visit gives the edge. -/
theorem s7s_jout_of_wall (hy : IsCrossing P {a, M})
    (h2 : ∀ w : Visit P, w.2.val = M - 1 → w.1 ≠ xPair hx → visitParameter w < visitParameter (G11_vef hx))
    (h3 : ∀ w : Visit P, w.2.val = M → w.1 ≠ xPair hy →
      visitParameter (G11_vgf hy) < visitParameter w)
    (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q) (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) :
    G11_carrierEdge hn hG hS q (G11_vgf hy) hyq = G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1 := by
  have hk := s7s_cornerMark_of_wall hn hG hS q hx h2 hxq
  have hsucc := s7s_markSuccessor_vertex_first hn hG hy h3
  have hwS : (G11_vgf hy).1 ∉ S := ((mem_geoCarrierCrossings hG.cg S q (G11_vgf hy).1).mp hyq).1
  have hbk : GeoBlockInterior hG.cg S q (G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1) 1 := by
    intro i h1 hi
    have hi1 : i = 1 := le_antisymm hi h1
    subst hi1
    refine ⟨G11_vgf hy, ?_, hwS, ?_⟩
    · rw [pow_one, hk, geoSmoothingSuccessor_vertex, hsucc]
    · rw [hk]; rfl
  obtain ⟨r', -, hρ', hb', -, -⟩ := gu1_carrierEdge_block hn hG hS q (G11_vgf hy) hyq
  have h := geo_block_mark_eq hG.cg S q hbk hb'
    (by rw [pow_one, hk, geoSmoothingSuccessor_vertex, hsucc, hρ'])
  exact h.1.symm

end S7SiteBlocks

/-! #### s7s.10 The wall data (U110-A/B): the `P`-level form, the sign condition, the assembly, the two black boxes -/

section S7SiteWall

open GeoCarrier RProof

/-- **The `P`-level wall data of the bigon side** (sm-4:407-447, 618-620; lem:wall-sides (V) window clauses):
(1) every edge other than `M−1`, `M`, `a` misses the closed contact triangle `conv{x, P M, y}`; (2) `x`'s
visit is the LAST visit on the edge `M−1` (the window `(x, M]` is empty); (3) `y`'s visit is the FIRST on
the edge `M` (the window `[M, y)` is empty); (4) no visit lies strictly between the two contact visits on
`a`.  Consumed by `s7s_siteData_of_wall`. -/
def s7s_WallTriangleData (P : LabelledTuple n) (M a : ZMod n) (hx : IsCrossing P {M - 1, a})
    (hy : IsCrossing P {a, M}) : Prop :=
  (∀ e : ZMod n, e ≠ M - 1 → e ≠ M → e ≠ a → Disjoint (edgeSegment P e) (s7s_K hx hy)) ∧
  (∀ w : Visit P, w.2.val = M - 1 → w.1 ≠ xPair hx → visitParameter w < visitParameter (G11_vef hx)) ∧
  (∀ w : Visit P, w.2.val = M → w.1 ≠ xPair hy → visitParameter (G11_vgf hy) < visitParameter w) ∧
  (∀ w : Visit P, w.2.val = a →
    ¬ (visitParameter (G11_vfe hx) < visitParameter w ∧ visitParameter w < visitParameter (G11_vfg hy)) ∧
    ¬ (visitParameter (G11_vfg hy) < visitParameter w ∧ visitParameter w < visitParameter (G11_vfe hx)))

variable {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CarrierGeometry P)
  {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)
  {M a : ZMod n} (hx : IsCrossing P {M - 1, a}) (hy : IsCrossing P {a, M})

omit [NeZero n] in
/-- **The contact sign condition of the site, PROVED from the planar geometry** (no wall data): at a
vertex–edge contact where both edges `M−1`, `M` cross the edge `a`, the vertex `P M` lies on one side of
the line of `a` and `P (M−1)`, `P (M+1)` on the other, so the two contact crossing signs alternate:
`(1 − t_x) det(E_{M−1}, E_a) = t_y det(E_a, E_M)` with `0 < 1 − t_x`, `0 < t_y` (`det(E_a, P M − x) =
det(E_a, P M − y)` since `x, y` lie on the line of `a`). -/
theorem s7s_contact_sign {P : LabelledTuple n} (hP : CrossingGeometry P) {M a : ZMod n}
    (hx : IsCrossing P {M - 1, a}) (hy : IsCrossing P {a, M}) :
    crossingSign P (M - 1) a = crossingSign P a M := by
  have hxin : M - 1 ∈ (xPair hx).val := mem_pair_left _ _
  have hxa : a ∈ (xPair hx).val := mem_pair_right _ _
  have hya : a ∈ (xPair hy).val := mem_pair_left _ _
  have hyM : M ∈ (xPair hy).val := mem_pair_right _ _
  obtain ⟨-, htx1⟩ := crossingParameter_interior_of_geometry hP (xPair hx) (M - 1) hxin
  obtain ⟨hty0, -⟩ := crossingParameter_interior_of_geometry hP (xPair hy) M hyM
  set tx := crossingParameter (xPair hx) (M - 1) hxin with htx
  set ty := crossingParameter (xPair hy) M hyM with hty
  set rx := crossingParameter (xPair hx) a hxa with hrx
  set ry := crossingParameter (xPair hy) a hya with hry
  have ex : crossingPoint (xPair hx) = edgePoint P (M - 1) tx := gu2_xpt _ _ hxin
  have ex' : crossingPoint (xPair hx) = edgePoint P a rx := gu2_xpt _ _ hxa
  have ey : crossingPoint (xPair hy) = edgePoint P M ty := gu2_xpt _ _ hyM
  have ey' : crossingPoint (xPair hy) = edgePoint P a ry := gu2_xpt _ _ hya
  have hM1 : P M = edgePoint P (M - 1) 1 := by rw [edgePoint_one, sub_add_cancel]
  have hM0 : P M = edgePoint P M 0 := (edgePoint_zero P M).symm
  have e1 : P M - crossingPoint (xPair hx) = (1 - tx) • edge P (M - 1) := by
    rw [hM1, ex, gu2_edgePoint_sub]
  have e2 : P M - crossingPoint (xPair hy) = (0 - ty) • edge P M := by
    rw [hM0, ey, gu2_edgePoint_sub]
  have e3 : crossingPoint (xPair hy) - crossingPoint (xPair hx) = (ry - rx) • edge P a := by
    rw [ey', ex', gu2_edgePoint_sub]
  have key : det (edge P a) (P M - crossingPoint (xPair hx)) =
      det (edge P a) (P M - crossingPoint (xPair hy)) := by
    have hsplit : P M - crossingPoint (xPair hx) =
        (P M - crossingPoint (xPair hy)) + (crossingPoint (xPair hy) - crossingPoint (xPair hx)) := by
      abel
    rw [hsplit, det_add_right, e3, det_smul_self, add_zero]
  rw [e1, e2, det_smul_right, det_smul_right] at key
  have h1 : 0 < 1 - tx := by linarith
  have hA : det (edge P (M - 1)) (edge P a) = -det (edge P a) (edge P (M - 1)) :=
    det_swap (edge P a) (edge P (M - 1))
  have key' : (1 - tx) * det (edge P (M - 1)) (edge P a) = ty * det (edge P a) (edge P M) := by
    rw [hA]; linear_combination -key
  unfold crossingSign
  calc SignType.sign (det (edge P (M - 1)) (edge P a))
      = SignType.sign ((1 - tx) * det (edge P (M - 1)) (edge P a)) := by
        rw [sign_mul, sign_pos h1, one_mul]
    _ = SignType.sign (ty * det (edge P a) (edge P M)) := by rw [key']
    _ = SignType.sign (det (edge P a) (edge P M)) := by rw [sign_mul, sign_pos hty0, one_mul]

/-- **BLACK BOX (this unit's own remaining content; NOT proved).**  Clearance of the carrier edges that lie
on one of the three LOCAL `P`-edges `M−1`, `M`, `a` and are not the local piece itself (`jout`, `corner`,
`sgn`, `adj_s` and the non-local part of `clear` are PROVED).  Route, per edge: a point of the carrier edge
`h` in `K` lies on the `P`-edge (`gu2_edgeSegment_sub`) and on a side line of the triangle, hence on that side
(`RProof.gu2_mem_segment_ab_of_line`-type barycentric lemma), i.e. at a parameter in `[t_x, 1]` (edge `M−1`),
`[0, t_y]` (edge `M`), between `r_x, r_y` (edge `a`); the block `h = [c_h, c_{h+1}]` (`geoCornerPolygon_block`:
a positive multiple of `edge P e`, incoming edge `e` at `c_{h+1}`) has true-corner ends that are selected visits
on `e` (the vertex end would force `h = j_in` / `h = j_in + 1` by `geoCornerMark_injective` and
`s7s_cornerMark_of_wall`), whose parameters the window clauses (2)/(3) put below `t_x` / above `t_y`, and
whose parameter range cannot straddle `(r_x, r_y)` without a mark strictly between the two contact visits
(4) or containing them (then `h = j_s` by `geo_block_mark_eq`).  Estimate 300-450 lines (the `a`-edge case is
the long one). -/
theorem s7s_clear_local (hW : s7s_WallTriangleData P M a hx hy)
    (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q) (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q)
    (h : ZMod (geoCornerCount hG.cg S q)) (h1 : h ≠ G11_carrierEdge hn hG hS q (G11_vef hx) hxq)
    (h2 : h ≠ G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1)
    (h3 : h ≠ G11_carrierEdge hn hG hS q (G11_vfe hx) hxq)
    (he : (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = M - 1 ∨
      (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = M ∨
      (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = a) :
    Disjoint (edgeSegment (geoCornerPolygon hG.cg S q) h) (s7s_K hx hy) := by
  sorry

/-- **`clear` of `s7s_SiteData`**: the carrier edges on a NON-local `P`-edge are cleared by the `P`-level
clause (1) through `gu2_edgeSegment_sub` (PROVED); the local ones are the black box `s7s_clear_local`. -/
theorem s7s_carrier_data_of_wall (hW : s7s_WallTriangleData P M a hx hy)
    (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q) (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) :
    ∀ h : ZMod (geoCornerCount hG.cg S q), h ≠ G11_carrierEdge hn hG hS q (G11_vef hx) hxq →
      h ≠ G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1 → h ≠ G11_carrierEdge hn hG hS q (G11_vfe hx) hxq →
      Disjoint (edgeSegment (geoCornerPolygon hG.cg S q) h) (s7s_K hx hy) := by
  intro h h1 h2 h3
  by_cases he : (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = M - 1 ∨
      (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = M ∨
      (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = a
  · exact s7s_clear_local hn hG hS q hx hy hW hxq hyq h h1 h2 h3 he
  · have hne1 : (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 ≠ M - 1 := fun h' => he (Or.inl h')
    have hne2 : (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 ≠ M := fun h' => he (Or.inr (Or.inl h'))
    have hne3 : (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 ≠ a := fun h' => he (Or.inr (Or.inr h'))
    exact (hW.1 _ hne1 hne2 hne3).mono_left (gu2_edgeSegment_sub hn hG hS q h)

/-- The bundled site data from the `P`-level wall data: `adj_s` is the window clause (4) verbatim, `sgn` is
`s7s_contact_sign`, `corner` is `s7s_cornerPolygon_of_wall`, `jout` is `s7s_jout_of_wall`, and `clear` is `s7s_carrier_data_of_wall` (non-local edges proved; local edges = the black box `s7s_clear_local`). -/
theorem s7s_siteData_of_wall (hW : s7s_WallTriangleData P M a hx hy)
    (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q) (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) :
    s7s_SiteData hn hG hS q hx hy hxq hyq := by
  exact ⟨s7s_jout_of_wall hn hG hS q hx hy hW.2.1 hW.2.2.1 hxq hyq,
    s7s_cornerPolygon_of_wall hn hG hS q hx hW.2.1 hxq, hW.2.2.2,
    s7s_contact_sign hG.cg hx hy, s7s_carrier_data_of_wall hn hG hS q hx hy hW hxq hyq⟩

end S7SiteWall

/-- **BLACK BOX (U110-A/B wall data; NOT proved here).**  At a bigon wall (`g.BigonAt M a`), below some
radius, on the side whose polygon carries BOTH contact crossings `{M−1, a}`, `{a, M}` (the `H` side,
`VertexCrossingData`: `X(P₊) ∆ X(P₋) = {{a,M−1},{a,M}}`), the `P`-level wall data holds: (1) the closed
contact triangle is clear of the other edges (the printed emptiness sm-4:618-620, from
`ContactParameterWindows` + `contact_persistent_parameters_approach`), (2)-(4) the window clauses of
`VertexLocalData.visit_windows` / `InContactVisitWindow` (U_S7A_REPORT §1.7 `s7a_exists_sideLocal`).
Estimate 300-500 lines on the accepted `vertex_sides`. -/
theorem s7s_wallTriangleData_of_bigon (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n)
    (h : g.BigonAt M a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (b : Bool) (t : g.SideParameter), t.val < δ →
      ∀ (hx : IsCrossing (g.sideTuple b t).1 {M - 1, a}) (hy : IsCrossing (g.sideTuple b t).1 {a, M}),
        s7s_WallTriangleData (g.sideTuple b t).1 M a hx hy := by
  sorry

end S7Site


/-- The bigon branch (sm-4:407-874): two-newborn sector `B = (1−ε)J` (contact triangle: a crossing-free
uniform carrier, `corner_values_i`), universal skein extraction eq. s7c:universal-extraction (lp:core
skein, R-II deletion, oriented smoothing), lem:homflyrows two-component row, the rotation ledger, and the
two floor-dependent branches (interlacing: `Ω_H − Ω_L = −ω₁ω₂`; noninterlacing: every returned row zero,
the one-newborn rows by cb:singleton).  `a_floor` enters at the two half contact carriers (uniform for
`ε = 1`, one-dissent for `ε = 0`), read as carriers of the decompositions `T_i` of the generic halves
`λ_i` (sm-4:800-835); cb:singleton enters at the one-newborn rows (sm-4:777-783) — both printed
dependencies are explicit parameters. -/
theorem s7_bigon_law_at (hF : FloorTheoremData) (hsing : CbSingletonData) (hn : 3 ≤ n)
    (g : WallGerm n) (M a : ZMod n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  sorry


end VertexEdge

/-- **Row 110, conditional on thm:floor AND cb:singleton** (the printed dependency list of
tools/claims.py; library material).  PROVED from the two branch leaves: the wall is of bigon or sliding
type (`vertexEdge_bigon_or_sliding`); both side parameters are moved below the branch radius by chamber
constancy along each side (`cornerStateSum_side_eq`). -/
theorem thm_C_S7_of (hF : FloorTheoremData) (hsing : CbSingletonData) : CS7Data := by
  refine ⟨?_⟩
  intro n _ hn g M a h h₁ h₂ tp tm
  obtain ⟨δ, hδ, hlaw⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1).2.1 h₂) := by
    rcases g.vertexEdge_bigon_or_sliding h with hb | hs
    · exact s7_bigon_law_at hF hsing hn g M a hb h₁ h₂
    · exact s7_sliding_law_at hn g M a hs h₁ h₂
  have hr := g.radius_pos
  let t : g.SideParameter := ⟨min δ g.radius / 2, by
    constructor
    · have := lt_min hδ hr; linarith
    · have := min_le_right δ g.radius; linarith⟩
  have ht : t.val < δ := by
    show min δ g.radius / 2 < δ
    have := min_le_left δ g.radius; linarith
  rw [cornerStateSum_side_eq hn g true tp t, cornerStateSum_side_eq hn g false tm t]
  exact hlaw t ht

/-- **Row 110, conditional on the floor alone** (the row theorem `SM.thm_C_S7 := thm_C_S7_of_floor
SM.thm_floor` once row 100 lands). -/
theorem thm_C_S7_of_floor (hF : FloorTheoremData) : CS7Data :=
  thm_C_S7_of hF (cb_singleton_of_floor hF)


/-- Row 110 thm:C-S7 (FIXED target name, axiom-policy.json): the assembly on thm:floor (row 100). -/
theorem thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor

end

end SM
