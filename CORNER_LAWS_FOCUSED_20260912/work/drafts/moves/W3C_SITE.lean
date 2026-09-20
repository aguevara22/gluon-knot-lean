import SM.Smoothing
import SM.MarkedProducts
import SM.SingleCrossing
import CV.FullTwist
import RProof.GenericTransport
import SM.BigonDeletion
import RProof.RALedgers

/-! # The G11 core on a switched positive diagram (row 177 (4)) — Wave 3 skeleton (unit U-W3-0)

Skeleton written 2026-09-15 by the Wave-3 architect from `work/drafts/moves/Port_GenericTransportSw_draft.lean`
(the four FROZEN declarations `G11_ConfigSw`, `G11_core_sw_statement`, `G11_core_sw` (statement) and
`esc_switch_riii_of_chain` are byte-identical to the draft; `import SM.BigonDeletion` added).  Everything
else is new and `w3`-prefixed: the construction API of the switched G11 core (units (a)–(e) of
PLAN_FINAL.md §5 Wave 3, sub-leaves `w3a_*` … `w3e_*`), the PROVED assembly of `G11_core_sw` from the
sub-leaves, the row-level assembly `w3e_strong_case_sw`, and the row 177 (6) material (`w3g_*` the two
`j = 2` bigon sites on smoothing outputs, `w3h_*` the reduced-smoothed-record lemma).  Report:
`work/drafts/moves/W3_SKELETON_REPORT.md`.

**Structural finding (pre-review).**  Every lemma of the accepted `RProof.G11_Params` namespace
(GenericTransport.lean 235–8630: Units B–D, D8, E) is stated for `π : G11_Params C` with `C : G11_Config k`,
and `G11_Config.trans` (`¬ IsAlternating …`) is FALSE for a K3-side configuration (the over-order of the
positive lift is cyclic there — that is why row 177 switches `x` first).  Hence NO term of `G11_Config k`
exists for the 177 sites and the accepted shadow-level material (`X₀`, `X₁`, `M₀`, `M₁`, the disc, the arcs,
the move match, `exists_Ψ₀`, …) cannot be instantiated "verbatim" as PLAN §5 Wave 3 assumed.  The skeleton
therefore introduces the trans-free copy `G11_ParamsSw` and states, as sub-leaves, exactly the facts about
it that the switched instance needs; their proofs are copies of the accepted proofs (which never use `trans`
except in `gu6_htrans`, consumed only by `riii`).  Nothing under `work/lean` is touched.

Conventions: namespace `SM.Link`, `open RProof`; `w3a_` unit (a) (trans-free parametrisation, D8/E stated
for general local over data), `w3b_` unit (b) (switch transport, PROVED), `w3c_` unit (c) (D8′), `w3d_`
unit (d) (E′), `w3e_` unit (e) (A′ + F′ + the row-level assembly), `w3g_`/`w3h_` row 177 (6). -/

namespace SM.Link

open SM

noncomputable section

/-! ## 4. Row 177 (4): the RIII through the wall on a SWITCHED positive diagram (G11 generalised) -/

section RIIISw

open RProof

/-- **A triangle configuration with one switched local crossing** (row 177 (4): the `K3` over-order is
cyclic on the positive lift and becomes transitive after switching `x`).  `G11_Config` minus its
`trans` clause plus the switched pair and the transitivity of the SWITCHED over-order. -/
structure G11_ConfigSw (k : ℕ) [NeZero k] where
  hk : 3 ≤ k
  X : LabelledTuple k
  gen : (Shadow.single ⟨k, hk, X⟩).Generic
  m : ZMod k
  p : ZMod k
  q : ZMod k
  hmp : IsCrossing X {m, p}
  hmq : IsCrossing X {m, q}
  hpq : IsCrossing X {p, q}
  order : crossingParameter (xPair hmp) m (mem_pair_left m p) <
    crossingParameter (xPair hmq) m (mem_pair_left m q)
  clear_frontier : ∀ h : ZMod k, h ≠ m → h ≠ p → h ≠ q →
    ∀ x ∈ edgeSegment X h, x ∉ frontier (G11_triangle X hmp hmq hpq)
  clear_vertex : ∀ i : ZMod k, X i ∉ G11_triangle X hmp hmq hpq
  /-- which local pair is switched: `0 = {m,p}`, `1 = {m,q}`, `2 = {p,q}` -/
  sw : Fin 3
  /-- the switched over-order is transitive -/
  trans_sw : ¬ IsAlternating (if sw = 0 then -crossingSign X m p else crossingSign X m p)
    (if sw = 1 then -crossingSign X m q else crossingSign X m q)
    (if sw = 2 then -crossingSign X p q else crossingSign X p q)

namespace G11_ConfigSw

variable {k : ℕ} [NeZero k] (C : G11_ConfigSw k)

def comp : PolyComp := ⟨k, C.hk, C.X⟩

/-- the switched local crossing, read on the shadow -/
def xs : (Shadow.single C.comp).Crossing :=
  (Shadow.singleCrossingEquiv C.comp).symm
    (if C.sw = 0 then xPair C.hmp else if C.sw = 1 then xPair C.hmq else xPair C.hpq)

/-- `D₀^{sw}`: the positive diagram of `X` switched at the local crossing `xs` -/
def D₀sw : Diagram := ((Shadow.single C.comp).positiveDiagram C.gen).switch C.xs

theorem D₀sw_componentCount : C.D₀sw.componentCount = 1 := rfl

def vmp : Visit C.X := ⟨xPair C.hmp, ⟨C.m, mem_pair_left _ _⟩⟩
def vpm : Visit C.X := ⟨xPair C.hmp, ⟨C.p, mem_pair_right _ _⟩⟩
def vmq : Visit C.X := ⟨xPair C.hmq, ⟨C.m, mem_pair_left _ _⟩⟩
def vqm : Visit C.X := ⟨xPair C.hmq, ⟨C.q, mem_pair_right _ _⟩⟩
def vpq : Visit C.X := ⟨xPair C.hpq, ⟨C.p, mem_pair_left _ _⟩⟩
def vqp : Visit C.X := ⟨xPair C.hpq, ⟨C.q, mem_pair_right _ _⟩⟩

/-- the three adjacent transpositions of the RIII move (as `G11_Config.σ`) -/
def σ : Equiv.Perm (Visit C.X) :=
  Equiv.swap C.vmp C.vmq * (Equiv.swap C.vpm C.vpq * Equiv.swap C.vqm C.vqp)

def σD : Equiv.Perm C.D₀sw.Γ.Visit :=
  (Shadow.singleVisitEquiv C.comp).symm.permCongr C.σ

end G11_ConfigSw

/-- **G11 core on the switched diagram** (the statement of `RProof.G11_core_statement` with `D₀`
replaced by `D₀^{sw}`): a diagram `D₁` with the same HOMFLY and an occurrence bijection twisted by the
three transpositions.  Realisation (PLAN_FINAL §5 Wave 3): G11 Units B–D verbatim (shadow-level: `X₀`,
`X₁`, the disc, the arcs, the move match, the crossings inside `U`), D8 / Unit E / Unit F re-derived for
over data "positive except at `xs`" — after a statement-neutral refactor of D8/E to take the over data
of the six local visits as a parameter (DESIGN_A §2's process graft). -/
def G11_core_sw_statement {k : ℕ} [NeZero k] (C : G11_ConfigSw k) : Prop :=
  ∃ (D₁ : Diagram) (Ψ : C.D₀sw.Γ.Visit ≃ D₁.Γ.Visit),
    D₁.componentCount = 1 ∧
    homfly D₁ = homfly C.D₀sw ∧
    (∀ v, Ψ (C.D₀sw.twin v) = D₁.twin (Ψ v)) ∧
    (∀ v, D₁.overBit (Ψ v) = C.D₀sw.overBit v) ∧
    (∀ v, D₁.sign (Ψ v).1 = C.D₀sw.sign v.1) ∧
    (∀ u v w, D₁.VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔ C.D₀sw.VisitBetween (C.σD u) (C.σD v) (C.σD w))

/-! ## W3 — the construction API of the switched G11 core (units (a)–(e); inserted before the leaf)

### W3.0 Additive API of `G11_ConfigSw` (all PROVED): the unswitched `D₀`, the three local crossings
and six local occurrences of `D₀`, the closed-triangle clearance, and the switched over relations. -/

namespace G11_ConfigSw

variable {k : ℕ} [NeZero k] (C : G11_ConfigSw k)

/-- the UNSWITCHED positive diagram `D₀` of the configuration; `D₀sw = D₀.switch xs` by `rfl` -/
def D₀ : Diagram := (Shadow.single C.comp).positiveDiagram C.gen

theorem D₀sw_eq_switch : C.D₀sw = C.D₀.switch C.xs := rfl

theorem D₀_componentCount : C.D₀.componentCount = 1 := rfl

/-- the three local crossings of `D₀` (`{m,p}`, `{m,q}`, `{p,q}`) read on the shadow -/
def x_mp : C.D₀.Γ.Crossing := (Shadow.singleCrossingEquiv C.comp).symm (xPair C.hmp)
def x_mq : C.D₀.Γ.Crossing := (Shadow.singleCrossingEquiv C.comp).symm (xPair C.hmq)
def x_pq : C.D₀.Γ.Crossing := (Shadow.singleCrossingEquiv C.comp).symm (xPair C.hpq)

/-- the switched crossing is the local crossing selected by `sw` -/
theorem xs_eq : C.xs = if C.sw = 0 then C.x_mp else if C.sw = 1 then C.x_mq else C.x_pq := by
  unfold xs x_mp x_mq x_pq
  by_cases h0 : C.sw = 0
  · simp [h0]
  · by_cases h1 : C.sw = 1
    · simp [h1]
    · simp [h0, h1]

/-- the six local occurrences of `D₀` (`G11_Config.v_mp` … for the switched configuration) -/
def v_mp : C.D₀.Γ.Visit := (Shadow.singleVisitEquiv C.comp).symm C.vmp
def v_pm : C.D₀.Γ.Visit := (Shadow.singleVisitEquiv C.comp).symm C.vpm
def v_mq : C.D₀.Γ.Visit := (Shadow.singleVisitEquiv C.comp).symm C.vmq
def v_qm : C.D₀.Γ.Visit := (Shadow.singleVisitEquiv C.comp).symm C.vqm
def v_pq : C.D₀.Γ.Visit := (Shadow.singleVisitEquiv C.comp).symm C.vpq
def v_qp : C.D₀.Γ.Visit := (Shadow.singleVisitEquiv C.comp).symm C.vqp

theorem v_mp_fst : C.v_mp.1 = C.x_mp := RProof.G11_Params.gu6_sv_fst_eq _ _
theorem v_pm_fst : C.v_pm.1 = C.x_mp := RProof.G11_Params.gu6_sv_fst_eq _ _
theorem v_mq_fst : C.v_mq.1 = C.x_mq := RProof.G11_Params.gu6_sv_fst_eq _ _
theorem v_qm_fst : C.v_qm.1 = C.x_mq := RProof.G11_Params.gu6_sv_fst_eq _ _
theorem v_pq_fst : C.v_pq.1 = C.x_pq := RProof.G11_Params.gu6_sv_fst_eq _ _
theorem v_qp_fst : C.v_qp.1 = C.x_pq := RProof.G11_Params.gu6_sv_fst_eq _ _

/-- **Glue (PROVED, the copy of `G11_Config.clear_edge`): no other edge meets the closed triangle.** -/
theorem clear_edge : ∀ h : ZMod k, h ≠ C.m → h ≠ C.p → h ≠ C.q →
    ∀ x ∈ edgeSegment C.X h, x ∉ G11_triangle C.X C.hmp C.hmq C.hpq := by
  intro h hm hp hq x hx hxΔ
  obtain ⟨y, hy, hyF⟩ := G11_preconnected_meets_frontier (G11_edgeSegment_isPreconnected C.X h)
    ⟨x, hx, hxΔ⟩ ⟨C.X h, ⟨0, le_rfl, zero_le_one, (edgePoint_zero C.X h).symm⟩, C.clear_vertex h⟩
  exact C.clear_frontier h hm hp hq y hy hyF

/-- the three determinants of the configuration are nonzero (generic shadow) -/
theorem det_mp_ne : det (edge C.X C.m) (edge C.X C.p) ≠ 0 :=
  RProof.G11_Params.gu6_det_ne_zero_single C.gen C.hmp
theorem det_mq_ne : det (edge C.X C.m) (edge C.X C.q) ≠ 0 :=
  RProof.G11_Params.gu6_det_ne_zero_single C.gen C.hmq
theorem det_pq_ne : det (edge C.X C.p) (edge C.X C.q) ≠ 0 :=
  RProof.G11_Params.gu6_det_ne_zero_single C.gen C.hpq

/-- **The switched local over relations** ("`m` is over `p` on `D₀^{sw}`" etc.), as the Props fed to the
parametrised D8 (`w3a_riii_param`): the positive relation `0 < det`, flipped at the switched pair. -/
def Rmp_sw : Prop := (0 < det (edge C.X C.m) (edge C.X C.p)) ↔ C.sw ≠ 0
def Rmq_sw : Prop := (0 < det (edge C.X C.m) (edge C.X C.q)) ↔ C.sw ≠ 1
def Rpq_sw : Prop := (0 < det (edge C.X C.p) (edge C.X C.q)) ↔ C.sw ≠ 2

/-- **(c) The switched height order is transitive** — `trans_sw` read in the `gu6_htrans` form consumed
by the parametrised D8 (PROVED: case split on `sw` and on the three determinant signs). -/
theorem w3c_htrans_sw : ¬ (C.Rmp_sw ∧ C.Rpq_sw ∧ ¬ C.Rmq_sw) ∧ ¬ (¬ C.Rmp_sw ∧ ¬ C.Rpq_sw ∧ C.Rmq_sw) := by
  have hmp := C.det_mp_ne
  have hmq := C.det_mq_ne
  have hpq := C.det_pq_ne
  have ht := C.trans_sw
  unfold Rmp_sw Rmq_sw Rpq_sw
  unfold IsAlternating crossingSign at ht
  generalize C.sw = s at ht ⊢
  rcases lt_or_gt_of_ne hmp with h1 | h1 <;> rcases lt_or_gt_of_ne hmq with h2 | h2 <;>
    rcases lt_or_gt_of_ne hpq with h3 | h3 <;>
    simp only [sign_pos, sign_neg, h1, h2, h3, not_lt.mpr h1.le, not_lt.mpr h2.le, not_lt.mpr h3.le] at ht ⊢ <;>
    fin_cases s <;> simp at ht ⊢

end G11_ConfigSw
/-! ### W3-(a) The trans-free parameter structure `G11_ParamsSw` and the facts about it the switched
instance needs (sub-leaves `w3a_*`; each proof is a copy of the accepted `G11_Params` proof with
`G11_Config` → `G11_ConfigSw`, none of which uses `trans`). -/

/-- the centroid of the triangle (copy of `G11_centroid` for the switched configuration) -/
def G11_centroidSw {k : ℕ} [NeZero k] (C : G11_ConfigSw k) : Plane :=
  (1 / 3 : ℝ) • (crossingPoint (xPair C.hmp) + crossingPoint (xPair C.hmq) + crossingPoint (xPair C.hpq))

/-- the disc `U` (copy of `G11_discOf`) -/
def G11_discOfSw {k : ℕ} [NeZero k] (C : G11_ConfigSw k) (r : ℝ) : Set Plane :=
  (fun y => G11_centroidSw C + (1 + r) • (y - G11_centroidSw C)) '' G11_triangle C.X C.hmp C.hmq C.hpq

/-- **The parameters of the move for a switched configuration** — the fields of `RProof.G11_Params`
verbatim over `G11_ConfigSw` (no field mentions `trans`). -/
structure G11_ParamsSw {k : ℕ} [NeZero k] (C : G11_ConfigSw k) where
  t₁ : ℝ
  t₂ : ℝ
  t₃ : ℝ
  lam : ℝ
  r : ℝ
  ht₁ : 0 < t₁
  h₁ : t₁ < crossingParameter (xPair C.hmp) C.m (mem_pair_left _ _)
  h₂ : crossingParameter (xPair C.hmp) C.m (mem_pair_left _ _) < t₂
  h₃ : t₂ < crossingParameter (xPair C.hmq) C.m (mem_pair_left _ _)
  h₄ : crossingParameter (xPair C.hmq) C.m (mem_pair_left _ _) < t₃
  ht₃ : t₃ < 1
  hlam : 1 < lam
  hr : 0 < r
  theta_sub : convexHull ℝ {edgePoint C.X C.m t₁,
      edgePoint C.X C.m t₂ + lam • (crossingPoint (xPair C.hpq) - edgePoint C.X C.m t₂),
      edgePoint C.X C.m t₃} ⊆ interior (G11_discOfSw C r)
  disc_clear_edge : ∀ h : ZMod k, h ≠ C.m → h ≠ C.p → h ≠ C.q →
    ∀ x ∈ edgeSegment C.X h, x ∉ G11_discOfSw C r
  disc_clear_vertex : ∀ i : ZMod k, C.X i ∉ G11_discOfSw C r


/-! ### W3-A1 (unit BC): the trans-free copy of `RProof.GenericTransport` lines 235–4917 (Units B–C of the
accepted `G11_Params` namespace) over `G11_ConfigSw`, produced mechanically (`G11_Config → G11_ConfigSw`,
`G11_Params → G11_ParamsSw`, `G11_discOf → G11_discOfSw`, `G11_centroid → G11_centroidSw`); the `C`-free
helpers of the accepted namespace are NOT copied but reused by name through the scoped `open` below. -/

section W3A1Copy

open SM.GeoCarrier SM.Carrier

namespace G11_ParamsSw

variable {k : ℕ} [NeZero k] {C : G11_ConfigSw k} (π : G11_ParamsSw C)

open RProof.G11_Params (gu3_IsVisitIso gu3_adjacent_natCast_iff gu3_bool_eq_of_iff gu3_centroid_ball_subset gu3_cramer gu3_cramer_core gu3_crossingPoint_of_visitPt gu3_crossingPoint_symm gu3_cyc_of_not gu3_edgePoint_sub gu3_eq_twin_of_ne gu3_exists_visitEquiv gu3_homfly_of_reparam gu3_isOver_iff_det_pos gu3_lab_val gu3_mapPt_injective gu3_mapPt_under gu3_mem_convexHull_three gu3_other_congr gu3_overBit_of_visitPt gu3_overBit_pair gu3_pt_ext gu3_pt_of_eval_eq_crossingPoint gu3_remote_lab gu3_remote_natCast_iff gu3_remote_of_isCrossing gu3_subdiv_lab gu3_subdiv_lab_succ gu3_subdiv_mA gu3_subdiv_mB gu3_subdiv_mC gu3_subdiv_mD gu3_subdiv_mD_succ gu3_subdiv_natCast gu3_traversalBetween_iff gu3_twin_of_visitPt gu3_visitBetween_of_visitPt gu3_visit_ext gu4_cramer gu4_crossingPoint_mem_interior gu4_crossingPoint_mem_pair gu4_det_add_left gu4_det_add_right gu4_det_self gu4_det_smul_left gu4_det_smul_right gu4_det_sub_left gu4_det_sub_right gu4_eq_of_det_eq gu4_gen_regular gu4_gen_tail gu4_gen_trans gu4_gen_triple gu4_mem_edgeInterior_iff gu4_mem_edgeSegment_iff gu4_mem_edgeSegment_of_convex gu4_ne_of_remote gu4_remote_of_isCrossing gu4_sub_of_mem_edge gu5_both gu5_edgePoint_eq gu5_edgePoint_mem_segment gu5_edgeSegment_eq_segment gu5_entry gu5_exit gu5_pt_ext)


theorem hk₃ (_π : G11_ParamsSw C) : 3 ≤ k + 3 := by omega

/-- the subdivided polygon `X₀` -/
noncomputable def X₀ : LabelledTuple (k + 3) := G11_subdiv C.X C.m π.t₁ π.t₂ π.t₃

/-- the label of the middle new vertex `m₀` -/
def mid (_π : G11_ParamsSw C) : ZMod (k + 3) := ((C.m.val + 2 : ℕ) : ZMod (k + 3))

/-- the labels of the four pieces of `m` in `X₀`: `[X m, p_in]`, `[p_in, m₀]`, `[m₀, p_out]`, `[p_out, X (m+1)]` -/
def mA (_π : G11_ParamsSw C) : ZMod (k + 3) := (C.m.val : ZMod (k + 3))
def mB (_π : G11_ParamsSw C) : ZMod (k + 3) := ((C.m.val + 1 : ℕ) : ZMod (k + 3))
def mC (_π : G11_ParamsSw C) : ZMod (k + 3) := ((C.m.val + 2 : ℕ) : ZMod (k + 3))
def mD (_π : G11_ParamsSw C) : ZMod (k + 3) := ((C.m.val + 3 : ℕ) : ZMod (k + 3))

/-- the labels of `p`, `q` in `X₀` -/
def p' (_π : G11_ParamsSw C) : ZMod (k + 3) := G11_lab C.m C.p
def q' (_π : G11_ParamsSw C) : ZMod (k + 3) := G11_lab C.m C.q

/-- the apex `w = m₀ + λ (x_pq − m₀)` -/
noncomputable def apex : Plane :=
  edgePoint C.X C.m π.t₂ + π.lam • (crossingPoint (xPair C.hpq) - edgePoint C.X C.m π.t₂)

/-- the moved polygon `X₁`: `m₀` replaced by the apex -/
noncomputable def X₁ : LabelledTuple (k + 3) := Function.update π.X₀ π.mid π.apex

/-- the disc -/
noncomputable def U : Set Plane := G11_discOfSw C π.r

/-! ### Unit B leaves — the flat subdivision -/

/-! ### U3 helpers (Block A) — label arithmetic of the subdivision, the off-edge facts, and the
`appendVertex` chain `X ≅ shift (m+1) X → +p_in → +m₀ → +p_out ≅ X₀` -/

/-! #### the pieces of `m` in `X₀` -/

theorem gu3_X₀_mA : π.X₀ π.mA = C.X C.m := gu3_subdiv_mA C.X C.m π.t₁ π.t₂ π.t₃
theorem gu3_X₀_mB : π.X₀ π.mB = edgePoint C.X C.m π.t₁ := gu3_subdiv_mB C.X C.m π.t₁ π.t₂ π.t₃
theorem gu3_X₀_mC : π.X₀ π.mC = edgePoint C.X C.m π.t₂ := gu3_subdiv_mC C.X C.m π.t₁ π.t₂ π.t₃
theorem gu3_X₀_mD : π.X₀ π.mD = edgePoint C.X C.m π.t₃ := gu3_subdiv_mD C.X C.m π.t₁ π.t₂ π.t₃
theorem gu3_X₀_mD_succ : π.X₀ (π.mD + 1) = C.X (C.m + 1) :=
  gu3_subdiv_mD_succ C.X C.m π.t₁ π.t₂ π.t₃

theorem gu3_mA_add_one : π.mA + 1 = π.mB := (Nat.cast_add_one _).symm
theorem gu3_mB_add_one : π.mB + 1 = π.mC := by
  show ((C.m.val + 1 : ℕ) : ZMod (k + 3)) + 1 = ((C.m.val + 2 : ℕ) : ZMod (k + 3))
  push_cast
  ring
theorem gu3_mC_add_one : π.mC + 1 = π.mD := by
  show ((C.m.val + 2 : ℕ) : ZMod (k + 3)) + 1 = ((C.m.val + 3 : ℕ) : ZMod (k + 3))
  push_cast
  ring

theorem gu3_edge_mA : edge π.X₀ π.mA = π.t₁ • edge C.X C.m := by
  rw [edge, gu3_mA_add_one, gu3_X₀_mB, gu3_X₀_mA, edgePoint]
  abel
theorem gu3_edge_mB : edge π.X₀ π.mB = (π.t₂ - π.t₁) • edge C.X C.m := by
  rw [edge, gu3_mB_add_one, gu3_X₀_mC, gu3_X₀_mB, edgePoint, edgePoint, sub_smul]
  abel
theorem gu3_edge_mC : edge π.X₀ π.mC = (π.t₃ - π.t₂) • edge C.X C.m := by
  rw [edge, gu3_mC_add_one, gu3_X₀_mD, gu3_X₀_mC, edgePoint, edgePoint, sub_smul]
  abel
theorem gu3_edge_mD : edge π.X₀ π.mD = (1 - π.t₃) • edge C.X C.m := by
  rw [edge, gu3_X₀_mD_succ, gu3_X₀_mD, edgePoint, sub_smul, one_smul]
  simp only [edge]
  abel

theorem gu3_edgePoint_mB (s : ℝ) :
    edgePoint π.X₀ π.mB s = edgePoint C.X C.m (π.t₁ + s * (π.t₂ - π.t₁)) := by
  rw [edgePoint, gu3_X₀_mB, gu3_edge_mB, edgePoint, edgePoint, smul_smul, add_assoc, ← add_smul]
theorem gu3_edgePoint_mC (s : ℝ) :
    edgePoint π.X₀ π.mC s = edgePoint C.X C.m (π.t₂ + s * (π.t₃ - π.t₂)) := by
  rw [edgePoint, gu3_X₀_mC, gu3_edge_mC, edgePoint, edgePoint, smul_smul, add_assoc, ← add_smul]

theorem gu3_t₁_lt_t₂ : π.t₁ < π.t₂ := π.h₁.trans π.h₂
theorem gu3_t₂_lt_t₃ : π.t₂ < π.t₃ := π.h₃.trans π.h₄
theorem gu3_t₁_lt_one : π.t₁ < 1 := by linarith [π.gu3_t₁_lt_t₂, π.gu3_t₂_lt_t₃, π.ht₃]
theorem gu3_t₂_lt_one : π.t₂ < 1 := by linarith [π.gu3_t₂_lt_t₃, π.ht₃]

theorem gu3_mem_edgeSegment_mB {t : ℝ} (h1 : π.t₁ ≤ t) (h2 : t ≤ π.t₂) :
    edgePoint C.X C.m t ∈ edgeSegment π.X₀ π.mB := by
  have hpos : 0 < π.t₂ - π.t₁ := sub_pos.mpr π.gu3_t₁_lt_t₂
  refine ⟨(t - π.t₁) / (π.t₂ - π.t₁), div_nonneg (by linarith) hpos.le,
    (div_le_one hpos).mpr (by linarith), ?_⟩
  rw [gu3_edgePoint_mB, div_mul_cancel₀ _ hpos.ne']
  congr 1
  ring
theorem gu3_mem_edgeSegment_mC {t : ℝ} (h1 : π.t₂ ≤ t) (h2 : t ≤ π.t₃) :
    edgePoint C.X C.m t ∈ edgeSegment π.X₀ π.mC := by
  have hpos : 0 < π.t₃ - π.t₂ := sub_pos.mpr π.gu3_t₂_lt_t₃
  refine ⟨(t - π.t₂) / (π.t₃ - π.t₂), div_nonneg (by linarith) hpos.le,
    (div_le_one hpos).mpr (by linarith), ?_⟩
  rw [gu3_edgePoint_mC, div_mul_cancel₀ _ hpos.ne']
  congr 1
  ring
theorem gu3_edgeSegment_mB_subset : edgeSegment π.X₀ π.mB ⊆ edgeSegment C.X C.m := by
  rintro x ⟨s, hs0, hs1, rfl⟩
  rw [gu3_edgePoint_mB]
  have h12 := π.gu3_t₁_lt_t₂
  refine ⟨_, ?_, ?_, rfl⟩
  · nlinarith [π.ht₁]
  · nlinarith [π.gu3_t₂_lt_one]
theorem gu3_edgeSegment_mC_subset : edgeSegment π.X₀ π.mC ⊆ edgeSegment C.X C.m := by
  rintro x ⟨s, hs0, hs1, rfl⟩
  rw [gu3_edgePoint_mC]
  have h23 := π.gu3_t₂_lt_t₃
  refine ⟨_, ?_, ?_, rfl⟩
  · nlinarith [π.ht₁, π.gu3_t₁_lt_t₂]
  · nlinarith [π.ht₃]

/-! #### the old edges in `X₀` -/

theorem gu3_X₀_lab (i : ZMod k) : π.X₀ (G11_lab C.m i) = C.X i :=
  gu3_subdiv_lab C.X C.m π.t₁ π.t₂ π.t₃ i
theorem gu3_X₀_lab_succ {i : ZMod k} (hi : i ≠ C.m) : π.X₀ (G11_lab C.m i + 1) = C.X (i + 1) :=
  gu3_subdiv_lab_succ C.X C.m π.t₁ π.t₂ π.t₃ hi
theorem gu3_edge_lab {i : ZMod k} (hi : i ≠ C.m) : edge π.X₀ (G11_lab C.m i) = edge C.X i := by
  rw [edge, edge, gu3_X₀_lab_succ π hi, gu3_X₀_lab]
theorem gu3_edgeSegment_lab {i : ZMod k} (hi : i ≠ C.m) :
    edgeSegment π.X₀ (G11_lab C.m i) = edgeSegment C.X i := by
  simp only [edgeSegment, edgePoint, gu3_edge_lab π hi, gu3_X₀_lab]

/-! #### geometry of the configuration used by the subdivision -/

theorem gu3_edge_ne_zero (C : G11_ConfigSw k) (i : ZMod k) : edge C.X i ≠ 0 :=
  ((regular_iff_edges C.X).mp (C.gen.regular 0) i).1

theorem gu3_geometry (C : G11_ConfigSw k) : CrossingGeometry C.X :=
  crossingGeometry_of_single_generic C.hk C.gen

/-- a common point of the two edges of a crossing is its double point -/
theorem gu3_common_eq (C : G11_ConfigSw k) {i j : ZMod k} (h : IsCrossing C.X {i, j}) {x : Plane}
    (hi : x ∈ edgeSegment C.X i) (hj : x ∈ edgeSegment C.X j) : x = crossingPoint (xPair h) := by
  apply crossingPoint_unique_of_geometry (gu3_geometry C) (xPair h) x
  intro l hl
  rcases Finset.mem_insert.mp hl with rfl | hl
  · exact hi
  · rw [Finset.mem_singleton.mp hl]
    exact hj

theorem gu3_param_interior (C : G11_ConfigSw k) {i j : ZMod k} (h : IsCrossing C.X {i, j}) :
    0 < crossingParameter (xPair h) i (mem_pair_left i j) ∧
      crossingParameter (xPair h) i (mem_pair_left i j) < 1 :=
  crossingParameter_interior_of_geometry (gu3_geometry C) (xPair h) i (mem_pair_left i j)

theorem gu3_p_ne_m (C : G11_ConfigSw k) : C.p ≠ C.m :=
  fun h => gu3_remote_of_isCrossing C.hmp (adjacent_of_eq h.symm)
theorem gu3_q_ne_m (C : G11_ConfigSw k) : C.q ≠ C.m :=
  fun h => gu3_remote_of_isCrossing C.hmq (adjacent_of_eq h.symm)

/-- a point of the base `[p_in, p_out]` of `Θ` lies in `Θ` -/
theorem gu3_mem_theta {t : ℝ} (h1 : π.t₁ ≤ t) (h3 : t ≤ π.t₃) :
    edgePoint C.X C.m t ∈ convexHull ℝ {edgePoint C.X C.m π.t₁,
      edgePoint C.X C.m π.t₂ + π.lam • (crossingPoint (xPair C.hpq) - edgePoint C.X C.m π.t₂),
      edgePoint C.X C.m π.t₃} := by
  have hpos : 0 < π.t₃ - π.t₁ := by linarith [π.gu3_t₁_lt_t₂, π.gu3_t₂_lt_t₃]
  have hin : edgePoint C.X C.m π.t₁ ∈ convexHull ℝ {edgePoint C.X C.m π.t₁,
      edgePoint C.X C.m π.t₂ + π.lam • (crossingPoint (xPair C.hpq) - edgePoint C.X C.m π.t₂),
      edgePoint C.X C.m π.t₃} := subset_convexHull ℝ _ (by simp)
  have hout : edgePoint C.X C.m π.t₃ ∈ convexHull ℝ {edgePoint C.X C.m π.t₁,
      edgePoint C.X C.m π.t₂ + π.lam • (crossingPoint (xPair C.hpq) - edgePoint C.X C.m π.t₂),
      edgePoint C.X C.m π.t₃} := subset_convexHull ℝ _ (by simp)
  have key := (convex_convexHull ℝ _) hin hout
    (div_nonneg (sub_nonneg.mpr h3) hpos.le) (div_nonneg (sub_nonneg.mpr h1) hpos.le)
    (by rw [← add_div, show π.t₃ - t + (t - π.t₁) = π.t₃ - π.t₁ by ring, div_self hpos.ne'])
  convert key using 1
  simp only [edgePoint, smul_add, smul_smul]
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    field_simp
    ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring

theorem gu3_mem_U {t : ℝ} (h1 : π.t₁ ≤ t) (h3 : t ≤ π.t₃) : edgePoint C.X C.m t ∈ π.U :=
  interior_subset (π.theta_sub (π.gu3_mem_theta h1 h3))

/-- **the off-edge fact**: a point of the base of `Θ` other than the two local double points lies on no
edge of `X` other than `m` (on `p`, `q` it would be the double point; every other edge misses `U`) -/
theorem gu3_pt_off {t : ℝ} (h1 : π.t₁ ≤ t) (h3 : t ≤ π.t₃)
    (hmp : t ≠ crossingParameter (xPair C.hmp) C.m (mem_pair_left _ _))
    (hmq : t ≠ crossingParameter (xPair C.hmq) C.m (mem_pair_left _ _)) :
    ∀ h : ZMod k, h ≠ C.m → edgePoint C.X C.m t ∉ edgeSegment C.X h := by
  intro h hh hmem
  have hm : edgePoint C.X C.m t ∈ edgeSegment C.X C.m :=
    ⟨t, by linarith [π.ht₁], by linarith [π.ht₃], rfl⟩
  by_cases hp : h = C.p
  · subst hp
    have hx := gu3_common_eq C C.hmp hm hmem
    rw [(crossingParameter_spec (xPair C.hmp) C.m (mem_pair_left _ _)).2.2] at hx
    exact hmp (edgePoint_injective (gu3_edge_ne_zero C C.m) hx)
  by_cases hq : h = C.q
  · subst hq
    have hx := gu3_common_eq C C.hmq hm hmem
    rw [(crossingParameter_spec (xPair C.hmq) C.m (mem_pair_left _ _)).2.2] at hx
    exact hmq (edgePoint_injective (gu3_edge_ne_zero C C.m) hx)
  exact π.disc_clear_edge h hh hp hq _ hmem (π.gu3_mem_U h1 h3)

/-! #### the `appendVertex` chain -/

/-- `X` shifted so that the moved edge `m` becomes the closing edge `-1` -/
noncomputable def gu3_Y (C : G11_ConfigSw k) : LabelledTuple k := shift (C.m + 1) C.X

theorem gu3_Y_generic (C : G11_ConfigSw k) : (Shadow.single ⟨k, C.hk, gu3_Y C⟩).Generic :=
  single_generic_shift C.hk C.X (C.m + 1) C.gen

theorem gu3_Y_neg_one (C : G11_ConfigSw k) : gu3_Y C (-1) = C.X C.m := by
  show C.X (-1 + (C.m + 1)) = C.X C.m
  congr 1
  ring

theorem gu3_edge_Y (C : G11_ConfigSw k) : edge (gu3_Y C) (-1) = edge C.X C.m := by
  rw [gu3_Y, edge_shift]
  congr 1
  ring

theorem gu3_edgePoint_Y (C : G11_ConfigSw k) (t : ℝ) :
    edgePoint (gu3_Y C) (-1) t = edgePoint C.X C.m t := by
  rw [gu3_Y, edgePoint_shift]
  congr 1
  ring

theorem gu3_edgeSegment_Y (C : G11_ConfigSw k) (e : ZMod k) :
    edgeSegment (gu3_Y C) e = edgeSegment C.X (e + (C.m + 1)) :=
  edgeSegment_shift _ _ _

/-- the rescaled parameters of the second and third flat vertices -/
noncomputable def gu3_u₂ (π : G11_ParamsSw C) : ℝ := (π.t₂ - π.t₁) / (1 - π.t₁)
noncomputable def gu3_u₃ (π : G11_ParamsSw C) : ℝ := (π.t₃ - π.t₂) / (1 - π.t₂)

theorem gu3_u₂_pos : 0 < π.gu3_u₂ :=
  div_pos (sub_pos.mpr π.gu3_t₁_lt_t₂) (sub_pos.mpr π.gu3_t₁_lt_one)
theorem gu3_u₂_lt_one : π.gu3_u₂ < 1 :=
  (div_lt_one (sub_pos.mpr π.gu3_t₁_lt_one)).mpr (by linarith [π.gu3_t₂_lt_one])
theorem gu3_u₃_pos : 0 < π.gu3_u₃ :=
  div_pos (sub_pos.mpr π.gu3_t₂_lt_t₃) (sub_pos.mpr π.gu3_t₂_lt_one)
theorem gu3_u₃_lt_one : π.gu3_u₃ < 1 :=
  (div_lt_one (sub_pos.mpr π.gu3_t₂_lt_one)).mpr (by linarith [π.ht₃])
theorem gu3_u₂_mul : π.gu3_u₂ * (1 - π.t₁) = π.t₂ - π.t₁ :=
  div_mul_cancel₀ _ (sub_pos.mpr π.gu3_t₁_lt_one).ne'
theorem gu3_u₃_mul : π.gu3_u₃ * (1 - π.t₂) = π.t₃ - π.t₂ :=
  div_mul_cancel₀ _ (sub_pos.mpr π.gu3_t₂_lt_one).ne'

/-- the three flat subdivisions -/
noncomputable def gu3_Y₁ (π : G11_ParamsSw C) : LabelledTuple (k + 1) := appendVertex (gu3_Y C) π.t₁
noncomputable def gu3_Y₂ (π : G11_ParamsSw C) : LabelledTuple (k + 2) := appendVertex π.gu3_Y₁ π.gu3_u₂
noncomputable def gu3_Y₃ (π : G11_ParamsSw C) : LabelledTuple (k + 3) := appendVertex π.gu3_Y₂ π.gu3_u₃

theorem gu3_Y₁_neg_one : π.gu3_Y₁ (-1) = edgePoint C.X C.m π.t₁ := by
  rw [gu3_Y₁, ← insertedIndex_eq_neg_one, appendVertex_new, gu3_edgePoint_Y]
theorem gu3_edge_Y₁ : edge π.gu3_Y₁ (-1) = (1 - π.t₁) • edge C.X C.m := by
  rw [gu3_Y₁, ← insertedIndex_eq_neg_one, edge_appendVertex_new, gu3_edge_Y]
theorem gu3_edgePoint_Y₁ (s : ℝ) :
    edgePoint π.gu3_Y₁ (-1) s = edgePoint C.X C.m (π.t₁ + s * (1 - π.t₁)) := by
  rw [edgePoint, gu3_Y₁_neg_one, gu3_edge_Y₁, edgePoint, edgePoint, smul_smul, add_assoc,
    ← add_smul]
theorem gu3_Y₂_neg_one : π.gu3_Y₂ (-1) = edgePoint C.X C.m π.t₂ := by
  rw [gu3_Y₂, ← insertedIndex_eq_neg_one, appendVertex_new, gu3_edgePoint_Y₁, gu3_u₂_mul]
  congr 1
  ring
theorem gu3_edge_Y₂ : edge π.gu3_Y₂ (-1) = (1 - π.t₂) • edge C.X C.m := by
  rw [gu3_Y₂, ← insertedIndex_eq_neg_one, edge_appendVertex_new, gu3_edge_Y₁, smul_smul]
  congr 1
  have := π.gu3_u₂_mul
  linear_combination -this
theorem gu3_edgePoint_Y₂ (s : ℝ) :
    edgePoint π.gu3_Y₂ (-1) s = edgePoint C.X C.m (π.t₂ + s * (1 - π.t₂)) := by
  rw [edgePoint, gu3_Y₂_neg_one, gu3_edge_Y₂, edgePoint, edgePoint, smul_smul, add_assoc,
    ← add_smul]
theorem gu3_Y₂_apex : edgePoint π.gu3_Y₂ (-1) π.gu3_u₃ = edgePoint C.X C.m π.t₃ := by
  rw [gu3_edgePoint_Y₂, gu3_u₃_mul]
  congr 1
  ring

/-- the first half-edge `[X m, p_in]` of `Y₁` -/
theorem gu3_edgePoint_half₁ (s : ℝ) :
    edgePoint π.gu3_Y₁ (insertIndex (-1 : ZMod k)) s = edgePoint C.X C.m (s * π.t₁) := by
  rw [edgePoint, edgePoint, gu3_Y₁, edge_appendVertex_last, appendVertex_old, gu3_Y_neg_one,
    gu3_edge_Y, smul_smul]
theorem gu3_not_mem_half₁ {t : ℝ} (ht : π.t₁ < t) :
    edgePoint C.X C.m t ∉ edgeSegment π.gu3_Y₁ (insertIndex (-1 : ZMod k)) := by
  rintro ⟨s, hs0, hs1, hs⟩
  rw [gu3_edgePoint_half₁] at hs
  have := edgePoint_injective (gu3_edge_ne_zero C C.m) hs
  nlinarith [mul_nonneg (sub_nonneg.mpr hs1) π.ht₁.le]
theorem gu3_edgeSegment_Y₁_old {i : ZMod k} (hi : i ≠ -1) :
    edgeSegment π.gu3_Y₁ (insertIndex i) = edgeSegment C.X (i + (C.m + 1)) := by
  rw [gu3_Y₁, edgeSegment_appendVertex_old _ _ hi, gu3_edgeSegment_Y]

/-- the second half-edge `[p_in, m₀]` of `Y₂` -/
theorem gu3_edgePoint_half₂ (s : ℝ) :
    edgePoint π.gu3_Y₂ (insertIndex (-1 : ZMod (k + 1))) s =
      edgePoint C.X C.m (π.t₁ + s * (π.t₂ - π.t₁)) := by
  rw [edgePoint, gu3_Y₂, edge_appendVertex_last, appendVertex_old, gu3_Y₁_neg_one, gu3_edge_Y₁,
    smul_smul, smul_smul, edgePoint, edgePoint, add_assoc, ← add_smul, mul_assoc, gu3_u₂_mul]
theorem gu3_not_mem_half₂ {t : ℝ} (ht : π.t₂ < t) :
    edgePoint C.X C.m t ∉ edgeSegment π.gu3_Y₂ (insertIndex (-1 : ZMod (k + 1))) := by
  rintro ⟨s, hs0, hs1, hs⟩
  rw [gu3_edgePoint_half₂] at hs
  have := edgePoint_injective (gu3_edge_ne_zero C C.m) hs
  nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_pos.mpr π.gu3_t₁_lt_t₂).le]
theorem gu3_edgeSegment_Y₂_old {i : ZMod (k + 1)} (hi : i ≠ -1) :
    edgeSegment π.gu3_Y₂ (insertIndex i) = edgeSegment π.gu3_Y₁ i := by
  rw [gu3_Y₂, edgeSegment_appendVertex_old _ _ hi]

theorem gu3_hoff₁ : ∀ e : ZMod k, e ≠ -1 →
    edgePoint (gu3_Y C) (-1) π.t₁ ∉ edgeSegment (gu3_Y C) e := by
  intro e he
  rw [gu3_edgePoint_Y, gu3_edgeSegment_Y]
  refine π.gu3_pt_off le_rfl (by linarith [π.gu3_t₁_lt_t₂, π.gu3_t₂_lt_t₃]) π.h₁.ne
    (by linarith [π.h₁, π.h₂, π.h₃] : π.t₁ < _).ne _ ?_
  intro h
  apply he
  linear_combination h

theorem gu3_Y₁_generic : (Shadow.single ⟨k + 1, Nat.le_succ_of_le C.hk, π.gu3_Y₁⟩).Generic :=
  single_generic_appendVertex C.hk (gu3_Y C) π.ht₁ π.gu3_t₁_lt_one (gu3_Y_generic C) π.gu3_hoff₁

theorem gu3_hoff₂ : ∀ e : ZMod (k + 1), e ≠ -1 →
    edgePoint π.gu3_Y₁ (-1) π.gu3_u₂ ∉ edgeSegment π.gu3_Y₁ e := by
  intro e he
  have hpt : edgePoint π.gu3_Y₁ (-1) π.gu3_u₂ = edgePoint C.X C.m π.t₂ := by
    rw [gu3_edgePoint_Y₁, gu3_u₂_mul]
    congr 1
    ring
  rw [hpt]
  rcases insertion_indices_exhaust e with he' | ⟨i, rfl⟩
  · exact absurd (he'.trans insertedIndex_eq_neg_one) he
  · by_cases hi : i = -1
    · subst hi
      exact π.gu3_not_mem_half₁ π.gu3_t₁_lt_t₂
    · rw [π.gu3_edgeSegment_Y₁_old hi]
      refine π.gu3_pt_off π.gu3_t₁_lt_t₂.le π.gu3_t₂_lt_t₃.le π.h₂.ne' π.h₃.ne _ ?_
      intro h
      apply hi
      linear_combination h

theorem gu3_Y₂_generic :
    (Shadow.single ⟨k + 2, Nat.le_succ_of_le (Nat.le_succ_of_le C.hk), π.gu3_Y₂⟩).Generic :=
  single_generic_appendVertex (Nat.le_succ_of_le C.hk) π.gu3_Y₁ π.gu3_u₂_pos π.gu3_u₂_lt_one
    π.gu3_Y₁_generic π.gu3_hoff₂

theorem gu3_hoff₃ : ∀ e : ZMod (k + 2), e ≠ -1 →
    edgePoint π.gu3_Y₂ (-1) π.gu3_u₃ ∉ edgeSegment π.gu3_Y₂ e := by
  intro e he
  rw [gu3_Y₂_apex]
  rcases insertion_indices_exhaust e with he' | ⟨i, rfl⟩
  · exact absurd (he'.trans insertedIndex_eq_neg_one) he
  · by_cases hi : i = -1
    · subst hi
      exact π.gu3_not_mem_half₂ π.gu3_t₂_lt_t₃
    · rw [π.gu3_edgeSegment_Y₂_old hi]
      rcases insertion_indices_exhaust i with hi' | ⟨i', rfl⟩
      · exact absurd (hi'.trans insertedIndex_eq_neg_one) hi
      · by_cases hi'' : i' = -1
        · subst hi''
          exact π.gu3_not_mem_half₁ (π.gu3_t₁_lt_t₂.trans π.gu3_t₂_lt_t₃)
        · rw [π.gu3_edgeSegment_Y₁_old hi'']
          refine π.gu3_pt_off (π.gu3_t₁_lt_t₂.trans π.gu3_t₂_lt_t₃).le le_rfl
            (by linarith [π.h₂, π.h₃, π.h₄] : _ < π.t₃).ne' π.h₄.ne' _ ?_
          intro h
          apply hi''
          linear_combination h

theorem gu3_Y₃_generic : (Shadow.single ⟨k + 3, π.hk₃, π.gu3_Y₃⟩).Generic :=
  single_generic_appendVertex (Nat.le_succ_of_le (Nat.le_succ_of_le C.hk)) π.gu3_Y₂ π.gu3_u₃_pos
    π.gu3_u₃_lt_one π.gu3_Y₂_generic π.gu3_hoff₃

/-- `Y₃` read at a natural label -/
theorem gu3_Y₃_natCast (a : ℕ) (ha : a < k + 3) :
    π.gu3_Y₃ (a : ZMod (k + 3)) =
      if a < k then C.X ((a : ZMod k) + (C.m + 1))
      else if a = k then edgePoint C.X C.m π.t₁
      else if a = k + 1 then edgePoint C.X C.m π.t₂
      else edgePoint C.X C.m π.t₃ := by
  have e3 : ((a : ZMod (k + 3))).val = a := ZMod.val_natCast_of_lt ha
  simp only [gu3_Y₃, appendVertex, e3]
  by_cases h2 : a < k + 2
  · rw [ite_eq_left h2]
    have e2 : ((a : ZMod (k + 2))).val = a := ZMod.val_natCast_of_lt h2
    simp only [gu3_Y₂, appendVertex, e2]
    by_cases h1 : a < k + 1
    · rw [ite_eq_left h1]
      have e1 : ((a : ZMod (k + 1))).val = a := ZMod.val_natCast_of_lt h1
      simp only [gu3_Y₁, appendVertex, e1]
      by_cases h0 : a < k
      · rw [ite_eq_left h0, ite_eq_left h0]
        rfl
      · rw [ite_eq_right h0, ite_eq_right h0, ite_eq_left (by omega), gu3_edgePoint_Y]
    · rw [ite_eq_right h1, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), gu3_edgePoint_Y₁,
        gu3_u₂_mul]
      congr 1
      ring
  · rw [ite_eq_right h2, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), gu3_Y₂_apex]

theorem gu3_cast_add_m (C : G11_ConfigSw k) (a : ℕ) :
    ((a : ZMod k) + (C.m + 1)) = ((a + C.m.val + 1 : ℕ) : ZMod k) := by
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val, add_assoc]

/-- **the re-indexing** `Y₃ ≅ X₀`: `X₀ j = Y₃ (j + (k - 1 - m))`. -/
theorem gu3_reindexed_Y₃_X₀ : Reindexed π.gu3_Y₃ π.X₀ := by
  have hmk := C.m.val_lt
  refine ⟨rfl, k - 1 - C.m.val, fun j => ?_⟩
  have hj := j.val_lt
  conv_lhs => rw [← ZMod.natCast_zmod_val j]
  show G11_subdiv C.X C.m π.t₁ π.t₂ π.t₃ _ = _
  rw [gu3_subdiv_natCast C.X C.m π.t₁ π.t₂ π.t₃ _ hj]
  by_cases h0 : j.val ≤ C.m.val
  · rw [ite_eq_left h0, π.gu3_Y₃_natCast _ (by omega), ite_eq_left (by omega), gu3_cast_add_m]
    congr 1
    rw [show j.val + (k - 1 - C.m.val) + C.m.val + 1 = j.val + k by omega, Nat.cast_add,
      ZMod.natCast_self, add_zero]
  · rw [ite_eq_right h0]
    by_cases h1 : j.val = C.m.val + 1
    · rw [ite_eq_left h1, π.gu3_Y₃_natCast _ (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    · rw [ite_eq_right h1]
      by_cases h2 : j.val = C.m.val + 2
      · rw [ite_eq_left h2, π.gu3_Y₃_natCast _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_left (by omega)]
      · rw [ite_eq_right h2]
        by_cases h3 : j.val = C.m.val + 3
        · rw [ite_eq_left h3, π.gu3_Y₃_natCast _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
            ite_eq_right (by omega)]
        · rw [ite_eq_right h3]
          rw [show j.val + (k - 1 - C.m.val) = (j.val - C.m.val - 4) + (k + 3) by omega,
            Nat.cast_add, ZMod.natCast_self, add_zero, π.gu3_Y₃_natCast _ (by omega),
            ite_eq_left (by omega), gu3_cast_add_m]
          congr 2
          omega

/-- **B1.** `X₀` is a generic one-component shadow (three accepted flat subdivisions
`single_generic_appendVertex` after the re-indexing `Reindexed` putting `m` last; `hoff` from the
configuration: the three new points lie on `m` only). -/
theorem X₀_generic : (Shadow.single ⟨k + 3, π.hk₃, π.X₀⟩).Generic := by
  exact single_generic_of_reindexed π.gu3_reindexed_Y₃_X₀ π.hk₃ π.hk₃ π.gu3_Y₃_generic

/-- `M₀`: the positive diagram of `X₀`. -/
noncomputable def M₀ : Diagram := (Shadow.single ⟨k + 3, π.hk₃, π.X₀⟩).positiveDiagram π.X₀_generic

theorem M₀_componentCount : π.M₀.componentCount = 1 := rfl

/-! ### U3 helpers (Block B) — the five reparametrizations `D₀ → Y → Y₁ → Y₂ → Y₃ → M₀` -/

theorem gu3_reparam₁ (C : G11_ConfigSw k) :
    Reparam C.D₀ ((Shadow.single ⟨k, C.hk, gu3_Y C⟩).positiveDiagram (gu3_Y_generic C)) :=
  reparam_positiveDiagram_single_shift ⟨k, C.hk, C.X⟩ (C.m + 1) C.gen (gu3_Y_generic C)

theorem gu3_reparam₂ :
    Reparam ((Shadow.single ⟨k, C.hk, gu3_Y C⟩).positiveDiagram (gu3_Y_generic C))
      ((Shadow.single ⟨k + 1, Nat.le_succ_of_le C.hk, π.gu3_Y₁⟩).positiveDiagram
        π.gu3_Y₁_generic) :=
  reparam_positiveDiagram_single_appendVertex C.hk (gu3_Y C) π.ht₁ π.gu3_t₁_lt_one
    (gu3_Y_generic C) π.gu3_hoff₁ π.gu3_Y₁_generic

theorem gu3_reparam₃ :
    Reparam ((Shadow.single ⟨k + 1, Nat.le_succ_of_le C.hk, π.gu3_Y₁⟩).positiveDiagram
        π.gu3_Y₁_generic)
      ((Shadow.single ⟨k + 2, Nat.le_succ_of_le (Nat.le_succ_of_le C.hk), π.gu3_Y₂⟩).positiveDiagram
        π.gu3_Y₂_generic) :=
  reparam_positiveDiagram_single_appendVertex (Nat.le_succ_of_le C.hk) π.gu3_Y₁ π.gu3_u₂_pos
    π.gu3_u₂_lt_one π.gu3_Y₁_generic π.gu3_hoff₂ π.gu3_Y₂_generic

theorem gu3_reparam₄ :
    Reparam ((Shadow.single ⟨k + 2, Nat.le_succ_of_le (Nat.le_succ_of_le C.hk), π.gu3_Y₂⟩).positiveDiagram
        π.gu3_Y₂_generic)
      ((Shadow.single ⟨k + 3, π.hk₃, π.gu3_Y₃⟩).positiveDiagram π.gu3_Y₃_generic) :=
  reparam_positiveDiagram_single_appendVertex (Nat.le_succ_of_le (Nat.le_succ_of_le C.hk))
    π.gu3_Y₂ π.gu3_u₃_pos π.gu3_u₃_lt_one π.gu3_Y₂_generic π.gu3_hoff₃ π.gu3_Y₃_generic

theorem gu3_reparam₅ :
    Reparam ((Shadow.single ⟨k + 3, π.hk₃, π.gu3_Y₃⟩).positiveDiagram π.gu3_Y₃_generic) π.M₀ := by
  obtain ⟨r, hr⟩ := reindexed_eq_shift π.gu3_reindexed_Y₃_X₀
  have key : ∀ (Z : LabelledTuple (k + 3)) (hZ : (Shadow.single ⟨k + 3, π.hk₃, Z⟩).Generic),
      Z = shift r π.gu3_Y₃ →
      Reparam ((Shadow.single ⟨k + 3, π.hk₃, π.gu3_Y₃⟩).positiveDiagram π.gu3_Y₃_generic)
        ((Shadow.single ⟨k + 3, π.hk₃, Z⟩).positiveDiagram hZ) := by
    rintro Z hZ rfl
    exact reparam_positiveDiagram_single_shift ⟨k + 3, π.hk₃, π.gu3_Y₃⟩ r π.gu3_Y₃_generic hZ
  exact key π.X₀ π.X₀_generic hr

/-- **B2.** `P(M₀) = P(D₀)`: `homfly_positiveDiagram_single_of_reindexed` + three applications of
`homfly_positiveDiagram_single_appendVertex` (planar isotopy, `homfly_planar`). -/
theorem homfly_M₀ : homfly π.M₀ = homfly C.D₀ := by
  exact ((gu3_homfly_of_reparam (gu3_reparam₁ C)).trans ((gu3_homfly_of_reparam π.gu3_reparam₂).trans
    ((gu3_homfly_of_reparam π.gu3_reparam₃).trans ((gu3_homfly_of_reparam π.gu3_reparam₄).trans
      (gu3_homfly_of_reparam π.gu3_reparam₅))))).symm

/-! ### U3 helpers (Block C) — the labels `p'`, `q'` and the remoteness of the local pairs -/

theorem gu3_edgeSegment_p' : edgeSegment π.X₀ π.p' = edgeSegment C.X C.p :=
  π.gu3_edgeSegment_lab (gu3_p_ne_m C)
theorem gu3_edgeSegment_q' : edgeSegment π.X₀ π.q' = edgeSegment C.X C.q :=
  π.gu3_edgeSegment_lab (gu3_q_ne_m C)
theorem gu3_edge_p' : edge π.X₀ π.p' = edge C.X C.p := π.gu3_edge_lab (gu3_p_ne_m C)
theorem gu3_edge_q' : edge π.X₀ π.q' = edge C.X C.q := π.gu3_edge_lab (gu3_q_ne_m C)

theorem gu3_remote_mB_p' : remote π.mB π.p' := by
  have h := (gu3_remote_natCast_iff C.m.val_lt C.p.val_lt).mp
    (by have := gu3_remote_of_isCrossing C.hmp
        rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])
  have hmk := C.m.val_lt
  have hpk := C.p.val_lt
  show remote ((C.m.val + 1 : ℕ) : ZMod (k + 3)) (G11_lab C.m C.p)
  rw [← ZMod.natCast_zmod_val (G11_lab C.m C.p), gu3_remote_natCast_iff (by omega) (ZMod.val_lt _),
    gu3_lab_val]
  split_ifs <;> first | omega | (simp only [and_false, or_false]; omega)

theorem gu3_remote_mC_q' : remote π.mC π.q' := by
  have h := (gu3_remote_natCast_iff C.m.val_lt C.q.val_lt).mp
    (by have := gu3_remote_of_isCrossing C.hmq
        rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])
  have hmk := C.m.val_lt
  have hqk := C.q.val_lt
  show remote ((C.m.val + 2 : ℕ) : ZMod (k + 3)) (G11_lab C.m C.q)
  rw [← ZMod.natCast_zmod_val (G11_lab C.m C.q), gu3_remote_natCast_iff (by omega) (ZMod.val_lt _),
    gu3_lab_val]
  split_ifs <;> first | omega | (simp only [and_false, or_false]; omega)

theorem gu3_remote_p'_q' : remote π.p' π.q' := gu3_remote_lab (gu3_remote_of_isCrossing C.hpq)

/-- **B3.** The crossings of `X₀` carrying the three local double points: `x_mp` on `[p_in, m₀]`, `x_mq` on
`[m₀, p_out]`, `x_pq` on `p', q'` (from `t₁ < t(x_mp) < t₂ < t(x_mq) < t₃` and `edgeSegment_appendVertex_*`). -/
theorem X₀_cross_mp : IsCrossing π.X₀ {π.mB, π.p'} := by
  exact ⟨π.mB, π.p', rfl, π.gu3_remote_mB_p', crossingPoint (xPair C.hmp), by
    rw [(crossingParameter_spec (xPair C.hmp) C.m (mem_pair_left _ _)).2.2]
    exact π.gu3_mem_edgeSegment_mB π.h₁.le π.h₂.le, by
    rw [gu3_edgeSegment_p']
    exact crossingPoint_mem _ _ (mem_pair_right _ _)⟩

theorem X₀_cross_mq : IsCrossing π.X₀ {π.mC, π.q'} := by
  exact ⟨π.mC, π.q', rfl, π.gu3_remote_mC_q', crossingPoint (xPair C.hmq), by
    rw [(crossingParameter_spec (xPair C.hmq) C.m (mem_pair_left _ _)).2.2]
    exact π.gu3_mem_edgeSegment_mC π.h₃.le π.h₄.le, by
    rw [gu3_edgeSegment_q']
    exact crossingPoint_mem _ _ (mem_pair_right _ _)⟩

theorem X₀_cross_pq : IsCrossing π.X₀ {π.p', π.q'} := by
  exact ⟨π.p', π.q', rfl, π.gu3_remote_p'_q', crossingPoint (xPair C.hpq), by
    rw [gu3_edgeSegment_p']
    exact crossingPoint_mem _ _ (mem_pair_left _ _), by
    rw [gu3_edgeSegment_q']
    exact crossingPoint_mem _ _ (mem_pair_right _ _)⟩

/-- the six local visits of `M₀` (through `singleVisitEquiv`) -/
noncomputable def w_mp : π.M₀.Γ.Visit :=
  (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₀⟩).symm ⟨xPair π.X₀_cross_mp, ⟨π.mB, mem_pair_left _ _⟩⟩
noncomputable def w_pm : π.M₀.Γ.Visit :=
  (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₀⟩).symm ⟨xPair π.X₀_cross_mp, ⟨π.p', mem_pair_right _ _⟩⟩
noncomputable def w_mq : π.M₀.Γ.Visit :=
  (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₀⟩).symm ⟨xPair π.X₀_cross_mq, ⟨π.mC, mem_pair_left _ _⟩⟩
noncomputable def w_qm : π.M₀.Γ.Visit :=
  (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₀⟩).symm ⟨xPair π.X₀_cross_mq, ⟨π.q', mem_pair_right _ _⟩⟩
noncomputable def w_pq : π.M₀.Γ.Visit :=
  (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₀⟩).symm ⟨xPair π.X₀_cross_pq, ⟨π.p', mem_pair_left _ _⟩⟩
noncomputable def w_qp : π.M₀.Γ.Visit :=
  (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₀⟩).symm ⟨xPair π.X₀_cross_pq, ⟨π.q', mem_pair_right _ _⟩⟩

/-! ### U3 helpers (Block D) — from a reparametrization to an occurrence bijection carrying twins, over
bits and the cyclic order; the over bits of a one-component positive diagram -/

theorem gu3_IsVisitIso_trans {D D' D'' : Diagram} {Ψ : D.Γ.Visit ≃ D'.Γ.Visit}
    {Ψ' : D'.Γ.Visit ≃ D''.Γ.Visit} (h : gu3_IsVisitIso Ψ) (h' : gu3_IsVisitIso Ψ') :
    gu3_IsVisitIso (Ψ.trans Ψ') := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h1', h2', h3', h4'⟩ := h'
  refine ⟨fun v => ?_, fun v => ?_, fun u v w => ?_, fun v => ?_⟩
  · simp only [Equiv.trans_apply]
    rw [h1, h1']
  · simp only [Equiv.trans_apply]
    rw [h2', h2]
  · simp only [Equiv.trans_apply]
    rw [h3', h3]
  · simp only [Equiv.trans_apply]
    rw [h4', h4]

theorem gu3_visitIso_of_reparam (A B : PolyComp) (hA : (Shadow.single A).Generic)
    (hB : (Shadow.single B).Generic)
    (h : Reparam ((Shadow.single A).positiveDiagram hA) ((Shadow.single B).positiveDiagram hB)) :
    ∃ Ψ : ((Shadow.single A).positiveDiagram hA).Γ.Visit ≃
      ((Shadow.single B).positiveDiagram hB).Γ.Visit, gu3_IsVisitIso Ψ := by
  obtain ⟨r⟩ := h
  obtain ⟨Ψ, hΨ⟩ := gu3_exists_visitEquiv r
  exact ⟨Ψ, gu3_twin_of_visitPt r Ψ hΨ, gu3_overBit_of_visitPt r Ψ hΨ,
    gu3_visitBetween_of_visitPt A B hA hB r Ψ hΨ, gu3_crossingPoint_of_visitPt r Ψ hΨ⟩

/-! #### over bits of a one-component positive diagram -/

/-! #### the six local double points and over bits of `M₀` -/

theorem gu3_cp_mp : crossingPoint (xPair π.X₀_cross_mp) = crossingPoint (xPair C.hmp) :=
  gu3_common_eq C C.hmp (π.gu3_edgeSegment_mB_subset (crossingPoint_mem _ _ (mem_pair_left _ _)))
    (by rw [← gu3_edgeSegment_p']; exact crossingPoint_mem _ _ (mem_pair_right _ _))
theorem gu3_cp_mq : crossingPoint (xPair π.X₀_cross_mq) = crossingPoint (xPair C.hmq) :=
  gu3_common_eq C C.hmq (π.gu3_edgeSegment_mC_subset (crossingPoint_mem _ _ (mem_pair_left _ _)))
    (by rw [← gu3_edgeSegment_q']; exact crossingPoint_mem _ _ (mem_pair_right _ _))
theorem gu3_cp_pq : crossingPoint (xPair π.X₀_cross_pq) = crossingPoint (xPair C.hpq) :=
  gu3_common_eq C C.hpq
    (by rw [← gu3_edgeSegment_p']; exact crossingPoint_mem _ _ (mem_pair_left _ _))
    (by rw [← gu3_edgeSegment_q']; exact crossingPoint_mem _ _ (mem_pair_right _ _))

theorem gu3_cp_v_mp : C.D₀.Γ.crossingPoint C.v_mp.1 = crossingPoint (xPair C.hmp) :=
  gu3_crossingPoint_symm C.comp C.gen _ _
theorem gu3_cp_v_pm : C.D₀.Γ.crossingPoint C.v_pm.1 = crossingPoint (xPair C.hmp) :=
  gu3_crossingPoint_symm C.comp C.gen _ _
theorem gu3_cp_v_mq : C.D₀.Γ.crossingPoint C.v_mq.1 = crossingPoint (xPair C.hmq) :=
  gu3_crossingPoint_symm C.comp C.gen _ _
theorem gu3_cp_v_qm : C.D₀.Γ.crossingPoint C.v_qm.1 = crossingPoint (xPair C.hmq) :=
  gu3_crossingPoint_symm C.comp C.gen _ _
theorem gu3_cp_v_pq : C.D₀.Γ.crossingPoint C.v_pq.1 = crossingPoint (xPair C.hpq) :=
  gu3_crossingPoint_symm C.comp C.gen _ _
theorem gu3_cp_v_qp : C.D₀.Γ.crossingPoint C.v_qp.1 = crossingPoint (xPair C.hpq) :=
  gu3_crossingPoint_symm C.comp C.gen _ _
theorem gu3_cp_w_mp : π.M₀.Γ.crossingPoint π.w_mp.1 = crossingPoint (xPair π.X₀_cross_mp) :=
  gu3_crossingPoint_symm ⟨k + 3, π.hk₃, π.X₀⟩ π.X₀_generic _ _
theorem gu3_cp_w_pm : π.M₀.Γ.crossingPoint π.w_pm.1 = crossingPoint (xPair π.X₀_cross_mp) :=
  gu3_crossingPoint_symm ⟨k + 3, π.hk₃, π.X₀⟩ π.X₀_generic _ _
theorem gu3_cp_w_mq : π.M₀.Γ.crossingPoint π.w_mq.1 = crossingPoint (xPair π.X₀_cross_mq) :=
  gu3_crossingPoint_symm ⟨k + 3, π.hk₃, π.X₀⟩ π.X₀_generic _ _
theorem gu3_cp_w_qm : π.M₀.Γ.crossingPoint π.w_qm.1 = crossingPoint (xPair π.X₀_cross_mq) :=
  gu3_crossingPoint_symm ⟨k + 3, π.hk₃, π.X₀⟩ π.X₀_generic _ _
theorem gu3_cp_w_pq : π.M₀.Γ.crossingPoint π.w_pq.1 = crossingPoint (xPair π.X₀_cross_pq) :=
  gu3_crossingPoint_symm ⟨k + 3, π.hk₃, π.X₀⟩ π.X₀_generic _ _
theorem gu3_cp_w_qp : π.M₀.Γ.crossingPoint π.w_qp.1 = crossingPoint (xPair π.X₀_cross_pq) :=
  gu3_crossingPoint_symm ⟨k + 3, π.hk₃, π.X₀⟩ π.X₀_generic _ _

/-- an occurrence bijection with the U3 properties is determined on the local occurrences by the
double point and the over bit -/
theorem gu3_image_eq (Ψ₀ : C.D₀.Γ.Visit ≃ π.M₀.Γ.Visit) (hΨ : gu3_IsVisitIso Ψ₀)
    {v : C.D₀.Γ.Visit} {w : π.M₀.Γ.Visit}
    (hcp : π.M₀.Γ.crossingPoint w.1 = C.D₀.Γ.crossingPoint v.1)
    (hbit : π.M₀.overBit w = C.D₀.overBit v) : Ψ₀ v = w := by
  obtain ⟨-, h2, -, h4⟩ := hΨ
  apply gu3_visit_ext π.M₀
  · apply π.M₀.generic.crossingPoint_injective
    rw [h4 v, hcp]
  · rw [h2 v, hbit]

/-- **B4.** The record of `M₀` is the record of `D₀` (the subdivision is a reparametrization): an occurrence
bijection `Ψ₀` carrying twins, over bits, signs and the cyclic order (`traversalBetween_subdivPt`,
`subdivKeyMap_strictMono`, `det_edge_subdivPt_pos_iff`), sending the six local visits to the six local
visits. -/
theorem exists_Ψ₀ : ∃ Ψ₀ : C.D₀.Γ.Visit ≃ π.M₀.Γ.Visit,
    (∀ v, Ψ₀ (C.D₀.twin v) = π.M₀.twin (Ψ₀ v)) ∧
    (∀ v, π.M₀.overBit (Ψ₀ v) = C.D₀.overBit v) ∧
    (∀ v, π.M₀.sign (Ψ₀ v).1 = C.D₀.sign v.1) ∧
    (∀ u v w, π.M₀.VisitBetween (Ψ₀ u) (Ψ₀ v) (Ψ₀ w) ↔ C.D₀.VisitBetween u v w) ∧
    Ψ₀ C.v_mp = π.w_mp ∧ Ψ₀ C.v_pm = π.w_pm ∧ Ψ₀ C.v_mq = π.w_mq ∧
    Ψ₀ C.v_qm = π.w_qm ∧ Ψ₀ C.v_pq = π.w_pq ∧ Ψ₀ C.v_qp = π.w_qp := by
  obtain ⟨Ψ₁, h₁⟩ := gu3_visitIso_of_reparam C.comp ⟨k, C.hk, gu3_Y C⟩ C.gen (gu3_Y_generic C)
    (gu3_reparam₁ C)
  obtain ⟨Ψ₂, h₂⟩ := gu3_visitIso_of_reparam ⟨k, C.hk, gu3_Y C⟩
    ⟨k + 1, Nat.le_succ_of_le C.hk, π.gu3_Y₁⟩ (gu3_Y_generic C) π.gu3_Y₁_generic π.gu3_reparam₂
  obtain ⟨Ψ₃, h₃⟩ := gu3_visitIso_of_reparam ⟨k + 1, Nat.le_succ_of_le C.hk, π.gu3_Y₁⟩
    ⟨k + 2, Nat.le_succ_of_le (Nat.le_succ_of_le C.hk), π.gu3_Y₂⟩ π.gu3_Y₁_generic
    π.gu3_Y₂_generic π.gu3_reparam₃
  obtain ⟨Ψ₄, h₄⟩ := gu3_visitIso_of_reparam
    ⟨k + 2, Nat.le_succ_of_le (Nat.le_succ_of_le C.hk), π.gu3_Y₂⟩ ⟨k + 3, π.hk₃, π.gu3_Y₃⟩
    π.gu3_Y₂_generic π.gu3_Y₃_generic π.gu3_reparam₄
  obtain ⟨Ψ₅, h₅⟩ := gu3_visitIso_of_reparam ⟨k + 3, π.hk₃, π.gu3_Y₃⟩ ⟨k + 3, π.hk₃, π.X₀⟩
    π.gu3_Y₃_generic π.X₀_generic π.gu3_reparam₅
  let Ψ₀ : C.D₀.Γ.Visit ≃ π.M₀.Γ.Visit := Ψ₁.trans (Ψ₂.trans (Ψ₃.trans (Ψ₄.trans Ψ₅)))
  have hΨ : gu3_IsVisitIso Ψ₀ :=
    gu3_IsVisitIso_trans h₁ (gu3_IsVisitIso_trans h₂ (gu3_IsVisitIso_trans h₃
      (gu3_IsVisitIso_trans h₄ h₅)))
  have hdet_mp : 0 < det (edge π.X₀ π.mB) (edge π.X₀ π.p') ↔ 0 < det (edge C.X C.m) (edge C.X C.p) := by
    rw [gu3_edge_mB, gu3_edge_p', det_smul_left]
    exact mul_pos_iff_of_pos_left (sub_pos.mpr π.gu3_t₁_lt_t₂)
  have hdet_pm : 0 < det (edge π.X₀ π.p') (edge π.X₀ π.mB) ↔ 0 < det (edge C.X C.p) (edge C.X C.m) := by
    rw [det_swap, det_swap (edge C.X C.m) (edge C.X C.p), gu3_edge_mB, gu3_edge_p', det_smul_left,
      ← mul_neg]
    exact mul_pos_iff_of_pos_left (sub_pos.mpr π.gu3_t₁_lt_t₂)
  have hdet_mq : 0 < det (edge π.X₀ π.mC) (edge π.X₀ π.q') ↔ 0 < det (edge C.X C.m) (edge C.X C.q) := by
    rw [gu3_edge_mC, gu3_edge_q', det_smul_left]
    exact mul_pos_iff_of_pos_left (sub_pos.mpr π.gu3_t₂_lt_t₃)
  have hdet_qm : 0 < det (edge π.X₀ π.q') (edge π.X₀ π.mC) ↔ 0 < det (edge C.X C.q) (edge C.X C.m) := by
    rw [det_swap, det_swap (edge C.X C.m) (edge C.X C.q), gu3_edge_mC, gu3_edge_q', det_smul_left,
      ← mul_neg]
    exact mul_pos_iff_of_pos_left (sub_pos.mpr π.gu3_t₂_lt_t₃)
  have hdet_pq : 0 < det (edge π.X₀ π.p') (edge π.X₀ π.q') ↔ 0 < det (edge C.X C.p) (edge C.X C.q) := by
    rw [gu3_edge_p', gu3_edge_q']
  have hdet_qp : 0 < det (edge π.X₀ π.q') (edge π.X₀ π.p') ↔ 0 < det (edge C.X C.q) (edge C.X C.p) := by
    rw [gu3_edge_p', gu3_edge_q']
  have hpm_ne : π.p' ≠ π.mB := fun h => π.gu3_remote_mB_p' (adjacent_of_eq h.symm)
  have hqm_ne : π.q' ≠ π.mC := fun h => π.gu3_remote_mC_q' (adjacent_of_eq h.symm)
  have hpq_ne : π.p' ≠ π.q' := fun h => π.gu3_remote_p'_q' (adjacent_of_eq h)
  have hmp_ne : C.m ≠ C.p := (gu3_p_ne_m C).symm
  have hmq_ne : C.m ≠ C.q := (gu3_q_ne_m C).symm
  have hpq_ne' : C.p ≠ C.q := fun h => gu3_remote_of_isCrossing C.hpq (adjacent_of_eq h)
  refine ⟨Ψ₀, hΨ.1, hΨ.2.1, fun v => ?_, hΨ.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Shadow.positiveDiagram_sign _ _ _).trans (Shadow.positiveDiagram_sign _ _ _).symm
  · refine π.gu3_image_eq Ψ₀ hΨ ?_ ?_
    · rw [gu3_cp_w_mp, gu3_cp_v_mp, gu3_cp_mp]
    · exact gu3_bool_eq_of_iff ((gu3_overBit_pair ⟨k + 3, π.hk₃, π.X₀⟩ π.X₀_generic π.X₀_cross_mp
        (mem_pair_left _ _) (mem_pair_right _ _) hpm_ne.symm).trans (hdet_mp.trans
        (gu3_overBit_pair C.comp C.gen C.hmp (mem_pair_left _ _) (mem_pair_right _ _) hmp_ne).symm))
  · refine π.gu3_image_eq Ψ₀ hΨ ?_ ?_
    · rw [gu3_cp_w_pm, gu3_cp_v_pm, gu3_cp_mp]
    · exact gu3_bool_eq_of_iff ((gu3_overBit_pair ⟨k + 3, π.hk₃, π.X₀⟩ π.X₀_generic π.X₀_cross_mp
        (mem_pair_right _ _) (mem_pair_left _ _) hpm_ne).trans (hdet_pm.trans
        (gu3_overBit_pair C.comp C.gen C.hmp (mem_pair_right _ _) (mem_pair_left _ _)
          hmp_ne.symm).symm))
  · refine π.gu3_image_eq Ψ₀ hΨ ?_ ?_
    · rw [gu3_cp_w_mq, gu3_cp_v_mq, gu3_cp_mq]
    · exact gu3_bool_eq_of_iff ((gu3_overBit_pair ⟨k + 3, π.hk₃, π.X₀⟩ π.X₀_generic π.X₀_cross_mq
        (mem_pair_left _ _) (mem_pair_right _ _) hqm_ne.symm).trans (hdet_mq.trans
        (gu3_overBit_pair C.comp C.gen C.hmq (mem_pair_left _ _) (mem_pair_right _ _) hmq_ne).symm))
  · refine π.gu3_image_eq Ψ₀ hΨ ?_ ?_
    · rw [gu3_cp_w_qm, gu3_cp_v_qm, gu3_cp_mq]
    · exact gu3_bool_eq_of_iff ((gu3_overBit_pair ⟨k + 3, π.hk₃, π.X₀⟩ π.X₀_generic π.X₀_cross_mq
        (mem_pair_right _ _) (mem_pair_left _ _) hqm_ne).trans (hdet_qm.trans
        (gu3_overBit_pair C.comp C.gen C.hmq (mem_pair_right _ _) (mem_pair_left _ _)
          hmq_ne.symm).symm))
  · refine π.gu3_image_eq Ψ₀ hΨ ?_ ?_
    · rw [gu3_cp_w_pq, gu3_cp_v_pq, gu3_cp_pq]
    · exact gu3_bool_eq_of_iff ((gu3_overBit_pair ⟨k + 3, π.hk₃, π.X₀⟩ π.X₀_generic π.X₀_cross_pq
        (mem_pair_left _ _) (mem_pair_right _ _) hpq_ne).trans (hdet_pq.trans
        (gu3_overBit_pair C.comp C.gen C.hpq (mem_pair_left _ _) (mem_pair_right _ _) hpq_ne').symm))
  · refine π.gu3_image_eq Ψ₀ hΨ ?_ ?_
    · rw [gu3_cp_w_qp, gu3_cp_v_qp, gu3_cp_pq]
    · exact gu3_bool_eq_of_iff ((gu3_overBit_pair ⟨k + 3, π.hk₃, π.X₀⟩ π.X₀_generic π.X₀_cross_pq
        (mem_pair_right _ _) (mem_pair_left _ _) hpq_ne.symm).trans (hdet_qp.trans
        (gu3_overBit_pair C.comp C.gen C.hpq (mem_pair_right _ _) (mem_pair_left _ _)
          hpq_ne'.symm).symm))

/-! ### U4 helpers (general): plane algebra, labels, shadow genericity read at label level -/

/-! shadow genericity of a one-component shadow, read at label level -/

/-! ### U4 helpers: the frame `(a; dm, v)` of the configuration and the functionals `α, β, γ` -/

/-- the three double points `a = x_mp`, `b = x_mq`, `c = x_pq` -/
noncomputable def gu4_a (_π : G11_ParamsSw C) : Plane := crossingPoint (xPair C.hmp)
noncomputable def gu4_b (_π : G11_ParamsSw C) : Plane := crossingPoint (xPair C.hmq)
noncomputable def gu4_c (_π : G11_ParamsSw C) : Plane := crossingPoint (xPair C.hpq)
/-- the parameters of `a`, `b` on `m` -/
noncomputable def gu4_tmp (_π : G11_ParamsSw C) : ℝ :=
  crossingParameter (xPair C.hmp) C.m (mem_pair_left _ _)
noncomputable def gu4_tmq (_π : G11_ParamsSw C) : ℝ :=
  crossingParameter (xPair C.hmq) C.m (mem_pair_left _ _)
/-- the direction of `m` and the frame vector `v = c − a` -/
noncomputable def gu4_dm (_π : G11_ParamsSw C) : Plane := edge C.X C.m
noncomputable def gu4_v (π : G11_ParamsSw C) : Plane := π.gu4_c - π.gu4_a
/-- the frame determinant `E = det dm v ≠ 0` -/
noncomputable def gu4_E (π : G11_ParamsSw C) : ℝ := det π.gu4_dm π.gu4_v
/-- the frame functionals: `α` vanishes on the line `p` (through `a, c`), `β` on the line `m`, `γ` on
the line `q` (through `b, c`) -/
noncomputable def gu4_α (π : G11_ParamsSw C) (y : Plane) : ℝ := det (y - π.gu4_a) π.gu4_v
noncomputable def gu4_β (π : G11_ParamsSw C) (y : Plane) : ℝ := det π.gu4_dm (y - π.gu4_a)
noncomputable def gu4_γ (π : G11_ParamsSw C) (y : Plane) : ℝ := det (y - π.gu4_b) (π.gu4_c - π.gu4_b)
/-- the three flat vertices `p_in, m₀, p_out` -/
noncomputable def gu4_pin (π : G11_ParamsSw C) : Plane := edgePoint C.X C.m π.t₁
noncomputable def gu4_m0 (π : G11_ParamsSw C) : Plane := edgePoint C.X C.m π.t₂
noncomputable def gu4_pout (π : G11_ParamsSw C) : Plane := edgePoint C.X C.m π.t₃

theorem gu4_h₁ : π.t₁ < π.gu4_tmp := π.h₁
theorem gu4_h₂ : π.gu4_tmp < π.t₂ := π.h₂
theorem gu4_h₃ : π.t₂ < π.gu4_tmq := π.h₃
theorem gu4_h₄ : π.gu4_tmq < π.t₃ := π.h₄

theorem gu4_a_eq : π.gu4_a = C.X C.m + π.gu4_tmp • π.gu4_dm :=
  (crossingParameter_spec (xPair C.hmp) C.m (mem_pair_left _ _)).2.2
theorem gu4_b_eq : π.gu4_b = C.X C.m + π.gu4_tmq • π.gu4_dm :=
  (crossingParameter_spec (xPair C.hmq) C.m (mem_pair_left _ _)).2.2

theorem gu4_a_mem_m : π.gu4_a ∈ edgeSegment C.X C.m := (gu4_crossingPoint_mem_pair C.hmp).1
theorem gu4_a_mem_p : π.gu4_a ∈ edgeSegment C.X C.p := (gu4_crossingPoint_mem_pair C.hmp).2
theorem gu4_b_mem_m : π.gu4_b ∈ edgeSegment C.X C.m := (gu4_crossingPoint_mem_pair C.hmq).1
theorem gu4_b_mem_q : π.gu4_b ∈ edgeSegment C.X C.q := (gu4_crossingPoint_mem_pair C.hmq).2
theorem gu4_c_mem_p : π.gu4_c ∈ edgeSegment C.X C.p := (gu4_crossingPoint_mem_pair C.hpq).1
theorem gu4_c_mem_q : π.gu4_c ∈ edgeSegment C.X C.q := (gu4_crossingPoint_mem_pair C.hpq).2

theorem gu4_remote_mp (_π : G11_ParamsSw C) : remote C.m C.p := gu4_remote_of_isCrossing C.hmp
theorem gu4_remote_mq (_π : G11_ParamsSw C) : remote C.m C.q := gu4_remote_of_isCrossing C.hmq
theorem gu4_remote_pq (_π : G11_ParamsSw C) : remote C.p C.q := gu4_remote_of_isCrossing C.hpq

theorem gu4_det_mp (π : G11_ParamsSw C) : det (edge C.X C.m) (edge C.X C.p) ≠ 0 :=
  gu4_gen_trans C.gen _ _ π.gu4_remote_mp ⟨π.gu4_a, π.gu4_a_mem_m, π.gu4_a_mem_p⟩
theorem gu4_det_mq (π : G11_ParamsSw C) : det (edge C.X C.m) (edge C.X C.q) ≠ 0 :=
  gu4_gen_trans C.gen _ _ π.gu4_remote_mq ⟨π.gu4_b, π.gu4_b_mem_m, π.gu4_b_mem_q⟩
theorem gu4_det_pq (π : G11_ParamsSw C) : det (edge C.X C.p) (edge C.X C.q) ≠ 0 :=
  gu4_gen_trans C.gen _ _ π.gu4_remote_pq ⟨π.gu4_c, π.gu4_c_mem_p, π.gu4_c_mem_q⟩

/-- `a ≠ c` (else a triple point of `m, p, q`) -/
theorem gu4_a_ne_c : π.gu4_a ≠ π.gu4_c := by
  intro h
  have ha := gu4_crossingPoint_mem_interior C.gen C.hmp
  have hc := gu4_crossingPoint_mem_interior C.gen C.hpq
  refine gu4_gen_triple C.gen ⟨C.m, C.p, C.q, gu4_ne_of_remote π.gu4_remote_mp,
    gu4_ne_of_remote π.gu4_remote_pq, gu4_ne_of_remote π.gu4_remote_mq, π.gu4_a, ⟨ha.1, ha.2⟩, ?_⟩
  rw [h]
  exact hc.2

theorem gu4_b_ne_c : π.gu4_b ≠ π.gu4_c := by
  intro h
  have hb := gu4_crossingPoint_mem_interior C.gen C.hmq
  have hc := gu4_crossingPoint_mem_interior C.gen C.hpq
  refine gu4_gen_triple C.gen ⟨C.m, C.q, C.p, gu4_ne_of_remote π.gu4_remote_mq,
    (gu4_ne_of_remote π.gu4_remote_pq).symm, gu4_ne_of_remote π.gu4_remote_mp, π.gu4_b,
    ⟨hb.1, hb.2⟩, ?_⟩
  rw [h]
  exact hc.1

/-- `v = c − a` is a nonzero multiple of the direction of `p` -/
theorem gu4_v_eq : ∃ κ : ℝ, κ ≠ 0 ∧ π.gu4_v = κ • edge C.X C.p := by
  obtain ⟨κ, hκ⟩ := gu4_sub_of_mem_edge π.gu4_a_mem_p π.gu4_c_mem_p
  refine ⟨κ, ?_, hκ⟩
  rintro rfl
  rw [zero_smul, sub_eq_zero] at hκ
  exact π.gu4_a_ne_c hκ.symm

/-- `c − b` is a nonzero multiple of the direction of `q` -/
theorem gu4_cb_eq : ∃ κ : ℝ, κ ≠ 0 ∧ π.gu4_c - π.gu4_b = κ • edge C.X C.q := by
  obtain ⟨κ, hκ⟩ := gu4_sub_of_mem_edge π.gu4_b_mem_q π.gu4_c_mem_q
  refine ⟨κ, ?_, hκ⟩
  rintro rfl
  rw [zero_smul, sub_eq_zero] at hκ
  exact π.gu4_b_ne_c hκ.symm

theorem gu4_E_ne : π.gu4_E ≠ 0 := by
  obtain ⟨κ, hκ, hv⟩ := π.gu4_v_eq
  unfold gu4_E
  rw [hv, gu4_det_smul_right]
  exact mul_ne_zero hκ π.gu4_det_mp

theorem gu4_b_sub_a : π.gu4_b = π.gu4_a + (π.gu4_tmq - π.gu4_tmp) • π.gu4_dm := by
  rw [π.gu4_a_eq, π.gu4_b_eq, sub_smul]
  abel

theorem gu4_c_eq : π.gu4_c = π.gu4_a + π.gu4_v := by
  unfold gu4_v
  abel

/-- any point of `m` in the frame -/
theorem gu4_edgePoint_m (t : ℝ) :
    edgePoint C.X C.m t = π.gu4_a + (t - π.gu4_tmp) • π.gu4_dm + (0 : ℝ) • π.gu4_v := by
  rw [zero_smul, add_zero, π.gu4_a_eq, sub_smul]
  simp only [edgePoint, gu4_dm]
  abel

/-- the frame functionals on `a + s • dm + t • v` -/
theorem gu4_α_frame (s t : ℝ) : π.gu4_α (π.gu4_a + s • π.gu4_dm + t • π.gu4_v) = s * π.gu4_E := by
  simp only [gu4_α, gu4_E, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem gu4_β_frame (s t : ℝ) : π.gu4_β (π.gu4_a + s • π.gu4_dm + t • π.gu4_v) = t * π.gu4_E := by
  simp only [gu4_β, gu4_E, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem gu4_γ_frame (s t : ℝ) : π.gu4_γ (π.gu4_a + s • π.gu4_dm + t • π.gu4_v) =
    (s + (π.gu4_tmq - π.gu4_tmp) * (t - 1)) * π.gu4_E := by
  rw [gu4_γ, π.gu4_b_sub_a, π.gu4_c_eq]
  simp only [gu4_E, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- every point in the frame -/
theorem gu4_frame (y : Plane) :
    y = π.gu4_a + (π.gu4_α y / π.gu4_E) • π.gu4_dm + (π.gu4_β y / π.gu4_E) • π.gu4_v := by
  have h := gu4_cramer π.gu4_dm π.gu4_v (y - π.gu4_a) π.gu4_E_ne
  unfold gu4_α gu4_β gu4_E
  rw [add_assoc, ← h]
  abel

theorem gu4_eq_of_αβ {y z : Plane} (hα : π.gu4_α y = π.gu4_α z) (hβ : π.gu4_β y = π.gu4_β z) :
    y = z := by
  rw [π.gu4_frame y, π.gu4_frame z, hα, hβ]

/-- `γ` is determined by `α, β`: `γ = α + L (β − E)` where `L = tmq − tmp` -/
theorem gu4_γ_eq (y : Plane) :
    π.gu4_γ y = π.gu4_α y + (π.gu4_tmq - π.gu4_tmp) * (π.gu4_β y - π.gu4_E) := by
  have h := π.gu4_γ_frame (π.gu4_α y / π.gu4_E) (π.gu4_β y / π.gu4_E)
  rw [← π.gu4_frame y] at h
  rw [h]
  have hE := π.gu4_E_ne
  field_simp

/-- the lines: `α = 0` on `p`, `γ = 0` on `q`, `β = 0` on `m` -/
theorem gu4_α_of_mem_p {y : Plane} (hy : y ∈ edgeSegment C.X C.p) : π.gu4_α y = 0 := by
  obtain ⟨κ, hκ⟩ := gu4_sub_of_mem_edge π.gu4_a_mem_p hy
  obtain ⟨κ', -, hv⟩ := π.gu4_v_eq
  unfold gu4_α
  rw [hκ, hv, gu4_det_smul_left, gu4_det_smul_right, gu4_det_self, mul_zero, mul_zero]

theorem gu4_γ_of_mem_q {y : Plane} (hy : y ∈ edgeSegment C.X C.q) : π.gu4_γ y = 0 := by
  obtain ⟨κ, hκ⟩ := gu4_sub_of_mem_edge π.gu4_b_mem_q hy
  obtain ⟨κ', -, hv⟩ := π.gu4_cb_eq
  unfold gu4_γ
  rw [hκ, hv, gu4_det_smul_left, gu4_det_smul_right, gu4_det_self, mul_zero, mul_zero]

theorem gu4_β_of_m (t : ℝ) : π.gu4_β (edgePoint C.X C.m t) = 0 := by
  rw [π.gu4_edgePoint_m t, gu4_β_frame, zero_mul]

theorem gu4_α_of_m (t : ℝ) : π.gu4_α (edgePoint C.X C.m t) = (t - π.gu4_tmp) * π.gu4_E := by
  rw [π.gu4_edgePoint_m t, gu4_α_frame]

theorem gu4_γ_of_m (t : ℝ) : π.gu4_γ (edgePoint C.X C.m t) = (t - π.gu4_tmq) * π.gu4_E := by
  rw [π.gu4_edgePoint_m t, gu4_γ_frame]
  ring

/-- a point with `α = β = 0` is `a`; with `α = 0`, `γ = 0` it is `c`; with `β = 0`, `γ = 0` it is `b` -/
theorem gu4_eq_a_of {y : Plane} (hα : π.gu4_α y = 0) (hβ : π.gu4_β y = 0) : y = π.gu4_a := by
  apply π.gu4_eq_of_αβ
  · rw [hα]; simp [gu4_α, det]
  · rw [hβ]; simp [gu4_β, det]

theorem gu4_eq_c_of {y : Plane} (hα : π.gu4_α y = 0) (hγ : π.gu4_γ y = 0) : y = π.gu4_c := by
  have hE := π.gu4_E_ne
  have hL : 0 < π.gu4_tmq - π.gu4_tmp := sub_pos.mpr C.order
  have h := π.gu4_γ_eq y
  rw [hγ, hα] at h
  have hβ : π.gu4_β y = π.gu4_E := by
    have : (π.gu4_tmq - π.gu4_tmp) * (π.gu4_β y - π.gu4_E) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hL.ne'
    · linarith
  apply π.gu4_eq_of_αβ
  · rw [hα, π.gu4_c_eq, gu4_α, add_sub_cancel_left, gu4_det_self]
  · rw [hβ, π.gu4_c_eq, gu4_β, add_sub_cancel_left]; rfl

theorem gu4_eq_b_of {y : Plane} (hβ : π.gu4_β y = 0) (hγ : π.gu4_γ y = 0) : y = π.gu4_b := by
  have hE := π.gu4_E_ne
  have h := π.gu4_γ_eq y
  rw [hγ, hβ] at h
  have hα : π.gu4_α y = (π.gu4_tmq - π.gu4_tmp) * π.gu4_E := by linarith
  apply π.gu4_eq_of_αβ
  · rw [hα, π.gu4_b_sub_a, gu4_α, add_sub_cancel_left, gu4_det_smul_left]; rfl
  · rw [hβ, π.gu4_b_sub_a, gu4_β, add_sub_cancel_left, gu4_det_smul_right, gu4_det_self, mul_zero]

/-! ### U4 helpers: the labels of `X₀` and `X₁` -/

theorem gu4_mval_lt (_π : G11_ParamsSw C) : C.m.val < k := ZMod.val_lt C.m

theorem gu4_val_mA : π.mA.val = C.m.val :=
  ZMod.val_cast_of_lt (by have := π.gu4_mval_lt; omega)
theorem gu4_val_mB : π.mB.val = C.m.val + 1 :=
  ZMod.val_cast_of_lt (by have := π.gu4_mval_lt; omega)
theorem gu4_val_mC : π.mC.val = C.m.val + 2 :=
  ZMod.val_cast_of_lt (by have := π.gu4_mval_lt; omega)
theorem gu4_val_mD : π.mD.val = C.m.val + 3 :=
  ZMod.val_cast_of_lt (by have := π.gu4_mval_lt; omega)

theorem gu4_mA_ne_mB : π.mA ≠ π.mB := fun h => by
  have := congrArg ZMod.val h; rw [gu4_val_mA, gu4_val_mB] at this; omega
theorem gu4_mA_ne_mC : π.mA ≠ π.mC := fun h => by
  have := congrArg ZMod.val h; rw [gu4_val_mA, gu4_val_mC] at this; omega
theorem gu4_mA_ne_mD : π.mA ≠ π.mD := fun h => by
  have := congrArg ZMod.val h; rw [gu4_val_mA, gu4_val_mD] at this; omega
theorem gu4_mB_ne_mC : π.mB ≠ π.mC := fun h => by
  have := congrArg ZMod.val h; rw [gu4_val_mB, gu4_val_mC] at this; omega
theorem gu4_mB_ne_mD : π.mB ≠ π.mD := fun h => by
  have := congrArg ZMod.val h; rw [gu4_val_mB, gu4_val_mD] at this; omega
theorem gu4_mC_ne_mD : π.mC ≠ π.mD := fun h => by
  have := congrArg ZMod.val h; rw [gu4_val_mC, gu4_val_mD] at this; omega

theorem gu4_mA_succ : π.mA + 1 = π.mB := by simp only [mA, mB]; push_cast; ring
theorem gu4_mB_succ : π.mB + 1 = π.mC := by simp only [mB, mC]; push_cast; ring
theorem gu4_mC_succ : π.mC + 1 = π.mD := by simp only [mC, mD]; push_cast; ring
theorem gu4_mid_eq : π.mid = π.mC := rfl

theorem gu4_X₀_apply (j : ZMod (k + 3)) : π.X₀ j =
    if j.val ≤ C.m.val then C.X (j.val : ZMod k)
    else if j.val = C.m.val + 1 then π.gu4_pin
    else if j.val = C.m.val + 2 then π.gu4_m0
    else if j.val = C.m.val + 3 then π.gu4_pout
    else C.X ((j.val - 3 : ℕ) : ZMod k) := rfl

theorem gu4_X₀_mA : π.X₀ π.mA = C.X C.m := by
  rw [gu4_X₀_apply, ite_eq_left (le_of_eq π.gu4_val_mA), gu4_val_mA, ZMod.natCast_zmod_val]
theorem gu4_X₀_mB : π.X₀ π.mB = π.gu4_pin := by
  rw [gu4_X₀_apply, gu4_val_mB, ite_eq_right (by omega), ite_eq_left rfl]
theorem gu4_X₀_mC : π.X₀ π.mC = π.gu4_m0 := by
  rw [gu4_X₀_apply, gu4_val_mC, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
theorem gu4_X₀_mD : π.X₀ π.mD = π.gu4_pout := by
  rw [gu4_X₀_apply, gu4_val_mD, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

theorem gu4_X₀_mD_succ : π.X₀ (π.mD + 1) = C.X (C.m + 1) := by
  have hm := π.gu4_mval_lt
  have h4 : π.mD + 1 = ((C.m.val + 4 : ℕ) : ZMod (k + 3)) := by simp only [mD]; push_cast; ring
  rw [h4, gu4_X₀_apply]
  rcases lt_or_eq_of_le (show C.m.val + 4 ≤ k + 3 by omega) with hlt | heq
  · rw [ZMod.val_cast_of_lt hlt, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
    congr 1
    rw [show C.m.val + 4 - 3 = C.m.val + 1 by omega]
    push_cast
    rw [ZMod.natCast_zmod_val]
  · rw [heq, ZMod.natCast_self, ZMod.val_zero, ite_eq_left (Nat.zero_le _)]
    congr 1
    have hmk : C.m = ((k - 1 : ℕ) : ZMod k) := by
      rw [← ZMod.natCast_zmod_val C.m]
      congr 1
      omega
    rw [hmk, Nat.cast_zero, Smoothing.zcast_sub_self (by omega : 1 ≤ k), Nat.cast_one,
      neg_add_cancel]

theorem gu4_val_lab (i : ZMod k) (_hi : i ≠ C.m) :
    (G11_lab C.m i).val = if i.val ≤ C.m.val then i.val else i.val + 3 := by
  have hi' := ZMod.val_lt i
  unfold G11_lab
  split_ifs with h
  · exact ZMod.val_cast_of_lt (by omega)
  · exact ZMod.val_cast_of_lt (by omega)

theorem gu4_lab_spec (i : ZMod k) (hi : i ≠ C.m) :
    π.X₀ (G11_lab C.m i) = C.X i ∧ π.X₀ (G11_lab C.m i + 1) = C.X (i + 1) := by
  have hi' := ZMod.val_lt i
  have hm := π.gu4_mval_lt
  have hne : i.val ≠ C.m.val := fun h => hi (ZMod.val_injective k h)
  by_cases hle : i.val ≤ C.m.val
  · have hlt : i.val < C.m.val := lt_of_le_of_ne hle hne
    have hlab : G11_lab C.m i = ((i.val : ℕ) : ZMod (k + 3)) := by
      unfold G11_lab; rw [ite_eq_left hle]
    constructor
    · rw [hlab, gu4_X₀_apply, ZMod.val_cast_of_lt (by omega), ite_eq_left hle, ZMod.natCast_zmod_val]
    · rw [hlab, ← Nat.cast_add_one, gu4_X₀_apply, ZMod.val_cast_of_lt (by omega), ite_eq_left (by omega)]
      congr 1
      push_cast
      rw [ZMod.natCast_zmod_val]
  · have hgt : C.m.val < i.val := lt_of_not_ge hle
    have hlab : G11_lab C.m i = ((i.val + 3 : ℕ) : ZMod (k + 3)) := by
      unfold G11_lab; rw [ite_eq_right hle]
    constructor
    · rw [hlab, gu4_X₀_apply, ZMod.val_cast_of_lt (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega)]
      congr 1
      rw [Nat.add_sub_cancel, ZMod.natCast_zmod_val]
    · rw [hlab, ← Nat.cast_add_one, gu4_X₀_apply]
      rcases lt_or_eq_of_le (show i.val + 3 + 1 ≤ k + 3 by omega) with hlt | heq
      · rw [ZMod.val_cast_of_lt hlt, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)]
        congr 1
        rw [show i.val + 3 + 1 - 3 = i.val + 1 by omega]
        push_cast
        rw [ZMod.natCast_zmod_val]
      · rw [heq, ZMod.natCast_self, ZMod.val_zero, ite_eq_left (Nat.zero_le _)]
        congr 1
        have hik : i = ((k - 1 : ℕ) : ZMod k) := by
          rw [← ZMod.natCast_zmod_val i]
          congr 1
          omega
        rw [hik, Nat.cast_zero, Smoothing.zcast_sub_self (by omega : 1 ≤ k), Nat.cast_one,
          neg_add_cancel]

theorem gu4_label_cases (j : ZMod (k + 3)) :
    j = π.mA ∨ j = π.mB ∨ j = π.mC ∨ j = π.mD ∨ ∃ i : ZMod k, i ≠ C.m ∧ j = G11_lab C.m i := by
  have hj := ZMod.val_lt j
  have hm := π.gu4_mval_lt
  have hj' : j = ((j.val : ℕ) : ZMod (k + 3)) := (ZMod.natCast_zmod_val j).symm
  rcases (by omega : j.val < C.m.val ∨ j.val = C.m.val ∨ j.val = C.m.val + 1 ∨
      j.val = C.m.val + 2 ∨ j.val = C.m.val + 3 ∨ C.m.val + 4 ≤ j.val) with h | h | h | h | h | h
  · right; right; right; right
    refine ⟨((j.val : ℕ) : ZMod k), ?_, ?_⟩
    · intro he
      have := congrArg ZMod.val he
      rw [ZMod.val_cast_of_lt (by omega)] at this
      omega
    · unfold G11_lab
      rw [ZMod.val_cast_of_lt (by omega), ite_eq_left h.le]
      exact hj'
  · left; rw [hj', h]; rfl
  · right; left; rw [hj', h]; rfl
  · right; right; left; rw [hj', h]; rfl
  · right; right; right; left; rw [hj', h]; rfl
  · right; right; right; right
    refine ⟨((j.val - 3 : ℕ) : ZMod k), ?_, ?_⟩
    · intro he
      have := congrArg ZMod.val he
      rw [ZMod.val_cast_of_lt (by omega)] at this
      omega
    · unfold G11_lab
      rw [ZMod.val_cast_of_lt (by omega), ite_eq_right (by omega), show j.val - 3 + 3 = j.val by omega]
      exact hj'

theorem gu4_lab_ne_pieces (i : ZMod k) (hi : i ≠ C.m) :
    G11_lab C.m i ≠ π.mA ∧ G11_lab C.m i ≠ π.mB ∧ G11_lab C.m i ≠ π.mC ∧ G11_lab C.m i ≠ π.mD := by
  have hv := gu4_val_lab i hi
  have hne : i.val ≠ C.m.val := fun h => hi (ZMod.val_injective k h)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrArg ZMod.val h; rw [hv, gu4_val_mA] at this; split_ifs at this <;> omega
  · have := congrArg ZMod.val h; rw [hv, gu4_val_mB] at this; split_ifs at this <;> omega
  · have := congrArg ZMod.val h; rw [hv, gu4_val_mC] at this; split_ifs at this <;> omega
  · have := congrArg ZMod.val h; rw [hv, gu4_val_mD] at this; split_ifs at this <;> omega

theorem gu4_lab_injective {i i' : ZMod k} (hi : i ≠ C.m) (hi' : i' ≠ C.m)
    (h : G11_lab C.m i = G11_lab C.m i') : i = i' := by
  have hv := congrArg ZMod.val h
  rw [gu4_val_lab i hi, gu4_val_lab i' hi'] at hv
  apply ZMod.val_injective
  split_ifs at hv <;> omega

theorem gu4_p_ne_m (π : G11_ParamsSw C) : C.p ≠ C.m := (remote_endpoints _ _ π.gu4_remote_mp).1
theorem gu4_q_ne_m (π : G11_ParamsSw C) : C.q ≠ C.m := (remote_endpoints _ _ π.gu4_remote_mq).1
theorem gu4_q_ne_p (π : G11_ParamsSw C) : C.q ≠ C.p := (remote_endpoints _ _ π.gu4_remote_pq).1

theorem gu4_seg_X₀_lab (i : ZMod k) (hi : i ≠ C.m) :
    edgeSegment π.X₀ (G11_lab C.m i) = edgeSegment C.X i := by
  simp only [edgeSegment, edgePoint, edge, (π.gu4_lab_spec i hi).1, (π.gu4_lab_spec i hi).2]
theorem gu4_int_X₀_lab (i : ZMod k) (hi : i ≠ C.m) :
    edgeInterior π.X₀ (G11_lab C.m i) = edgeInterior C.X i := by
  simp only [edgeInterior, edgePoint, edge, (π.gu4_lab_spec i hi).1, (π.gu4_lab_spec i hi).2]
theorem gu4_edge_X₀_lab (i : ZMod k) (hi : i ≠ C.m) :
    edge π.X₀ (G11_lab C.m i) = edge C.X i := by
  simp only [edge, (π.gu4_lab_spec i hi).1, (π.gu4_lab_spec i hi).2]

theorem gu4_seg_X₀_p' : edgeSegment π.X₀ π.p' = edgeSegment C.X C.p := π.gu4_seg_X₀_lab C.p π.gu4_p_ne_m
theorem gu4_seg_X₀_q' : edgeSegment π.X₀ π.q' = edgeSegment C.X C.q := π.gu4_seg_X₀_lab C.q π.gu4_q_ne_m
theorem gu4_edge_X₀_p' : edge π.X₀ π.p' = edge C.X C.p := π.gu4_edge_X₀_lab C.p π.gu4_p_ne_m
theorem gu4_edge_X₀_q' : edge π.X₀ π.q' = edge C.X C.q := π.gu4_edge_X₀_lab C.q π.gu4_q_ne_m
theorem gu4_p'_ne : π.p' ≠ π.mA ∧ π.p' ≠ π.mB ∧ π.p' ≠ π.mC ∧ π.p' ≠ π.mD :=
  π.gu4_lab_ne_pieces C.p π.gu4_p_ne_m
theorem gu4_q'_ne : π.q' ≠ π.mA ∧ π.q' ≠ π.mB ∧ π.q' ≠ π.mC ∧ π.q' ≠ π.mD :=
  π.gu4_lab_ne_pieces C.q π.gu4_q_ne_m
theorem gu4_p'_ne_q' : π.p' ≠ π.q' := fun h => π.gu4_q_ne_p (gu4_lab_injective π.gu4_p_ne_m π.gu4_q_ne_m h).symm

/-! the four pieces of `m` in `X₀` -/

theorem gu4_pin_eq : π.gu4_pin = C.X C.m + π.t₁ • π.gu4_dm := rfl
theorem gu4_m0_eq : π.gu4_m0 = C.X C.m + π.t₂ • π.gu4_dm := rfl
theorem gu4_pout_eq : π.gu4_pout = C.X C.m + π.t₃ • π.gu4_dm := rfl
theorem gu4_Xm_eq : C.X C.m = C.X C.m + (0 : ℝ) • π.gu4_dm := by simp
theorem gu4_Xm1_eq : C.X (C.m + 1) = C.X C.m + (1 : ℝ) • π.gu4_dm := by simp [gu4_dm, edge]

theorem gu4_edge_X₀_mA : edge π.X₀ π.mA = π.t₁ • π.gu4_dm := by
  rw [edge, gu4_mA_succ, gu4_X₀_mB, gu4_X₀_mA, gu4_pin_eq, add_sub_cancel_left]
theorem gu4_edge_X₀_mB : edge π.X₀ π.mB = (π.t₂ - π.t₁) • π.gu4_dm := by
  rw [edge, gu4_mB_succ, gu4_X₀_mC, gu4_X₀_mB, gu4_m0_eq, gu4_pin_eq, sub_smul]; abel
theorem gu4_edge_X₀_mC : edge π.X₀ π.mC = (π.t₃ - π.t₂) • π.gu4_dm := by
  rw [edge, gu4_mC_succ, gu4_X₀_mD, gu4_X₀_mC, gu4_pout_eq, gu4_m0_eq, sub_smul]; abel
theorem gu4_edge_X₀_mD : edge π.X₀ π.mD = (1 - π.t₃) • π.gu4_dm := by
  rw [edge, gu4_X₀_mD_succ, gu4_X₀_mD, gu4_Xm1_eq, gu4_pout_eq, sub_smul]; abel

theorem gu4_mem_mA (y : Plane) :
    y ∈ edgeSegment π.X₀ π.mA ↔ ∃ t, 0 ≤ t ∧ t ≤ π.t₁ ∧ y = edgePoint C.X C.m t :=
  gu4_mem_edgeSegment_iff π.X₀ π.mA (Q := C.X C.m) (u := π.gu4_dm)
    (by rw [gu4_X₀_mA]; exact π.gu4_Xm_eq) (by rw [gu4_mA_succ, gu4_X₀_mB]; rfl) π.ht₁ y
theorem gu4_mem_mB (y : Plane) :
    y ∈ edgeSegment π.X₀ π.mB ↔ ∃ t, π.t₁ ≤ t ∧ t ≤ π.t₂ ∧ y = edgePoint C.X C.m t :=
  gu4_mem_edgeSegment_iff π.X₀ π.mB (Q := C.X C.m) (u := π.gu4_dm)
    (by rw [gu4_X₀_mB]; rfl) (by rw [gu4_mB_succ, gu4_X₀_mC]; rfl) (π.gu4_h₁.trans π.gu4_h₂) y
theorem gu4_mem_mC (y : Plane) :
    y ∈ edgeSegment π.X₀ π.mC ↔ ∃ t, π.t₂ ≤ t ∧ t ≤ π.t₃ ∧ y = edgePoint C.X C.m t :=
  gu4_mem_edgeSegment_iff π.X₀ π.mC (Q := C.X C.m) (u := π.gu4_dm)
    (by rw [gu4_X₀_mC]; rfl) (by rw [gu4_mC_succ, gu4_X₀_mD]; rfl) (π.gu4_h₃.trans π.gu4_h₄) y
theorem gu4_mem_mD (y : Plane) :
    y ∈ edgeSegment π.X₀ π.mD ↔ ∃ t, π.t₃ ≤ t ∧ t ≤ 1 ∧ y = edgePoint C.X C.m t :=
  gu4_mem_edgeSegment_iff π.X₀ π.mD (Q := C.X C.m) (u := π.gu4_dm)
    (by rw [gu4_X₀_mD]; rfl) (by rw [gu4_X₀_mD_succ]; exact π.gu4_Xm1_eq) π.ht₃ y

/-! `X₁` -/

theorem gu4_X₁_of_ne (j : ZMod (k + 3)) (hj : j ≠ π.mC) : π.X₁ j = π.X₀ j :=
  Function.update_of_ne hj _ _
theorem gu4_X₁_mC : π.X₁ π.mC = π.apex := Function.update_self _ _ _
theorem gu4_X₁_mA : π.X₁ π.mA = C.X C.m := by rw [π.gu4_X₁_of_ne _ π.gu4_mA_ne_mC, gu4_X₀_mA]
theorem gu4_X₁_mB : π.X₁ π.mB = π.gu4_pin := by rw [π.gu4_X₁_of_ne _ π.gu4_mB_ne_mC, gu4_X₀_mB]
theorem gu4_X₁_mD : π.X₁ π.mD = π.gu4_pout := by
  rw [π.gu4_X₁_of_ne _ π.gu4_mC_ne_mD.symm, gu4_X₀_mD]

theorem gu4_succ_ne_mC (j : ZMod (k + 3)) (hj : j ≠ π.mB) : j + 1 ≠ π.mC :=
  fun h => hj (add_right_cancel (h.trans π.gu4_mB_succ.symm))

theorem gu4_X₁_mD_succ : π.X₁ (π.mD + 1) = C.X (C.m + 1) := by
  rw [π.gu4_X₁_of_ne _ (π.gu4_succ_ne_mC _ π.gu4_mB_ne_mD.symm), gu4_X₀_mD_succ]

theorem gu4_seg_X₁_eq (i : ZMod (k + 3)) (hi : i ≠ π.mB) (hi' : i ≠ π.mC) :
    edgeSegment π.X₁ i = edgeSegment π.X₀ i := by
  simp only [edgeSegment, edgePoint, edge, π.gu4_X₁_of_ne _ hi', π.gu4_X₁_of_ne _ (π.gu4_succ_ne_mC i hi)]
theorem gu4_int_X₁_eq (i : ZMod (k + 3)) (hi : i ≠ π.mB) (hi' : i ≠ π.mC) :
    edgeInterior π.X₁ i = edgeInterior π.X₀ i := by
  simp only [edgeInterior, edgePoint, edge, π.gu4_X₁_of_ne _ hi',
    π.gu4_X₁_of_ne _ (π.gu4_succ_ne_mC i hi)]
theorem gu4_edge_X₁_eq (i : ZMod (k + 3)) (hi : i ≠ π.mB) (hi' : i ≠ π.mC) :
    edge π.X₁ i = edge π.X₀ i := by
  rw [edge, edge, π.gu4_X₁_of_ne _ hi', π.gu4_X₁_of_ne _ (π.gu4_succ_ne_mC i hi)]

theorem gu4_edge_X₁_mB : edge π.X₁ π.mB = π.apex - π.gu4_pin := by
  rw [edge, gu4_mB_succ, gu4_X₁_mC, gu4_X₁_mB]
theorem gu4_edge_X₁_mC : edge π.X₁ π.mC = π.gu4_pout - π.apex := by
  rw [edge, gu4_mC_succ, gu4_X₁_mD, gu4_X₁_mC]

theorem gu4_mem_segB (y : Plane) : y ∈ edgeSegment π.X₁ π.mB ↔
    ∃ σ : ℝ, 0 ≤ σ ∧ σ ≤ 1 ∧ y = π.gu4_pin + σ • (π.apex - π.gu4_pin) := by
  simp only [edgeSegment, edgePoint, gu4_X₁_mB, gu4_edge_X₁_mB, Set.mem_ofPred_eq]
theorem gu4_mem_intB (y : Plane) : y ∈ edgeInterior π.X₁ π.mB ↔
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ y = π.gu4_pin + σ • (π.apex - π.gu4_pin) := by
  simp only [edgeInterior, edgePoint, gu4_X₁_mB, gu4_edge_X₁_mB, Set.mem_ofPred_eq]
theorem gu4_mem_segC (y : Plane) : y ∈ edgeSegment π.X₁ π.mC ↔
    ∃ σ : ℝ, 0 ≤ σ ∧ σ ≤ 1 ∧ y = π.apex + σ • (π.gu4_pout - π.apex) := by
  simp only [edgeSegment, edgePoint, gu4_X₁_mC, gu4_edge_X₁_mC, Set.mem_ofPred_eq]
theorem gu4_mem_intC (y : Plane) : y ∈ edgeInterior π.X₁ π.mC ↔
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ y = π.apex + σ • (π.gu4_pout - π.apex) := by
  simp only [edgeInterior, edgePoint, gu4_X₁_mC, gu4_edge_X₁_mC, Set.mem_ofPred_eq]

/-! the apex and the bent edges in the frame -/

theorem gu4_apex_frame :
    π.apex = π.gu4_a + ((1 - π.lam) * (π.t₂ - π.gu4_tmp)) • π.gu4_dm + π.lam • π.gu4_v := by
  have hm0 : edgePoint C.X C.m π.t₂ = π.gu4_a + (π.t₂ - π.gu4_tmp) • π.gu4_dm := by
    rw [π.gu4_edgePoint_m π.t₂, zero_smul, add_zero]
  have hc : crossingPoint (xPair C.hpq) = π.gu4_a + π.gu4_v := π.gu4_c_eq
  rw [apex, hm0, hc]
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring

theorem gu4_segB_frame (σ : ℝ) : π.gu4_pin + σ • (π.apex - π.gu4_pin) =
    π.gu4_a + ((1 - σ) * (π.t₁ - π.gu4_tmp) + σ * ((1 - π.lam) * (π.t₂ - π.gu4_tmp))) • π.gu4_dm +
      (σ * π.lam) • π.gu4_v := by
  rw [gu4_apex_frame, gu4_pin, π.gu4_edgePoint_m π.t₁]
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring

theorem gu4_segC_frame (σ : ℝ) : π.apex + σ • (π.gu4_pout - π.apex) =
    π.gu4_a + ((1 - σ) * ((1 - π.lam) * (π.t₂ - π.gu4_tmp)) + σ * (π.t₃ - π.gu4_tmp)) • π.gu4_dm +
      ((1 - σ) * π.lam) • π.gu4_v := by
  rw [gu4_apex_frame, gu4_pout, π.gu4_edgePoint_m π.t₃]
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring

theorem gu4_α_segB (σ : ℝ) : π.gu4_α (π.gu4_pin + σ • (π.apex - π.gu4_pin)) =
    ((1 - σ) * (π.t₁ - π.gu4_tmp) + σ * ((1 - π.lam) * (π.t₂ - π.gu4_tmp))) * π.gu4_E := by
  rw [gu4_segB_frame, gu4_α_frame]
theorem gu4_β_segB (σ : ℝ) : π.gu4_β (π.gu4_pin + σ • (π.apex - π.gu4_pin)) =
    (σ * π.lam) * π.gu4_E := by
  rw [gu4_segB_frame, gu4_β_frame]
theorem gu4_γ_segB (σ : ℝ) : π.gu4_γ (π.gu4_pin + σ • (π.apex - π.gu4_pin)) =
    ((1 - σ) * (π.t₁ - π.gu4_tmq) + σ * ((π.lam - 1) * (π.gu4_tmq - π.t₂))) * π.gu4_E := by
  rw [gu4_segB_frame, gu4_γ_frame]; ring
theorem gu4_α_segC (σ : ℝ) : π.gu4_α (π.apex + σ • (π.gu4_pout - π.apex)) =
    ((1 - σ) * ((1 - π.lam) * (π.t₂ - π.gu4_tmp)) + σ * (π.t₃ - π.gu4_tmp)) * π.gu4_E := by
  rw [gu4_segC_frame, gu4_α_frame]
theorem gu4_β_segC (σ : ℝ) : π.gu4_β (π.apex + σ • (π.gu4_pout - π.apex)) =
    ((1 - σ) * π.lam) * π.gu4_E := by
  rw [gu4_segC_frame, gu4_β_frame]
theorem gu4_γ_segC (σ : ℝ) : π.gu4_γ (π.apex + σ • (π.gu4_pout - π.apex)) =
    ((1 - σ) * ((π.lam - 1) * (π.gu4_tmq - π.t₂)) + σ * (π.t₃ - π.gu4_tmq)) * π.gu4_E := by
  rw [gu4_segC_frame, gu4_γ_frame]; ring

/-- the bent edge `[p_in, w]` stays strictly on the `a`-side of the line `p` -/
theorem gu4_segB_coeff_neg {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    (1 - σ) * (π.t₁ - π.gu4_tmp) + σ * ((1 - π.lam) * (π.t₂ - π.gu4_tmp)) < 0 := by
  have hA : π.t₁ - π.gu4_tmp < 0 := sub_neg.mpr π.gu4_h₁
  have hB : (1 - π.lam) * (π.t₂ - π.gu4_tmp) < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr π.hlam) (sub_pos.mpr π.gu4_h₂)
  rcases lt_or_eq_of_le h1 with hlt | rfl
  · have := mul_neg_of_pos_of_neg (sub_pos.mpr hlt) hA
    have := mul_nonpos_of_nonneg_of_nonpos h0 hB.le
    linarith
  · simpa using hB

/-- the bent edge `[w, p_out]` stays strictly on the far side of the line `q` -/
theorem gu4_segC_coeff_pos {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    0 < (1 - σ) * ((π.lam - 1) * (π.gu4_tmq - π.t₂)) + σ * (π.t₃ - π.gu4_tmq) := by
  have hA : 0 < (π.lam - 1) * (π.gu4_tmq - π.t₂) :=
    mul_pos (sub_pos.mpr π.hlam) (sub_pos.mpr π.gu4_h₃)
  have hB : 0 < π.t₃ - π.gu4_tmq := sub_pos.mpr π.gu4_h₄
  rcases lt_or_eq_of_le h1 with hlt | rfl
  · have := mul_pos (sub_pos.mpr hlt) hA
    have := mul_nonneg h0 hB.le
    linarith
  · simpa using hB

/-! the disc `U` -/

theorem gu4_theta_sub_U : convexHull ℝ {π.gu4_pin, π.apex, π.gu4_pout} ⊆ π.U :=
  fun _ hy => interior_subset (π.theta_sub hy)

theorem gu4_segB_sub_U {y : Plane} (hy : y ∈ edgeSegment π.X₁ π.mB) : y ∈ π.U := by
  obtain ⟨σ, h0, h1, rfl⟩ := (π.gu4_mem_segB y).mp hy
  apply π.gu4_theta_sub_U
  have hpin : π.gu4_pin ∈ convexHull ℝ {π.gu4_pin, π.apex, π.gu4_pout} :=
    subset_convexHull ℝ _ (by simp)
  have hapex : π.apex ∈ convexHull ℝ {π.gu4_pin, π.apex, π.gu4_pout} :=
    subset_convexHull ℝ _ (by simp)
  have := (convex_convexHull ℝ _) hpin hapex (sub_nonneg.mpr h1) h0 (by ring)
  convert this using 1
  rw [smul_sub, sub_smul, one_smul]; abel

theorem gu4_segC_sub_U {y : Plane} (hy : y ∈ edgeSegment π.X₁ π.mC) : y ∈ π.U := by
  obtain ⟨σ, h0, h1, rfl⟩ := (π.gu4_mem_segC y).mp hy
  apply π.gu4_theta_sub_U
  have hapex : π.apex ∈ convexHull ℝ {π.gu4_pin, π.apex, π.gu4_pout} :=
    subset_convexHull ℝ _ (by simp)
  have hpout : π.gu4_pout ∈ convexHull ℝ {π.gu4_pin, π.apex, π.gu4_pout} :=
    subset_convexHull ℝ _ (by simp)
  have := (convex_convexHull ℝ _) hapex hpout (sub_nonneg.mpr h1) h0 (by ring)
  convert this using 1
  rw [smul_sub, sub_smul, one_smul]; abel

/-- the centroid lies in the closed triangle -/
theorem gu4_centroid_mem_Δ (_π : G11_ParamsSw C) :
    G11_centroidSw C ∈ G11_triangle C.X C.hmp C.hmq C.hpq := by
  unfold G11_centroidSw G11_triangle
  have ha : crossingPoint (xPair C.hmp) ∈ convexHull ℝ
      {crossingPoint (xPair C.hmp), crossingPoint (xPair C.hmq), crossingPoint (xPair C.hpq)} :=
    subset_convexHull ℝ _ (by simp)
  have hb : crossingPoint (xPair C.hmq) ∈ convexHull ℝ
      {crossingPoint (xPair C.hmp), crossingPoint (xPair C.hmq), crossingPoint (xPair C.hpq)} :=
    subset_convexHull ℝ _ (by simp)
  have hc : crossingPoint (xPair C.hpq) ∈ convexHull ℝ
      {crossingPoint (xPair C.hmp), crossingPoint (xPair C.hmq), crossingPoint (xPair C.hpq)} :=
    subset_convexHull ℝ _ (by simp)
  have h1 := (convex_convexHull ℝ _) ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have h2 := (convex_convexHull ℝ _) h1 hc (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num)
  convert h2 using 1
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- `U` is convex (the image of a convex set under a homothety) -/
theorem gu4_convex_U : Convex ℝ π.U := by
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  obtain ⟨x₁, hx₁, rfl⟩ := hy₁
  obtain ⟨x₂, hx₂, rfl⟩ := hy₂
  refine ⟨a • x₁ + b • x₂, (convex_convexHull ℝ _) hx₁ hx₂ ha hb hab, ?_⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring

/-- the closed triangle lies in `U` (the pre-image of a point of `Δ` is a convex combination of it and
the centroid) -/
theorem gu4_Δ_sub_U : G11_triangle C.X C.hmp C.hmq C.hpq ⊆ π.U := by
  intro y hy
  have hr := π.hr
  have hz := π.gu4_centroid_mem_Δ
  have hpos : 0 < 1 + π.r := by linarith
  refine ⟨(1 / (1 + π.r)) • y + (π.r / (1 + π.r)) • G11_centroidSw C,
    (convex_convexHull ℝ _) hy hz (by positivity) (by positivity)
      (by rw [← add_div, div_eq_one_iff_eq hpos.ne']), ?_⟩
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> field_simp <;> ring

theorem gu4_a_mem_U : π.gu4_a ∈ π.U := π.gu4_Δ_sub_U (subset_convexHull ℝ _ (by simp [gu4_a]))
theorem gu4_b_mem_U : π.gu4_b ∈ π.U := π.gu4_Δ_sub_U (subset_convexHull ℝ _ (by simp [gu4_b]))
theorem gu4_c_mem_U : π.gu4_c ∈ π.U := π.gu4_Δ_sub_U (subset_convexHull ℝ _ (by simp [gu4_c]))

theorem gu4_old_edge_off_U (i : ZMod k) (hi : i ≠ C.m) (hp : i ≠ C.p) (hq : i ≠ C.q) {y : Plane}
    (hy : y ∈ edgeSegment π.X₀ (G11_lab C.m i)) : y ∉ π.U := by
  rw [π.gu4_seg_X₀_lab i hi] at hy
  exact π.disc_clear_edge i hi hp hq y hy

theorem gu4_old_vertex_off_U (j : ZMod (k + 3)) (hB : j ≠ π.mB) (hC : j ≠ π.mC) (hD : j ≠ π.mD) :
    π.X₀ j ∉ π.U := by
  rcases π.gu4_label_cases j with h | h | h | h | ⟨i, hi, h⟩
  · rw [h, gu4_X₀_mA]; exact π.disc_clear_vertex C.m
  · exact absurd h hB
  · exact absurd h hC
  · exact absurd h hD
  · rw [h, (π.gu4_lab_spec i hi).1]; exact π.disc_clear_vertex i

/-! ### U4 helpers: the two new double points `y_p ∈ p ∩ [w, p_out]`, `y_q ∈ q ∩ [p_in, w]` -/

theorem gu4_dm_ne : π.gu4_dm ≠ 0 := by
  intro h
  apply π.gu4_E_ne
  unfold gu4_E
  rw [h]
  simp [det]

theorem gu4_edgePoint_m_injective (π : G11_ParamsSw C) : Function.Injective (edgePoint C.X C.m) :=
  edgePoint_injective π.gu4_dm_ne

theorem gu4_lam_pos : 0 < π.lam := zero_lt_one.trans π.hlam

/-- the parameter of `y_p` on `[w, p_out]` -/
noncomputable def gu4_σp (π : G11_ParamsSw C) : ℝ :=
  (π.lam - 1) * (π.t₂ - π.gu4_tmp) / ((π.lam - 1) * (π.t₂ - π.gu4_tmp) + (π.t₃ - π.gu4_tmp))
/-- the parameter of `y_q` on `[p_in, w]` -/
noncomputable def gu4_σq (π : G11_ParamsSw C) : ℝ :=
  (π.gu4_tmq - π.t₁) / ((π.gu4_tmq - π.t₁) + (π.lam - 1) * (π.gu4_tmq - π.t₂))
noncomputable def gu4_yp (π : G11_ParamsSw C) : Plane := π.apex + π.gu4_σp • (π.gu4_pout - π.apex)
noncomputable def gu4_yq (π : G11_ParamsSw C) : Plane := π.gu4_pin + π.gu4_σq • (π.apex - π.gu4_pin)

theorem gu4_σp_denom_pos : 0 < (π.lam - 1) * (π.t₂ - π.gu4_tmp) + (π.t₃ - π.gu4_tmp) := by
  have := mul_pos (sub_pos.mpr π.hlam) (sub_pos.mpr π.gu4_h₂)
  have := π.gu4_h₂.trans (π.gu4_h₃.trans π.gu4_h₄)
  linarith
theorem gu4_σq_denom_pos : 0 < (π.gu4_tmq - π.t₁) + (π.lam - 1) * (π.gu4_tmq - π.t₂) := by
  have := mul_pos (sub_pos.mpr π.hlam) (sub_pos.mpr π.gu4_h₃)
  have := π.gu4_h₁.trans (π.gu4_h₂.trans π.gu4_h₃)
  linarith

theorem gu4_σp_pos : 0 < π.gu4_σp :=
  div_pos (mul_pos (sub_pos.mpr π.hlam) (sub_pos.mpr π.gu4_h₂)) π.gu4_σp_denom_pos
theorem gu4_σp_lt_one : π.gu4_σp < 1 := by
  unfold gu4_σp
  rw [div_lt_one π.gu4_σp_denom_pos]
  have := π.gu4_h₂.trans (π.gu4_h₃.trans π.gu4_h₄)
  linarith
theorem gu4_σq_pos : 0 < π.gu4_σq :=
  div_pos (sub_pos.mpr (π.gu4_h₁.trans (π.gu4_h₂.trans π.gu4_h₃))) π.gu4_σq_denom_pos
theorem gu4_σq_lt_one : π.gu4_σq < 1 := by
  unfold gu4_σq
  rw [div_lt_one π.gu4_σq_denom_pos]
  have := mul_pos (sub_pos.mpr π.hlam) (sub_pos.mpr π.gu4_h₃)
  linarith

/-- the `α`-coefficient of `[w, p_out]` vanishes exactly at `σ_p` -/
theorem gu4_σp_unique {σ : ℝ}
    (h : (1 - σ) * ((1 - π.lam) * (π.t₂ - π.gu4_tmp)) + σ * (π.t₃ - π.gu4_tmp) = 0) :
    σ = π.gu4_σp := by
  unfold gu4_σp
  rw [eq_div_iff π.gu4_σp_denom_pos.ne']
  linear_combination h
theorem gu4_α_coeff_σp :
    (1 - π.gu4_σp) * ((1 - π.lam) * (π.t₂ - π.gu4_tmp)) + π.gu4_σp * (π.t₃ - π.gu4_tmp) = 0 := by
  have hD := π.gu4_σp_denom_pos
  unfold gu4_σp
  field_simp
  ring
/-- the `γ`-coefficient of `[p_in, w]` vanishes exactly at `σ_q` -/
theorem gu4_σq_unique {σ : ℝ}
    (h : (1 - σ) * (π.t₁ - π.gu4_tmq) + σ * ((π.lam - 1) * (π.gu4_tmq - π.t₂)) = 0) :
    σ = π.gu4_σq := by
  unfold gu4_σq
  rw [eq_div_iff π.gu4_σq_denom_pos.ne']
  linear_combination h
theorem gu4_γ_coeff_σq :
    (1 - π.gu4_σq) * (π.t₁ - π.gu4_tmq) + π.gu4_σq * ((π.lam - 1) * (π.gu4_tmq - π.t₂)) = 0 := by
  have hD := π.gu4_σq_denom_pos
  unfold gu4_σq
  field_simp
  ring

theorem gu4_yp_mem_segC : π.gu4_yp ∈ edgeSegment π.X₁ π.mC :=
  (π.gu4_mem_segC _).mpr ⟨π.gu4_σp, π.gu4_σp_pos.le, π.gu4_σp_lt_one.le, rfl⟩
theorem gu4_yq_mem_segB : π.gu4_yq ∈ edgeSegment π.X₁ π.mB :=
  (π.gu4_mem_segB _).mpr ⟨π.gu4_σq, π.gu4_σq_pos.le, π.gu4_σq_lt_one.le, rfl⟩
theorem gu4_α_yp : π.gu4_α π.gu4_yp = 0 := by
  rw [gu4_yp, gu4_α_segC, gu4_α_coeff_σp, zero_mul]
theorem gu4_γ_yq : π.gu4_γ π.gu4_yq = 0 := by
  rw [gu4_yq, gu4_γ_segB, gu4_γ_coeff_σq, zero_mul]
theorem gu4_yp_mem_U : π.gu4_yp ∈ π.U := π.gu4_segC_sub_U π.gu4_yp_mem_segC
theorem gu4_yq_mem_U : π.gu4_yq ∈ π.U := π.gu4_segB_sub_U π.gu4_yq_mem_segB

/-- `y_p = a + t_p • v` with `t_p = (1 − σ_p) λ` -/
theorem gu4_yp_eq : π.gu4_yp = π.gu4_a + ((1 - π.gu4_σp) * π.lam) • π.gu4_v := by
  rw [gu4_yp, gu4_segC_frame, gu4_α_coeff_σp, zero_smul, add_zero]
/-- `y_q = b + t_q • (c − b)` with `t_q = σ_q λ` -/
theorem gu4_yq_eq : π.gu4_yq = π.gu4_b + (π.gu4_σq * π.lam) • (π.gu4_c - π.gu4_b) := by
  have hγ := π.gu4_γ_coeff_σq
  rw [gu4_yq, gu4_segB_frame, π.gu4_b_sub_a, π.gu4_c_eq]
  have hs : (1 - π.gu4_σq) * (π.t₁ - π.gu4_tmp) + π.gu4_σq * ((1 - π.lam) * (π.t₂ - π.gu4_tmp)) =
      (π.gu4_tmq - π.gu4_tmp) * (1 - π.gu4_σq * π.lam) := by linear_combination hγ
  rw [hs]
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring

/-- **the new double points lie on the old strands** (convexity capture by `U`) -/
theorem gu4_yp_mem_p : π.gu4_yp ∈ edgeSegment C.X C.p := by
  obtain ⟨κ, -, hv⟩ := π.gu4_v_eq
  obtain ⟨sa, -, -, ha⟩ := π.gu4_a_mem_p
  have hy : π.gu4_yp = C.X C.p + (sa + (1 - π.gu4_σp) * π.lam * κ) • edge C.X C.p := by
    rw [gu4_yp_eq, hv, ha]
    simp only [edgePoint]
    refine Prod.ext ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
  rw [hy]
  exact gu4_mem_edgeSegment_of_convex π.gu4_convex_U (π.disc_clear_vertex C.p)
    (π.disc_clear_vertex (C.p + 1)) π.gu4_a_mem_p π.gu4_a_mem_U (hy ▸ π.gu4_yp_mem_U)

theorem gu4_yq_mem_q : π.gu4_yq ∈ edgeSegment C.X C.q := by
  obtain ⟨κ, -, hv⟩ := π.gu4_cb_eq
  obtain ⟨sb, -, -, hb⟩ := π.gu4_b_mem_q
  have hy : π.gu4_yq = C.X C.q + (sb + π.gu4_σq * π.lam * κ) • edge C.X C.q := by
    rw [gu4_yq_eq, hv, hb]
    simp only [edgePoint]
    refine Prod.ext ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
  rw [hy]
  exact gu4_mem_edgeSegment_of_convex π.gu4_convex_U (π.disc_clear_vertex C.q)
    (π.disc_clear_vertex (C.q + 1)) π.gu4_b_mem_q π.gu4_b_mem_U (hy ▸ π.gu4_yq_mem_U)

/-! ### U4 helpers: where the bent edges meet the other edges -/

theorem gu4_α_apex : π.gu4_α π.apex = ((1 - π.lam) * (π.t₂ - π.gu4_tmp)) * π.gu4_E := by
  rw [gu4_apex_frame, gu4_α_frame]
theorem gu4_β_apex : π.gu4_β π.apex = π.lam * π.gu4_E := by
  rw [gu4_apex_frame, gu4_β_frame]
theorem gu4_γ_apex : π.gu4_γ π.apex = ((π.lam - 1) * (π.gu4_tmq - π.t₂)) * π.gu4_E := by
  rw [gu4_apex_frame, gu4_γ_frame]; ring

/-- the apex is on no edge of `X₀` other than `mB, mC` -/
theorem gu4_apex_not_mem_X₀ (b : ZMod (k + 3)) (hbB : b ≠ π.mB) (hbC : b ≠ π.mC) :
    π.apex ∉ edgeSegment π.X₀ b := by
  intro hmem
  have hE := π.gu4_E_ne
  have hlam := π.gu4_lam_pos
  rcases π.gu4_label_cases b with h | h | h | h | ⟨i, hi, h⟩
  · rw [h, gu4_mem_mA] at hmem
    obtain ⟨t, -, -, ht⟩ := hmem
    have := π.gu4_β_of_m t
    rw [← ht, gu4_β_apex] at this
    exact mul_ne_zero hlam.ne' hE this
  · exact hbB h
  · exact hbC h
  · rw [h, gu4_mem_mD] at hmem
    obtain ⟨t, -, -, ht⟩ := hmem
    have := π.gu4_β_of_m t
    rw [← ht, gu4_β_apex] at this
    exact mul_ne_zero hlam.ne' hE this
  · by_cases hp : i = C.p
    · subst hp
      rw [h, π.gu4_seg_X₀_lab _ hi] at hmem
      have := π.gu4_α_of_mem_p hmem
      rw [gu4_α_apex] at this
      exact mul_ne_zero (mul_neg_of_neg_of_pos (sub_neg.mpr π.hlam) (sub_pos.mpr π.gu4_h₂)).ne hE this
    by_cases hq : i = C.q
    · subst hq
      rw [h, π.gu4_seg_X₀_lab _ hi] at hmem
      have := π.gu4_γ_of_mem_q hmem
      rw [gu4_γ_apex] at this
      exact mul_ne_zero (mul_pos (sub_pos.mpr π.hlam) (sub_pos.mpr π.gu4_h₃)).ne' hE this
    · rw [h] at hmem
      exact π.gu4_old_edge_off_U i hi hp hq hmem
        (π.gu4_segB_sub_U ((π.gu4_mem_segB _).mpr ⟨1, zero_le_one, le_rfl, by simp⟩))

theorem gu4_pout_not_mem_segB : π.gu4_pout ∉ edgeSegment π.X₁ π.mB := by
  intro hmem
  obtain ⟨σ, -, -, hσ⟩ := (π.gu4_mem_segB _).mp hmem
  have h1 := π.gu4_β_of_m π.t₃
  have h2 := π.gu4_β_segB σ
  rw [← hσ] at h2
  change π.gu4_β π.gu4_pout = 0 at h1
  rw [h1] at h2
  have hσ0 : σ = 0 := by
    rcases mul_eq_zero.mp h2.symm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h π.gu4_lam_pos.ne'
    · exact absurd h π.gu4_E_ne
  rw [hσ0, zero_smul, add_zero] at hσ
  have := π.gu4_edgePoint_m_injective hσ
  linarith [π.gu4_h₁, π.gu4_h₂, π.gu4_h₃, π.gu4_h₄]

theorem gu4_pin_not_mem_segC : π.gu4_pin ∉ edgeSegment π.X₁ π.mC := by
  intro hmem
  obtain ⟨σ, -, -, hσ⟩ := (π.gu4_mem_segC _).mp hmem
  have h1 := π.gu4_β_of_m π.t₁
  have h2 := π.gu4_β_segC σ
  rw [← hσ] at h2
  change π.gu4_β π.gu4_pin = 0 at h1
  rw [h1] at h2
  have hσ1 : σ = 1 := by
    rcases mul_eq_zero.mp h2.symm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · linarith
      · exact absurd h π.gu4_lam_pos.ne'
    · exact absurd h π.gu4_E_ne
  rw [hσ1, one_smul, add_sub_cancel] at hσ
  have := π.gu4_edgePoint_m_injective hσ
  linarith [π.gu4_h₁, π.gu4_h₂, π.gu4_h₃, π.gu4_h₄]

/-- the two bent edges meet only at the apex -/
theorem gu4_corner {σ σ' : ℝ}
    (h : π.gu4_pin + σ • (π.apex - π.gu4_pin) = π.apex + σ' • (π.gu4_pout - π.apex)) :
    σ = 1 ∧ σ' = 0 := by
  have hE := π.gu4_E_ne
  have hβ := π.gu4_β_segB σ
  rw [h, gu4_β_segC] at hβ
  have hα := π.gu4_α_segB σ
  rw [h, gu4_α_segC] at hα
  have hβ' : (1 - σ') * π.lam = σ * π.lam := mul_right_cancel₀ hE hβ
  have hσ' : σ' = 1 - σ := by
    have := mul_right_cancel₀ π.gu4_lam_pos.ne' hβ'
    linarith
  have hα' := mul_right_cancel₀ hE hα
  rw [hσ'] at hα'
  have h13 : π.t₁ - π.t₃ ≠ 0 := by linarith [π.gu4_h₁, π.gu4_h₂, π.gu4_h₃, π.gu4_h₄]
  have hσ1 : σ = 1 := by
    have : (1 - σ) * (π.t₁ - π.t₃) = 0 := by linear_combination -hα'
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h h13
  exact ⟨hσ1, by rw [hσ', hσ1]; ring⟩

/-- **master lemma for `[p_in, w]`**: an edge of `X₀` other than `mB, mC` meeting `[p_in, w]` is `q'`,
or `mA` at the shared vertex `p_in`. -/
theorem gu4_meet_B {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (d : ZMod (k + 3)) (hdB : d ≠ π.mB)
    (hdC : d ≠ π.mC) (hd : π.gu4_pin + σ • (π.apex - π.gu4_pin) ∈ edgeSegment π.X₀ d) :
    d = π.q' ∨ (d = π.mA ∧ σ = 0) := by
  have hE := π.gu4_E_ne
  have hlam := π.gu4_lam_pos
  have hβ0 : ∀ t, π.gu4_pin + σ • (π.apex - π.gu4_pin) = edgePoint C.X C.m t → σ = 0 := by
    intro t ht
    have h2 := π.gu4_β_segB σ
    rw [ht, gu4_β_of_m] at h2
    rcases mul_eq_zero.mp h2.symm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h hlam.ne'
    · exact absurd h hE
  rcases π.gu4_label_cases d with h | h | h | h | ⟨i, hi, h⟩
  · right
    rw [h, gu4_mem_mA] at hd
    obtain ⟨t, -, -, ht⟩ := hd
    exact ⟨h, hβ0 t ht⟩
  · exact absurd h hdB
  · exact absurd h hdC
  · exfalso
    rw [h, gu4_mem_mD] at hd
    obtain ⟨t, ht3, -, ht⟩ := hd
    have hσ := hβ0 t ht
    rw [hσ, zero_smul, add_zero] at ht
    have := π.gu4_edgePoint_m_injective ht
    linarith [π.gu4_h₁, π.gu4_h₂, π.gu4_h₃, π.gu4_h₄]
  · by_cases hp : i = C.p
    · exfalso
      subst hp
      rw [h, π.gu4_seg_X₀_lab _ hi] at hd
      have := π.gu4_α_of_mem_p hd
      rw [gu4_α_segB] at this
      exact mul_ne_zero (π.gu4_segB_coeff_neg h0 h1).ne hE this
    by_cases hq : i = C.q
    · left
      subst hq
      exact h
    · exfalso
      rw [h] at hd
      exact π.gu4_old_edge_off_U i hi hp hq hd
        (π.gu4_segB_sub_U ((π.gu4_mem_segB _).mpr ⟨σ, h0, h1, rfl⟩))

/-- **master lemma for `[w, p_out]`**: an edge of `X₀` other than `mB, mC` meeting `[w, p_out]` is `p'`,
or `mD` at the shared vertex `p_out`. -/
theorem gu4_meet_C {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (d : ZMod (k + 3)) (hdB : d ≠ π.mB)
    (hdC : d ≠ π.mC) (hd : π.apex + σ • (π.gu4_pout - π.apex) ∈ edgeSegment π.X₀ d) :
    d = π.p' ∨ (d = π.mD ∧ σ = 1) := by
  have hE := π.gu4_E_ne
  have hlam := π.gu4_lam_pos
  have hβ0 : ∀ t, π.apex + σ • (π.gu4_pout - π.apex) = edgePoint C.X C.m t → σ = 1 := by
    intro t ht
    have h2 := π.gu4_β_segC σ
    rw [ht, gu4_β_of_m] at h2
    rcases mul_eq_zero.mp h2.symm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · linarith
      · exact absurd h hlam.ne'
    · exact absurd h hE
  rcases π.gu4_label_cases d with h | h | h | h | ⟨i, hi, h⟩
  · exfalso
    rw [h, gu4_mem_mA] at hd
    obtain ⟨t, -, ht1, ht⟩ := hd
    have hσ := hβ0 t ht
    rw [hσ, one_smul, add_sub_cancel] at ht
    have := π.gu4_edgePoint_m_injective ht
    linarith [π.gu4_h₁, π.gu4_h₂, π.gu4_h₃, π.gu4_h₄]
  · exact absurd h hdB
  · exact absurd h hdC
  · right
    rw [h, gu4_mem_mD] at hd
    obtain ⟨t, -, -, ht⟩ := hd
    exact ⟨h, hβ0 t ht⟩
  · by_cases hp : i = C.p
    · left
      subst hp
      exact h
    by_cases hq : i = C.q
    · exfalso
      subst hq
      rw [h, π.gu4_seg_X₀_lab _ hi] at hd
      have := π.gu4_γ_of_mem_q hd
      rw [gu4_γ_segC] at this
      exact mul_ne_zero (π.gu4_segC_coeff_pos h0 h1).ne' hE this
    · exfalso
      rw [h] at hd
      exact π.gu4_old_edge_off_U i hi hp hq hd
        (π.gu4_segC_sub_U ((π.gu4_mem_segC _).mpr ⟨σ, h0, h1, rfl⟩))

/-- an interior point of `[p_in, w]` lies on no other edge of `X₁` except `q'` -/
theorem gu4_intB_partner {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) (d : ZMod (k + 3)) (hdB : d ≠ π.mB)
    (hd : π.gu4_pin + σ • (π.apex - π.gu4_pin) ∈ edgeSegment π.X₁ d) : d = π.q' := by
  by_cases hdC : d = π.mC
  · exfalso
    subst hdC
    obtain ⟨σ', -, -, h⟩ := (π.gu4_mem_segC _).mp hd
    exact h1.ne (π.gu4_corner h).1
  · rw [π.gu4_seg_X₁_eq d hdB hdC] at hd
    rcases π.gu4_meet_B h0.le h1.le d hdB hdC hd with h | ⟨-, h⟩
    · exact h
    · exact absurd h h0.ne'

/-- an interior point of `[w, p_out]` lies on no other edge of `X₁` except `p'` -/
theorem gu4_intC_partner {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) (d : ZMod (k + 3)) (hdC : d ≠ π.mC)
    (hd : π.apex + σ • (π.gu4_pout - π.apex) ∈ edgeSegment π.X₁ d) : d = π.p' := by
  by_cases hdB : d = π.mB
  · exfalso
    subst hdB
    obtain ⟨σ', -, -, h⟩ := (π.gu4_mem_segB _).mp hd
    exact h0.ne' (π.gu4_corner h.symm).2
  · rw [π.gu4_seg_X₁_eq d hdB hdC] at hd
    rcases π.gu4_meet_C h0.le h1.le d hdB hdC hd with h | ⟨-, h⟩
    · exact h
    · exact absurd h h1.ne

/-! ### U4 helpers: the determinants of the bent edges against `p`, `q`, `m` -/

theorem gu4_v_eq' : π.gu4_v = (π.gu4_c - π.gu4_b) + (π.gu4_tmq - π.gu4_tmp) • π.gu4_dm := by
  rw [π.gu4_b_sub_a, gu4_v]; abel

/-- `det(d_p, p_out − w) = K · det(d_p, d_m)`, `K = (t₃ − t₂) + λ (t₂ − t(x_mp)) > 0` -/
theorem gu4_det_p_segC : det (edge C.X C.p) (π.gu4_pout - π.apex) =
    ((π.t₃ - π.t₂) + π.lam * (π.t₂ - π.gu4_tmp)) * det (edge C.X C.p) (edge C.X C.m) := by
  obtain ⟨κ, -, hv⟩ := π.gu4_v_eq
  rw [gu4_apex_frame, gu4_pout, π.gu4_edgePoint_m π.t₃, hv]
  simp only [gu4_dm, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring
theorem gu4_Kp_pos : 0 < (π.t₃ - π.t₂) + π.lam * (π.t₂ - π.gu4_tmp) := by
  have := mul_pos π.gu4_lam_pos (sub_pos.mpr π.gu4_h₂)
  have := π.gu4_h₃.trans π.gu4_h₄
  linarith

/-- `det(d_q, w − p_in) = K' · det(d_q, d_m)`, `K' = (t₂ − t₁) + λ (t(x_mq) − t₂) > 0` -/
theorem gu4_det_q_segB : det (edge C.X C.q) (π.apex - π.gu4_pin) =
    ((π.t₂ - π.t₁) + π.lam * (π.gu4_tmq - π.t₂)) * det (edge C.X C.q) (edge C.X C.m) := by
  obtain ⟨κ, -, hcb⟩ := π.gu4_cb_eq
  rw [gu4_apex_frame, gu4_pin, π.gu4_edgePoint_m π.t₁, gu4_v_eq', hcb]
  simp only [gu4_dm, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring
theorem gu4_Kq_pos : 0 < (π.t₂ - π.t₁) + π.lam * (π.gu4_tmq - π.t₂) := by
  have := mul_pos π.gu4_lam_pos (sub_pos.mpr π.gu4_h₃)
  have := π.gu4_h₁.trans π.gu4_h₂
  linarith

theorem gu4_det_segB_segC : det (π.apex - π.gu4_pin) (π.gu4_pout - π.apex) =
    -(π.lam * (π.t₃ - π.t₁)) * π.gu4_E := by
  rw [gu4_apex_frame, gu4_pin, gu4_pout, π.gu4_edgePoint_m π.t₁, π.gu4_edgePoint_m π.t₃]
  simp only [gu4_E, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring
theorem gu4_det_mA_segB : det (π.t₁ • π.gu4_dm) (π.apex - π.gu4_pin) = π.t₁ * π.lam * π.gu4_E := by
  rw [gu4_apex_frame, gu4_pin, π.gu4_edgePoint_m π.t₁]
  simp only [gu4_E, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring
theorem gu4_det_segC_mD : det (π.gu4_pout - π.apex) ((1 - π.t₃) • π.gu4_dm) =
    (1 - π.t₃) * π.lam * π.gu4_E := by
  rw [gu4_apex_frame, gu4_pout, π.gu4_edgePoint_m π.t₃]
  simp only [gu4_E, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring

/-! ### U4 helpers: the four clauses of the genericity of `X₁` -/

theorem gu4_X₁_regular : Regular π.X₁ := by
  intro i
  have hreg₀ : Regular π.X₀ := gu4_gen_regular π.X₀_generic
  have hE := π.gu4_E_ne
  have hlam := π.gu4_lam_pos
  by_cases hB : i = π.mB
  · subst hB
    have hpred : π.mB - 1 = π.mA := by rw [← gu4_mA_succ]; ring
    rw [hpred, π.gu4_edge_X₁_eq _ π.gu4_mA_ne_mB π.gu4_mA_ne_mC, gu4_edge_X₀_mA, gu4_edge_X₁_mB]
    apply SM.Link.regularPair_of_det_ne_zero
    rw [gu4_det_mA_segB]
    exact mul_ne_zero (mul_ne_zero π.ht₁.ne' hlam.ne') hE
  by_cases hC : i = π.mC
  · subst hC
    have hpred : π.mC - 1 = π.mB := by rw [← gu4_mB_succ]; ring
    rw [hpred, gu4_edge_X₁_mB, gu4_edge_X₁_mC]
    apply SM.Link.regularPair_of_det_ne_zero
    rw [gu4_det_segB_segC]
    have : π.t₃ - π.t₁ ≠ 0 := by linarith [π.gu4_h₁, π.gu4_h₂, π.gu4_h₃, π.gu4_h₄]
    exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero hlam.ne' this)) hE
  by_cases hD : i = π.mD
  · subst hD
    have hpred : π.mD - 1 = π.mC := by rw [← gu4_mC_succ]; ring
    rw [hpred, gu4_edge_X₁_mC, π.gu4_edge_X₁_eq _ π.gu4_mB_ne_mD.symm π.gu4_mC_ne_mD.symm,
      gu4_edge_X₀_mD]
    apply SM.Link.regularPair_of_det_ne_zero
    rw [gu4_det_segC_mD]
    have : 1 - π.t₃ ≠ 0 := by linarith [π.ht₃]
    exact mul_ne_zero (mul_ne_zero this hlam.ne') hE
  · have h1 : i - 1 ≠ π.mB := fun h => hC (by rw [← gu4_mB_succ, ← h]; ring)
    have h2 : i - 1 ≠ π.mC := fun h => hD (by rw [← gu4_mC_succ, ← h]; ring)
    rw [π.gu4_edge_X₁_eq i hB hC, π.gu4_edge_X₁_eq (i - 1) h1 h2]
    exact hreg₀ i

theorem gu4_X₁_tail (a b : ZMod (k + 3)) (h : ¬ incident a b) : π.X₁ a ∉ edgeSegment π.X₁ b := by
  have hba : b ≠ a := fun e => h (Or.inr e)
  have hba' : b ≠ a - 1 := fun e => h (Or.inl e)
  intro hmem
  by_cases haC : a = π.mC
  · subst haC
    have hbB : b ≠ π.mB := fun e => hba' (by rw [e, ← gu4_mB_succ]; ring)
    rw [gu4_X₁_mC, π.gu4_seg_X₁_eq b hbB hba] at hmem
    exact π.gu4_apex_not_mem_X₀ b hbB hba hmem
  · rw [π.gu4_X₁_of_ne a haC] at hmem
    by_cases hbB : b = π.mB
    · subst hbB
      by_cases haD : a = π.mD
      · subst haD
        rw [gu4_X₀_mD] at hmem
        exact π.gu4_pout_not_mem_segB hmem
      · exact π.gu4_old_vertex_off_U a hba.symm haC haD (π.gu4_segB_sub_U hmem)
    by_cases hbC : b = π.mC
    · subst hbC
      have haD : a ≠ π.mD := fun e => hba' (by rw [e, ← gu4_mC_succ]; ring)
      by_cases haB : a = π.mB
      · subst haB
        rw [gu4_X₀_mB] at hmem
        exact π.gu4_pin_not_mem_segC hmem
      · exact π.gu4_old_vertex_off_U a haB haC haD (π.gu4_segC_sub_U hmem)
    · rw [π.gu4_seg_X₁_eq b hbB hbC] at hmem
      exact gu4_gen_tail π.X₀_generic a b h hmem

/-- transversality with one bent edge -/
theorem gu4_X₁_trans_bent (a b : ZMod (k + 3)) (ha : a = π.mB ∨ a = π.mC) (hbB : b ≠ π.mB)
    (hbC : b ≠ π.mC) (h : ¬ adjacent a b)
    (hm : (edgeSegment π.X₁ a ∩ edgeSegment π.X₁ b).Nonempty) :
    det (edge π.X₁ a) (edge π.X₁ b) ≠ 0 := by
  obtain ⟨y, hya, hyb⟩ := hm
  rw [π.gu4_seg_X₁_eq b hbB hbC] at hyb
  rw [π.gu4_edge_X₁_eq b hbB hbC]
  rcases ha with rfl | rfl
  · obtain ⟨σ, h0, h1, rfl⟩ := (π.gu4_mem_segB y).mp hya
    rcases π.gu4_meet_B h0 h1 b hbB hbC hyb with hb | ⟨hb, -⟩
    · subst hb
      rw [gu4_edge_X₁_mB, gu4_edge_X₀_q', det_swap, gu4_det_q_segB, det_swap]
      exact neg_ne_zero.mpr (mul_ne_zero π.gu4_Kq_pos.ne' (neg_ne_zero.mpr π.gu4_det_mq))
    · exact absurd (Or.inl (by rw [hb, ← gu4_mA_succ]; ring)) h
  · obtain ⟨σ, h0, h1, rfl⟩ := (π.gu4_mem_segC y).mp hya
    rcases π.gu4_meet_C h0 h1 b hbB hbC hyb with hb | ⟨hb, -⟩
    · subst hb
      rw [gu4_edge_X₁_mC, gu4_edge_X₀_p', det_swap, gu4_det_p_segC, det_swap]
      exact neg_ne_zero.mpr (mul_ne_zero π.gu4_Kp_pos.ne' (neg_ne_zero.mpr π.gu4_det_mp))
    · exact absurd (Or.inr (Or.inr (by rw [hb, ← gu4_mC_succ]; ring))) h

theorem gu4_X₁_trans (a b : ZMod (k + 3)) (h : ¬ adjacent a b)
    (hm : (edgeSegment π.X₁ a ∩ edgeSegment π.X₁ b).Nonempty) :
    det (edge π.X₁ a) (edge π.X₁ b) ≠ 0 := by
  by_cases ha : a = π.mB ∨ a = π.mC
  · by_cases hb : b = π.mB ∨ b = π.mC
    · exfalso
      apply h
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact Or.inr (Or.inl (sub_self _))
      · exact Or.inr (Or.inr (by rw [← gu4_mB_succ]; ring))
      · exact Or.inl (by rw [← gu4_mB_succ]; ring)
      · exact Or.inr (Or.inl (sub_self _))
    · simp only [not_or] at hb
      exact π.gu4_X₁_trans_bent a b ha hb.1 hb.2 h hm
  · simp only [not_or] at ha
    by_cases hb : b = π.mB ∨ b = π.mC
    · have h' : ¬ adjacent b a := fun hadj => h (adjacent_symm' hadj)
      have hm' : (edgeSegment π.X₁ b ∩ edgeSegment π.X₁ a).Nonempty := by
        rwa [Set.inter_comm]
      have := π.gu4_X₁_trans_bent b a hb ha.1 ha.2 h' hm'
      rw [det_swap]
      exact neg_ne_zero.mpr this
    · simp only [not_or] at hb
      rw [π.gu4_edge_X₁_eq a ha.1 ha.2, π.gu4_edge_X₁_eq b hb.1 hb.2]
      rw [π.gu4_seg_X₁_eq a ha.1 ha.2, π.gu4_seg_X₁_eq b hb.1 hb.2] at hm
      exact gu4_gen_trans π.X₀_generic a b h hm

theorem gu4_X₁_triple : ¬ ∃ a b c : ZMod (k + 3), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    (edgeInterior π.X₁ a ∩ edgeInterior π.X₁ b ∩ edgeInterior π.X₁ c).Nonempty := by
  rintro ⟨a, b, c, hab, hbc, hac, y, ⟨hya, hyb⟩, hyc⟩
  have key : ∀ a b c : ZMod (k + 3), a ≠ b → b ≠ c → a ≠ c → y ∈ edgeInterior π.X₁ a →
      y ∈ edgeInterior π.X₁ b → y ∈ edgeInterior π.X₁ c → (a = π.mB ∨ a = π.mC) → False := by
    intro a b c hab hbc hac hya hyb hyc ha
    rcases ha with rfl | rfl
    · obtain ⟨σ, h0, h1, hy⟩ := (π.gu4_mem_intB y).mp hya
      rw [hy] at hyb hyc
      have hb := π.gu4_intB_partner h0 h1 b hab.symm (edgeInterior_subset_edgeSegment _ _ hyb)
      have hc := π.gu4_intB_partner h0 h1 c hac.symm (edgeInterior_subset_edgeSegment _ _ hyc)
      exact hbc (hb.trans hc.symm)
    · obtain ⟨σ, h0, h1, hy⟩ := (π.gu4_mem_intC y).mp hya
      rw [hy] at hyb hyc
      have hb := π.gu4_intC_partner h0 h1 b hab.symm (edgeInterior_subset_edgeSegment _ _ hyb)
      have hc := π.gu4_intC_partner h0 h1 c hac.symm (edgeInterior_subset_edgeSegment _ _ hyc)
      exact hbc (hb.trans hc.symm)
  by_cases haB : a = π.mB ∨ a = π.mC
  · exact key a b c hab hbc hac hya hyb hyc haB
  by_cases hbB : b = π.mB ∨ b = π.mC
  · exact key b a c hab.symm hac hbc hyb hya hyc hbB
  by_cases hcB : c = π.mB ∨ c = π.mC
  · exact key c a b hac.symm hab hbc.symm hyc hya hyb hcB
  · simp only [not_or] at haB hbB hcB
    rw [π.gu4_int_X₁_eq a haB.1 haB.2] at hya
    rw [π.gu4_int_X₁_eq b hbB.1 hbB.2] at hyb
    rw [π.gu4_int_X₁_eq c hcB.1 hcB.2] at hyc
    exact gu4_gen_triple π.X₀_generic ⟨a, b, c, hab, hbc, hac, y, ⟨hya, hyb⟩, hyc⟩

/-! ### Unit C leaves — the moved polygon -/

/-- **C1.** `X₁` is a generic one-component shadow: `regular` (the two bent edges are nonzero, not
antiparallel to their neighbours), `tail_off` (the apex is on no edge; no old vertex is on a bent edge —
both edges lie in `Θ ⊆ interior U`, which meets no vertex), `transverse` (bent edge against `p'`, `q'`:
`det ≠ 0` by the explicit formulas; against every other edge: disjoint, `Θ ⊆ interior U` and
`disc_clear_edge`; against the neighbouring `m`-pieces: adjacent), `no_triple` (the bent edges meet `p'`,
`q'` at two distinct points different from `x_pq`; nothing else enters `Θ`). -/
theorem X₁_generic : (Shadow.single ⟨k + 3, π.hk₃, π.X₁⟩).Generic := by
  exact Shadow.single_generic_of _ π.gu4_X₁_regular π.gu4_X₁_tail π.gu4_X₁_trans π.gu4_X₁_triple

/-- `M₁`: the positive diagram of `X₁`. -/
noncomputable def M₁ : Diagram := (Shadow.single ⟨k + 3, π.hk₃, π.X₁⟩).positiveDiagram π.X₁_generic

theorem M₁_componentCount : π.M₁.componentCount = 1 := rfl

/-- **C2.** The crossings of `X₁` involving a bent edge: `p'` crosses `[w, p_out]` (label `mC`) and `q'`
crosses `[p_in, w]` (label `mB`) — `p` enters `Θ` on the left half of the base, passes `x_pq` on the median
`(m₀, w)` and exits through the right side; `q` symmetrically. -/
theorem X₁_cross_pC : IsCrossing π.X₁ {π.p', π.mC} := by
  refine ⟨π.p', π.mC, rfl, ?_, π.gu4_yp, ?_, π.gu4_yp_mem_segC⟩
  · rintro (h | h | h)
    · exact π.gu4_p'_ne.2.2.2 (by rw [← gu4_mC_succ]; linear_combination -h)
    · exact π.gu4_p'_ne.2.2.1 (by linear_combination -h)
    · exact π.gu4_p'_ne.2.1 (by linear_combination -h - π.gu4_mB_succ)
  · rw [π.gu4_seg_X₁_eq _ π.gu4_p'_ne.2.1 π.gu4_p'_ne.2.2.1, gu4_seg_X₀_p']
    exact π.gu4_yp_mem_p

theorem X₁_cross_qB : IsCrossing π.X₁ {π.q', π.mB} := by
  refine ⟨π.q', π.mB, rfl, ?_, π.gu4_yq, ?_, π.gu4_yq_mem_segB⟩
  · rintro (h | h | h)
    · exact π.gu4_q'_ne.2.2.1 (by rw [← gu4_mB_succ]; linear_combination -h)
    · exact π.gu4_q'_ne.2.1 (by linear_combination -h)
    · exact π.gu4_q'_ne.1 (by linear_combination -h - π.gu4_mA_succ)
  · rw [π.gu4_seg_X₁_eq _ π.gu4_q'_ne.2.1 π.gu4_q'_ne.2.2.1, gu4_seg_X₀_q']
    exact π.gu4_yq_mem_q

/-- **C3.** Every other crossing of `X₁` is a crossing of `X₀` not involving `mB, mC`, with the same
double point (the strands are literally the same segments), and conversely. -/
theorem X₁_cross_iff (s : Finset (ZMod (k + 3))) (hs : π.mB ∉ s) (hs' : π.mC ∉ s) :
    IsCrossing π.X₁ s ↔ IsCrossing π.X₀ s := by
  constructor
  · rintro ⟨i, j, rfl, hr, hm⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs hs'
    refine ⟨i, j, rfl, hr, ?_⟩
    rwa [π.gu4_seg_X₁_eq i (Ne.symm hs.1) (Ne.symm hs'.1), π.gu4_seg_X₁_eq j (Ne.symm hs.2) (Ne.symm hs'.2)] at hm
  · rintro ⟨i, j, rfl, hr, hm⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs hs'
    refine ⟨i, j, rfl, hr, ?_⟩
    rwa [π.gu4_seg_X₁_eq i (Ne.symm hs.1) (Ne.symm hs'.1), π.gu4_seg_X₁_eq j (Ne.symm hs.2) (Ne.symm hs'.2)]

/-- **C4.** The over bits at the two new crossings agree with the old ones: `sgn det(edge p', edge [w,p_out])
= sgn det(edge p, edge m)` and `sgn det(edge q', edge [p_in,w]) = sgn det(edge q, edge m)` (in the
coordinates `b = x`-axis, `x_mp = (0,0)`, `x_mq = (1,0)`, `m₀ = (μ,0)`, `x_pq = (u,h)`, `w = (μ+λ(u−μ), λh)`:
`det(d_p, p_out − w) = −h(1+ε−μ+λμ)`, `det(d_q, w − p_in) = −h(λ(1−μ)+μ+ε)`, both of the sign of
`det(d_p, d_m) = det(d_q, d_m) = −h`). -/
theorem X₁_sign_pC : crossingSign π.X₁ π.p' π.mC = crossingSign C.X C.p C.m := by
  unfold crossingSign
  rw [π.gu4_edge_X₁_eq _ π.gu4_p'_ne.2.1 π.gu4_p'_ne.2.2.1, gu4_edge_X₀_p', gu4_edge_X₁_mC,
    gu4_det_p_segC, sign_mul, sign_pos π.gu4_Kp_pos, one_mul]

theorem X₁_sign_qB : crossingSign π.X₁ π.q' π.mB = crossingSign C.X C.q C.m := by
  unfold crossingSign
  rw [π.gu4_edge_X₁_eq _ π.gu4_q'_ne.2.1 π.gu4_q'_ne.2.2.1, gu4_edge_X₀_q', gu4_edge_X₁_mB,
    gu4_det_q_segB, sign_mul, sign_pos π.gu4_Kq_pos, one_mul]

/-! ### Unit D leaves — the disc and the Reidemeister-III site -/

/-! ### U3 helpers (Block E) — the triangle `Δ`, its centroid, and the homothetic disc `U` -/

theorem gu3_a_ne_d (C : G11_ConfigSw k) :
    crossingPoint (xPair C.hmp) ≠ crossingPoint (xPair C.hpq) := by
  intro h
  have h1 := crossingPoint_injective_of_geometry (gu3_geometry C) h
  have hval : ({C.m, C.p} : Finset (ZMod k)) = {C.p, C.q} := congrArg Subtype.val h1
  have hm : C.m ∈ ({C.p, C.q} : Finset (ZMod k)) := hval ▸ mem_pair_left C.m C.p
  rcases Finset.mem_insert.mp hm with h2 | h2
  · exact gu3_p_ne_m C h2.symm
  · exact gu3_q_ne_m C (Finset.mem_singleton.mp h2).symm

/-- the three double points are not collinear -/
theorem gu3_det_triangle (C : G11_ConfigSw k) :
    det (crossingPoint (xPair C.hmq) - crossingPoint (xPair C.hmp))
      (crossingPoint (xPair C.hpq) - crossingPoint (xPair C.hmp)) ≠ 0 := by
  have ha := (crossingParameter_spec (xPair C.hmp) C.m (mem_pair_left _ _)).2.2
  have hb := (crossingParameter_spec (xPair C.hmq) C.m (mem_pair_left _ _)).2.2
  have ha' := (crossingParameter_spec (xPair C.hmp) C.p (mem_pair_right _ _)).2.2
  have hd := (crossingParameter_spec (xPair C.hpq) C.p (mem_pair_left _ _)).2.2
  have h1 : crossingPoint (xPair C.hmq) - crossingPoint (xPair C.hmp) =
      (crossingParameter (xPair C.hmq) C.m (mem_pair_left _ _) -
        crossingParameter (xPair C.hmp) C.m (mem_pair_left _ _)) • edge C.X C.m := by
    rw [ha, hb, gu3_edgePoint_sub]
  have h2 : crossingPoint (xPair C.hpq) - crossingPoint (xPair C.hmp) =
      (crossingParameter (xPair C.hpq) C.p (mem_pair_left _ _) -
        crossingParameter (xPair C.hmp) C.p (mem_pair_right _ _)) • edge C.X C.p := by
    rw [ha', hd, gu3_edgePoint_sub]
  rw [h1, h2, det_smul_smul_plane]
  refine mul_ne_zero (mul_ne_zero (sub_pos.mpr C.order).ne' ?_) ?_
  · intro h0
    apply gu3_a_ne_d C
    rw [ha', hd, sub_eq_zero.mp h0]
  · exact ((gu3_geometry C).2.1 C.m C.p (gu3_remote_of_isCrossing C.hmp) _
      (crossingPoint_mem (xPair C.hmp) C.m (mem_pair_left _ _))
      (crossingPoint_mem (xPair C.hmp) C.p (mem_pair_right _ _))).2.2

/-- the centroid lies in the open triangle -/
theorem gu3_centroid_mem_interior (C : G11_ConfigSw k) :
    G11_centroidSw C ∈ interior (G11_triangle C.X C.hmp C.hmq C.hpq) := by
  obtain ⟨ε, hε, hsub⟩ := gu3_centroid_ball_subset (crossingPoint (xPair C.hmp))
    (crossingPoint (xPair C.hmq) - crossingPoint (xPair C.hmp))
    (crossingPoint (xPair C.hpq) - crossingPoint (xPair C.hmp)) (gu3_det_triangle C)
  have hc : G11_centroidSw C = crossingPoint (xPair C.hmp) +
      (1/3 : ℝ) • (crossingPoint (xPair C.hmq) - crossingPoint (xPair C.hmp)) +
      (1/3 : ℝ) • (crossingPoint (xPair C.hpq) - crossingPoint (xPair C.hmp)) := by
    unfold G11_centroidSw
    module
  have hΔ : G11_triangle C.X C.hmp C.hmq C.hpq = convexHull ℝ {crossingPoint (xPair C.hmp),
      crossingPoint (xPair C.hmp) + (crossingPoint (xPair C.hmq) - crossingPoint (xPair C.hmp)),
      crossingPoint (xPair C.hmp) + (crossingPoint (xPair C.hpq) - crossingPoint (xPair C.hmp))} := by
    unfold G11_triangle
    rw [add_sub_cancel, add_sub_cancel]
  rw [mem_interior, hΔ]
  refine ⟨Metric.ball (G11_centroidSw C) ε, ?_, Metric.isOpen_ball, Metric.mem_ball_self hε⟩
  rw [hc]
  exact hsub

theorem gu3_triangle_compact (C : G11_ConfigSw k) : IsCompact (G11_triangle C.X C.hmp C.hmq C.hpq) :=
  (((Set.finite_singleton _).insert _).insert _).isCompact_convexHull ℝ

theorem gu3_disc_convex (C : G11_ConfigSw k) (r : ℝ) : Convex ℝ (G11_discOfSw C r) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ s t hs ht hst
  refine ⟨s • x + t • y, convex_convexHull ℝ _ hx hy hs ht hst, ?_⟩
  obtain rfl : t = 1 - s := by linarith
  module

theorem gu3_disc_compact (C : G11_ConfigSw k) (r : ℝ) : IsCompact (G11_discOfSw C r) :=
  (gu3_triangle_compact C).image (by fun_prop)

/-- **the closed triangle lies in the open disc** (for every margin `r > 0`) -/
theorem gu3_triangle_sub_interior_disc (C : G11_ConfigSw k) {r : ℝ} (hr : 0 < r) :
    G11_triangle C.X C.hmp C.hmq C.hpq ⊆ interior (G11_discOfSw C r) := by
  intro y hy
  have hs0 : 0 < 1 / (1 + r) := by positivity
  have hs1 : 1 / (1 + r) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  let g : Plane → Plane := fun z => G11_centroidSw C + (1 / (1 + r)) • (z - G11_centroidSw C)
  have hg : Continuous g := by fun_prop
  have hgy : g y ∈ interior (G11_triangle C.X C.hmp C.hmq C.hpq) := by
    have hconv : Convex ℝ (G11_triangle C.X C.hmp C.hmq C.hpq) := convex_convexHull ℝ _
    have := hconv.combo_interior_self_mem_interior
      (gu3_centroid_mem_interior C) hy (sub_pos.mpr hs1) hs0.le
      (sub_add_cancel (1 : ℝ) (1 / (1 + r)))
    have e : g y = (1 - 1 / (1 + r)) • G11_centroidSw C + (1 / (1 + r)) • y := by
      show G11_centroidSw C + (1 / (1 + r)) • (y - G11_centroidSw C) = _
      module
    rw [e]
    exact this
  rw [mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset (hg.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hgy))
  intro z hz
  refine ⟨g z, interior_subset hz, ?_⟩
  show G11_centroidSw C + (1 + r) • (G11_centroidSw C + (1 / (1 + r)) • (z - G11_centroidSw C) -
    G11_centroidSw C) = z
  rw [add_sub_cancel_left, smul_smul, mul_one_div_cancel (by positivity : (1 + r : ℝ) ≠ 0),
    one_smul, add_sub_cancel]

/-- **D1.** `U` is a disc (`IsDisc`: convex, compact, nonempty interior) — the image of the convex hull of
three affinely independent points under a homothety. -/
theorem disc_isDisc : IsDisc π.U := by
  exact ⟨gu3_disc_convex C π.r, gu3_disc_compact C π.r, ⟨crossingPoint (xPair C.hmp),
    gu3_triangle_sub_interior_disc C π.hr (subset_convexHull ℝ _ (by simp))⟩⟩

/-- **D2.** The closed triangle lies in the open disc. -/
theorem triangle_sub_interior : G11_triangle C.X C.hmp C.hmq C.hpq ⊆ interior π.U := by
  exact gu3_triangle_sub_interior_disc C π.hr

/-! ### U4 helpers (D3–D4): the double points inside `U` -/

theorem gu4_a_mem_intU : π.gu4_a ∈ interior π.U :=
  π.triangle_sub_interior (subset_convexHull ℝ _ (by simp [gu4_a]))
theorem gu4_b_mem_intU : π.gu4_b ∈ interior π.U :=
  π.triangle_sub_interior (subset_convexHull ℝ _ (by simp [gu4_b]))
theorem gu4_c_mem_intU : π.gu4_c ∈ interior π.U :=
  π.triangle_sub_interior (subset_convexHull ℝ _ (by simp [gu4_c]))

theorem gu4_segB_sub_theta {y : Plane} (hy : y ∈ edgeSegment π.X₁ π.mB) :
    y ∈ convexHull ℝ {π.gu4_pin, π.apex, π.gu4_pout} := by
  obtain ⟨σ, h0, h1, rfl⟩ := (π.gu4_mem_segB y).mp hy
  have hpin : π.gu4_pin ∈ convexHull ℝ {π.gu4_pin, π.apex, π.gu4_pout} :=
    subset_convexHull ℝ _ (by simp)
  have hapex : π.apex ∈ convexHull ℝ {π.gu4_pin, π.apex, π.gu4_pout} :=
    subset_convexHull ℝ _ (by simp)
  have := (convex_convexHull ℝ _) hpin hapex (sub_nonneg.mpr h1) h0 (by ring)
  convert this using 1
  rw [smul_sub, sub_smul, one_smul]; abel

theorem gu4_segC_sub_theta {y : Plane} (hy : y ∈ edgeSegment π.X₁ π.mC) :
    y ∈ convexHull ℝ {π.gu4_pin, π.apex, π.gu4_pout} := by
  obtain ⟨σ, h0, h1, rfl⟩ := (π.gu4_mem_segC y).mp hy
  have hapex : π.apex ∈ convexHull ℝ {π.gu4_pin, π.apex, π.gu4_pout} :=
    subset_convexHull ℝ _ (by simp)
  have hpout : π.gu4_pout ∈ convexHull ℝ {π.gu4_pin, π.apex, π.gu4_pout} :=
    subset_convexHull ℝ _ (by simp)
  have := (convex_convexHull ℝ _) hapex hpout (sub_nonneg.mpr h1) h0 (by ring)
  convert this using 1
  rw [smul_sub, sub_smul, one_smul]; abel

theorem gu4_yp_mem_intU : π.gu4_yp ∈ interior π.U :=
  π.theta_sub (π.gu4_segC_sub_theta π.gu4_yp_mem_segC)
theorem gu4_yq_mem_intU : π.gu4_yq ∈ interior π.U :=
  π.theta_sub (π.gu4_segB_sub_theta π.gu4_yq_mem_segB)

/-- the three local double points of `X₀` are `a, b, c` -/
theorem gu4_cp_X₀_mp : crossingPoint (xPair π.X₀_cross_mp) = π.gu4_a := by
  obtain ⟨h1, h2⟩ := gu4_crossingPoint_mem_pair π.X₀_cross_mp
  rw [gu4_mem_mB] at h1
  obtain ⟨t, -, -, ht⟩ := h1
  rw [gu4_seg_X₀_p'] at h2
  apply π.gu4_eq_a_of (π.gu4_α_of_mem_p h2)
  rw [ht]
  exact π.gu4_β_of_m t
theorem gu4_cp_X₀_mq : crossingPoint (xPair π.X₀_cross_mq) = π.gu4_b := by
  obtain ⟨h1, h2⟩ := gu4_crossingPoint_mem_pair π.X₀_cross_mq
  rw [gu4_mem_mC] at h1
  obtain ⟨t, -, -, ht⟩ := h1
  rw [gu4_seg_X₀_q'] at h2
  refine π.gu4_eq_b_of ?_ (π.gu4_γ_of_mem_q h2)
  rw [ht]
  exact π.gu4_β_of_m t
theorem gu4_cp_X₀_pq : crossingPoint (xPair π.X₀_cross_pq) = π.gu4_c := by
  obtain ⟨h1, h2⟩ := gu4_crossingPoint_mem_pair π.X₀_cross_pq
  rw [gu4_seg_X₀_p'] at h1
  rw [gu4_seg_X₀_q'] at h2
  exact π.gu4_eq_c_of (π.gu4_α_of_mem_p h1) (π.gu4_γ_of_mem_q h2)

/-- the two new double points of `X₁` are `y_p`, `y_q` -/
theorem gu4_cp_X₁_pC : crossingPoint (xPair π.X₁_cross_pC) = π.gu4_yp := by
  obtain ⟨h1, h2⟩ := gu4_crossingPoint_mem_pair π.X₁_cross_pC
  rw [π.gu4_seg_X₁_eq _ π.gu4_p'_ne.2.1 π.gu4_p'_ne.2.2.1, gu4_seg_X₀_p'] at h1
  obtain ⟨σ, -, -, hσ⟩ := (π.gu4_mem_segC _).mp h2
  have hα := π.gu4_α_of_mem_p h1
  rw [hσ, gu4_α_segC] at hα
  have := π.gu4_σp_unique ((mul_eq_zero.mp hα).resolve_right π.gu4_E_ne)
  rw [hσ, this]
  rfl
theorem gu4_cp_X₁_qB : crossingPoint (xPair π.X₁_cross_qB) = π.gu4_yq := by
  obtain ⟨h1, h2⟩ := gu4_crossingPoint_mem_pair π.X₁_cross_qB
  rw [π.gu4_seg_X₁_eq _ π.gu4_q'_ne.2.1 π.gu4_q'_ne.2.2.1, gu4_seg_X₀_q'] at h1
  obtain ⟨σ, -, -, hσ⟩ := (π.gu4_mem_segB _).mp h2
  have hγ := π.gu4_γ_of_mem_q h1
  rw [hσ, gu4_γ_segB] at hγ
  have := π.gu4_σq_unique ((mul_eq_zero.mp hγ).resolve_right π.gu4_E_ne)
  rw [hσ, this]
  rfl

/-- the labels of the edges of `X₀` that meet `U`: the four `m`-pieces, `p'`, `q'` -/
theorem gu4_classify_X₀ (l : ZMod (k + 3)) {z : Plane} (hz : z ∈ edgeSegment π.X₀ l) (hU : z ∈ π.U) :
    (l = π.mA ∨ l = π.mB ∨ l = π.mC ∨ l = π.mD) ∨ l = π.p' ∨ l = π.q' := by
  rcases π.gu4_label_cases l with h | h | h | h | ⟨i, hi, h⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
  · by_cases hp : i = C.p
    · subst hp
      exact Or.inr (Or.inl h)
    by_cases hq : i = C.q
    · subst hq
      exact Or.inr (Or.inr h)
    · exfalso
      rw [h] at hz
      exact π.gu4_old_edge_off_U i hi hp hq hz hU

/-- a point of an `m`-piece of `X₀` is `edgePoint X m t` with `t` in the piece's range -/
theorem gu4_mpiece_param (l : ZMod (k + 3)) (hl : l = π.mA ∨ l = π.mB ∨ l = π.mC ∨ l = π.mD)
    {z : Plane} (hz : z ∈ edgeSegment π.X₀ l) :
    ∃ t, z = edgePoint C.X C.m t ∧ ((l = π.mA ∧ t ≤ π.t₁) ∨ (l = π.mB ∧ π.t₁ ≤ t ∧ t ≤ π.t₂) ∨
      (l = π.mC ∧ π.t₂ ≤ t ∧ t ≤ π.t₃) ∨ (l = π.mD ∧ π.t₃ ≤ t)) := by
  rcases hl with rfl | rfl | rfl | rfl
  · obtain ⟨t, -, ht1, ht⟩ := (π.gu4_mem_mA z).mp hz
    exact ⟨t, ht, Or.inl ⟨rfl, ht1⟩⟩
  · obtain ⟨t, ht1, ht2, ht⟩ := (π.gu4_mem_mB z).mp hz
    exact ⟨t, ht, Or.inr (Or.inl ⟨rfl, ht1, ht2⟩)⟩
  · obtain ⟨t, ht2, ht3, ht⟩ := (π.gu4_mem_mC z).mp hz
    exact ⟨t, ht, Or.inr (Or.inr (Or.inl ⟨rfl, ht2, ht3⟩))⟩
  · obtain ⟨t, ht3, -, ht⟩ := (π.gu4_mem_mD z).mp hz
    exact ⟨t, ht, Or.inr (Or.inr (Or.inr ⟨rfl, ht3⟩))⟩

theorem gu4_adj_AB : adjacent π.mA π.mB := Or.inr (Or.inr (by rw [← gu4_mA_succ]; ring))
theorem gu4_adj_BC : adjacent π.mB π.mC := Or.inr (Or.inr (by rw [← gu4_mB_succ]; ring))
theorem gu4_adj_CD : adjacent π.mC π.mD := Or.inr (Or.inr (by rw [← gu4_mC_succ]; ring))

/-- two remote `m`-pieces of `X₀` are disjoint -/
theorem gu4_mpieces_disjoint {i j : ZMod (k + 3)} (hi : i = π.mA ∨ i = π.mB ∨ i = π.mC ∨ i = π.mD)
    (hj : j = π.mA ∨ j = π.mB ∨ j = π.mC ∨ j = π.mD) (hr : remote i j) {z : Plane}
    (hzi : z ∈ edgeSegment π.X₀ i) (hzj : z ∈ edgeSegment π.X₀ j) : False := by
  obtain ⟨t, ht, hti⟩ := π.gu4_mpiece_param i hi hzi
  obtain ⟨t', ht', htj⟩ := π.gu4_mpiece_param j hj hzj
  have htt : t = t' := π.gu4_edgePoint_m_injective (ht.symm.trans ht')
  subst htt
  have h1 := π.gu4_h₁
  have h2 := π.gu4_h₂
  have h3 := π.gu4_h₃
  have h4 := π.gu4_h₄
  have hne := gu4_ne_of_remote hr
  have hAB := π.gu4_adj_AB
  have hBC := π.gu4_adj_BC
  have hCD := π.gu4_adj_CD
  rcases hti with ⟨rfl, hA⟩ | ⟨rfl, hB⟩ | ⟨rfl, hC⟩ | ⟨rfl, hD⟩ <;>
    rcases htj with ⟨rfl, hA'⟩ | ⟨rfl, hB'⟩ | ⟨rfl, hC'⟩ | ⟨rfl, hD'⟩ <;>
    first
    | exact hne rfl
    | exact hr hAB
    | exact hr hBC
    | exact hr hCD
    | exact hr (adjacent_symm' hAB)
    | exact hr (adjacent_symm' hBC)
    | exact hr (adjacent_symm' hCD)
    | linarith

/-- the only `m`-piece of `X₀` meeting `p` is `mB` (at `a`) -/
theorem gu4_mpiece_p' {i : ZMod (k + 3)} (hi : i = π.mA ∨ i = π.mB ∨ i = π.mC ∨ i = π.mD) {z : Plane}
    (hzi : z ∈ edgeSegment π.X₀ i) (hz : z ∈ edgeSegment C.X C.p) : i = π.mB := by
  obtain ⟨t, ht, hti⟩ := π.gu4_mpiece_param i hi hzi
  have hα := π.gu4_α_of_mem_p hz
  rw [ht, gu4_α_of_m] at hα
  have htt : t = π.gu4_tmp := by
    have := (mul_eq_zero.mp hα).resolve_right π.gu4_E_ne
    linarith
  have h1 := π.gu4_h₁
  have h2 := π.gu4_h₂
  have h3 := π.gu4_h₃
  have h4 := π.gu4_h₄
  rcases hti with ⟨rfl, hA⟩ | ⟨rfl, -⟩ | ⟨rfl, hC⟩ | ⟨rfl, hD⟩
  · exfalso; linarith
  · rfl
  · exfalso; linarith
  · exfalso; linarith

/-- the only `m`-piece of `X₀` meeting `q` is `mC` (at `b`) -/
theorem gu4_mpiece_q' {i : ZMod (k + 3)} (hi : i = π.mA ∨ i = π.mB ∨ i = π.mC ∨ i = π.mD) {z : Plane}
    (hzi : z ∈ edgeSegment π.X₀ i) (hz : z ∈ edgeSegment C.X C.q) : i = π.mC := by
  obtain ⟨t, ht, hti⟩ := π.gu4_mpiece_param i hi hzi
  have hγ := π.gu4_γ_of_mem_q hz
  rw [ht, gu4_γ_of_m] at hγ
  have htt : t = π.gu4_tmq := by
    have := (mul_eq_zero.mp hγ).resolve_right π.gu4_E_ne
    linarith
  have h1 := π.gu4_h₁
  have h2 := π.gu4_h₂
  have h3 := π.gu4_h₃
  have h4 := π.gu4_h₄
  rcases hti with ⟨rfl, hA⟩ | ⟨rfl, hB⟩ | ⟨rfl, -⟩ | ⟨rfl, hD⟩
  · exfalso; linarith
  · exfalso; linarith
  · rfl
  · exfalso; linarith

/-- **the pairs of edges of `X₀` meeting inside `U`**: exactly `{mB, p'}`, `{mC, q'}`, `{p', q'}` -/
theorem gu4_inner_pair_X₀ {i j : ZMod (k + 3)} (hr : remote i j) {z : Plane}
    (hzi : z ∈ edgeSegment π.X₀ i) (hzj : z ∈ edgeSegment π.X₀ j) (hU : z ∈ π.U) :
    ({i, j} : Finset (ZMod (k + 3))) = {π.mB, π.p'} ∨
      ({i, j} : Finset (ZMod (k + 3))) = {π.mC, π.q'} ∨
      ({i, j} : Finset (ZMod (k + 3))) = {π.p', π.q'} := by
  have hne := gu4_ne_of_remote hr
  rcases π.gu4_classify_X₀ i hzi hU with hmi | rfl | rfl <;>
    rcases π.gu4_classify_X₀ j hzj hU with hmj | rfl | rfl
  · exact (π.gu4_mpieces_disjoint hmi hmj hr hzi hzj).elim
  · left
    rw [π.gu4_mpiece_p' hmi hzi (by rwa [gu4_seg_X₀_p'] at hzj)]
  · right; left
    rw [π.gu4_mpiece_q' hmi hzi (by rwa [gu4_seg_X₀_q'] at hzj)]
  · left
    rw [Finset.pair_comm, π.gu4_mpiece_p' hmj hzj (by rwa [gu4_seg_X₀_p'] at hzi)]
  · exact absurd rfl hne
  · right; right; rfl
  · right; left
    rw [Finset.pair_comm, π.gu4_mpiece_q' hmj hzj (by rwa [gu4_seg_X₀_q'] at hzi)]
  · right; right
    exact Finset.pair_comm _ _
  · exact absurd rfl hne

/-- **D3.** The inner crossings of `M₀` are exactly the three local ones (every other double point lies on
an edge outside `U`, `disc_clear_edge`). -/
theorem inner_M₀ (y : π.M₀.Γ.Crossing) :
    π.M₀.Γ.crossingPoint y ∈ interior π.U ↔
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ y = xPair π.X₀_cross_mp ∨
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ y = xPair π.X₀_cross_mq ∨
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ y = xPair π.X₀_cross_pq := by
  have hpt : π.M₀.Γ.crossingPoint y =
      crossingPoint (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ y) :=
    Shadow.single_crossingPoint _ π.X₀_generic y
  rw [hpt]
  set x := Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ y with hx
  constructor
  · intro hint
    obtain ⟨i, j, hs, hr, -⟩ := x.2
    have hi : crossingPoint x ∈ edgeSegment π.X₀ i :=
      crossingPoint_mem x i (by rw [hs]; exact Finset.mem_insert_self _ _)
    have hj : crossingPoint x ∈ edgeSegment π.X₀ j :=
      crossingPoint_mem x j (by rw [hs]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rcases π.gu4_inner_pair_X₀ hr hi hj (interior_subset hint) with h | h | h
    · exact Or.inl (Subtype.ext (hs.trans h))
    · exact Or.inr (Or.inl (Subtype.ext (hs.trans h)))
    · exact Or.inr (Or.inr (Subtype.ext (hs.trans h)))
  · rintro (h | h | h)
    · rw [h, gu4_cp_X₀_mp]; exact π.gu4_a_mem_intU
    · rw [h, gu4_cp_X₀_mq]; exact π.gu4_b_mem_intU
    · rw [h, gu4_cp_X₀_pq]; exact π.gu4_c_mem_intU

/-- `x_pq` is a crossing of `X₁` (unmoved strands, `X₁_cross_iff`). -/
theorem X₁_cross_pq : IsCrossing π.X₁ {π.p', π.q'} := by
  exact (π.X₁_cross_iff {π.p', π.q'}
    (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm π.gu4_p'_ne.2.1, Ne.symm π.gu4_q'_ne.2.1⟩)
    (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm π.gu4_p'_ne.2.2.1, Ne.symm π.gu4_q'_ne.2.2.1⟩)).mpr π.X₀_cross_pq

/-- the third double point of `X₁` inside `U` is still `c` -/
theorem gu4_cp_X₁_pq : crossingPoint (xPair π.X₁_cross_pq) = π.gu4_c := by
  obtain ⟨h1, h2⟩ := gu4_crossingPoint_mem_pair π.X₁_cross_pq
  rw [π.gu4_seg_X₁_eq _ π.gu4_p'_ne.2.1 π.gu4_p'_ne.2.2.1, gu4_seg_X₀_p'] at h1
  rw [π.gu4_seg_X₁_eq _ π.gu4_q'_ne.2.1 π.gu4_q'_ne.2.2.1, gu4_seg_X₀_q'] at h2
  exact π.gu4_eq_c_of (π.gu4_α_of_mem_p h1) (π.gu4_γ_of_mem_q h2)

/-- the labels of the edges of `X₁` that meet `U` -/
theorem gu4_classify_X₁ (l : ZMod (k + 3)) {z : Plane} (hz : z ∈ edgeSegment π.X₁ l) (hU : z ∈ π.U) :
    (l = π.mA ∨ l = π.mD) ∨ l = π.mB ∨ l = π.mC ∨ l = π.p' ∨ l = π.q' := by
  by_cases hB : l = π.mB
  · exact Or.inr (Or.inl hB)
  by_cases hC : l = π.mC
  · exact Or.inr (Or.inr (Or.inl hC))
  rw [π.gu4_seg_X₁_eq l hB hC] at hz
  rcases π.gu4_classify_X₀ l hz hU with (h | h | h | h) | h | h
  · exact Or.inl (Or.inl h)
  · exact absurd h hB
  · exact absurd h hC
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem gu4_ad_ne {l : ZMod (k + 3)} (h : l = π.mA ∨ l = π.mD) : l ≠ π.mB ∧ l ≠ π.mC := by
  rcases h with rfl | rfl
  · exact ⟨π.gu4_mA_ne_mB, π.gu4_mA_ne_mC⟩
  · exact ⟨π.gu4_mB_ne_mD.symm, π.gu4_mC_ne_mD.symm⟩
theorem gu4_ad_m {l : ZMod (k + 3)} (h : l = π.mA ∨ l = π.mD) :
    l = π.mA ∨ l = π.mB ∨ l = π.mC ∨ l = π.mD := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))

/-- **the pairs of edges of `X₁` meeting inside `U`**: exactly `{p', mC}`, `{q', mB}`, `{p', q'}` -/
theorem gu4_inner_pair_X₁ {i j : ZMod (k + 3)} (hr : remote i j) {z : Plane}
    (hzi : z ∈ edgeSegment π.X₁ i) (hzj : z ∈ edgeSegment π.X₁ j) (hU : z ∈ π.U) :
    ({i, j} : Finset (ZMod (k + 3))) = {π.p', π.mC} ∨
      ({i, j} : Finset (ZMod (k + 3))) = {π.q', π.mB} ∨
      ({i, j} : Finset (ZMod (k + 3))) = {π.p', π.q'} := by
  have hne := gu4_ne_of_remote hr
  have hAB := π.gu4_adj_AB
  have hBC := π.gu4_adj_BC
  have hCD := π.gu4_adj_CD
  have hp'B := π.gu4_p'_ne.2.1
  have hp'C := π.gu4_p'_ne.2.2.1
  have hq'B := π.gu4_q'_ne.2.1
  have hq'C := π.gu4_q'_ne.2.2.1
  rcases π.gu4_classify_X₁ i hzi hU with hai | rfl | rfl | rfl | rfl <;>
    rcases π.gu4_classify_X₁ j hzj hU with haj | rfl | rfl | rfl | rfl
  · -- (a, a)
    exact (π.gu4_mpieces_disjoint (π.gu4_ad_m hai) (π.gu4_ad_m haj) hr
      (by rwa [π.gu4_seg_X₁_eq i (π.gu4_ad_ne hai).1 (π.gu4_ad_ne hai).2] at hzi)
      (by rwa [π.gu4_seg_X₁_eq j (π.gu4_ad_ne haj).1 (π.gu4_ad_ne haj).2] at hzj)).elim
  · -- (a, mB)
    exfalso
    rw [π.gu4_seg_X₁_eq i (π.gu4_ad_ne hai).1 (π.gu4_ad_ne hai).2] at hzi
    obtain ⟨σ, h0, h1, rfl⟩ := (π.gu4_mem_segB z).mp hzj
    rcases hai with rfl | rfl
    · exact hr hAB
    · rcases π.gu4_meet_B h0 h1 _ π.gu4_mB_ne_mD.symm π.gu4_mC_ne_mD.symm hzi with h | ⟨h, -⟩
      · exact π.gu4_q'_ne.2.2.2 h.symm
      · exact π.gu4_mA_ne_mD h.symm
  · -- (a, mC)
    exfalso
    rw [π.gu4_seg_X₁_eq i (π.gu4_ad_ne hai).1 (π.gu4_ad_ne hai).2] at hzi
    obtain ⟨σ, h0, h1, rfl⟩ := (π.gu4_mem_segC z).mp hzj
    rcases hai with rfl | rfl
    · rcases π.gu4_meet_C h0 h1 _ π.gu4_mA_ne_mB π.gu4_mA_ne_mC hzi with h | ⟨h, -⟩
      · exact π.gu4_p'_ne.1 h.symm
      · exact π.gu4_mA_ne_mD h
    · exact hr (adjacent_symm' hCD)
  · -- (a, p')
    exfalso
    rw [π.gu4_seg_X₁_eq i (π.gu4_ad_ne hai).1 (π.gu4_ad_ne hai).2] at hzi
    rw [π.gu4_seg_X₁_eq _ hp'B hp'C, gu4_seg_X₀_p'] at hzj
    have := π.gu4_mpiece_p' (π.gu4_ad_m hai) hzi hzj
    rcases hai with rfl | rfl
    · exact π.gu4_mA_ne_mB this
    · exact π.gu4_mB_ne_mD this.symm
  · -- (a, q')
    exfalso
    rw [π.gu4_seg_X₁_eq i (π.gu4_ad_ne hai).1 (π.gu4_ad_ne hai).2] at hzi
    rw [π.gu4_seg_X₁_eq _ hq'B hq'C, gu4_seg_X₀_q'] at hzj
    have := π.gu4_mpiece_q' (π.gu4_ad_m hai) hzi hzj
    rcases hai with rfl | rfl
    · exact π.gu4_mA_ne_mC this
    · exact π.gu4_mC_ne_mD this.symm
  · -- (mB, a)
    exfalso
    rw [π.gu4_seg_X₁_eq j (π.gu4_ad_ne haj).1 (π.gu4_ad_ne haj).2] at hzj
    obtain ⟨σ, h0, h1, rfl⟩ := (π.gu4_mem_segB z).mp hzi
    rcases haj with rfl | rfl
    · exact hr (adjacent_symm' hAB)
    · rcases π.gu4_meet_B h0 h1 _ π.gu4_mB_ne_mD.symm π.gu4_mC_ne_mD.symm hzj with h | ⟨h, -⟩
      · exact π.gu4_q'_ne.2.2.2 h.symm
      · exact π.gu4_mA_ne_mD h.symm
  · -- (mB, mB)
    exact absurd rfl hne
  · -- (mB, mC)
    exact (hr hBC).elim
  · -- (mB, p')
    exfalso
    rw [π.gu4_seg_X₁_eq _ hp'B hp'C] at hzj
    obtain ⟨σ, h0, h1, rfl⟩ := (π.gu4_mem_segB z).mp hzi
    rcases π.gu4_meet_B h0 h1 _ hp'B hp'C hzj with h | ⟨h, -⟩
    · exact π.gu4_p'_ne_q' h
    · exact π.gu4_p'_ne.1 h
  · -- (mB, q')
    right; left
    exact Finset.pair_comm _ _
  · -- (mC, a)
    exfalso
    rw [π.gu4_seg_X₁_eq j (π.gu4_ad_ne haj).1 (π.gu4_ad_ne haj).2] at hzj
    obtain ⟨σ, h0, h1, rfl⟩ := (π.gu4_mem_segC z).mp hzi
    rcases haj with rfl | rfl
    · rcases π.gu4_meet_C h0 h1 _ π.gu4_mA_ne_mB π.gu4_mA_ne_mC hzj with h | ⟨h, -⟩
      · exact π.gu4_p'_ne.1 h.symm
      · exact π.gu4_mA_ne_mD h
    · exact hr hCD
  · -- (mC, mB)
    exact (hr (adjacent_symm' hBC)).elim
  · -- (mC, mC)
    exact absurd rfl hne
  · -- (mC, p')
    left
    exact Finset.pair_comm _ _
  · -- (mC, q')
    exfalso
    rw [π.gu4_seg_X₁_eq _ hq'B hq'C] at hzj
    obtain ⟨σ, h0, h1, rfl⟩ := (π.gu4_mem_segC z).mp hzi
    rcases π.gu4_meet_C h0 h1 _ hq'B hq'C hzj with h | ⟨h, -⟩
    · exact π.gu4_p'_ne_q' h.symm
    · exact π.gu4_q'_ne.2.2.2 h
  · -- (p', a)
    exfalso
    rw [π.gu4_seg_X₁_eq j (π.gu4_ad_ne haj).1 (π.gu4_ad_ne haj).2] at hzj
    rw [π.gu4_seg_X₁_eq _ hp'B hp'C, gu4_seg_X₀_p'] at hzi
    have := π.gu4_mpiece_p' (π.gu4_ad_m haj) hzj hzi
    rcases haj with rfl | rfl
    · exact π.gu4_mA_ne_mB this
    · exact π.gu4_mB_ne_mD this.symm
  · -- (p', mB)
    exfalso
    rw [π.gu4_seg_X₁_eq _ hp'B hp'C] at hzi
    obtain ⟨σ, h0, h1, rfl⟩ := (π.gu4_mem_segB z).mp hzj
    rcases π.gu4_meet_B h0 h1 _ hp'B hp'C hzi with h | ⟨h, -⟩
    · exact π.gu4_p'_ne_q' h
    · exact π.gu4_p'_ne.1 h
  · -- (p', mC)
    left; rfl
  · -- (p', p')
    exact absurd rfl hne
  · -- (p', q')
    right; right; rfl
  · -- (q', a)
    exfalso
    rw [π.gu4_seg_X₁_eq j (π.gu4_ad_ne haj).1 (π.gu4_ad_ne haj).2] at hzj
    rw [π.gu4_seg_X₁_eq _ hq'B hq'C, gu4_seg_X₀_q'] at hzi
    have := π.gu4_mpiece_q' (π.gu4_ad_m haj) hzj hzi
    rcases haj with rfl | rfl
    · exact π.gu4_mA_ne_mC this
    · exact π.gu4_mC_ne_mD this.symm
  · -- (q', mB)
    right; left; rfl
  · -- (q', mC)
    exfalso
    rw [π.gu4_seg_X₁_eq _ hq'B hq'C] at hzi
    obtain ⟨σ, h0, h1, rfl⟩ := (π.gu4_mem_segC z).mp hzj
    rcases π.gu4_meet_C h0 h1 _ hq'B hq'C hzi with h | ⟨h, -⟩
    · exact π.gu4_p'_ne_q' h.symm
    · exact π.gu4_q'_ne.2.2.2 h
  · -- (q', p')
    right; right
    exact Finset.pair_comm _ _
  · -- (q', q')
    exact absurd rfl hne

/-- **D4.** The inner crossings of `M₁` are exactly `x_pq` and the two new ones. -/
theorem inner_M₁ (y : π.M₁.Γ.Crossing) :
    π.M₁.Γ.crossingPoint y ∈ interior π.U ↔
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩ y = xPair π.X₁_cross_pC ∨
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩ y = xPair π.X₁_cross_qB ∨
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩ y = xPair π.X₁_cross_pq := by
  have hpt : π.M₁.Γ.crossingPoint y =
      crossingPoint (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩ y) :=
    Shadow.single_crossingPoint _ π.X₁_generic y
  rw [hpt]
  set x := Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩ y with hx
  constructor
  · intro hint
    obtain ⟨i, j, hs, hr, -⟩ := x.2
    have hi : crossingPoint x ∈ edgeSegment π.X₁ i :=
      crossingPoint_mem x i (by rw [hs]; exact Finset.mem_insert_self _ _)
    have hj : crossingPoint x ∈ edgeSegment π.X₁ j :=
      crossingPoint_mem x j (by rw [hs]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rcases π.gu4_inner_pair_X₁ hr hi hj (interior_subset hint) with h | h | h
    · exact Or.inl (Subtype.ext (hs.trans h))
    · exact Or.inr (Or.inl (Subtype.ext (hs.trans h)))
    · exact Or.inr (Or.inr (Subtype.ext (hs.trans h)))
  · rintro (h | h | h)
    · rw [h, gu4_cp_X₁_pC]; exact π.gu4_yp_mem_intU
    · rw [h, gu4_cp_X₁_qB]; exact π.gu4_yq_mem_intU
    · rw [h, gu4_cp_X₁_pq]; exact π.gu4_c_mem_intU

/-! ### U5 helpers (labels and vertices of `X₀`, the bent triangle `Θ`, common points, entry/exit
parameters along a segment). All names `gu5_*`. -/

theorem gu5_mA_val : π.mA.val = C.m.val := by
  unfold mA; rw [ZMod.val_natCast, Nat.mod_eq_of_lt]; have := ZMod.val_lt C.m; omega

theorem gu5_mB_val : π.mB.val = C.m.val + 1 := by
  unfold mB; rw [ZMod.val_natCast, Nat.mod_eq_of_lt]; have := ZMod.val_lt C.m; omega

theorem gu5_mC_val : π.mC.val = C.m.val + 2 := by
  unfold mC; rw [ZMod.val_natCast, Nat.mod_eq_of_lt]; have := ZMod.val_lt C.m; omega

theorem gu5_mD_val : π.mD.val = C.m.val + 3 := by
  unfold mD; rw [ZMod.val_natCast, Nat.mod_eq_of_lt]; have := ZMod.val_lt C.m; omega

theorem gu5_mA_add_one : π.mA + 1 = π.mB := by unfold mA mB; push_cast; ring
theorem gu5_mB_add_one : π.mB + 1 = π.mC := by unfold mB mC; push_cast; ring
theorem gu5_mC_add_one : π.mC + 1 = π.mD := by unfold mC mD; push_cast; ring

theorem gu5_mA_ne_mB : π.mA ≠ π.mB := fun h => by
  have := congrArg ZMod.val h; rw [gu5_mA_val, gu5_mB_val] at this; omega
theorem gu5_mA_ne_mC : π.mA ≠ π.mC := fun h => by
  have := congrArg ZMod.val h; rw [gu5_mA_val, gu5_mC_val] at this; omega
theorem gu5_mA_ne_mD : π.mA ≠ π.mD := fun h => by
  have := congrArg ZMod.val h; rw [gu5_mA_val, gu5_mD_val] at this; omega
theorem gu5_mB_ne_mC : π.mB ≠ π.mC := fun h => by
  have := congrArg ZMod.val h; rw [gu5_mB_val, gu5_mC_val] at this; omega
theorem gu5_mB_ne_mD : π.mB ≠ π.mD := fun h => by
  have := congrArg ZMod.val h; rw [gu5_mB_val, gu5_mD_val] at this; omega
theorem gu5_mC_ne_mD : π.mC ≠ π.mD := fun h => by
  have := congrArg ZMod.val h; rw [gu5_mC_val, gu5_mD_val] at this; omega

theorem gu5_X₀_apply (j : ZMod (k + 3)) : π.X₀ j =
    (if j.val ≤ C.m.val then C.X (j.val : ZMod k)
     else if j.val = C.m.val + 1 then edgePoint C.X C.m π.t₁
     else if j.val = C.m.val + 2 then edgePoint C.X C.m π.t₂
     else if j.val = C.m.val + 3 then edgePoint C.X C.m π.t₃
     else C.X ((j.val - 3 : ℕ) : ZMod k)) := rfl

theorem gu5_X₀_mA : π.X₀ π.mA = C.X C.m := by
  rw [gu5_X₀_apply, ite_eq_left (by rw [gu5_mA_val]), gu5_mA_val, ZMod.natCast_zmod_val]

theorem gu5_X₀_mB : π.X₀ π.mB = edgePoint C.X C.m π.t₁ := by
  rw [gu5_X₀_apply, ite_eq_right (by rw [gu5_mB_val]; omega), ite_eq_left (by rw [gu5_mB_val])]

theorem gu5_X₀_mC : π.X₀ π.mC = edgePoint C.X C.m π.t₂ := by
  rw [gu5_X₀_apply, ite_eq_right (by rw [gu5_mC_val]; omega), ite_eq_right (by rw [gu5_mC_val]; omega),
    ite_eq_left (by rw [gu5_mC_val])]

theorem gu5_X₀_mD : π.X₀ π.mD = edgePoint C.X C.m π.t₃ := by
  rw [gu5_X₀_apply, ite_eq_right (by rw [gu5_mD_val]; omega), ite_eq_right (by rw [gu5_mD_val]; omega),
    ite_eq_right (by rw [gu5_mD_val]; omega), ite_eq_left (by rw [gu5_mD_val])]

theorem gu5_X₀_mD_succ : π.X₀ (π.mD + 1) = C.X (C.m + 1) := by
  have hm := ZMod.val_lt C.m
  have h4 : π.mD + 1 = ((C.m.val + 4 : ℕ) : ZMod (k + 3)) := by unfold mD; push_cast; ring
  rw [h4, gu5_X₀_apply]
  by_cases hk : C.m.val + 1 < k
  · have hv : ((C.m.val + 4 : ℕ) : ZMod (k + 3)).val = C.m.val + 4 := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [ite_eq_right (by rw [hv]; omega), ite_eq_right (by rw [hv]; omega), ite_eq_right (by rw [hv]; omega),
      ite_eq_right (by rw [hv]; omega), hv]
    congr 1
    rw [show C.m.val + 4 - 3 = C.m.val + 1 by omega]
    push_cast
    rw [ZMod.natCast_zmod_val]
  · have hk' : C.m.val + 1 = k := by omega
    have hz : ((C.m.val + 4 : ℕ) : ZMod (k + 3)) = 0 := by
      rw [show C.m.val + 4 = k + 3 by omega]; exact ZMod.natCast_self _
    rw [hz, ite_eq_left (by rw [ZMod.val_zero]; exact Nat.zero_le _), ZMod.val_zero]
    congr 1
    rw [← ZMod.natCast_zmod_val C.m]
    push_cast
    rw [show ((C.m.val : ZMod k) + 1) = ((C.m.val + 1 : ℕ) : ZMod k) by push_cast; rfl, hk',
      ZMod.natCast_self]

theorem gu5_lab_of_lt {i : ZMod k} (h : i.val < C.m.val) :
    G11_lab C.m i = (i.val : ZMod (k + 3)) := by
  unfold G11_lab; rw [ite_eq_left h.le]

theorem gu5_lab_of_gt {i : ZMod k} (h : C.m.val < i.val) :
    G11_lab C.m i = ((i.val + 3 : ℕ) : ZMod (k + 3)) := by
  unfold G11_lab; rw [ite_eq_right (not_le.mpr h)]

theorem gu5_lab_val_of_lt {i : ZMod k} (h : i.val < C.m.val) : (G11_lab C.m i).val = i.val := by
  have := ZMod.val_lt C.m
  rw [gu5_lab_of_lt h, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

theorem gu5_lab_val_of_gt {i : ZMod k} (h : C.m.val < i.val) :
    (G11_lab C.m i).val = i.val + 3 := by
  have := ZMod.val_lt i
  rw [gu5_lab_of_gt h, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

theorem gu5_val_lt_or_gt {i : ZMod k} (hi : i ≠ C.m) : i.val < C.m.val ∨ C.m.val < i.val := by
  rcases lt_trichotomy i.val C.m.val with h | h | h
  · exact Or.inl h
  · exact absurd (ZMod.val_injective k h) hi
  · exact Or.inr h

theorem gu5_X₀_lab {i : ZMod k} (hi : i ≠ C.m) : π.X₀ (G11_lab C.m i) = C.X i := by
  rcases gu5_val_lt_or_gt hi with h | h
  · rw [gu5_X₀_apply, ite_eq_left (by rw [gu5_lab_val_of_lt h]; exact h.le), gu5_lab_val_of_lt h,
      ZMod.natCast_zmod_val]
  · rw [gu5_X₀_apply, ite_eq_right (by rw [gu5_lab_val_of_gt h]; omega),
      ite_eq_right (by rw [gu5_lab_val_of_gt h]; omega), ite_eq_right (by rw [gu5_lab_val_of_gt h]; omega),
      ite_eq_right (by rw [gu5_lab_val_of_gt h]; omega), gu5_lab_val_of_gt h, Nat.add_sub_cancel,
      ZMod.natCast_zmod_val]

theorem gu5_X₀_lab_succ {i : ZMod k} (hi : i ≠ C.m) : π.X₀ (G11_lab C.m i + 1) = C.X (i + 1) := by
  have hm := ZMod.val_lt C.m
  have hik := ZMod.val_lt i
  rcases gu5_val_lt_or_gt hi with h | h
  · have h1 : G11_lab C.m i + 1 = ((i.val + 1 : ℕ) : ZMod (k + 3)) := by
      rw [gu5_lab_of_lt h]; push_cast; rfl
    have hv : ((i.val + 1 : ℕ) : ZMod (k + 3)).val = i.val + 1 := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [h1, gu5_X₀_apply, ite_eq_left (by rw [hv]; omega), hv]
    congr 1
    push_cast
    rw [ZMod.natCast_zmod_val]
  · have h1 : G11_lab C.m i + 1 = ((i.val + 4 : ℕ) : ZMod (k + 3)) := by
      rw [gu5_lab_of_gt h]; push_cast; ring
    rw [h1, gu5_X₀_apply]
    by_cases hk : i.val + 1 < k
    · have hv : ((i.val + 4 : ℕ) : ZMod (k + 3)).val = i.val + 4 := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      rw [ite_eq_right (by rw [hv]; omega), ite_eq_right (by rw [hv]; omega), ite_eq_right (by rw [hv]; omega),
        ite_eq_right (by rw [hv]; omega), hv]
      congr 1
      rw [show i.val + 4 - 3 = i.val + 1 by omega]
      push_cast
      rw [ZMod.natCast_zmod_val]
    · have hk' : i.val + 1 = k := by omega
      have hz : ((i.val + 4 : ℕ) : ZMod (k + 3)) = 0 := by
        rw [show i.val + 4 = k + 3 by omega]; exact ZMod.natCast_self _
      rw [hz, ite_eq_left (by rw [ZMod.val_zero]; exact Nat.zero_le _), ZMod.val_zero]
      congr 1
      rw [← ZMod.natCast_zmod_val i]
      push_cast
      rw [show ((i.val : ZMod k) + 1) = ((i.val + 1 : ℕ) : ZMod k) by push_cast; rfl, hk',
        ZMod.natCast_self]

theorem gu5_edgePoint_lab {i : ZMod k} (hi : i ≠ C.m) (θ : ℝ) :
    edgePoint π.X₀ (G11_lab C.m i) θ = edgePoint C.X i θ := by
  unfold edgePoint edge; rw [gu5_X₀_lab π hi, gu5_X₀_lab_succ π hi]

theorem gu5_edgeSegment_lab {i : ZMod k} (hi : i ≠ C.m) :
    edgeSegment π.X₀ (G11_lab C.m i) = edgeSegment C.X i := by
  simp only [edgeSegment, gu5_edgePoint_lab π hi]

theorem gu5_lab_ne {i : ZMod k} (hi : i ≠ C.m) :
    G11_lab C.m i ≠ π.mA ∧ G11_lab C.m i ≠ π.mB ∧ G11_lab C.m i ≠ π.mC ∧ G11_lab C.m i ≠ π.mD := by
  have hA := gu5_mA_val π; have hB := gu5_mB_val π; have hC := gu5_mC_val π; have hD := gu5_mD_val π
  rcases gu5_val_lt_or_gt hi with h | h
  · have hv := gu5_lab_val_of_lt h
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
      · have := congrArg ZMod.val e; omega
  · have hv := gu5_lab_val_of_gt h
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
      · have := congrArg ZMod.val e; omega

theorem gu5_lab_inj {i j : ZMod k} (hi : i ≠ C.m) (hj : j ≠ C.m) (h : G11_lab C.m i = G11_lab C.m j) :
    i = j := by
  apply ZMod.val_injective
  have h' := congrArg ZMod.val h
  rcases gu5_val_lt_or_gt hi with hi' | hi' <;> rcases gu5_val_lt_or_gt hj with hj' | hj'
  · rwa [gu5_lab_val_of_lt hi', gu5_lab_val_of_lt hj'] at h'
  · rw [gu5_lab_val_of_lt hi', gu5_lab_val_of_gt hj'] at h'; omega
  · rw [gu5_lab_val_of_gt hi', gu5_lab_val_of_lt hj'] at h'; omega
  · rw [gu5_lab_val_of_gt hi', gu5_lab_val_of_gt hj'] at h'; omega

theorem gu5_label_cases (j : ZMod (k + 3)) :
    j = π.mA ∨ j = π.mB ∨ j = π.mC ∨ j = π.mD ∨ ∃ i : ZMod k, i ≠ C.m ∧ j = G11_lab C.m i := by
  have hm := ZMod.val_lt C.m
  have hj := ZMod.val_lt j
  rcases lt_trichotomy j.val C.m.val with h | h | h
  · right; right; right; right
    refine ⟨(j.val : ZMod k), ?_, ?_⟩
    · intro e; have := congrArg ZMod.val e; rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
      omega
    · have hv : ((j.val : ℕ) : ZMod k).val = j.val := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      rw [gu5_lab_of_lt (by rw [hv]; exact h), hv, ZMod.natCast_zmod_val]
  · left; apply ZMod.val_injective; rw [gu5_mA_val]; exact h
  · rcases (by omega : j.val = C.m.val + 1 ∨ j.val = C.m.val + 2 ∨ j.val = C.m.val + 3 ∨
        C.m.val + 3 < j.val) with h1 | h1 | h1 | h1
    · right; left; apply ZMod.val_injective; rw [gu5_mB_val]; exact h1
    · right; right; left; apply ZMod.val_injective; rw [gu5_mC_val]; exact h1
    · right; right; right; left; apply ZMod.val_injective; rw [gu5_mD_val]; exact h1
    · right; right; right; right
      refine ⟨((j.val - 3 : ℕ) : ZMod k), ?_, ?_⟩
      · intro e; have := congrArg ZMod.val e
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at this; omega
      · have hv : ((j.val - 3 : ℕ) : ZMod k).val = j.val - 3 := by
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
        rw [gu5_lab_of_gt (by rw [hv]; omega), hv, show j.val - 3 + 3 = j.val by omega,
          ZMod.natCast_zmod_val]

theorem gu5_ne_of_isCrossing {i j : ZMod k} (h : IsCrossing C.X {i, j}) : i ≠ j := by
  obtain ⟨a, b, hs, hr, -⟩ := h
  have hab : a ≠ b := (remote_endpoints a b hr).1.symm
  intro hij
  rw [hij] at hs
  have ha : a ∈ ({j} : Finset (ZMod k)) := by
    rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self j)] at hs
    rw [hs]; exact Finset.mem_insert_self a {b}
  have hb : b ∈ ({j} : Finset (ZMod k)) := by
    rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self j)] at hs
    rw [hs]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  exact hab ((Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm)

theorem gu5_p_ne_m : C.p ≠ C.m := (gu5_ne_of_isCrossing C.hmp).symm
theorem gu5_q_ne_m : C.q ≠ C.m := (gu5_ne_of_isCrossing C.hmq).symm
theorem gu5_p_ne_q : C.p ≠ C.q := gu5_ne_of_isCrossing C.hpq

theorem gu5_p'_ne : π.p' ≠ π.mA ∧ π.p' ≠ π.mB ∧ π.p' ≠ π.mC ∧ π.p' ≠ π.mD := gu5_lab_ne π gu5_p_ne_m
theorem gu5_q'_ne : π.q' ≠ π.mA ∧ π.q' ≠ π.mB ∧ π.q' ≠ π.mC ∧ π.q' ≠ π.mD := gu5_lab_ne π gu5_q_ne_m
theorem gu5_p'_ne_q' : π.p' ≠ π.q' := fun h => gu5_p_ne_q (gu5_lab_inj gu5_p_ne_m gu5_q_ne_m h)

theorem gu5_edgePoint_p' (θ : ℝ) : edgePoint π.X₀ π.p' θ = edgePoint C.X C.p θ :=
  gu5_edgePoint_lab π gu5_p_ne_m θ
theorem gu5_edgePoint_q' (θ : ℝ) : edgePoint π.X₀ π.q' θ = edgePoint C.X C.q θ :=
  gu5_edgePoint_lab π gu5_q_ne_m θ

theorem gu5_edgePoint_mA (θ : ℝ) : edgePoint π.X₀ π.mA θ = edgePoint C.X C.m (θ * π.t₁) := by
  unfold edgePoint edge
  rw [gu5_mA_add_one, gu5_X₀_mA, gu5_X₀_mB]
  unfold edgePoint edge
  module

theorem gu5_edgePoint_mB (θ : ℝ) :
    edgePoint π.X₀ π.mB θ = edgePoint C.X C.m (π.t₁ + θ * (π.t₂ - π.t₁)) := by
  unfold edgePoint edge
  rw [gu5_mB_add_one, gu5_X₀_mB, gu5_X₀_mC]
  unfold edgePoint edge
  module

theorem gu5_edgePoint_mC (θ : ℝ) :
    edgePoint π.X₀ π.mC θ = edgePoint C.X C.m (π.t₂ + θ * (π.t₃ - π.t₂)) := by
  unfold edgePoint edge
  rw [gu5_mC_add_one, gu5_X₀_mC, gu5_X₀_mD]
  unfold edgePoint edge
  module

theorem gu5_edgePoint_mD (θ : ℝ) :
    edgePoint π.X₀ π.mD θ = edgePoint C.X C.m (π.t₃ + θ * (1 - π.t₃)) := by
  unfold edgePoint edge
  rw [gu5_X₀_mD_succ, gu5_X₀_mD]
  unfold edgePoint edge
  module

/-! #### `X₁` versus `X₀` -/

theorem gu5_X₁_of_ne {j : ZMod (k + 3)} (h : j ≠ π.mC) : π.X₁ j = π.X₀ j :=
  Function.update_of_ne h _ _

theorem gu5_X₁_mC : π.X₁ π.mC = π.apex := Function.update_self _ _ _
theorem gu5_X₁_mB : π.X₁ π.mB = π.X₀ π.mB := gu5_X₁_of_ne π (gu5_mB_ne_mC π)
theorem gu5_X₁_mD : π.X₁ π.mD = π.X₀ π.mD := gu5_X₁_of_ne π (gu5_mC_ne_mD π).symm

theorem gu5_succ_ne_mC {j : ZMod (k + 3)} (hB : j ≠ π.mB) : j + 1 ≠ π.mC :=
  fun h => hB (add_right_cancel (h.trans (gu5_mB_add_one π).symm))

theorem gu5_edgePoint_X₁ {j : ZMod (k + 3)} (hB : j ≠ π.mB) (hC : j ≠ π.mC) (θ : ℝ) :
    edgePoint π.X₁ j θ = edgePoint π.X₀ j θ := by
  unfold edgePoint edge; rw [gu5_X₁_of_ne π hC, gu5_X₁_of_ne π (gu5_succ_ne_mC π hB)]

theorem gu5_edge_X₁ {j : ZMod (k + 3)} (hB : j ≠ π.mB) (hC : j ≠ π.mC) :
    edge π.X₁ j = edge π.X₀ j := by
  unfold edge; rw [gu5_X₁_of_ne π hC, gu5_X₁_of_ne π (gu5_succ_ne_mC π hB)]

theorem gu5_edgeSegment_X₁ {j : ZMod (k + 3)} (hB : j ≠ π.mB) (hC : j ≠ π.mC) :
    edgeSegment π.X₁ j = edgeSegment π.X₀ j := by
  simp only [edgeSegment, gu5_edgePoint_X₁ π hB hC]

/-! #### The disc, the closed triangle and the bent triangle `Θ` -/

theorem gu5_U_convex : Convex ℝ π.U := π.disc_isDisc.convex
theorem gu5_U_closed : IsClosed π.U := π.disc_isDisc.isCompact.isClosed

theorem gu5_t₁_lt_t₂ : π.t₁ < π.t₂ := π.h₁.trans π.h₂
theorem gu5_t₂_lt_t₃ : π.t₂ < π.t₃ := π.h₃.trans π.h₄
theorem gu5_t₁_lt_t₃ : π.t₁ < π.t₃ := (gu5_t₁_lt_t₂ π).trans (gu5_t₂_lt_t₃ π)

/-- the bent triangle `Θ = conv{p_in, w, p_out}` -/
noncomputable def gu5_Θ : Set Plane := convexHull ℝ {π.X₀ π.mB, π.apex, π.X₀ π.mD}

theorem gu5_Θ_sub : gu5_Θ π ⊆ interior π.U := by
  unfold gu5_Θ; rw [gu5_X₀_mB, gu5_X₀_mD]; exact π.theta_sub

theorem gu5_Θ_convex : Convex ℝ (gu5_Θ π) := convex_convexHull ℝ _

theorem gu5_mB_mem_Θ : π.X₀ π.mB ∈ gu5_Θ π := subset_convexHull ℝ _ (by simp)
theorem gu5_apex_mem_Θ : π.apex ∈ gu5_Θ π := subset_convexHull ℝ _ (by simp)
theorem gu5_mD_mem_Θ : π.X₀ π.mD ∈ gu5_Θ π := subset_convexHull ℝ _ (by simp)

theorem gu5_mC_mem_Θ : π.X₀ π.mC ∈ gu5_Θ π := by
  apply (gu5_Θ_convex π).segment_subset (gu5_mB_mem_Θ π) (gu5_mD_mem_Θ π)
  rw [gu5_X₀_mB, gu5_X₀_mC, gu5_X₀_mD]
  exact gu5_edgePoint_mem_segment C.X C.m (gu5_t₁_lt_t₂ π).le (gu5_t₂_lt_t₃ π).le (gu5_t₁_lt_t₃ π)

theorem gu5_segB₀ {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : edgePoint π.X₀ π.mB θ ∈ interior π.U := by
  apply gu5_Θ_sub π
  have : edgePoint π.X₀ π.mB θ ∈ edgeSegment π.X₀ π.mB := ⟨θ, h0, h1, rfl⟩
  rw [gu5_edgeSegment_eq_segment, gu5_mB_add_one] at this
  exact (gu5_Θ_convex π).segment_subset (gu5_mB_mem_Θ π) (gu5_mC_mem_Θ π) this

theorem gu5_segC₀ {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : edgePoint π.X₀ π.mC θ ∈ interior π.U := by
  apply gu5_Θ_sub π
  have : edgePoint π.X₀ π.mC θ ∈ edgeSegment π.X₀ π.mC := ⟨θ, h0, h1, rfl⟩
  rw [gu5_edgeSegment_eq_segment, gu5_mC_add_one] at this
  exact (gu5_Θ_convex π).segment_subset (gu5_mC_mem_Θ π) (gu5_mD_mem_Θ π) this

theorem gu5_segB₁ {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : edgePoint π.X₁ π.mB θ ∈ interior π.U := by
  apply gu5_Θ_sub π
  have : edgePoint π.X₁ π.mB θ ∈ edgeSegment π.X₁ π.mB := ⟨θ, h0, h1, rfl⟩
  rw [gu5_edgeSegment_eq_segment, gu5_mB_add_one, gu5_X₁_mB, gu5_X₁_mC] at this
  exact (gu5_Θ_convex π).segment_subset (gu5_mB_mem_Θ π) (gu5_apex_mem_Θ π) this

theorem gu5_segC₁ {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : edgePoint π.X₁ π.mC θ ∈ interior π.U := by
  apply gu5_Θ_sub π
  have : edgePoint π.X₁ π.mC θ ∈ edgeSegment π.X₁ π.mC := ⟨θ, h0, h1, rfl⟩
  rw [gu5_edgeSegment_eq_segment, gu5_mC_add_one, gu5_X₁_mC, gu5_X₁_mD] at this
  exact (gu5_Θ_convex π).segment_subset (gu5_apex_mem_Θ π) (gu5_mD_mem_Θ π) this

theorem gu5_xmp_mem : crossingPoint (xPair C.hmp) ∈ interior π.U :=
  π.triangle_sub_interior (subset_convexHull ℝ _ (by simp))
theorem gu5_xmq_mem : crossingPoint (xPair C.hmq) ∈ interior π.U :=
  π.triangle_sub_interior (subset_convexHull ℝ _ (by simp))
theorem gu5_xpq_mem : crossingPoint (xPair C.hpq) ∈ interior π.U :=
  π.triangle_sub_interior (subset_convexHull ℝ _ (by simp))

/-- A common point of two crossing edges of `X` is their double point (genericity of `X`). -/
theorem gu5_common_point {i j : ZMod k} (hij : IsCrossing C.X {i, j}) {x : Plane}
    (hi : x ∈ edgeSegment C.X i) (hj : x ∈ edgeSegment C.X j) : x = crossingPoint (xPair hij) := by
  set y : (Shadow.single C.comp).Crossing := (Shadow.singleCrossingEquiv C.comp).symm (xPair hij) with hy
  have hy' : Shadow.singleCrossingEquiv C.comp y = xPair hij := Equiv.apply_symm_apply _ _
  have h1 : x = (Shadow.single C.comp).crossingPoint y := by
    apply C.gen.common_point_unique y
    intro s hs
    have hs' : Shadow.singleStrandEquiv C.comp s ∈ (Shadow.singleCrossingEquiv C.comp y).val :=
      (Shadow.mem_singleCrossingEquiv_iff C.comp y s).mpr hs
    rw [hy'] at hs'
    change s.2 ∈ ({i, j} : Finset (ZMod k)) at hs'
    change x ∈ edgeSegment C.X s.2
    rcases Finset.mem_insert.mp hs' with h | h
    · rw [h]; exact hi
    · rw [Finset.mem_singleton.mp h]; exact hj
  rw [h1, Shadow.single_crossingPoint C.comp C.gen y, hy']
  rfl

theorem gu5_common_mp {x : Plane} (hm : x ∈ edgeSegment C.X C.m) (hp : x ∈ edgeSegment C.X C.p) :
    x ∈ interior π.U := by
  rw [gu5_common_point C.hmp hm hp]; exact gu5_xmp_mem π
theorem gu5_common_mq {x : Plane} (hm : x ∈ edgeSegment C.X C.m) (hq : x ∈ edgeSegment C.X C.q) :
    x ∈ interior π.U := by
  rw [gu5_common_point C.hmq hm hq]; exact gu5_xmq_mem π
theorem gu5_common_pq {x : Plane} (hp : x ∈ edgeSegment C.X C.p) (hq : x ∈ edgeSegment C.X C.q) :
    x ∈ interior π.U := by
  rw [gu5_common_point C.hpq hp hq]; exact gu5_xpq_mem π

theorem gu5_edge_ne_zero (i : ZMod k) : edge C.X i ≠ 0 :=
  (Shadow.single C.comp).edge_ne_zero C.gen ⟨0, i⟩

theorem gu5_edge₀_ne_zero (j : ZMod (k + 3)) : edge π.X₀ j ≠ 0 :=
  (Shadow.single ⟨k + 3, π.hk₃, π.X₀⟩).edge_ne_zero π.X₀_generic ⟨0, j⟩

theorem gu5_edge₁_ne_zero (j : ZMod (k + 3)) : edge π.X₁ j ≠ 0 :=
  (Shadow.single ⟨k + 3, π.hk₃, π.X₁⟩).edge_ne_zero π.X₁_generic ⟨0, j⟩

/-! #### Entry and exit parameters of an affine line through a closed convex set -/

/-- The parameter interval of `p` (edge `p'` of both sides) inside `U`. -/
theorem gu5_exists_p : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
    (∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint C.X C.p θ ∈ π.U ↔ a ≤ θ ∧ θ ≤ b)) ∧
    (∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint C.X C.p θ ∈ interior π.U ↔ a < θ ∧ θ < b)) := by
  obtain ⟨h0, h1, hx⟩ := crossingParameter_spec (xPair C.hpq) C.p (mem_pair_left _ _)
  exact gu5_both C.X C.p (gu5_U_convex π) (gu5_U_closed π) (π.disc_clear_vertex _)
    (π.disc_clear_vertex _) h0 h1 (by rw [← hx]; exact gu5_xpq_mem π)

theorem gu5_exists_q : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
    (∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint C.X C.q θ ∈ π.U ↔ a ≤ θ ∧ θ ≤ b)) ∧
    (∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint C.X C.q θ ∈ interior π.U ↔ a < θ ∧ θ < b)) := by
  obtain ⟨h0, h1, hx⟩ := crossingParameter_spec (xPair C.hpq) C.q (mem_pair_right _ _)
  exact gu5_both C.X C.q (gu5_U_convex π) (gu5_U_closed π) (π.disc_clear_vertex _)
    (π.disc_clear_vertex _) h0 h1 (by rw [← hx]; exact gu5_xpq_mem π)

/-- The entry parameter on the first piece `mA = [X m, p_in]` of `m`. -/
theorem gu5_exists_A : ∃ a : ℝ, 0 < a ∧ a < 1 ∧
    (∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint π.X₀ π.mA θ ∈ π.U ↔ a ≤ θ)) ∧
    (∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint π.X₀ π.mA θ ∈ interior π.U ↔ a < θ)) := by
  have h0 : π.X₀ π.mA + (0 : ℝ) • edge π.X₀ π.mA ∉ π.U := by
    rw [zero_smul, add_zero, gu5_X₀_mA]; exact π.disc_clear_vertex _
  have h1 : π.X₀ π.mA + (1 : ℝ) • edge π.X₀ π.mA ∈ interior π.U := by
    rw [one_smul, edge, add_sub_cancel, gu5_mA_add_one]
    exact gu5_Θ_sub π (gu5_mB_mem_Θ π)
  obtain ⟨a, ha0, ha1, hU, hI⟩ := gu5_entry (gu5_U_convex π) (gu5_U_closed π) _ _ zero_lt_one h0 h1
  exact ⟨a, ha0, ha1, hU, hI⟩

/-- The exit parameter on the last piece `mD = [p_out, X (m+1)]` of `m`. -/
theorem gu5_exists_D : ∃ b : ℝ, 0 < b ∧ b < 1 ∧
    (∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint π.X₀ π.mD θ ∈ π.U ↔ θ ≤ b)) ∧
    (∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint π.X₀ π.mD θ ∈ interior π.U ↔ θ < b)) := by
  have h0 : π.X₀ π.mD + (0 : ℝ) • edge π.X₀ π.mD ∈ interior π.U := by
    rw [zero_smul, add_zero]; exact gu5_Θ_sub π (gu5_mD_mem_Θ π)
  have h1 : π.X₀ π.mD + (1 : ℝ) • edge π.X₀ π.mD ∉ π.U := by
    rw [one_smul, edge, add_sub_cancel, gu5_X₀_mD_succ]; exact π.disc_clear_vertex _
  obtain ⟨b, hb0, hb1, hU, hI⟩ := gu5_exit (gu5_U_convex π) (gu5_U_closed π) _ _ zero_lt_one h0 h1
  exact ⟨b, hb0, hb1, hU, hI⟩

/-! #### The two sides `X₀`, `X₁` share everything the clean/arc/match proofs use -/

/-- What the clean/arc/match proofs use about a side `Y ∈ {X₀, X₁}`: unmoved edges agree with `X₀`,
and the two edges at the moved vertex lie in the open disc. -/
structure gu5_Side (π : G11_ParamsSw C) (Y : LabelledTuple (k + 3)) : Prop where
  eq : ∀ j : ZMod (k + 3), j ≠ π.mB → j ≠ π.mC → ∀ θ : ℝ, edgePoint Y j θ = edgePoint π.X₀ j θ
  segB : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → edgePoint Y π.mB θ ∈ interior π.U
  segC : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → edgePoint Y π.mC θ ∈ interior π.U

theorem gu5_side₀ : gu5_Side π π.X₀ :=
  ⟨fun _ _ _ _ => rfl, fun _ h0 h1 => gu5_segB₀ π h0 h1, fun _ h0 h1 => gu5_segC₀ π h0 h1⟩

theorem gu5_side₁ : gu5_Side π π.X₁ :=
  ⟨fun _ hB hC θ => gu5_edgePoint_X₁ π hB hC θ, fun _ h0 h1 => gu5_segB₁ π h0 h1,
    fun _ h0 h1 => gu5_segC₁ π h0 h1⟩

section
variable {π}

theorem gu5_Side.mem_label {Y : LabelledTuple (k + 3)} (hS : gu5_Side π Y) {j : ZMod (k + 3)} {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hU : edgePoint Y j θ ∈ π.U) :
    j = π.mA ∨ j = π.mB ∨ j = π.mC ∨ j = π.mD ∨ j = π.p' ∨ j = π.q' := by
  by_cases hB : j = π.mB
  · exact Or.inr (Or.inl hB)
  by_cases hC : j = π.mC
  · exact Or.inr (Or.inr (Or.inl hC))
  rw [hS.eq j hB hC] at hU
  rcases gu5_label_cases π j with h | h | h | h | ⟨i, hi, rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · by_cases hp : i = C.p
    · subst hp; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    by_cases hq : i = C.q
    · subst hq; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    exfalso
    exact π.disc_clear_edge i hi hp hq _ (by rw [← gu5_edgeSegment_lab π hi]; exact ⟨θ, h0, h1, rfl⟩) hU

theorem gu5_Side.frontier_label {Y : LabelledTuple (k + 3)} (hS : gu5_Side π Y) {j : ZMod (k + 3)}
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hU : edgePoint Y j θ ∈ π.U)
    (hI : edgePoint Y j θ ∉ interior π.U) : j = π.mA ∨ j = π.mD ∨ j = π.p' ∨ j = π.q' := by
  rcases hS.mem_label h0 h1 hU with h | h | h | h | h | h
  · exact Or.inl h
  · subst h; exact absurd (hS.segB θ h0 h1) hI
  · subst h; exact absurd (hS.segC θ h0 h1) hI
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem gu5_Side.eval_mA {Y : LabelledTuple (k + 3)} (hS : gu5_Side π Y) (θ : ℝ) :
    edgePoint Y π.mA θ = edgePoint C.X C.m (θ * π.t₁) := by
  rw [hS.eq _ (gu5_mA_ne_mB π) (gu5_mA_ne_mC π), gu5_edgePoint_mA]

theorem gu5_Side.eval_mD {Y : LabelledTuple (k + 3)} (hS : gu5_Side π Y) (θ : ℝ) :
    edgePoint Y π.mD θ = edgePoint C.X C.m (π.t₃ + θ * (1 - π.t₃)) := by
  rw [hS.eq _ (gu5_mB_ne_mD π).symm (gu5_mC_ne_mD π).symm, gu5_edgePoint_mD]

theorem gu5_Side.eval_p' {Y : LabelledTuple (k + 3)} (hS : gu5_Side π Y) (θ : ℝ) :
    edgePoint Y π.p' θ = edgePoint C.X C.p θ := by
  rw [hS.eq _ (gu5_p'_ne π).2.1 (gu5_p'_ne π).2.2.1, gu5_edgePoint_p']

theorem gu5_Side.eval_q' {Y : LabelledTuple (k + 3)} (hS : gu5_Side π Y) (θ : ℝ) :
    edgePoint Y π.q' θ = edgePoint C.X C.q θ := by
  rw [hS.eq _ (gu5_q'_ne π).2.1 (gu5_q'_ne π).2.2.1, gu5_edgePoint_q']

theorem gu5_Side.mA_mem_m {Y : LabelledTuple (k + 3)} (hS : gu5_Side π Y) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) : edgePoint Y π.mA θ ∈ edgeSegment C.X C.m := by
  rw [hS.eval_mA]
  have := π.ht₁; have := π.ht₃; have := gu5_t₁_lt_t₃ π
  exact ⟨θ * π.t₁, mul_nonneg h0 π.ht₁.le, by nlinarith, rfl⟩

theorem gu5_Side.mD_mem_m {Y : LabelledTuple (k + 3)} (hS : gu5_Side π Y) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) : edgePoint Y π.mD θ ∈ edgeSegment C.X C.m := by
  rw [hS.eval_mD]
  have := π.ht₁; have := π.ht₃; have := gu5_t₁_lt_t₃ π
  exact ⟨π.t₃ + θ * (1 - π.t₃), by nlinarith, by nlinarith, rfl⟩

theorem gu5_Side.p'_mem_p {Y : LabelledTuple (k + 3)} (hS : gu5_Side π Y) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) : edgePoint Y π.p' θ ∈ edgeSegment C.X C.p := by
  rw [hS.eval_p']; exact ⟨θ, h0, h1, rfl⟩

theorem gu5_Side.q'_mem_q {Y : LabelledTuple (k + 3)} (hS : gu5_Side π Y) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) : edgePoint Y π.q' θ ∈ edgeSegment C.X C.q := by
  rw [hS.eval_q']; exact ⟨θ, h0, h1, rfl⟩

end

/-- **Clean** for a side: a frontier point of the trace is traversed once (two traversal points with the
same frontier point are on the same strand with the same parameter, or on two of `m, p, q` — then their
point is a double point, which lies in the open disc), and the vertex `X m` is outside `U`. -/
theorem gu5_clean {Y : LabelledTuple (k + 3)} (hY : (Shadow.single ⟨k + 3, π.hk₃, Y⟩).Generic)
    (hS : gu5_Side π Y) : Clean π.U ((Shadow.single ⟨k + 3, π.hk₃, Y⟩).positiveDiagram hY) := by
  have hcl := gu5_U_closed π
  have hem : edge C.X C.m ≠ 0 := gu5_edge_ne_zero C.m
  have hep : edge C.X C.p ≠ 0 := gu5_edge_ne_zero C.p
  have heq' : edge C.X C.q ≠ 0 := gu5_edge_ne_zero C.q
  have mixed : ∀ (j j' : ZMod (k + 3)) (θ θ' : Set.Ico (0:ℝ) 1), (j = π.mA ∨ j = π.mD) →
      (j' = π.p' ∨ j' = π.q') → edgePoint Y j θ.val = edgePoint Y j' θ'.val →
      edgePoint Y j θ.val ∈ interior π.U := by
    rintro j j' θ θ' hj hj' heq
    have hm : edgePoint Y j θ.val ∈ edgeSegment C.X C.m := by
      rcases hj with rfl | rfl
      · exact hS.mA_mem_m θ.2.1 θ.2.2.le
      · exact hS.mD_mem_m θ.2.1 θ.2.2.le
    rcases hj' with rfl | rfl
    · exact gu5_common_mp π hm (by rw [heq]; exact hS.p'_mem_p θ'.2.1 θ'.2.2.le)
    · exact gu5_common_mq π hm (by rw [heq]; exact hS.q'_mem_q θ'.2.1 θ'.2.2.le)
  refine ⟨?_, ?_⟩
  · rintro ⟨i, j, θ⟩ hq ⟨i', j', θ'⟩ hq' heq
    change edgePoint Y j θ.val ∈ frontier π.U at hq
    change edgePoint Y j' θ'.val ∈ frontier π.U at hq'
    change edgePoint Y j θ.val = edgePoint Y j' θ'.val at heq
    rw [hcl.frontier_eq] at hq hq'
    have hL := hS.frontier_label θ.2.1 θ.2.2.le hq.1 hq.2
    have hL' := hS.frontier_label θ'.2.1 θ'.2.2.le hq'.1 hq'.2
    suffices h : j = j' ∧ θ.val = θ'.val by
      exact gu5_pt_ext (Prod.ext h.1 (Subtype.ext h.2))
    have hjm : (j = π.mA ∨ j = π.mD) ∨ (j = π.p' ∨ j = π.q') := by
      rcases hL with h | h | h | h
      exacts [Or.inl (Or.inl h), Or.inl (Or.inr h), Or.inr (Or.inl h), Or.inr (Or.inr h)]
    have hjm' : (j' = π.mA ∨ j' = π.mD) ∨ (j' = π.p' ∨ j' = π.q') := by
      rcases hL' with h | h | h | h
      exacts [Or.inl (Or.inl h), Or.inl (Or.inr h), Or.inr (Or.inl h), Or.inr (Or.inr h)]
    have ht₁ := π.ht₁; have ht₃ := π.ht₃; have h13 := gu5_t₁_lt_t₃ π
    rcases hjm with hj | hj <;> rcases hjm' with hj' | hj'
    · rcases hj with rfl | rfl <;> rcases hj' with rfl | rfl
      · refine ⟨rfl, ?_⟩
        rw [hS.eval_mA, hS.eval_mA] at heq
        exact mul_right_cancel₀ ht₁.ne' (edgePoint_injective hem heq)
      · exfalso
        rw [hS.eval_mA, hS.eval_mD] at heq
        have h := edgePoint_injective hem heq
        have h1 : θ.val * π.t₁ ≤ π.t₁ := mul_le_of_le_one_left ht₁.le θ.2.2.le
        have h2 : 0 ≤ θ'.val * (1 - π.t₃) := mul_nonneg θ'.2.1 (by linarith)
        linarith
      · exfalso
        rw [hS.eval_mD, hS.eval_mA] at heq
        have h := edgePoint_injective hem heq
        have h1 : θ'.val * π.t₁ ≤ π.t₁ := mul_le_of_le_one_left ht₁.le θ'.2.2.le
        have h2 : 0 ≤ θ.val * (1 - π.t₃) := mul_nonneg θ.2.1 (by linarith)
        linarith
      · refine ⟨rfl, ?_⟩
        rw [hS.eval_mD, hS.eval_mD] at heq
        have h := edgePoint_injective hem heq
        exact mul_right_cancel₀ (sub_pos.mpr ht₃).ne' (add_left_cancel h)
    · exact absurd (mixed j j' θ θ' hj hj' heq) hq.2
    · rw [heq] at hq
      exact absurd (mixed j' j θ' θ hj' hj heq.symm) hq.2
    · rcases hj with rfl | rfl <;> rcases hj' with rfl | rfl
      · refine ⟨rfl, ?_⟩
        rw [hS.eval_p', hS.eval_p'] at heq
        exact edgePoint_injective hep heq
      · exact absurd (gu5_common_pq π (hS.p'_mem_p θ.2.1 θ.2.2.le)
          (by rw [heq]; exact hS.q'_mem_q θ'.2.1 θ'.2.2.le)) hq.2
      · exact absurd (gu5_common_pq π (by rw [heq]; exact hS.p'_mem_p θ'.2.1 θ'.2.2.le)
          (hS.q'_mem_q θ.2.1 θ.2.2.le)) hq.2
      · refine ⟨rfl, ?_⟩
        rw [hS.eval_q', hS.eval_q'] at heq
        exact edgePoint_injective heq' heq
  · intro i
    refine ⟨(π.mA, ⟨0, le_rfl, zero_lt_one⟩), ?_⟩
    change edgePoint Y π.mA 0 ∉ π.U
    rw [hS.eq _ (gu5_mA_ne_mB π) (gu5_mA_ne_mC π), edgePoint_zero, gu5_X₀_mA]
    exact π.disc_clear_vertex _

/-- Traversal betweenness from a point of `mA` to a point of `mD` (no wrap: the four pieces of `m` are
consecutive labels `m, m+1, m+2, m+3 < k+3`). -/
theorem gu5_between_m (θA θD : Set.Ico (0:ℝ) 1) (r : TraversalPoint (k + 3)) :
    traversalBetween (π.mA, θA) r (π.mD, θD) ↔
      (r.1 = π.mA ∧ θA.val < r.2.val) ∨ r.1 = π.mB ∨ r.1 = π.mC ∨ (r.1 = π.mD ∧ r.2.val < θD.val) := by
  obtain ⟨b, θ⟩ := r
  have hA := gu5_mA_val π; have hB := gu5_mB_val π; have hC := gu5_mC_val π; have hD := gu5_mD_val π
  have hθA := θA.2.1; have hθA' := θA.2.2; have hθD := θD.2.1; have hθD' := θD.2.2
  have hθ := θ.2.1; have hθ' := θ.2.2
  simp only [traversalBetween, traversalKey, hA, hD]
  push_cast
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have h3 : C.m.val < b.val + 1 := by
        have : (C.m.val : ℝ) < b.val + 1 := by linarith
        exact_mod_cast this
      have h4 : b.val < C.m.val + 4 := by
        have : (b.val : ℝ) < C.m.val + 4 := by linarith
        exact_mod_cast this
      rcases (by omega : b.val = C.m.val ∨ b.val = C.m.val + 1 ∨ b.val = C.m.val + 2 ∨
          b.val = C.m.val + 3) with hb | hb | hb | hb
      · refine Or.inl ⟨ZMod.val_injective _ (hb.trans hA.symm), ?_⟩
        rw [hb] at h1; linarith
      · exact Or.inr (Or.inl (ZMod.val_injective _ (hb.trans hB.symm)))
      · exact Or.inr (Or.inr (Or.inl (ZMod.val_injective _ (hb.trans hC.symm))))
      · refine Or.inr (Or.inr (Or.inr ⟨ZMod.val_injective _ (hb.trans hD.symm), ?_⟩))
        rw [hb] at h2; push_cast at h2; linarith
    · exfalso; linarith
    · exfalso; linarith
  · rintro (⟨hb, h3⟩ | hb | hb | ⟨hb, h3⟩)
    · rw [hb, hA]; exact Or.inl ⟨by linarith, by linarith⟩
    · rw [hb, hB]; push_cast; exact Or.inl ⟨by linarith, by linarith⟩
    · rw [hb, hC]; push_cast; exact Or.inl ⟨by linarith, by linarith⟩
    · rw [hb, hD]; push_cast; exact Or.inl ⟨by linarith, by linarith⟩

/-! #### The move match: the identity on traversal points -/

theorem gu5_not_mem_U_label (j : ZMod (k + 3)) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (h : edgePoint π.X₀ j θ ∉ π.U) : j ≠ π.mB ∧ j ≠ π.mC :=
  ⟨fun e => h (by rw [e]; exact interior_subset (gu5_segB₀ π h0 h1)),
    fun e => h (by rw [e]; exact interior_subset (gu5_segC₀ π h0 h1))⟩

theorem gu5_outside_iff (p : π.M₀.Γ.Pt) :
    π.M₀.Γ.eval p ∉ interior π.U ↔ π.M₁.Γ.eval (p : π.M₁.Γ.Pt) ∉ interior π.U := by
  obtain ⟨i, j, θ⟩ := p
  change edgePoint π.X₀ j θ.val ∉ interior π.U ↔ edgePoint π.X₁ j θ.val ∉ interior π.U
  by_cases hB : j = π.mB
  · rw [hB]
    simp only [gu5_segB₀ π θ.2.1 θ.2.2.le, gu5_segB₁ π θ.2.1 θ.2.2.le, not_true_eq_false]
  by_cases hC : j = π.mC
  · rw [hC]
    simp only [gu5_segC₀ π θ.2.1 θ.2.2.le, gu5_segC₁ π θ.2.1 θ.2.2.le, not_true_eq_false]
  rw [gu5_edgePoint_X₁ π hB hC]

theorem gu5_eval₁_eq (p : π.M₀.Γ.Pt) (h : π.M₀.Γ.eval p ∉ interior π.U) :
    π.M₁.Γ.eval (p : π.M₁.Γ.Pt) = π.M₀.Γ.eval p := by
  obtain ⟨i, j, θ⟩ := p
  change edgePoint π.X₀ j θ.val ∉ interior π.U at h
  change edgePoint π.X₁ j θ.val = edgePoint π.X₀ j θ.val
  have hB : j ≠ π.mB := fun e => h (by rw [e]; exact gu5_segB₀ π θ.2.1 θ.2.2.le)
  have hC : j ≠ π.mC := fun e => h (by rw [e]; exact gu5_segC₀ π θ.2.1 θ.2.2.le)
  exact gu5_edgePoint_X₁ π hB hC _

/-- the outside correspondence: the identity on traversal points -/
def gu5_φ : π.M₀.Γ.Outside π.U ≃ π.M₁.Γ.Outside π.U :=
  Equiv.subtypeEquiv (Equiv.refl _) (fun p => gu5_outside_iff π p)

theorem gu5_φ_val (p : π.M₀.Γ.Outside π.U) : (gu5_φ π p).1 = (p.1 : π.M₁.Γ.Pt) := rfl

theorem gu5_isCrossing_iff (s : Finset π.M₀.Γ.Strand) (hB : (⟨(0 : Fin 1), π.mB⟩ : π.M₀.Γ.Strand) ∉ s)
    (hC : (⟨(0 : Fin 1), π.mC⟩ : π.M₀.Γ.Strand) ∉ s) :
    π.M₀.Γ.IsCrossing s ↔ π.M₁.Γ.IsCrossing (s : Finset π.M₁.Γ.Strand) := by
  have hseg : ∀ t : π.M₀.Γ.Strand, t ∈ s → π.M₁.Γ.seg (t : π.M₁.Γ.Strand) = π.M₀.Γ.seg t := by
    rintro ⟨i, j⟩ ht
    obtain rfl : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) i (0 : Fin 1)
    change edgeSegment π.X₁ j = edgeSegment π.X₀ j
    exact gu5_edgeSegment_X₁ π (fun e => hB (e ▸ ht)) (fun e => hC (e ▸ ht))
  constructor
  · rintro ⟨a, b, rfl, hna, hmeet⟩
    refine ⟨a, b, rfl, hna, ?_⟩
    rw [hseg a (Finset.mem_insert_self _ _), hseg b (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))]
    exact hmeet
  · rintro ⟨a, b, rfl, hna, hmeet⟩
    refine ⟨a, b, rfl, hna, ?_⟩
    rw [hseg a (Finset.mem_insert_self _ _), hseg b (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))] at hmeet
    exact hmeet

theorem gu5_outer_not_mem₀ (y : π.M₀.Γ.Crossing) (hy : π.M₀.Γ.crossingPoint y ∉ interior π.U) :
    (⟨(0 : Fin 1), π.mB⟩ : π.M₀.Γ.Strand) ∉ y.val ∧ (⟨(0 : Fin 1), π.mC⟩ : π.M₀.Γ.Strand) ∉ y.val := by
  constructor
  · intro h
    obtain ⟨θ, h0, h1, hθ⟩ := π.M₀.Γ.crossingPoint_mem y h
    exact hy (by rw [hθ]; exact gu5_segB₀ π h0 h1)
  · intro h
    obtain ⟨θ, h0, h1, hθ⟩ := π.M₀.Γ.crossingPoint_mem y h
    exact hy (by rw [hθ]; exact gu5_segC₀ π h0 h1)

theorem gu5_outer_not_mem₁ (y : π.M₁.Γ.Crossing) (hy : π.M₁.Γ.crossingPoint y ∉ interior π.U) :
    (⟨(0 : Fin 1), π.mB⟩ : π.M₁.Γ.Strand) ∉ y.val ∧ (⟨(0 : Fin 1), π.mC⟩ : π.M₁.Γ.Strand) ∉ y.val := by
  constructor
  · intro h
    obtain ⟨θ, h0, h1, hθ⟩ := π.M₁.Γ.crossingPoint_mem y h
    exact hy (by rw [hθ]; exact gu5_segB₁ π h0 h1)
  · intro h
    obtain ⟨θ, h0, h1, hθ⟩ := π.M₁.Γ.crossingPoint_mem y h
    exact hy (by rw [hθ]; exact gu5_segC₁ π h0 h1)

theorem gu5_dir_eq {y₀ : π.M₀.Γ.Crossing} (hB : (⟨(0 : Fin 1), π.mB⟩ : π.M₀.Γ.Strand) ∉ y₀.val)
    (hC : (⟨(0 : Fin 1), π.mC⟩ : π.M₀.Γ.Strand) ∉ y₀.val) (s : π.M₀.Γ.Strand) (hs : s ∈ y₀.val) :
    π.M₁.Γ.dir (s : π.M₁.Γ.Strand) = π.M₀.Γ.dir s := by
  obtain ⟨i, j⟩ := s
  obtain rfl : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) i (0 : Fin 1)
  change edge π.X₁ j = edge π.X₀ j
  exact gu5_edge_X₁ π (fun e => hB (e ▸ hs)) (fun e => hC (e ▸ hs))

theorem gu5_crossingPoint_eq (y₀ : π.M₀.Γ.Crossing) (y₁ : π.M₁.Γ.Crossing)
    (hval : y₁.val = (y₀.val : Finset π.M₁.Γ.Strand)) (hB : (⟨(0 : Fin 1), π.mB⟩ : π.M₀.Γ.Strand) ∉ y₀.val)
    (hC : (⟨(0 : Fin 1), π.mC⟩ : π.M₀.Γ.Strand) ∉ y₀.val) :
    π.M₁.Γ.crossingPoint y₁ = π.M₀.Γ.crossingPoint y₀ := by
  symm
  apply π.X₁_generic.common_point_unique y₁
  intro s hs
  rw [hval] at hs
  obtain ⟨i, j⟩ := s
  obtain rfl : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) i (0 : Fin 1)
  change π.M₀.Γ.crossingPoint y₀ ∈ edgeSegment π.X₁ j
  rw [gu5_edgeSegment_X₁ π (fun e => hB (e ▸ hs)) (fun e => hC (e ▸ hs))]
  exact π.M₀.Γ.crossingPoint_mem y₀ hs

theorem gu5_overStrand_eq (y₀ : π.M₀.Γ.Crossing) (y₁ : π.M₁.Γ.Crossing)
    (hval : y₁.val = (y₀.val : Finset π.M₁.Γ.Strand)) (hB : (⟨(0 : Fin 1), π.mB⟩ : π.M₀.Γ.Strand) ∉ y₀.val)
    (hC : (⟨(0 : Fin 1), π.mC⟩ : π.M₀.Γ.Strand) ∉ y₀.val) :
    (π.M₁.overStrand y₁ : π.M₀.Γ.Strand) = π.M₀.overStrand y₀ := by
  have hmem₁ : (π.M₁.overStrand y₁ : π.M₀.Γ.Strand) ∈ y₀.val := by
    have := π.M₁.over_mem y₁; rwa [hval] at this
  have hmem₀ : (π.M₀.overStrand y₀ : π.M₁.Γ.Strand) ∈ y₁.val := by
    rw [hval]; exact π.M₀.over_mem y₀
  by_contra hne
  have h₀ : 0 < det (π.M₀.Γ.dir (π.M₀.overStrand y₀))
      (π.M₀.Γ.dir (π.M₀.Γ.other y₀ (π.M₀.over_mem y₀))) :=
    (Shadow.single ⟨k + 3, π.hk₃, π.X₀⟩).positiveDiagram_det_pos π.X₀_generic y₀
  have h₁ : 0 < det (π.M₁.Γ.dir (π.M₁.overStrand y₁))
      (π.M₁.Γ.dir (π.M₁.Γ.other y₁ (π.M₁.over_mem y₁))) :=
    (Shadow.single ⟨k + 3, π.hk₃, π.X₁⟩).positiveDiagram_det_pos π.X₁_generic y₁
  have e₀ : π.M₀.Γ.other y₀ (π.M₀.over_mem y₀) = π.M₁.overStrand y₁ :=
    (π.M₀.Γ.eq_other_of_mem_of_ne y₀ (π.M₀.over_mem y₀) hmem₁ hne).symm
  have e₁ : π.M₁.Γ.other y₁ (π.M₁.over_mem y₁) = π.M₀.overStrand y₀ :=
    (π.M₁.Γ.eq_other_of_mem_of_ne y₁ (π.M₁.over_mem y₁) hmem₀ (Ne.symm hne)).symm
  rw [e₀] at h₀
  rw [e₁, gu5_dir_eq π hB hC _ hmem₁, gu5_dir_eq π hB hC _ (π.M₀.over_mem y₀), det_swap] at h₁
  linarith

theorem gu5_underStrand_eq (y₀ : π.M₀.Γ.Crossing) (y₁ : π.M₁.Γ.Crossing)
    (hval : y₁.val = (y₀.val : Finset π.M₁.Γ.Strand)) (hB : (⟨(0 : Fin 1), π.mB⟩ : π.M₀.Γ.Strand) ∉ y₀.val)
    (hC : (⟨(0 : Fin 1), π.mC⟩ : π.M₀.Γ.Strand) ∉ y₀.val) :
    (π.M₁.underStrand y₁ : π.M₀.Γ.Strand) = π.M₀.underStrand y₀ := by
  have hover := gu5_overStrand_eq π y₀ y₁ hval hB hC
  have hmem : (π.M₁.underStrand y₁ : π.M₀.Γ.Strand) ∈ y₀.val := by
    have := π.M₁.under_mem y₁; rwa [hval] at this
  have hne : (π.M₁.underStrand y₁ : π.M₀.Γ.Strand) ≠ π.M₀.overStrand y₀ := by
    rw [← hover]; exact π.M₁.under_ne_over y₁
  exact π.M₀.Γ.eq_other_of_mem_of_ne y₀ (π.M₀.over_mem y₀) hmem hne

theorem gu5_crossingParam_eq (y₀ : π.M₀.Γ.Crossing) (y₁ : π.M₁.Γ.Crossing)
    (hval : y₁.val = (y₀.val : Finset π.M₁.Γ.Strand)) (hB : (⟨(0 : Fin 1), π.mB⟩ : π.M₀.Γ.Strand) ∉ y₀.val)
    (hC : (⟨(0 : Fin 1), π.mC⟩ : π.M₀.Γ.Strand) ∉ y₀.val) (s : π.M₀.Γ.Strand) (hs₀ : s ∈ y₀.val)
    (hs₁ : (s : π.M₁.Γ.Strand) ∈ y₁.val) :
    π.M₁.crossingParam y₁ hs₁ = π.M₀.crossingParam y₀ hs₀ := by
  obtain ⟨-, -, e₀⟩ := π.M₀.crossingParam_spec y₀ hs₀
  obtain ⟨-, -, e₁⟩ := π.M₁.crossingParam_spec y₁ hs₁
  rw [gu5_crossingPoint_eq π y₀ y₁ hval hB hC, e₀] at e₁
  obtain ⟨i, j⟩ := s
  obtain rfl : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) i (0 : Fin 1)
  change edgePoint π.X₀ j _ = edgePoint π.X₁ j _ at e₁
  rw [gu5_edgePoint_X₁ π (fun e => hB (e ▸ hs₀)) (fun e => hC (e ▸ hs₀))] at e₁
  exact (edgePoint_injective (gu5_edge₀_ne_zero π j) e₁).symm

/-- the outer crossings correspond by their strand pairs -/
def gu5_ψ_to (x : π.M₀.OuterCrossing π.U) : π.M₁.OuterCrossing π.U :=
  ⟨⟨x.1.val, (gu5_isCrossing_iff π x.1.val (gu5_outer_not_mem₀ π x.1 x.2).1
      (gu5_outer_not_mem₀ π x.1 x.2).2).mp x.1.2⟩,
    (congrArg (fun z : Plane => z ∉ interior π.U) (gu5_crossingPoint_eq π x.1
      ⟨x.1.val, (gu5_isCrossing_iff π x.1.val (gu5_outer_not_mem₀ π x.1 x.2).1
        (gu5_outer_not_mem₀ π x.1 x.2).2).mp x.1.2⟩ rfl (gu5_outer_not_mem₀ π x.1 x.2).1
      (gu5_outer_not_mem₀ π x.1 x.2).2)).mpr x.2⟩

def gu5_ψ_inv (y : π.M₁.OuterCrossing π.U) : π.M₀.OuterCrossing π.U :=
  ⟨⟨y.1.val, (gu5_isCrossing_iff π y.1.val (gu5_outer_not_mem₁ π y.1 y.2).1
      (gu5_outer_not_mem₁ π y.1 y.2).2).mpr y.1.2⟩,
    (congrArg (fun z : Plane => z ∉ interior π.U) (gu5_crossingPoint_eq π
      ⟨y.1.val, (gu5_isCrossing_iff π y.1.val (gu5_outer_not_mem₁ π y.1 y.2).1
        (gu5_outer_not_mem₁ π y.1 y.2).2).mpr y.1.2⟩ y.1 rfl (gu5_outer_not_mem₁ π y.1 y.2).1
      (gu5_outer_not_mem₁ π y.1 y.2).2)).mp y.2⟩

def gu5_ψ : π.M₀.OuterCrossing π.U ≃ π.M₁.OuterCrossing π.U where
  toFun := gu5_ψ_to π
  invFun := gu5_ψ_inv π
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext (Subtype.ext rfl)

theorem gu5_ψ_val (x : π.M₀.OuterCrossing π.U) : (gu5_ψ π x).1.val = (x.1.val : Finset π.M₁.Γ.Strand) :=
  rfl

theorem gu5_over_eq (x : π.M₀.OuterCrossing π.U) :
    gu5_φ π (π.M₀.outerOverPt x) = π.M₁.outerOverPt (gu5_ψ π x) := by
  apply Subtype.ext
  have hB := (gu5_outer_not_mem₀ π x.1 x.2).1
  have hC := (gu5_outer_not_mem₀ π x.1 x.2).2
  have hover : (π.M₁.overStrand (gu5_ψ π x).1 : π.M₀.Γ.Strand) = π.M₀.overStrand x.1 :=
    gu5_overStrand_eq π x.1 (gu5_ψ π x).1 rfl hB hC
  have h' : (π.M₀.overStrand x.1 : π.M₁.Γ.Strand) ∈ (gu5_ψ π x).1.val := π.M₀.over_mem x.1
  change π.M₀.visitPt (π.M₀.overVisit x.1) = π.M₁.visitPt (π.M₁.overVisit (gu5_ψ π x).1)
  refine (Shadow.mk_eq_mk_iff (π.M₀.overStrand x.1)
    (π.M₁.overStrand (gu5_ψ π x).1 : π.M₀.Γ.Strand) _ _).mpr ⟨hover.symm, Subtype.ext ?_⟩
  show π.M₀.crossingParam x.1 (π.M₀.over_mem x.1) =
    π.M₁.crossingParam (gu5_ψ π x).1 (π.M₁.over_mem _)
  rw [π.M₁.crossingParam_congr rfl hover (π.M₁.over_mem _) h']
  exact (gu5_crossingParam_eq π x.1 (gu5_ψ π x).1 rfl hB hC _ (π.M₀.over_mem x.1) h').symm

theorem gu5_under_eq (x : π.M₀.OuterCrossing π.U) :
    gu5_φ π (π.M₀.outerUnderPt x) = π.M₁.outerUnderPt (gu5_ψ π x) := by
  apply Subtype.ext
  have hB := (gu5_outer_not_mem₀ π x.1 x.2).1
  have hC := (gu5_outer_not_mem₀ π x.1 x.2).2
  have hunder : (π.M₁.underStrand (gu5_ψ π x).1 : π.M₀.Γ.Strand) = π.M₀.underStrand x.1 :=
    gu5_underStrand_eq π x.1 (gu5_ψ π x).1 rfl hB hC
  have h' : (π.M₀.underStrand x.1 : π.M₁.Γ.Strand) ∈ (gu5_ψ π x).1.val := π.M₀.under_mem x.1
  change π.M₀.visitPt (π.M₀.underVisit x.1) = π.M₁.visitPt (π.M₁.underVisit (gu5_ψ π x).1)
  refine (Shadow.mk_eq_mk_iff (π.M₀.underStrand x.1)
    (π.M₁.underStrand (gu5_ψ π x).1 : π.M₀.Γ.Strand) _ _).mpr ⟨hunder.symm, Subtype.ext ?_⟩
  show π.M₀.crossingParam x.1 (π.M₀.under_mem x.1) =
    π.M₁.crossingParam (gu5_ψ π x).1 (π.M₁.under_mem _)
  rw [π.M₁.crossingParam_congr rfl hunder (π.M₁.under_mem _) h']
  exact (gu5_crossingParam_eq π x.1 (gu5_ψ π x).1 rfl hB hC _ (π.M₀.under_mem x.1) h').symm

theorem gu5_dir_pos (p : π.M₀.Γ.Outside π.U) (hp : π.M₀.Γ.eval p.1 ∉ π.U) : ∃ l : ℝ, 0 < l ∧
    π.M₁.Γ.dir (π.M₁.Γ.strandOf (gu5_φ π p).1) = l • π.M₀.Γ.dir (π.M₀.Γ.strandOf p.1) := by
  refine ⟨1, one_pos, ?_⟩
  rw [one_smul, gu5_φ_val]
  obtain ⟨⟨i, j, θ⟩, hout⟩ := p
  change edgePoint π.X₀ j θ.val ∉ π.U at hp
  obtain ⟨hB, hC⟩ := gu5_not_mem_U_label π j θ.2.1 θ.2.2.le hp
  change edge π.X₁ j = edge π.X₀ j
  exact gu5_edge_X₁ π hB hC

theorem gu5_dir_eq_of_ne (s : π.M₀.Γ.Strand) (hB : s.2 ≠ π.mB) (hC : s.2 ≠ π.mC) :
    π.M₁.Γ.dir (s : π.M₁.Γ.Strand) = π.M₀.Γ.dir s := by
  obtain ⟨i, j⟩ := s
  change edge π.X₁ j = edge π.X₀ j
  exact gu5_edge_X₁ π hB hC

theorem gu5_dir_pos_before (p : π.M₀.Γ.Outside π.U) (hp : π.M₀.Γ.eval p.1 ∉ π.U) : ∃ l : ℝ, 0 < l ∧
    π.M₁.Γ.dir (π.M₁.Γ.strandBefore (gu5_φ π p).1) = l • π.M₀.Γ.dir (π.M₀.Γ.strandBefore p.1) := by
  refine ⟨1, one_pos, ?_⟩
  rw [one_smul, gu5_φ_val]
  obtain ⟨⟨i, j, θ⟩, hout⟩ := p
  change edgePoint π.X₀ j θ.val ∉ π.U at hp
  obtain ⟨hB, hC⟩ := gu5_not_mem_U_label π j θ.2.1 θ.2.2.le hp
  show π.M₁.Γ.dir (π.M₁.Γ.strandBefore ⟨i, (j, θ)⟩) = π.M₀.Γ.dir (π.M₀.Γ.strandBefore ⟨i, (j, θ)⟩)
  by_cases hθ : θ.val = 0
  · rw [π.M₁.Γ.strandBefore_of_zero ⟨i, (j, θ)⟩ hθ, π.M₀.Γ.strandBefore_of_zero ⟨i, (j, θ)⟩ hθ]
    have hD : j ≠ π.mD := by
      intro e
      apply hp
      rw [e, hθ, edgePoint_zero]
      exact interior_subset (gu5_Θ_sub π (gu5_mD_mem_Θ π))
    have hB' : (⟨i, j - 1⟩ : π.M₀.Γ.Strand).2 ≠ π.mB := by
      intro e
      change j - 1 = π.mB at e
      apply hC
      rw [← gu5_mB_add_one, ← e]
      exact (sub_add_cancel j 1).symm
    have hC' : (⟨i, j - 1⟩ : π.M₀.Γ.Strand).2 ≠ π.mC := by
      intro e
      change j - 1 = π.mC at e
      apply hD
      rw [← gu5_mC_add_one, ← e]
      exact (sub_add_cancel j 1).symm
    exact gu5_dir_eq_of_ne π ⟨i, j - 1⟩ hB' hC'
  · rw [π.M₁.Γ.strandBefore_of_ne_zero ⟨i, (j, θ)⟩ hθ, π.M₀.Γ.strandBefore_of_ne_zero ⟨i, (j, θ)⟩ hθ]
    exact gu5_dir_eq_of_ne π ⟨i, j⟩ hB hC

/-- **The move match `M₀ → M₁`.** -/
def gu5_moveMatch : MoveMatch π.U π.M₀ π.M₁ where
  φ := gu5_φ π
  eval_eq := fun p => gu5_eval₁_eq π p.1 p.2
  dir_pos := gu5_dir_pos π
  dir_pos_before := gu5_dir_pos_before π
  ψ := gu5_ψ π
  over_eq := gu5_over_eq π
  under_eq := gu5_under_eq π
  e := Equiv.refl _
  comp_eq := fun _ => rfl

/-! #### The arcs inside `U` -/

/-- the parameters of the three arcs (entry/exit parameters on `p`, on `q`, on `mA`/`mD`) with their
characterizations; common to both sides since the strands `p', q', mA, mD` are unmoved -/
structure gu5_ArcParams (π : G11_ParamsSw C) where
  ap : ℝ
  bp : ℝ
  aq : ℝ
  bq : ℝ
  aA : ℝ
  bD : ℝ
  hp0 : 0 < ap
  hp : ap < bp
  hp1 : bp < 1
  hq0 : 0 < aq
  hq : aq < bq
  hq1 : bq < 1
  hA0 : 0 < aA
  hA1 : aA < 1
  hD0 : 0 < bD
  hD1 : bD < 1
  Up : ∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint C.X C.p θ ∈ π.U ↔ ap ≤ θ ∧ θ ≤ bp)
  Ip : ∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint C.X C.p θ ∈ interior π.U ↔ ap < θ ∧ θ < bp)
  Uq : ∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint C.X C.q θ ∈ π.U ↔ aq ≤ θ ∧ θ ≤ bq)
  Iq : ∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint C.X C.q θ ∈ interior π.U ↔ aq < θ ∧ θ < bq)
  UA : ∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint π.X₀ π.mA θ ∈ π.U ↔ aA ≤ θ)
  IA : ∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint π.X₀ π.mA θ ∈ interior π.U ↔ aA < θ)
  UD : ∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint π.X₀ π.mD θ ∈ π.U ↔ θ ≤ bD)
  ID : ∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint π.X₀ π.mD θ ∈ interior π.U ↔ θ < bD)

theorem gu5_exists_arcParams : Nonempty (gu5_ArcParams π) := by
  obtain ⟨ap, bp, hp0, hp, hp1, Up, Ip⟩ := gu5_exists_p π
  obtain ⟨aq, bq, hq0, hq, hq1, Uq, Iq⟩ := gu5_exists_q π
  obtain ⟨aA, hA0, hA1, UA, IA⟩ := gu5_exists_A π
  obtain ⟨bD, hD0, hD1, UD, ID⟩ := gu5_exists_D π
  exact ⟨⟨ap, bp, aq, bq, aA, bD, hp0, hp, hp1, hq0, hq, hq1, hA0, hA1, hD0, hD1, Up, Ip, Uq, Iq,
    UA, IA, UD, ID⟩⟩

/-- the arc of the side `Y` on the single edge `j` from parameter `a` to parameter `b` -/
def gu5_arcE (Y : LabelledTuple (k + 3)) (j : ZMod (k + 3)) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < 1) : (Shadow.single ⟨k + 3, π.hk₃, Y⟩).Arc :=
  ⟨(0 : Fin 1), (j, ⟨a, ha, hab.trans hb⟩), (j, ⟨b, ha.trans hab.le, hb⟩)⟩

/-- the `m`-arc of the side `Y`: from parameter `aA` on `mA` to parameter `bD` on `mD` -/
def gu5_arcM (Y : LabelledTuple (k + 3)) {aA bD : ℝ} (h0A : 0 ≤ aA) (h1A : aA < 1) (h0D : 0 ≤ bD)
    (h1D : bD < 1) : (Shadow.single ⟨k + 3, π.hk₃, Y⟩).Arc :=
  ⟨(0 : Fin 1), (π.mA, ⟨aA, h0A, h1A⟩), (π.mD, ⟨bD, h0D, h1D⟩)⟩

theorem gu5_strand_eq_iff {Y : LabelledTuple (k + 3)} (i : Fin 1) (j j' : ZMod (k + 3)) :
    ((⟨i, j'⟩ : (Shadow.single ⟨k + 3, π.hk₃, Y⟩).Strand) = ⟨(0 : Fin 1), j⟩) ↔ j' = j := by
  constructor
  · intro h; exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  · intro h; exact Sigma.ext (Subsingleton.elim (α := Fin 1) _ _) (heq_of_eq h)

theorem gu5_pt_eq_iff {Y : LabelledTuple (k + 3)} (i i' : Fin 1) (j j' : ZMod (k + 3))
    (θ θ' : Set.Ico (0:ℝ) 1) :
    ((⟨i, (j, θ)⟩ : (Shadow.single ⟨k + 3, π.hk₃, Y⟩).Pt) = ⟨i', (j', θ')⟩) ↔
      j = j' ∧ θ.val = θ'.val := by
  constructor
  · intro h
    have h2 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [Prod.mk.injEq] at h2
    exact ⟨h2.1, by rw [h2.2]⟩
  · rintro ⟨rfl, h⟩
    exact Sigma.ext (Subsingleton.elim (α := Fin 1) _ _) (heq_of_eq (by rw [Subtype.ext h]))

theorem gu5_arcE_inner_iff {Y : LabelledTuple (k + 3)} (j : ZMod (k + 3)) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < 1) (i : Fin 1) (j' : ZMod (k + 3)) (θ : Set.Ico (0:ℝ) 1) :
    (gu5_arcE π Y j ha hab hb).Inner ⟨i, (j', θ)⟩ ↔ j' = j ∧ a < θ.val ∧ θ.val < b := by
  rw [Smoothing.arc_inner_iff_of_same_edge _ j ⟨a, ha, hab.trans hb⟩ ⟨b, ha.trans hab.le, hb⟩ rfl rfl
    hab]
  exact and_congr_left' (gu5_strand_eq_iff π i j j')

theorem gu5_arcE_mem_iff {Y : LabelledTuple (k + 3)} (j : ZMod (k + 3)) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < 1) (i : Fin 1) (j' : ZMod (k + 3)) (θ : Set.Ico (0:ℝ) 1) :
    (gu5_arcE π Y j ha hab hb).Mem ⟨i, (j', θ)⟩ ↔ j' = j ∧ a ≤ θ.val ∧ θ.val ≤ b := by
  rw [Smoothing.arc_mem_iff_of_same_edge _ j ⟨a, ha, hab.trans hb⟩ ⟨b, ha.trans hab.le, hb⟩ rfl rfl
    hab]
  exact and_congr_left' (gu5_strand_eq_iff π i j j')

theorem gu5_arcM_inner_iff {Y : LabelledTuple (k + 3)} {aA bD : ℝ} (h0A : 0 ≤ aA) (h1A : aA < 1)
    (h0D : 0 ≤ bD) (h1D : bD < 1) (i : Fin 1) (j : ZMod (k + 3)) (θ : Set.Ico (0:ℝ) 1) :
    (gu5_arcM π Y h0A h1A h0D h1D).Inner ⟨i, (j, θ)⟩ ↔
      (j = π.mA ∧ aA < θ.val) ∨ j = π.mB ∨ j = π.mC ∨ (j = π.mD ∧ θ.val < bD) := by
  constructor
  · rintro ⟨r, hr, hq⟩
    have hr' : r = (j, θ) := (eq_of_heq (Sigma.mk.inj_iff.mp hq).2).symm
    subst hr'
    exact (gu5_between_m π ⟨aA, h0A, h1A⟩ ⟨bD, h0D, h1D⟩ (j, θ)).mp hr
  · intro h
    refine ⟨(j, θ), (gu5_between_m π ⟨aA, h0A, h1A⟩ ⟨bD, h0D, h1D⟩ (j, θ)).mpr h, ?_⟩
    exact Sigma.ext (Subsingleton.elim (α := Fin 1) _ _) (heq_of_eq rfl)

theorem gu5_arcM_mem_iff {Y : LabelledTuple (k + 3)} {aA bD : ℝ} (h0A : 0 ≤ aA) (h1A : aA < 1)
    (h0D : 0 ≤ bD) (h1D : bD < 1) (i : Fin 1) (j : ZMod (k + 3)) (θ : Set.Ico (0:ℝ) 1) :
    (gu5_arcM π Y h0A h1A h0D h1D).Mem ⟨i, (j, θ)⟩ ↔
      (j = π.mA ∧ aA ≤ θ.val) ∨ j = π.mB ∨ j = π.mC ∨ (j = π.mD ∧ θ.val ≤ bD) := by
  have hs : ((⟨i, (j, θ)⟩ : (Shadow.single ⟨k + 3, π.hk₃, Y⟩).Pt) =
      (gu5_arcM π Y h0A h1A h0D h1D).startPt) ↔ j = π.mA ∧ θ.val = aA :=
    gu5_pt_eq_iff π i (0 : Fin 1) j π.mA θ ⟨aA, h0A, h1A⟩
  have ht : ((⟨i, (j, θ)⟩ : (Shadow.single ⟨k + 3, π.hk₃, Y⟩).Pt) =
      (gu5_arcM π Y h0A h1A h0D h1D).stopPt) ↔ j = π.mD ∧ θ.val = bD :=
    gu5_pt_eq_iff π i (0 : Fin 1) j π.mD θ ⟨bD, h0D, h1D⟩
  unfold Shadow.Arc.Mem
  rw [hs, ht, gu5_arcM_inner_iff]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | h | h | ⟨rfl, h⟩)
    · exact Or.inl ⟨rfl, h.ge⟩
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, h.le⟩))
    · exact Or.inl ⟨rfl, h.le⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, h.le⟩))
  · rintro (⟨rfl, h⟩ | h | h | ⟨rfl, h⟩)
    · rcases h.lt_or_eq with h | h
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
      · exact Or.inl ⟨rfl, h.symm⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · rcases h.lt_or_eq with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))))
      · exact Or.inr (Or.inl ⟨rfl, h⟩)

theorem gu5_isArc_arcE {Y : LabelledTuple (k + 3)} (j : ZMod (k + 3)) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < 1)
    (hU : ∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint Y j θ ∈ π.U ↔ a ≤ θ ∧ θ ≤ b))
    (hI : ∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint Y j θ ∈ interior π.U ↔ a < θ ∧ θ < b)) :
    (Shadow.single ⟨k + 3, π.hk₃, Y⟩).IsArc π.U (gu5_arcE π Y j ha hab hb) := by
  have hcl := gu5_U_closed π
  have ha1 : a ≤ 1 := (hab.trans hb).le
  have hb0 : 0 ≤ b := ha.trans hab.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact hab.ne (congrArg (fun r : TraversalPoint (k + 3) => r.2.val) h)
  · change edgePoint Y j a ∈ frontier π.U
    rw [hcl.frontier_eq]
    exact ⟨(hU a ha ha1).mpr ⟨le_rfl, hab.le⟩, fun h => lt_irrefl a ((hI a ha ha1).mp h).1⟩
  · change edgePoint Y j b ∈ frontier π.U
    rw [hcl.frontier_eq]
    exact ⟨(hU b hb0 hb.le).mpr ⟨hab.le, le_rfl⟩, fun h => lt_irrefl b ((hI b hb0 hb.le).mp h).2⟩
  · rintro ⟨i, j', θ⟩ hq
    rw [gu5_arcE_inner_iff] at hq
    obtain ⟨rfl, h1, h2⟩ := hq
    change edgePoint Y j' θ.val ∈ interior π.U
    exact (hI _ θ.2.1 θ.2.2.le).mpr ⟨h1, h2⟩

theorem gu5_isArc_arcM {Y : LabelledTuple (k + 3)} (hS : gu5_Side π Y) (A : gu5_ArcParams π) :
    (Shadow.single ⟨k + 3, π.hk₃, Y⟩).IsArc π.U (gu5_arcM π Y A.hA0.le A.hA1 A.hD0.le A.hD1) := by
  have hcl := gu5_U_closed π
  have hA := hS.eq π.mA (gu5_mA_ne_mB π) (gu5_mA_ne_mC π)
  have hD := hS.eq π.mD (gu5_mB_ne_mD π).symm (gu5_mC_ne_mD π).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact gu5_mA_ne_mD π (congrArg (fun r : TraversalPoint (k + 3) => r.1) h)
  · change edgePoint Y π.mA A.aA ∈ frontier π.U
    rw [hA, hcl.frontier_eq]
    exact ⟨(A.UA _ A.hA0.le A.hA1.le).mpr le_rfl, fun h => lt_irrefl _ ((A.IA _ A.hA0.le A.hA1.le).mp h)⟩
  · change edgePoint Y π.mD A.bD ∈ frontier π.U
    rw [hD, hcl.frontier_eq]
    exact ⟨(A.UD _ A.hD0.le A.hD1.le).mpr le_rfl, fun h => lt_irrefl _ ((A.ID _ A.hD0.le A.hD1.le).mp h)⟩
  · rintro ⟨i, j, θ⟩ hq
    rw [gu5_arcM_inner_iff] at hq
    change edgePoint Y j θ.val ∈ interior π.U
    rcases hq with ⟨rfl, h⟩ | rfl | rfl | ⟨rfl, h⟩
    · rw [hA]; exact (A.IA _ θ.2.1 θ.2.2.le).mpr h
    · exact hS.segB _ θ.2.1 θ.2.2.le
    · exact hS.segC _ θ.2.1 θ.2.2.le
    · rw [hD]; exact (A.ID _ θ.2.1 θ.2.2.le).mpr h

theorem gu5_isArc_arcP {Y : LabelledTuple (k + 3)} (hS : gu5_Side π Y) (A : gu5_ArcParams π) :
    (Shadow.single ⟨k + 3, π.hk₃, Y⟩).IsArc π.U (gu5_arcE π Y π.p' A.hp0.le A.hp A.hp1) :=
  gu5_isArc_arcE π π.p' A.hp0.le A.hp A.hp1
    (fun θ h0 h1 => by rw [hS.eval_p']; exact A.Up θ h0 h1)
    (fun θ h0 h1 => by rw [hS.eval_p']; exact A.Ip θ h0 h1)

theorem gu5_isArc_arcQ {Y : LabelledTuple (k + 3)} (hS : gu5_Side π Y) (A : gu5_ArcParams π) :
    (Shadow.single ⟨k + 3, π.hk₃, Y⟩).IsArc π.U (gu5_arcE π Y π.q' A.hq0.le A.hq A.hq1) :=
  gu5_isArc_arcE π π.q' A.hq0.le A.hq A.hq1
    (fun θ h0 h1 => by rw [hS.eval_q']; exact A.Uq θ h0 h1)
    (fun θ h0 h1 => by rw [hS.eval_q']; exact A.Iq θ h0 h1)

/-- **The arc cover** of a side: the three arcs on `p'`, `q'` and across the four pieces of `m`. -/
theorem gu5_arcCover {Y : LabelledTuple (k + 3)} (hS : gu5_Side π Y) (A : gu5_ArcParams π) :
    (Shadow.single ⟨k + 3, π.hk₃, Y⟩).ArcCover π.U
      {gu5_arcE π Y π.p' A.hp0.le A.hp A.hp1, gu5_arcE π Y π.q' A.hq0.le A.hq A.hq1,
        gu5_arcM π Y A.hA0.le A.hA1 A.hD0.le A.hD1} := by
  have hcl := gu5_U_closed π
  have hP := gu5_isArc_arcP π hS A
  have hQ := gu5_isArc_arcQ π hS A
  have hM := gu5_isArc_arcM π hS A
  have hp' := gu5_p'_ne π
  have hq' := gu5_q'_ne π
  have hpq := gu5_p'_ne_q' π
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    exacts [hP, hQ, hM]
  · rintro ⟨i, j, θ⟩
    constructor
    · intro hq
      change edgePoint Y j θ.val ∈ π.U at hq
      rcases hS.mem_label θ.2.1 θ.2.2.le hq with rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨gu5_arcM π Y A.hA0.le A.hA1 A.hD0.le A.hD1, by simp,
          (gu5_arcM_mem_iff π _ _ _ _ i _ θ).mpr (Or.inl ⟨rfl, ?_⟩)⟩
        rw [hS.eq _ (gu5_mA_ne_mB π) (gu5_mA_ne_mC π)] at hq
        exact (A.UA _ θ.2.1 θ.2.2.le).mp hq
      · exact ⟨gu5_arcM π Y A.hA0.le A.hA1 A.hD0.le A.hD1, by simp,
          (gu5_arcM_mem_iff π _ _ _ _ i _ θ).mpr (Or.inr (Or.inl rfl))⟩
      · exact ⟨gu5_arcM π Y A.hA0.le A.hA1 A.hD0.le A.hD1, by simp,
          (gu5_arcM_mem_iff π _ _ _ _ i _ θ).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩
      · refine ⟨gu5_arcM π Y A.hA0.le A.hA1 A.hD0.le A.hD1, by simp,
          (gu5_arcM_mem_iff π _ _ _ _ i _ θ).mpr (Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩)))⟩
        rw [hS.eq _ (gu5_mB_ne_mD π).symm (gu5_mC_ne_mD π).symm] at hq
        exact (A.UD _ θ.2.1 θ.2.2.le).mp hq
      · refine ⟨gu5_arcE π Y π.p' A.hp0.le A.hp A.hp1, by simp,
          (gu5_arcE_mem_iff π _ _ _ _ i _ θ).mpr ⟨rfl, ?_⟩⟩
        rw [hS.eval_p'] at hq
        exact (A.Up _ θ.2.1 θ.2.2.le).mp hq
      · refine ⟨gu5_arcE π Y π.q' A.hq0.le A.hq A.hq1, by simp,
          (gu5_arcE_mem_iff π _ _ _ _ i _ θ).mpr ⟨rfl, ?_⟩⟩
        rw [hS.eval_q'] at hq
        exact (A.Uq _ θ.2.1 θ.2.2.le).mp hq
    · rintro ⟨a, ha, hq⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · exact Smoothing.isArc_eval_mem_of_mem hP hcl hq
      · exact Smoothing.isArc_eval_mem_of_mem hQ hcl hq
      · exact Smoothing.isArc_eval_mem_of_mem hM hcl hq
  · intro a ha b hb hab q hqa hqb
    obtain ⟨i, j, θ⟩ := q
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    have labM : ∀ h : (gu5_arcM π Y A.hA0.le A.hA1 A.hD0.le A.hD1).Mem ⟨i, (j, θ)⟩,
        j = π.mA ∨ j = π.mB ∨ j = π.mC ∨ j = π.mD := by
      intro h
      rw [gu5_arcM_mem_iff] at h
      rcases h with ⟨h, -⟩ | h | h | ⟨h, -⟩
      exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr h))]
    have labP : ∀ h : (gu5_arcE π Y π.p' A.hp0.le A.hp A.hp1).Mem ⟨i, (j, θ)⟩, j = π.p' :=
      fun h => ((gu5_arcE_mem_iff π _ _ _ _ i _ θ).mp h).1
    have labQ : ∀ h : (gu5_arcE π Y π.q' A.hq0.le A.hq A.hq1).Mem ⟨i, (j, θ)⟩, j = π.q' :=
      fun h => ((gu5_arcE_mem_iff π _ _ _ _ i _ θ).mp h).1
    have PM : ∀ (h1 : j = π.p') (h2 : j = π.mA ∨ j = π.mB ∨ j = π.mC ∨ j = π.mD), False := by
      rintro rfl (h | h | h | h)
      exacts [hp'.1 h, hp'.2.1 h, hp'.2.2.1 h, hp'.2.2.2 h]
    have QM : ∀ (h1 : j = π.q') (h2 : j = π.mA ∨ j = π.mB ∨ j = π.mC ∨ j = π.mD), False := by
      rintro rfl (h | h | h | h)
      exacts [hq'.1 h, hq'.2.1 h, hq'.2.2.1 h, hq'.2.2.2 h]
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact hab rfl
    · exact hpq ((labP hqa).symm.trans (labQ hqb))
    · exact PM (labP hqa) (labM hqb)
    · exact hpq ((labP hqb).symm.trans (labQ hqa))
    · exact hab rfl
    · exact QM (labQ hqa) (labM hqb)
    · exact PM (labP hqb) (labM hqa)
    · exact QM (labQ hqb) (labM hqa)
    · exact hab rfl

theorem gu5_arcE_ne_arcE {Y : LabelledTuple (k + 3)} {j j' : ZMod (k + 3)} (h : j ≠ j') {a b a' b' : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) (ha' : 0 ≤ a') (hab' : a' < b') (hb' : b' < 1) :
    gu5_arcE π Y j ha hab hb ≠ gu5_arcE π Y j' ha' hab' hb' := fun e =>
  h (congrArg (fun r : (Shadow.single ⟨k + 3, π.hk₃, Y⟩).Arc => (r.start.1 : ZMod (k + 3))) e)

theorem gu5_arcE_ne_arcM {Y : LabelledTuple (k + 3)} {j : ZMod (k + 3)} (h : j ≠ π.mA) {a b aA bD : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) (h0A : 0 ≤ aA) (h1A : aA < 1) (h0D : 0 ≤ bD)
    (h1D : bD < 1) : gu5_arcE π Y j ha hab hb ≠ gu5_arcM π Y h0A h1A h0D h1D := fun e =>
  h (congrArg (fun r : (Shadow.single ⟨k + 3, π.hk₃, Y⟩).Arc => (r.start.1 : ZMod (k + 3))) e)

/-- **D5.** Both diagrams meet `U` cleanly (the six frontier points are distinct and traversed once; the
component leaves `U`). -/
theorem clean_M₀ : Clean π.U π.M₀ := by
  exact gu5_clean π π.X₀_generic (gu5_side₀ π)

theorem clean_M₁ : Clean π.U π.M₁ := by
  exact gu5_clean π π.X₁_generic (gu5_side₁ π)

/-- **D6.** The outside match with component bijection: the identity on traversal points (same labels
`ZMod (k+3)`, same parameters), `eval_eq` because only the vertex `m₀` moved and both bent edges lie in
`interior U`; directions of outside points are those of unmoved strands; outer crossings are the crossings
not involving `mB, mC` (`X₁_cross_iff`), with the same over data (positive diagrams, same `det`). -/
theorem exists_moveMatch : Nonempty (MoveMatch π.U π.M₀ π.M₁) := by
  exact ⟨gu5_moveMatch π⟩

/-- **D7.** The three arcs of `M₀` inside `U` (on `p'`, on `q'`, and the `m`-arc across the four pieces),
covering the trace of `M₀` inside `U`; and the three arcs of `M₁` (the `m`-arc now bent through the apex)
with the same six ends. Stated as the existence of the arc covers with matching ends. -/
theorem exists_arcCovers : ∃ (a b c : π.M₀.Γ.Arc) (a' b' c' : π.M₁.Γ.Arc),
    a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a' ≠ b' ∧ b' ≠ c' ∧ a' ≠ c' ∧
    π.M₀.Γ.ArcCover π.U {a, b, c} ∧ π.M₁.Γ.ArcCover π.U {a', b', c'} ∧
    π.M₁.Γ.eval a'.startPt = π.M₀.Γ.eval a.startPt ∧ π.M₁.Γ.eval a'.stopPt = π.M₀.Γ.eval a.stopPt ∧
    π.M₁.Γ.eval b'.startPt = π.M₀.Γ.eval b.startPt ∧ π.M₁.Γ.eval b'.stopPt = π.M₀.Γ.eval b.stopPt ∧
    π.M₁.Γ.eval c'.startPt = π.M₀.Γ.eval c.startPt ∧ π.M₁.Γ.eval c'.stopPt = π.M₀.Γ.eval c.stopPt := by
  obtain ⟨A⟩ := gu5_exists_arcParams π
  have hp' := gu5_p'_ne π
  have hq' := gu5_q'_ne π
  refine ⟨gu5_arcE π π.X₀ π.p' A.hp0.le A.hp A.hp1, gu5_arcE π π.X₀ π.q' A.hq0.le A.hq A.hq1,
    gu5_arcM π π.X₀ A.hA0.le A.hA1 A.hD0.le A.hD1,
    gu5_arcE π π.X₁ π.p' A.hp0.le A.hp A.hp1, gu5_arcE π π.X₁ π.q' A.hq0.le A.hq A.hq1,
    gu5_arcM π π.X₁ A.hA0.le A.hA1 A.hD0.le A.hD1,
    gu5_arcE_ne_arcE π (gu5_p'_ne_q' π) _ _ _ _ _ _, gu5_arcE_ne_arcM π hq'.1 _ _ _ _ _ _ _,
    gu5_arcE_ne_arcM π hp'.1 _ _ _ _ _ _ _,
    gu5_arcE_ne_arcE π (gu5_p'_ne_q' π) _ _ _ _ _ _, gu5_arcE_ne_arcM π hq'.1 _ _ _ _ _ _ _,
    gu5_arcE_ne_arcM π hp'.1 _ _ _ _ _ _ _,
    gu5_arcCover π (gu5_side₀ π) A, gu5_arcCover π (gu5_side₁ π) A, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gu5_edgePoint_X₁ π hp'.2.1 hp'.2.2.1 _
  · exact gu5_edgePoint_X₁ π hp'.2.1 hp'.2.2.1 _
  · exact gu5_edgePoint_X₁ π hq'.2.1 hq'.2.2.1 _
  · exact gu5_edgePoint_X₁ π hq'.2.1 hq'.2.2.1 _
  · exact gu5_edgePoint_X₁ π (gu5_mA_ne_mB π) (gu5_mA_ne_mC π) _
  · exact gu5_edgePoint_X₁ π (gu5_mB_ne_mD π).symm (gu5_mC_ne_mD π).symm _


end G11_ParamsSw

end W3A1Copy


/-! ### W3-(b) Switch transport (PROVED except the optional `Reparam` form): the record-level
data of a visit bijection, `IsRecordIsoData`, the frame and the move match all commute with switching
one crossing on each side, provided the bijection matches the two switched crossings.  The cyclic order
and the twins are shadow-level (`Iff.rfl` / `rfl`). -/

section W3Switch

variable {D D' : Diagram}

theorem w3b_visitBetween_switch (x : D.Γ.Crossing) (u v w : D.Γ.Visit) :
    (D.switch x).VisitBetween u v w ↔ D.VisitBetween u v w := Iff.rfl

theorem w3b_twin_switch (x : D.Γ.Crossing) (v : D.Γ.Visit) : (D.switch x).twin v = D.twin v := rfl

theorem w3b_componentCount_switch (x : D.Γ.Crossing) : (D.switch x).componentCount = D.componentCount := rfl

/-- the crossing correspondence of a twin-preserving bijection: two occurrences share a crossing iff their
images do -/
theorem w3b_fst_eq_iff_of_twin (Ψ : D.Γ.Visit ≃ D'.Γ.Visit) (htw : ∀ v, Ψ (D.twin v) = D'.twin (Ψ v))
    (v w : D.Γ.Visit) : (Ψ v).1 = (Ψ w).1 ↔ v.1 = w.1 := by
  constructor
  · intro h
    rcases D'.eq_or_eq_twin (Ψ w) (Ψ v) h with h1 | h1
    · rw [Ψ.injective h1]
    · rw [← htw] at h1
      rw [Ψ.injective h1]
      rfl
  · intro h
    rcases D.eq_or_eq_twin w v h with h1 | h1
    · rw [h1]
    · rw [h1, htw]
      rfl

theorem w3b_overBit_switch_of_visitIso (Ψ : D.Γ.Visit ≃ D'.Γ.Visit) (x : D.Γ.Crossing)
    (x' : D'.Γ.Crossing) (hx : ∀ v, (Ψ v).1 = x' ↔ v.1 = x)
    (hbit : ∀ v, D'.overBit (Ψ v) = D.overBit v) (v : D.Γ.Visit) :
    (D'.switch x').overBit (Ψ v) = (D.switch x).overBit v := by
  by_cases h : v.1 = x
  · rw [D'.switch_overBit_self x' (Ψ v) ((hx v).mpr h), D.switch_overBit_self x v h, hbit]
  · rw [D'.switch_overBit_of_ne x' (Ψ v) (fun e => h ((hx v).mp e)), D.switch_overBit_of_ne x v h, hbit]

theorem w3b_sign_switch_of_visitIso (Ψ : D.Γ.Visit ≃ D'.Γ.Visit) (x : D.Γ.Crossing)
    (x' : D'.Γ.Crossing) (hx : ∀ v, (Ψ v).1 = x' ↔ v.1 = x)
    (hsgn : ∀ v, D'.sign (Ψ v).1 = D.sign v.1) (v : D.Γ.Visit) :
    (D'.switch x').sign (Ψ v).1 = (D.switch x).sign v.1 := by
  rw [D'.switch_sign, D.switch_sign]
  by_cases h : v.1 = x
  · rw [if_pos ((hx v).mpr h), if_pos h, hsgn]
  · rw [if_neg (fun e => h ((hx v).mp e)), if_neg h, hsgn]

/-- CV's clauses (a)–(d) from the four clauses of the G11 core statements -/
theorem w3b_isRecordIsoData_of_clauses (Ψ : D.Γ.Visit ≃ D'.Γ.Visit)
    (htw : ∀ v, Ψ (D.twin v) = D'.twin (Ψ v)) (hbit : ∀ v, D'.overBit (Ψ v) = D.overBit v)
    (hsgn : ∀ v, D'.sign (Ψ v).1 = D.sign v.1)
    (hcyc : ∀ u v w, D'.VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔ D.VisitBetween u v w) :
    CV.IsRecordIsoData D D' Ψ where
  cyclic_order u v w h := (hcyc u v w).mpr h
  double_points := (CV.carriesDoublePoints_iff (ρ := D.record) (ρ' := D'.record) Ψ).2 htw
  over_under := (CV.carriesOverUnder_iff (ρ := D.record) (ρ' := D'.record) Ψ).2 hbit
  signs := hsgn

/-- `ax:gausscode` from the four clauses (one component both sides) -/
theorem w3b_homfly_of_clauses (hD : D.componentCount = 1) (hD' : D'.componentCount = 1)
    (Ψ : D.Γ.Visit ≃ D'.Γ.Visit)
    (htw : ∀ v, Ψ (D.twin v) = D'.twin (Ψ v)) (hbit : ∀ v, D'.overBit (Ψ v) = D.overBit v)
    (hsgn : ∀ v, D'.sign (Ψ v).1 = D.sign v.1)
    (hcyc : ∀ u v w, D'.VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔ D.VisitBetween u v w) :
    homfly D = homfly D' :=
  CV.gausscode_polynomial D D' hD hD'
    (CV.recordIsoOfData hD hD' Ψ (w3b_isRecordIsoData_of_clauses Ψ htw hbit hsgn hcyc))

/-- **(b) the record-level switch transport**: a visit bijection carrying twins, over bits, signs and the
cyclic order and matching the crossings `x ↦ x'` carries the same data between the switched diagrams,
hence `homfly (D.switch x) = homfly (D'.switch x')`.  This replaces the five `Reparam`-level
commutations of PLAN §5 (b) on the assembly's path. -/
theorem w3b_homfly_switch_of_clauses (hD : D.componentCount = 1) (hD' : D'.componentCount = 1)
    (Ψ : D.Γ.Visit ≃ D'.Γ.Visit) (x : D.Γ.Crossing) (x' : D'.Γ.Crossing)
    (hx : ∀ v, (Ψ v).1 = x' ↔ v.1 = x)
    (htw : ∀ v, Ψ (D.twin v) = D'.twin (Ψ v)) (hbit : ∀ v, D'.overBit (Ψ v) = D.overBit v)
    (hsgn : ∀ v, D'.sign (Ψ v).1 = D.sign v.1)
    (hcyc : ∀ u v w, D'.VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔ D.VisitBetween u v w) :
    homfly (D.switch x) = homfly (D'.switch x') :=
  w3b_homfly_of_clauses (D := D.switch x) (D' := D'.switch x') hD hD' Ψ htw
    (w3b_overBit_switch_of_visitIso Ψ x x' hx hbit) (w3b_sign_switch_of_visitIso Ψ x x' hx hsgn) hcyc

/-- `IsRecordIsoData` commutes with a matched switch -/
theorem w3b_isRecordIsoData_switch (Φ : D.Γ.Visit ≃ D'.Γ.Visit) (x : D.Γ.Crossing) (x' : D'.Γ.Crossing)
    (hx : ∀ v, (Φ v).1 = x' ↔ v.1 = x) (h : CV.IsRecordIsoData D D' Φ) :
    CV.IsRecordIsoData (D.switch x) (D'.switch x') Φ where
  cyclic_order := h.cyclic_order
  double_points := h.double_points
  over_under := (CV.carriesOverUnder_iff (ρ := (D.switch x).record) (ρ' := (D'.switch x').record) Φ).2
    (w3b_overBit_switch_of_visitIso Φ x x' hx
      ((CV.carriesOverUnder_iff (ρ := D.record) (ρ' := D'.record) Φ).1 h.over_under))
  signs v := w3b_sign_switch_of_visitIso Φ x x' hx h.signs v

/-- an outside match transports to a switch of the RIGHT diagram at an inner crossing (the mirror image
of the accepted `OutsideMatch.switch`) -/
def w3b_outsideMatch_switch_right {U : Set Plane} (m : OutsideMatch U D D') (x' : D'.Γ.Crossing)
    (hx' : D'.Γ.crossingPoint x' ∈ interior U) : OutsideMatch U D (D'.switch x') where
  φ := m.φ
  eval_eq := m.eval_eq
  dir_pos := m.dir_pos
  dir_pos_before := m.dir_pos_before
  ψ := m.ψ
  over_eq := fun y => by
    have hy : (m.ψ y).1 ≠ x' := fun e => (m.ψ y).2 (by rw [e]; exact hx')
    refine (m.over_eq y).trans (Subtype.ext ?_)
    show D'.visitPt (D'.overVisit (m.ψ y).1) = (D'.switch x').visitPt ((D'.switch x').overVisit (m.ψ y).1)
    rw [D'.switch_overVisit_of_ne x' hy]
    rfl
  under_eq := fun y => by
    have hy : (m.ψ y).1 ≠ x' := fun e => (m.ψ y).2 (by rw [e]; exact hx')
    refine (m.under_eq y).trans (Subtype.ext ?_)
    show D'.visitPt (D'.underVisit (m.ψ y).1) = (D'.switch x').visitPt ((D'.switch x').underVisit (m.ψ y).1)
    rw [D'.switch_underVisit_of_ne x' hy]
    rfl

/-- **(b) the move match commutes with a switch at an inner crossing on each side** -/
def w3b_moveMatch_switch {U : Set Plane} (m : MoveMatch U D D') (x : D.Γ.Crossing)
    (hx : D.Γ.crossingPoint x ∈ interior U) (x' : D'.Γ.Crossing)
    (hx' : D'.Γ.crossingPoint x' ∈ interior U) : MoveMatch U (D.switch x) (D'.switch x') :=
  { w3b_outsideMatch_switch_right (m.toOutsideMatch.switch x hx) x' hx' with
    e := m.e
    comp_eq := m.comp_eq }

/-- the frame is shadow-level -/
theorem w3b_localFrame_switch {U : Set Plane} (fr : LocalFrame U D D') (x : D.Γ.Crossing)
    (x' : D'.Γ.Crossing) : LocalFrame U (D.switch x) (D'.switch x') :=
  ⟨fr.disc, fr.clean.switch x, fr.clean'.switch x'⟩

/-- **(b) sub-leaf (OPTIONAL — not on the assembly's path):** a reparametrization commutes with switching
the crossings at one double point: `φ` traces the same points, so the two traversal points of `D` at the
double point of `x` (`gu3_pt_of_eval_eq_crossingPoint`) go to the two of `D'` at `x'`; `over_map`/`over_surj`
for the switched pair send the under occurrence of `x` (the new over occurrence) to the under occurrence of
`x'` and are unchanged elsewhere.  ≈ 150 lines.  The plan's route `D₀ ≃_Reparam M₀` for the homfly step is
replaced on the assembly's path by `w3b_homfly_switch_of_clauses` (record level, `ax:gausscode`, already in
the row's axiom footprint through Unit F). -/
theorem w3b_reparam_switch (h : Reparam D D') (x : D.Γ.Crossing) (x' : D'.Γ.Crossing)
    (_hx : D'.Γ.crossingPoint x' = D.Γ.crossingPoint x) : Reparam (D.switch x) (D'.switch x') := by
  sorry

end W3Switch

namespace G11_ParamsSw

variable {k : ℕ} [NeZero k] {C : G11_ConfigSw k} (π : G11_ParamsSw C)

def comp₀ : PolyComp := ⟨k + 3, π.hk₃, π.X₀⟩
def comp₁ : PolyComp := ⟨k + 3, π.hk₃, π.X₁⟩

/-- **(a) sub-leaf B1′** (copy of `G11_Params.X₀_generic`, GenericTransport 857): the subdivided polygon
is generic — the `appendVertex` chain `X ≅ shift (m+1) X → +p_in → +m₀ → +p_out ≅ X₀` (U3 Block A). -/
theorem w3a_X₀_generic : (Shadow.single π.comp₀).Generic := by
  exact π.X₀_generic

/-- **(a) sub-leaf C1′** (copy of `G11_Params.X₁_generic`, GenericTransport 2858): the moved polygon is
generic — the four genericity clauses at the apex (U4 helpers 2708–2850). -/
theorem w3a_X₁_generic : (Shadow.single π.comp₁).Generic := by
  exact π.X₁_generic


/-- the strand of label `i` of the one-component shadows of `X₀`, `X₁` -/
def st₀ (i : ZMod (k + 3)) : π.M₀.Γ.Strand := (⟨0, i⟩ : (Shadow.single π.comp₀).Strand)
def st₁ (i : ZMod (k + 3)) : π.M₁.Γ.Strand := (⟨0, i⟩ : (Shadow.single π.comp₁).Strand)

/-- **(a) sub-leaves** (copies of `X₀_cross_mp/mq/pq` :949–969 and `X₁_cross_pC/qB/pq` :2869–3380): the
three local pairs are crossings of `X₀` (`{mB, p'}`, `{mC, q'}`, `{p', q'}`) and of `X₁`
(`{p', mC}`, `{q', mB}`, `{p', q'}`). -/
theorem w3a_X₀_cross_mp : IsCrossing π.X₀ {π.mB, π.p'} := by
  exact π.X₀_cross_mp
theorem w3a_X₀_cross_mq : IsCrossing π.X₀ {π.mC, π.q'} := by
  exact π.X₀_cross_mq
theorem w3a_X₀_cross_pq : IsCrossing π.X₀ {π.p', π.q'} := by
  exact π.X₀_cross_pq
theorem w3a_X₁_cross_pC : IsCrossing π.X₁ {π.p', π.mC} := by
  exact π.X₁_cross_pC
theorem w3a_X₁_cross_qB : IsCrossing π.X₁ {π.q', π.mB} := by
  exact π.X₁_cross_qB
theorem w3a_X₁_cross_pq : IsCrossing π.X₁ {π.p', π.q'} := by
  exact π.X₁_cross_pq

/-- the three local crossings of `M₀` and of `M₁` (`gu6_y_mp` … for the switched configuration) -/
def y_mp : π.M₀.Γ.Crossing := (Shadow.singleCrossingEquiv π.comp₀).symm (xPair π.w3a_X₀_cross_mp)
def y_mq : π.M₀.Γ.Crossing := (Shadow.singleCrossingEquiv π.comp₀).symm (xPair π.w3a_X₀_cross_mq)
def y_pq : π.M₀.Γ.Crossing := (Shadow.singleCrossingEquiv π.comp₀).symm (xPair π.w3a_X₀_cross_pq)
def y'_pC : π.M₁.Γ.Crossing := (Shadow.singleCrossingEquiv π.comp₁).symm (xPair π.w3a_X₁_cross_pC)
def y'_qB : π.M₁.Γ.Crossing := (Shadow.singleCrossingEquiv π.comp₁).symm (xPair π.w3a_X₁_cross_qB)
def y'_pq : π.M₁.Γ.Crossing := (Shadow.singleCrossingEquiv π.comp₁).symm (xPair π.w3a_X₁_cross_pq)

/-- the six local occurrences of `M₁` (`w'_Cp` is the occurrence on the moved piece `mC` at the crossing with `p'`, the image of `w_mp` under `Ψ₁`); those of `M₀` (`w_mp` …) are the copy's -/
def w'_pC : π.M₁.Γ.Visit :=
  (Shadow.singleVisitEquiv π.comp₁).symm ⟨xPair π.w3a_X₁_cross_pC, ⟨π.p', mem_pair_left _ _⟩⟩
def w'_Cp : π.M₁.Γ.Visit :=
  (Shadow.singleVisitEquiv π.comp₁).symm ⟨xPair π.w3a_X₁_cross_pC, ⟨π.mC, mem_pair_right _ _⟩⟩
def w'_qB : π.M₁.Γ.Visit :=
  (Shadow.singleVisitEquiv π.comp₁).symm ⟨xPair π.w3a_X₁_cross_qB, ⟨π.q', mem_pair_left _ _⟩⟩
def w'_Bq : π.M₁.Γ.Visit :=
  (Shadow.singleVisitEquiv π.comp₁).symm ⟨xPair π.w3a_X₁_cross_qB, ⟨π.mB, mem_pair_right _ _⟩⟩
def w'_pq : π.M₁.Γ.Visit :=
  (Shadow.singleVisitEquiv π.comp₁).symm ⟨xPair π.w3a_X₁_cross_pq, ⟨π.p', mem_pair_left _ _⟩⟩
def w'_qp : π.M₁.Γ.Visit :=
  (Shadow.singleVisitEquiv π.comp₁).symm ⟨xPair π.w3a_X₁_cross_pq, ⟨π.q', mem_pair_right _ _⟩⟩

theorem w_mp_fst : π.w_mp.1 = π.y_mp := RProof.G11_Params.gu6_sv_fst_eq _ _
theorem w_pm_fst : π.w_pm.1 = π.y_mp := RProof.G11_Params.gu6_sv_fst_eq _ _
theorem w_mq_fst : π.w_mq.1 = π.y_mq := RProof.G11_Params.gu6_sv_fst_eq _ _
theorem w_qm_fst : π.w_qm.1 = π.y_mq := RProof.G11_Params.gu6_sv_fst_eq _ _
theorem w_pq_fst : π.w_pq.1 = π.y_pq := RProof.G11_Params.gu6_sv_fst_eq _ _
theorem w_qp_fst : π.w_qp.1 = π.y_pq := RProof.G11_Params.gu6_sv_fst_eq _ _
theorem w'_pC_fst : π.w'_pC.1 = π.y'_pC := RProof.G11_Params.gu6_sv_fst_eq _ _
theorem w'_Cp_fst : π.w'_Cp.1 = π.y'_pC := RProof.G11_Params.gu6_sv_fst_eq _ _
theorem w'_qB_fst : π.w'_qB.1 = π.y'_qB := RProof.G11_Params.gu6_sv_fst_eq _ _
theorem w'_Bq_fst : π.w'_Bq.1 = π.y'_qB := RProof.G11_Params.gu6_sv_fst_eq _ _
theorem w'_pq_fst : π.w'_pq.1 = π.y'_pq := RProof.G11_Params.gu6_sv_fst_eq _ _
theorem w'_qp_fst : π.w'_qp.1 = π.y'_pq := RProof.G11_Params.gu6_sv_fst_eq _ _

/-- **the switched crossing on each side**: `x₀` of `M₀` (= `xs` read on `X₀`), `x₁` of `M₁` (the same
local pair after the move: `{m,p} ↦ {p', mC}`, `{m,q} ↦ {q', mB}`, `{p,q} ↦ {p', q'}`) -/
def x₀ : π.M₀.Γ.Crossing := if C.sw = 0 then π.y_mp else if C.sw = 1 then π.y_mq else π.y_pq
def x₁ : π.M₁.Γ.Crossing := if C.sw = 0 then π.y'_pC else if C.sw = 1 then π.y'_qB else π.y'_pq

/-- `M₀^{sw}`, `M₁^{sw}`: the two sides of the switched RIII site -/
abbrev M₀sw : Diagram := π.M₀.switch π.x₀
abbrev M₁sw : Diagram := π.M₁.switch π.x₁

theorem M₀sw_componentCount : π.M₀sw.componentCount = 1 := rfl
theorem M₁sw_componentCount : π.M₁sw.componentCount = 1 := rfl

/-! ### W3-A1-DE — the trans-free copy of GenericTransport.lean 4918–8630 (Units D, D8, E) over
`G11_ParamsSw` (unit W3-A1, second prover, file `W3_A1_DE.lean`).  Mechanical: `G11_Config → G11_ConfigSw`,
`G11_Params → G11_ParamsSw`, `X₀_generic/X₁_generic/X*_cross_* → w3a_*` (the skeleton's sub-leaves); the
`C`-free helpers of the accepted namespace are reused by a selective `open RProof.G11_Params (…)`, not
copied; `gu6_htrans` is dropped (replaced by the `htrans` hypothesis of `w3a_riii_param`), `riii` is re-typed
as `w3a_riii_param`, `exists_Ψ₁` as `w3a_exists_Ψ₁`, `homfly_M₁`/`core_of_params` are the skeleton's
`w3c_homfly_M₁sw`/`G11_core_sw`.  The Unit B–C facts the copy consumes are the BC prover's; here they are
the BC prover's PROVED copies above (`section W3A1Copy`); the 8 aliases and 11 black boxes of
`W3_A1_DE.lean` are dropped here (assembled 2026-09-15, `W3_A1_ASSEMBLY_REPORT.md`). -/

section W3DECopy

open SM.GeoCarrier SM.Carrier
open RProof.G11_Params (gu6_D9_core_p gu6_D9_core_q gu6_arc_inner_of_path_bwd gu6_arc_inner_of_path_fwd gu6_arc_inner_of_path_start gu6_arc_start_between gu6_arc_two_paths gu6_before_iff gu6_common_eq_single gu6_cp_injective_single gu6_decode_start_same gu6_det_ne_zero_single gu6_edgePoint_comb gu6_edge_interior_of_convex gu6_edge_interior_of_convex' gu6_exists_arc_of_interior gu6_lab_val gu6_neg_iff_of_pos_iff gu6_outside_cmp gu6_overBit_iff_det gu6_over_under_of_neg gu6_over_under_of_pos gu6_riii_of_strands gu6_single_pt_eta gu6_strand_eq_iff gu6_subdiv_lab gu6_subdiv_lab_succ gu6_subdiv_mA gu6_subdiv_mB gu6_subdiv_mC gu6_subdiv_mD gu6_subdiv_mD_succ gu6_sv_fst' gu6_sv_fst_eq gu6_sv_ne gu6_sv_param_spec gu6_sv_strand' gu6_sv_visitPt_snd gu6_swap_edge gu6_tb_edge_start gu6_tb_same_edge gu6_tb_same_edge_of_start gu6_tb_span_one gu6_tb_span_two gu6_tb_vertex_between gu6_triple_eq gu6_visit_ext gu6_visit_ne_of_edge gu6_xPair_ne_of_not_mem gu6_svisit_ext gu6_sv_strand gu6_strand_ne)

variable {n : ℕ} [NeZero n]

/-! #### The copy proper (GenericTransport.lean 4918–8629 minus the `C`-free helpers) -/
/-! #### U6 helpers for D8 (a): vertices and edges of `X₀`, `X₁`; the four inner pieces lie in `Θ` -/

/-! the pieces of `m` in `X₀` and their labels -/

theorem gu6_X₀_mA : π.X₀ π.mA = C.X C.m := gu6_subdiv_mA C.X C.m π.t₁ π.t₂ π.t₃
theorem gu6_X₀_mB : π.X₀ π.mB = edgePoint C.X C.m π.t₁ := gu6_subdiv_mB C.X C.m π.t₁ π.t₂ π.t₃
theorem gu6_X₀_mC : π.X₀ π.mC = edgePoint C.X C.m π.t₂ := gu6_subdiv_mC C.X C.m π.t₁ π.t₂ π.t₃
theorem gu6_X₀_mD : π.X₀ π.mD = edgePoint C.X C.m π.t₃ := gu6_subdiv_mD C.X C.m π.t₁ π.t₂ π.t₃
theorem gu6_X₀_mD_succ : π.X₀ (π.mD + 1) = C.X (C.m + 1) :=
  gu6_subdiv_mD_succ C.X C.m π.t₁ π.t₂ π.t₃

theorem gu6_mA_val : π.mA.val = C.m.val := ZMod.val_natCast_of_lt (by have := C.m.val_lt; omega)
theorem gu6_mB_val : π.mB.val = C.m.val + 1 := ZMod.val_natCast_of_lt (by have := C.m.val_lt; omega)
theorem gu6_mC_val : π.mC.val = C.m.val + 2 := ZMod.val_natCast_of_lt (by have := C.m.val_lt; omega)
theorem gu6_mD_val : π.mD.val = C.m.val + 3 := ZMod.val_natCast_of_lt (by have := C.m.val_lt; omega)
theorem gu6_mid_eq_mC : π.mid = π.mC := rfl

theorem gu6_mA_add_one : π.mA + 1 = π.mB := (Nat.cast_add_one _).symm
theorem gu6_mB_add_one : π.mB + 1 = π.mC := by
  show ((C.m.val + 1 : ℕ) : ZMod (k + 3)) + 1 = ((C.m.val + 2 : ℕ) : ZMod (k + 3))
  push_cast
  ring
theorem gu6_mC_add_one : π.mC + 1 = π.mD := by
  show ((C.m.val + 2 : ℕ) : ZMod (k + 3)) + 1 = ((C.m.val + 3 : ℕ) : ZMod (k + 3))
  push_cast
  ring

theorem gu6_mA_ne_mB : π.mA ≠ π.mB := fun h => by
  have := congrArg ZMod.val h; rw [gu6_mA_val, gu6_mB_val] at this; omega
theorem gu6_mA_ne_mC : π.mA ≠ π.mC := fun h => by
  have := congrArg ZMod.val h; rw [gu6_mA_val, gu6_mC_val] at this; omega
theorem gu6_mB_ne_mC : π.mB ≠ π.mC := fun h => by
  have := congrArg ZMod.val h; rw [gu6_mB_val, gu6_mC_val] at this; omega
theorem gu6_mB_ne_mD : π.mB ≠ π.mD := fun h => by
  have := congrArg ZMod.val h; rw [gu6_mB_val, gu6_mD_val] at this; omega
theorem gu6_mC_ne_mD : π.mC ≠ π.mD := fun h => by
  have := congrArg ZMod.val h; rw [gu6_mC_val, gu6_mD_val] at this; omega
theorem gu6_mA_ne_mD : π.mA ≠ π.mD := fun h => by
  have := congrArg ZMod.val h; rw [gu6_mA_val, gu6_mD_val] at this; omega

theorem gu6_edge_mB : edge π.X₀ π.mB = (π.t₂ - π.t₁) • edge C.X C.m := by
  rw [edge, gu6_mB_add_one, gu6_X₀_mC, gu6_X₀_mB, edgePoint, edgePoint, sub_smul]
  abel
theorem gu6_edge_mC : edge π.X₀ π.mC = (π.t₃ - π.t₂) • edge C.X C.m := by
  rw [edge, gu6_mC_add_one, gu6_X₀_mD, gu6_X₀_mC, edgePoint, edgePoint, sub_smul]
  abel
theorem gu6_edgePoint_mB (s : ℝ) :
    edgePoint π.X₀ π.mB s = edgePoint C.X C.m (π.t₁ + s * (π.t₂ - π.t₁)) := by
  rw [edgePoint, gu6_X₀_mB, gu6_edge_mB, edgePoint, edgePoint, smul_smul, add_assoc, ← add_smul]
theorem gu6_edgePoint_mC (s : ℝ) :
    edgePoint π.X₀ π.mC s = edgePoint C.X C.m (π.t₂ + s * (π.t₃ - π.t₂)) := by
  rw [edgePoint, gu6_X₀_mC, gu6_edge_mC, edgePoint, edgePoint, smul_smul, add_assoc, ← add_smul]

theorem gu6_t₁_lt_t₂ : π.t₁ < π.t₂ := π.h₁.trans π.h₂
theorem gu6_t₂_lt_t₃ : π.t₂ < π.t₃ := π.h₃.trans π.h₄
theorem gu6_t₁_lt_t₃ : π.t₁ < π.t₃ := π.gu6_t₁_lt_t₂.trans π.gu6_t₂_lt_t₃

/-! the old edges in `X₀` -/

theorem gu6_X₀_lab (i : ZMod k) : π.X₀ (G11_lab C.m i) = C.X i :=
  gu6_subdiv_lab C.X C.m π.t₁ π.t₂ π.t₃ i
theorem gu6_X₀_lab_succ {i : ZMod k} (hi : i ≠ C.m) : π.X₀ (G11_lab C.m i + 1) = C.X (i + 1) :=
  gu6_subdiv_lab_succ C.X C.m π.t₁ π.t₂ π.t₃ hi
theorem gu6_edge_lab {i : ZMod k} (hi : i ≠ C.m) : edge π.X₀ (G11_lab C.m i) = edge C.X i := by
  rw [edge, edge, gu6_X₀_lab_succ π hi, gu6_X₀_lab]
theorem gu6_edgeSegment_lab {i : ZMod k} (hi : i ≠ C.m) :
    edgeSegment π.X₀ (G11_lab C.m i) = edgeSegment C.X i := by
  simp only [edgeSegment, edgePoint, gu6_edge_lab π hi, gu6_X₀_lab]

/-- the labels of `X₀` other than the three new-vertex labels are old labels -/
theorem gu6_exists_lab (j : ZMod (k + 3)) (h1 : j ≠ π.mB) (h2 : j ≠ π.mC) (h3 : j ≠ π.mD) :
    ∃ i : ZMod k, G11_lab C.m i = j := by
  have hj := j.val_lt
  have hm := C.m.val_lt
  have h1' : j.val ≠ C.m.val + 1 := fun h => h1 (by rw [← ZMod.natCast_zmod_val j, h]; rfl)
  have h2' : j.val ≠ C.m.val + 2 := fun h => h2 (by rw [← ZMod.natCast_zmod_val j, h]; rfl)
  have h3' : j.val ≠ C.m.val + 3 := fun h => h3 (by rw [← ZMod.natCast_zmod_val j, h]; rfl)
  by_cases hle : j.val ≤ C.m.val
  · refine ⟨(j.val : ZMod k), ?_⟩
    have hv : ((j.val : ZMod k)).val = j.val := ZMod.val_natCast_of_lt (by omega)
    rw [G11_lab, hv, ite_eq_left hle, ZMod.natCast_zmod_val]
  · refine ⟨((j.val - 3 : ℕ) : ZMod k), ?_⟩
    have hv : (((j.val - 3 : ℕ) : ZMod k)).val = j.val - 3 := ZMod.val_natCast_of_lt (by omega)
    rw [G11_lab, hv, ite_eq_right (by omega), show j.val - 3 + 3 = j.val by omega,
      ZMod.natCast_zmod_val]

theorem gu6_X₀_vertex_not_mem (j : ZMod (k + 3)) (h1 : j ≠ π.mB) (h2 : j ≠ π.mC) (h3 : j ≠ π.mD) :
    π.X₀ j ∉ π.U := by
  obtain ⟨i, rfl⟩ := π.gu6_exists_lab j h1 h2 h3
  rw [gu6_X₀_lab]
  exact π.disc_clear_vertex i

/-! `X₁`: only the vertex `mC = mid` moved -/

theorem gu6_X₁_of_ne {j : ZMod (k + 3)} (hj : j ≠ π.mC) : π.X₁ j = π.X₀ j :=
  Function.update_of_ne hj _ _
theorem gu6_X₁_mC : π.X₁ π.mC = π.apex := Function.update_self _ _ _
theorem gu6_X₁_mA : π.X₁ π.mA = C.X C.m := by rw [gu6_X₁_of_ne π π.gu6_mA_ne_mC, gu6_X₀_mA]
theorem gu6_X₁_mB : π.X₁ π.mB = edgePoint C.X C.m π.t₁ := by
  rw [gu6_X₁_of_ne π π.gu6_mB_ne_mC, gu6_X₀_mB]
theorem gu6_X₁_mD : π.X₁ π.mD = edgePoint C.X C.m π.t₃ := by
  rw [gu6_X₁_of_ne π π.gu6_mC_ne_mD.symm, gu6_X₀_mD]
theorem gu6_lab_ne_mC (i : ZMod k) : G11_lab C.m i ≠ π.mC := fun h => by
  have := congrArg ZMod.val h
  rw [gu6_lab_val, gu6_mC_val] at this
  split_ifs at this <;> omega
theorem gu6_lab_ne_mB (i : ZMod k) : G11_lab C.m i ≠ π.mB := fun h => by
  have := congrArg ZMod.val h
  rw [gu6_lab_val, gu6_mB_val] at this
  split_ifs at this <;> omega
theorem gu6_lab_ne_mD (i : ZMod k) : G11_lab C.m i ≠ π.mD := fun h => by
  have := congrArg ZMod.val h
  rw [gu6_lab_val, gu6_mD_val] at this
  split_ifs at this <;> omega
theorem gu6_lab_succ_ne_mC {i : ZMod k} (hi : i ≠ C.m) : G11_lab C.m i + 1 ≠ π.mC := by
  intro h
  have hik := i.val_lt
  have hmk := C.m.val_lt
  have him : i.val ≠ C.m.val := fun h => hi (ZMod.val_injective k h)
  have : Fact (1 < k + 3) := ⟨by omega⟩
  have hv : (G11_lab C.m i + 1).val = (G11_lab C.m i).val + 1 ∨ (G11_lab C.m i + 1).val = 0 := by
    rcases Nat.lt_or_ge ((G11_lab C.m i).val + 1) (k + 3) with hlt | hge
    · left
      rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt hlt]
    · right
      have := (G11_lab C.m i).val_lt
      rw [ZMod.val_add, ZMod.val_one, show (G11_lab C.m i).val + 1 = k + 3 by omega, Nat.mod_self]
  have := congrArg ZMod.val h
  rw [gu6_mC_val] at this
  rw [gu6_lab_val] at hv
  split_ifs at hv <;> omega
theorem gu6_X₁_lab (i : ZMod k) : π.X₁ (G11_lab C.m i) = C.X i := by
  rw [gu6_X₁_of_ne π (π.gu6_lab_ne_mC i), gu6_X₀_lab]
theorem gu6_X₁_lab_succ {i : ZMod k} (hi : i ≠ C.m) : π.X₁ (G11_lab C.m i + 1) = C.X (i + 1) := by
  rw [gu6_X₁_of_ne π (π.gu6_lab_succ_ne_mC hi), gu6_X₀_lab_succ π hi]
theorem gu6_edge_X₁_lab {i : ZMod k} (hi : i ≠ C.m) : edge π.X₁ (G11_lab C.m i) = edge C.X i := by
  rw [edge, edge, gu6_X₁_lab_succ π hi, gu6_X₁_lab]
theorem gu6_edgeSegment_X₁_lab {i : ZMod k} (hi : i ≠ C.m) :
    edgeSegment π.X₁ (G11_lab C.m i) = edgeSegment C.X i := by
  simp only [edgeSegment, edgePoint, gu6_edge_X₁_lab π hi, gu6_X₁_lab]
theorem gu6_X₁_vertex_not_mem (j : ZMod (k + 3)) (h1 : j ≠ π.mB) (h2 : j ≠ π.mC) (h3 : j ≠ π.mD) :
    π.X₁ j ∉ π.U := by
  rw [gu6_X₁_of_ne π h2]
  exact π.gu6_X₀_vertex_not_mem j h1 h2 h3

/-! the bent triangle `Θ` -/

/-- the bent triangle `Θ = conv{p_in, w, p_out}` -/
noncomputable def gu6_Θ : Set Plane :=
  convexHull ℝ {edgePoint C.X C.m π.t₁, π.apex, edgePoint C.X C.m π.t₃}

theorem gu6_Θ_sub_interior : π.gu6_Θ ⊆ interior π.U := π.theta_sub
theorem gu6_Θ_convex : Convex ℝ π.gu6_Θ := convex_convexHull ℝ _
theorem gu6_pin_mem_Θ : edgePoint C.X C.m π.t₁ ∈ π.gu6_Θ :=
  subset_convexHull ℝ _ (by simp)
theorem gu6_apex_mem_Θ : π.apex ∈ π.gu6_Θ :=
  subset_convexHull ℝ _ (by simp)
theorem gu6_pout_mem_Θ : edgePoint C.X C.m π.t₃ ∈ π.gu6_Θ :=
  subset_convexHull ℝ _ (by simp)

theorem gu6_base_mem_Θ {t : ℝ} (h1 : π.t₁ ≤ t) (h2 : t ≤ π.t₃) : edgePoint C.X C.m t ∈ π.gu6_Θ := by
  have hpos : 0 < π.t₃ - π.t₁ := sub_pos.mpr π.gu6_t₁_lt_t₃
  rw [gu6_edgePoint_comb C.X C.m π.gu6_t₁_lt_t₃.ne t]
  exact π.gu6_Θ_convex.add_smul_sub_mem π.gu6_pin_mem_Θ π.gu6_pout_mem_Θ
    ⟨div_nonneg (by linarith) hpos.le, (div_le_one hpos).mpr (by linarith)⟩

theorem gu6_seg_mB_sub_Θ : edgeSegment π.X₀ π.mB ⊆ π.gu6_Θ := by
  rintro x ⟨s, hs0, hs1, rfl⟩
  rw [gu6_edgePoint_mB]
  have h12 := π.gu6_t₁_lt_t₂
  have h23 := π.gu6_t₂_lt_t₃
  exact π.gu6_base_mem_Θ (by nlinarith) (by nlinarith)
theorem gu6_seg_mC_sub_Θ : edgeSegment π.X₀ π.mC ⊆ π.gu6_Θ := by
  rintro x ⟨s, hs0, hs1, rfl⟩
  rw [gu6_edgePoint_mC]
  have h12 := π.gu6_t₁_lt_t₂
  have h23 := π.gu6_t₂_lt_t₃
  exact π.gu6_base_mem_Θ (by nlinarith) (by nlinarith)
theorem gu6_seg_X₁_mB_sub_Θ : edgeSegment π.X₁ π.mB ⊆ π.gu6_Θ := by
  rintro x ⟨s, hs0, hs1, rfl⟩
  simp only [edgePoint, edge, gu6_mB_add_one, gu6_X₁_mC, gu6_X₁_mB]
  exact π.gu6_Θ_convex.add_smul_sub_mem π.gu6_pin_mem_Θ π.gu6_apex_mem_Θ ⟨hs0, hs1⟩
theorem gu6_seg_X₁_mC_sub_Θ : edgeSegment π.X₁ π.mC ⊆ π.gu6_Θ := by
  rintro x ⟨s, hs0, hs1, rfl⟩
  simp only [edgePoint, edge, gu6_mC_add_one, gu6_X₁_mD, gu6_X₁_mC]
  exact π.gu6_Θ_convex.add_smul_sub_mem π.gu6_apex_mem_Θ π.gu6_pout_mem_Θ ⟨hs0, hs1⟩

/-! #### U6 helpers for D8 (b): traversal betweenness on one component (key arithmetic) -/

/-! #### U6 helpers for D8 (c): cyclic-order lemmas and the position of arc ends -/

/-! #### U6 helpers for D8 (d): occurrences of a positive one-component diagram -/


/-! the six occurrences of `M₁` and the twelve local parameters -/

noncomputable def gu6_w'_pC : π.M₁.Γ.Visit :=
  (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm ⟨xPair π.X₁_cross_pC, ⟨π.p', mem_pair_left _ _⟩⟩
noncomputable def gu6_w'_Cp : π.M₁.Γ.Visit :=
  (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm ⟨xPair π.X₁_cross_pC, ⟨π.mC, mem_pair_right _ _⟩⟩
noncomputable def gu6_w'_qB : π.M₁.Γ.Visit :=
  (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm ⟨xPair π.X₁_cross_qB, ⟨π.q', mem_pair_left _ _⟩⟩
noncomputable def gu6_w'_Bq : π.M₁.Γ.Visit :=
  (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm ⟨xPair π.X₁_cross_qB, ⟨π.mB, mem_pair_right _ _⟩⟩
noncomputable def gu6_w'_pq : π.M₁.Γ.Visit :=
  (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm ⟨xPair π.X₁_cross_pq, ⟨π.p', mem_pair_left _ _⟩⟩
noncomputable def gu6_w'_qp : π.M₁.Γ.Visit :=
  (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm ⟨xPair π.X₁_cross_pq, ⟨π.q', mem_pair_right _ _⟩⟩

/-- the parameters of the local occurrences on their strands -/
noncomputable def gu6_s_mp : ℝ := π.M₀.crossingParam π.w_mp.1 π.w_mp.2.2
noncomputable def gu6_s_pm : ℝ := π.M₀.crossingParam π.w_pm.1 π.w_pm.2.2
noncomputable def gu6_s_mq : ℝ := π.M₀.crossingParam π.w_mq.1 π.w_mq.2.2
noncomputable def gu6_s_qm : ℝ := π.M₀.crossingParam π.w_qm.1 π.w_qm.2.2
noncomputable def gu6_s_pq : ℝ := π.M₀.crossingParam π.w_pq.1 π.w_pq.2.2
noncomputable def gu6_s_qp : ℝ := π.M₀.crossingParam π.w_qp.1 π.w_qp.2.2
noncomputable def gu6_s'_pC : ℝ := π.M₁.crossingParam π.gu6_w'_pC.1 π.gu6_w'_pC.2.2
noncomputable def gu6_s'_Cp : ℝ := π.M₁.crossingParam π.gu6_w'_Cp.1 π.gu6_w'_Cp.2.2
noncomputable def gu6_s'_qB : ℝ := π.M₁.crossingParam π.gu6_w'_qB.1 π.gu6_w'_qB.2.2
noncomputable def gu6_s'_Bq : ℝ := π.M₁.crossingParam π.gu6_w'_Bq.1 π.gu6_w'_Bq.2.2
noncomputable def gu6_s'_pq : ℝ := π.M₁.crossingParam π.gu6_w'_pq.1 π.gu6_w'_pq.2.2
noncomputable def gu6_s'_qp : ℝ := π.M₁.crossingParam π.gu6_w'_qp.1 π.gu6_w'_qp.2.2

theorem gu6_s_mp_spec : crossingPoint (xPair π.X₀_cross_mp) = edgePoint π.X₀ π.mB π.gu6_s_mp :=
  gu6_sv_param_spec π.X₀_generic _ _
theorem gu6_s_pm_spec : crossingPoint (xPair π.X₀_cross_mp) = edgePoint π.X₀ π.p' π.gu6_s_pm :=
  gu6_sv_param_spec π.X₀_generic _ _
theorem gu6_s_mq_spec : crossingPoint (xPair π.X₀_cross_mq) = edgePoint π.X₀ π.mC π.gu6_s_mq :=
  gu6_sv_param_spec π.X₀_generic _ _
theorem gu6_s_qm_spec : crossingPoint (xPair π.X₀_cross_mq) = edgePoint π.X₀ π.q' π.gu6_s_qm :=
  gu6_sv_param_spec π.X₀_generic _ _
theorem gu6_s_pq_spec : crossingPoint (xPair π.X₀_cross_pq) = edgePoint π.X₀ π.p' π.gu6_s_pq :=
  gu6_sv_param_spec π.X₀_generic _ _
theorem gu6_s_qp_spec : crossingPoint (xPair π.X₀_cross_pq) = edgePoint π.X₀ π.q' π.gu6_s_qp :=
  gu6_sv_param_spec π.X₀_generic _ _
theorem gu6_s'_pC_spec : crossingPoint (xPair π.X₁_cross_pC) = edgePoint π.X₁ π.p' π.gu6_s'_pC :=
  gu6_sv_param_spec π.X₁_generic _ _
theorem gu6_s'_Cp_spec : crossingPoint (xPair π.X₁_cross_pC) = edgePoint π.X₁ π.mC π.gu6_s'_Cp :=
  gu6_sv_param_spec π.X₁_generic _ _
theorem gu6_s'_qB_spec : crossingPoint (xPair π.X₁_cross_qB) = edgePoint π.X₁ π.q' π.gu6_s'_qB :=
  gu6_sv_param_spec π.X₁_generic _ _
theorem gu6_s'_Bq_spec : crossingPoint (xPair π.X₁_cross_qB) = edgePoint π.X₁ π.mB π.gu6_s'_Bq :=
  gu6_sv_param_spec π.X₁_generic _ _
theorem gu6_s'_pq_spec : crossingPoint (xPair π.X₁_cross_pq) = edgePoint π.X₁ π.p' π.gu6_s'_pq :=
  gu6_sv_param_spec π.X₁_generic _ _
theorem gu6_s'_qp_spec : crossingPoint (xPair π.X₁_cross_pq) = edgePoint π.X₁ π.q' π.gu6_s'_qp :=
  gu6_sv_param_spec π.X₁_generic _ _

theorem gu6_s_mp_pos : 0 < π.gu6_s_mp := π.M₀.crossingParam_pos _ _
theorem gu6_s_mp_lt_one : π.gu6_s_mp < 1 := π.M₀.crossingParam_lt_one _ _
theorem gu6_s_pm_pos : 0 < π.gu6_s_pm := π.M₀.crossingParam_pos _ _
theorem gu6_s_pm_lt_one : π.gu6_s_pm < 1 := π.M₀.crossingParam_lt_one _ _
theorem gu6_s_mq_pos : 0 < π.gu6_s_mq := π.M₀.crossingParam_pos _ _
theorem gu6_s_mq_lt_one : π.gu6_s_mq < 1 := π.M₀.crossingParam_lt_one _ _
theorem gu6_s_qm_pos : 0 < π.gu6_s_qm := π.M₀.crossingParam_pos _ _
theorem gu6_s_qm_lt_one : π.gu6_s_qm < 1 := π.M₀.crossingParam_lt_one _ _
theorem gu6_s_pq_pos : 0 < π.gu6_s_pq := π.M₀.crossingParam_pos _ _
theorem gu6_s_pq_lt_one : π.gu6_s_pq < 1 := π.M₀.crossingParam_lt_one _ _
theorem gu6_s_qp_pos : 0 < π.gu6_s_qp := π.M₀.crossingParam_pos _ _
theorem gu6_s_qp_lt_one : π.gu6_s_qp < 1 := π.M₀.crossingParam_lt_one _ _
theorem gu6_s'_pC_pos : 0 < π.gu6_s'_pC := π.M₁.crossingParam_pos _ _
theorem gu6_s'_pC_lt_one : π.gu6_s'_pC < 1 := π.M₁.crossingParam_lt_one _ _
theorem gu6_s'_Cp_pos : 0 < π.gu6_s'_Cp := π.M₁.crossingParam_pos _ _
theorem gu6_s'_Cp_lt_one : π.gu6_s'_Cp < 1 := π.M₁.crossingParam_lt_one _ _
theorem gu6_s'_qB_pos : 0 < π.gu6_s'_qB := π.M₁.crossingParam_pos _ _
theorem gu6_s'_qB_lt_one : π.gu6_s'_qB < 1 := π.M₁.crossingParam_lt_one _ _
theorem gu6_s'_Bq_pos : 0 < π.gu6_s'_Bq := π.M₁.crossingParam_pos _ _
theorem gu6_s'_Bq_lt_one : π.gu6_s'_Bq < 1 := π.M₁.crossingParam_lt_one _ _
theorem gu6_s'_pq_pos : 0 < π.gu6_s'_pq := π.M₁.crossingParam_pos _ _
theorem gu6_s'_pq_lt_one : π.gu6_s'_pq < 1 := π.M₁.crossingParam_lt_one _ _
theorem gu6_s'_qp_pos : 0 < π.gu6_s'_qp := π.M₁.crossingParam_pos _ _
theorem gu6_s'_qp_lt_one : π.gu6_s'_qp < 1 := π.M₁.crossingParam_lt_one _ _

/-- the traversal points of the twelve local occurrences -/
theorem gu6_w_mp_pt : (π.M₀.visitPt π.w_mp).2 = (π.mB, ⟨π.gu6_s_mp, π.gu6_s_mp_pos.le, π.gu6_s_mp_lt_one⟩) :=
  gu6_sv_visitPt_snd π.X₀_generic _ _
theorem gu6_w_pm_pt : (π.M₀.visitPt π.w_pm).2 = (π.p', ⟨π.gu6_s_pm, π.gu6_s_pm_pos.le, π.gu6_s_pm_lt_one⟩) :=
  gu6_sv_visitPt_snd π.X₀_generic _ _
theorem gu6_w_mq_pt : (π.M₀.visitPt π.w_mq).2 = (π.mC, ⟨π.gu6_s_mq, π.gu6_s_mq_pos.le, π.gu6_s_mq_lt_one⟩) :=
  gu6_sv_visitPt_snd π.X₀_generic _ _
theorem gu6_w_qm_pt : (π.M₀.visitPt π.w_qm).2 = (π.q', ⟨π.gu6_s_qm, π.gu6_s_qm_pos.le, π.gu6_s_qm_lt_one⟩) :=
  gu6_sv_visitPt_snd π.X₀_generic _ _
theorem gu6_w_pq_pt : (π.M₀.visitPt π.w_pq).2 = (π.p', ⟨π.gu6_s_pq, π.gu6_s_pq_pos.le, π.gu6_s_pq_lt_one⟩) :=
  gu6_sv_visitPt_snd π.X₀_generic _ _
theorem gu6_w_qp_pt : (π.M₀.visitPt π.w_qp).2 = (π.q', ⟨π.gu6_s_qp, π.gu6_s_qp_pos.le, π.gu6_s_qp_lt_one⟩) :=
  gu6_sv_visitPt_snd π.X₀_generic _ _
theorem gu6_w'_pC_pt : (π.M₁.visitPt π.gu6_w'_pC).2 = (π.p', ⟨π.gu6_s'_pC, π.gu6_s'_pC_pos.le, π.gu6_s'_pC_lt_one⟩) :=
  gu6_sv_visitPt_snd π.X₁_generic _ _
theorem gu6_w'_Cp_pt : (π.M₁.visitPt π.gu6_w'_Cp).2 = (π.mC, ⟨π.gu6_s'_Cp, π.gu6_s'_Cp_pos.le, π.gu6_s'_Cp_lt_one⟩) :=
  gu6_sv_visitPt_snd π.X₁_generic _ _
theorem gu6_w'_qB_pt : (π.M₁.visitPt π.gu6_w'_qB).2 = (π.q', ⟨π.gu6_s'_qB, π.gu6_s'_qB_pos.le, π.gu6_s'_qB_lt_one⟩) :=
  gu6_sv_visitPt_snd π.X₁_generic _ _
theorem gu6_w'_Bq_pt : (π.M₁.visitPt π.gu6_w'_Bq).2 = (π.mB, ⟨π.gu6_s'_Bq, π.gu6_s'_Bq_pos.le, π.gu6_s'_Bq_lt_one⟩) :=
  gu6_sv_visitPt_snd π.X₁_generic _ _
theorem gu6_w'_pq_pt : (π.M₁.visitPt π.gu6_w'_pq).2 = (π.p', ⟨π.gu6_s'_pq, π.gu6_s'_pq_pos.le, π.gu6_s'_pq_lt_one⟩) :=
  gu6_sv_visitPt_snd π.X₁_generic _ _
theorem gu6_w'_qp_pt : (π.M₁.visitPt π.gu6_w'_qp).2 = (π.q', ⟨π.gu6_s'_qp, π.gu6_s'_qp_pos.le, π.gu6_s'_qp_lt_one⟩) :=
  gu6_sv_visitPt_snd π.X₁_generic _ _

/-! the local double points of `X₀`, `X₁` are those of `X` -/

theorem gu6_edge_ne_zero (i : ZMod k) : edge C.X i ≠ 0 :=
  ((regular_iff_edges C.X).mp (C.gen.regular 0) i).1
theorem gu6_edge_X₀_ne_zero (j : ZMod (k + 3)) : edge π.X₀ j ≠ 0 :=
  ((regular_iff_edges π.X₀).mp (π.X₀_generic.regular 0) j).1
theorem gu6_edge_X₁_ne_zero (j : ZMod (k + 3)) : edge π.X₁ j ≠ 0 :=
  ((regular_iff_edges π.X₁).mp (π.X₁_generic.regular 0) j).1

theorem gu6_p_ne_m : C.p ≠ C.m := (P1.ne_of_isCrossing_pair C.hmp).symm
theorem gu6_q_ne_m : C.q ≠ C.m := (P1.ne_of_isCrossing_pair C.hmq).symm
theorem gu6_p_ne_q : C.p ≠ C.q := P1.ne_of_isCrossing_pair C.hpq

theorem gu6_seg_p' : edgeSegment π.X₀ π.p' = edgeSegment C.X C.p := gu6_edgeSegment_lab π (gu6_p_ne_m (C := C))
theorem gu6_seg_q' : edgeSegment π.X₀ π.q' = edgeSegment C.X C.q := gu6_edgeSegment_lab π (gu6_q_ne_m (C := C))
theorem gu6_seg_X₁_p' : edgeSegment π.X₁ π.p' = edgeSegment C.X C.p := gu6_edgeSegment_X₁_lab π (gu6_p_ne_m (C := C))
theorem gu6_seg_X₁_q' : edgeSegment π.X₁ π.q' = edgeSegment C.X C.q := gu6_edgeSegment_X₁_lab π (gu6_q_ne_m (C := C))

theorem gu6_edgePoint_X₀_p' (s : ℝ) : edgePoint π.X₀ π.p' s = edgePoint C.X C.p s := by
  show edgePoint π.X₀ (G11_lab C.m C.p) s = edgePoint C.X C.p s
  rw [edgePoint, edgePoint, gu6_edge_lab π (gu6_p_ne_m (C := C)), gu6_X₀_lab]
theorem gu6_edgePoint_X₀_q' (s : ℝ) : edgePoint π.X₀ π.q' s = edgePoint C.X C.q s := by
  show edgePoint π.X₀ (G11_lab C.m C.q) s = edgePoint C.X C.q s
  rw [edgePoint, edgePoint, gu6_edge_lab π (gu6_q_ne_m (C := C)), gu6_X₀_lab]
theorem gu6_edgePoint_X₁_p' (s : ℝ) : edgePoint π.X₁ π.p' s = edgePoint C.X C.p s := by
  show edgePoint π.X₁ (G11_lab C.m C.p) s = edgePoint C.X C.p s
  rw [edgePoint, edgePoint, gu6_edge_X₁_lab π (gu6_p_ne_m (C := C)), gu6_X₁_lab]
theorem gu6_edgePoint_X₁_q' (s : ℝ) : edgePoint π.X₁ π.q' s = edgePoint C.X C.q s := by
  show edgePoint π.X₁ (G11_lab C.m C.q) s = edgePoint C.X C.q s
  rw [edgePoint, edgePoint, gu6_edge_X₁_lab π (gu6_q_ne_m (C := C)), gu6_X₁_lab]

theorem gu6_seg_mB_sub : edgeSegment π.X₀ π.mB ⊆ edgeSegment C.X C.m := by
  rintro x ⟨s, hs0, hs1, rfl⟩
  rw [gu6_edgePoint_mB]
  have h12 := π.gu6_t₁_lt_t₂
  have h23 := π.gu6_t₂_lt_t₃
  have := π.ht₁
  have := π.ht₃
  refine ⟨_, ?_, ?_, rfl⟩ <;> nlinarith
theorem gu6_seg_mC_sub : edgeSegment π.X₀ π.mC ⊆ edgeSegment C.X C.m := by
  rintro x ⟨s, hs0, hs1, rfl⟩
  rw [gu6_edgePoint_mC]
  have h12 := π.gu6_t₁_lt_t₂
  have h23 := π.gu6_t₂_lt_t₃
  have := π.ht₁
  have := π.ht₃
  refine ⟨_, ?_, ?_, rfl⟩ <;> nlinarith

/-- a common point of two edges of a crossing of `X` is its double point -/
theorem gu6_common_eq {i j : ZMod k} (h : IsCrossing C.X {i, j}) {x : Plane}
    (hi : x ∈ edgeSegment C.X i) (hj : x ∈ edgeSegment C.X j) : x = crossingPoint (xPair h) :=
  gu6_common_eq_single C.gen h hi hj

theorem gu6_cp0_mp : crossingPoint (xPair π.X₀_cross_mp) = crossingPoint (xPair C.hmp) :=
  gu6_common_eq C.hmp (π.gu6_seg_mB_sub (crossingPoint_mem _ _ (mem_pair_left _ _)))
    (by rw [← gu6_seg_p']; exact crossingPoint_mem _ _ (mem_pair_right _ _))
theorem gu6_cp0_mq : crossingPoint (xPair π.X₀_cross_mq) = crossingPoint (xPair C.hmq) :=
  gu6_common_eq C.hmq (π.gu6_seg_mC_sub (crossingPoint_mem _ _ (mem_pair_left _ _)))
    (by rw [← gu6_seg_q']; exact crossingPoint_mem _ _ (mem_pair_right _ _))
theorem gu6_cp0_pq : crossingPoint (xPair π.X₀_cross_pq) = crossingPoint (xPair C.hpq) :=
  gu6_common_eq C.hpq (by rw [← gu6_seg_p']; exact crossingPoint_mem _ _ (mem_pair_left _ _))
    (by rw [← gu6_seg_q']; exact crossingPoint_mem _ _ (mem_pair_right _ _))
theorem gu6_cp1_pq : crossingPoint (xPair π.X₁_cross_pq) = crossingPoint (xPair C.hpq) :=
  gu6_common_eq C.hpq (by rw [← gu6_seg_X₁_p']; exact crossingPoint_mem _ _ (mem_pair_left _ _))
    (by rw [← gu6_seg_X₁_q']; exact crossingPoint_mem _ _ (mem_pair_right _ _))

/-- the parameter of `x_pq` on `p'` (resp. `q'`) is the same on both sides -/
theorem gu6_s'_pq_eq : π.gu6_s'_pq = π.gu6_s_pq := by
  apply edgePoint_injective (π.gu6_edge_X₀_ne_zero π.p')
  have h1 := π.gu6_s'_pq_spec
  have h2 := π.gu6_s_pq_spec
  rw [gu6_cp1_pq] at h1
  rw [gu6_cp0_pq] at h2
  have he : edgePoint π.X₁ π.p' π.gu6_s'_pq = edgePoint π.X₀ π.p' π.gu6_s'_pq := by
    rw [gu6_edgePoint_X₁_p', gu6_edgePoint_X₀_p']
  rw [← he, ← h1, h2]
theorem gu6_s'_qp_eq : π.gu6_s'_qp = π.gu6_s_qp := by
  apply edgePoint_injective (π.gu6_edge_X₀_ne_zero π.q')
  have h1 := π.gu6_s'_qp_spec
  have h2 := π.gu6_s_qp_spec
  rw [gu6_cp1_pq] at h1
  rw [gu6_cp0_pq] at h2
  have he : edgePoint π.X₁ π.q' π.gu6_s'_qp = edgePoint π.X₀ π.q' π.gu6_s'_qp := by
    rw [gu6_edgePoint_X₁_q', gu6_edgePoint_X₀_q']
  rw [← he, ← h1, h2]

/-! #### U6 helpers for D8 (e): the reversal along `p` and `q` (D9) and the over strands -/


/-- the base parameters of the two crossings of `m` -/
noncomputable def gu6_a : ℝ := crossingParameter (xPair C.hmp) C.m (mem_pair_left _ _)
noncomputable def gu6_b : ℝ := crossingParameter (xPair C.hmq) C.m (mem_pair_left _ _)
theorem gu6_a_spec : crossingPoint (xPair C.hmp) = edgePoint C.X C.m (gu6_a (C := C)) :=
  (crossingParameter_spec _ _ _).2.2
theorem gu6_b_spec : crossingPoint (xPair C.hmq) = edgePoint C.X C.m (gu6_b (C := C)) :=
  (crossingParameter_spec _ _ _).2.2
theorem gu6_a_lt : gu6_a (C := C) < π.t₂ := π.h₂
theorem gu6_t₁_lt_a : π.t₁ < gu6_a (C := C) := π.h₁
theorem gu6_t₂_lt_b : π.t₂ < gu6_b (C := C) := π.h₃
theorem gu6_b_lt : gu6_b (C := C) < π.t₃ := π.h₄

/-- **D9 along `p`**: `x_pq` lies strictly between `x_mp` and `x_mp'` on `p'`. -/
theorem gu6_D9_p : π.gu6_s_pm < π.gu6_s_pq ↔ π.gu6_s_pq < π.gu6_s'_pC := by
  have hs₁ : C.X C.p + π.gu6_s_pm • edge C.X C.p = C.X C.m + gu6_a (C := C) • edge C.X C.m := by
    have h := π.gu6_s_pm_spec
    rw [gu6_cp0_mp, gu6_edgePoint_X₀_p', gu6_a_spec] at h
    exact h.symm
  have hs₂ : C.X C.p + π.gu6_s_pq • edge C.X C.p = crossingPoint (xPair C.hpq) := by
    have h := π.gu6_s_pq_spec
    rw [gu6_cp0_pq, gu6_edgePoint_X₀_p'] at h
    exact h.symm
  have hs₃ : C.X C.p + π.gu6_s'_pC • edge C.X C.p =
      (C.X C.m + π.t₂ • edge C.X C.m + π.lam • (crossingPoint (xPair C.hpq) - (C.X C.m + π.t₂ • edge C.X C.m))) +
      π.gu6_s'_Cp • ((C.X C.m + π.t₃ • edge C.X C.m) -
        (C.X C.m + π.t₂ • edge C.X C.m + π.lam • (crossingPoint (xPair C.hpq) - (C.X C.m + π.t₂ • edge C.X C.m)))) := by
    have h := π.gu6_s'_pC_spec
    rw [gu6_edgePoint_X₁_p'] at h
    have h' := π.gu6_s'_Cp_spec
    rw [edgePoint, edge, gu6_mC_add_one, gu6_X₁_mD, gu6_X₁_mC] at h'
    rw [edgePoint] at h
    rw [← h, h']
    rfl
  exact gu6_D9_core_p (C.X C.m) (C.X C.p) (edge C.X C.m) (edge C.X C.p) (crossingPoint (xPair C.hpq))
    (gu6_a (C := C)) π.t₂ π.t₃ π.lam π.gu6_s'_Cp _ _ _ (gu6_det_ne_zero_single C.gen C.hmp) π.gu6_a_lt
    π.gu6_t₂_lt_t₃ π.hlam π.gu6_s'_Cp_pos.le hs₁ hs₂ hs₃

/-- **D9 along `q`**: `x_pq` lies strictly between `x_mq` and `x_mq'` on `q'`. -/
theorem gu6_D9_q : π.gu6_s_qm < π.gu6_s_qp ↔ π.gu6_s_qp < π.gu6_s'_qB := by
  have hs₁ : C.X C.q + π.gu6_s_qm • edge C.X C.q = C.X C.m + gu6_b (C := C) • edge C.X C.m := by
    have h := π.gu6_s_qm_spec
    rw [gu6_cp0_mq, gu6_edgePoint_X₀_q', gu6_b_spec] at h
    exact h.symm
  have hs₂ : C.X C.q + π.gu6_s_qp • edge C.X C.q = crossingPoint (xPair C.hpq) := by
    have h := π.gu6_s_qp_spec
    rw [gu6_cp0_pq, gu6_edgePoint_X₀_q'] at h
    exact h.symm
  have hs₃ : C.X C.q + π.gu6_s'_qB • edge C.X C.q = (C.X C.m + π.t₁ • edge C.X C.m) +
      π.gu6_s'_Bq • ((C.X C.m + π.t₂ • edge C.X C.m + π.lam • (crossingPoint (xPair C.hpq) - (C.X C.m + π.t₂ • edge C.X C.m))) -
        (C.X C.m + π.t₁ • edge C.X C.m)) := by
    have h := π.gu6_s'_qB_spec
    rw [gu6_edgePoint_X₁_q'] at h
    have h' := π.gu6_s'_Bq_spec
    rw [edgePoint, edge, gu6_mB_add_one, gu6_X₁_mC, gu6_X₁_mB] at h'
    rw [edgePoint] at h
    rw [← h, h']
    rfl
  exact gu6_D9_core_q (C.X C.m) (C.X C.q) (edge C.X C.m) (edge C.X C.q) (crossingPoint (xPair C.hpq))
    (gu6_b (C := C)) π.t₁ π.t₂ π.lam π.gu6_s'_Bq _ _ _ (gu6_det_ne_zero_single C.gen C.hmq) π.gu6_t₂_lt_b
    π.gu6_t₁_lt_t₂ π.hlam π.gu6_s'_Bq_lt_one.le hs₁ hs₂ hs₃

/-! #### U6 helpers for D8 (f): the arcs of `M₀` and `M₁` inside `U` -/

theorem gu6_U_convex : Convex ℝ π.U := π.disc_isDisc.convex
theorem gu6_U_closed : IsClosed π.U := π.disc_isDisc.isCompact.isClosed

/-! evaluation and vertex facts on the two shadows -/

theorem gu6_eval₀ (i : Fin 1) (r : TraversalPoint (k + 3)) :
    π.M₀.Γ.eval ⟨i, r⟩ = edgePoint π.X₀ r.1 r.2.val := rfl
theorem gu6_eval₁ (i : Fin 1) (r : TraversalPoint (k + 3)) :
    π.M₁.Γ.eval ⟨i, r⟩ = edgePoint π.X₁ r.1 r.2.val := rfl

theorem gu6_X₀_mA_not_mem : π.X₀ π.mA ∉ π.U :=
  π.gu6_X₀_vertex_not_mem _ π.gu6_mA_ne_mB π.gu6_mA_ne_mC π.gu6_mA_ne_mD
theorem gu6_X₀_p'_not_mem : π.X₀ π.p' ∉ π.U :=
  π.gu6_X₀_vertex_not_mem _ (π.gu6_lab_ne_mB _) (π.gu6_lab_ne_mC _) (π.gu6_lab_ne_mD _)
theorem gu6_X₀_q'_not_mem : π.X₀ π.q' ∉ π.U :=
  π.gu6_X₀_vertex_not_mem _ (π.gu6_lab_ne_mB _) (π.gu6_lab_ne_mC _) (π.gu6_lab_ne_mD _)

theorem gu6_edgePoint_mB_interior (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    edgePoint π.X₀ π.mB θ ∈ interior π.U :=
  π.gu6_Θ_sub_interior (π.gu6_seg_mB_sub_Θ ⟨θ, h0, h1, rfl⟩)
theorem gu6_edgePoint_mC_interior (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    edgePoint π.X₀ π.mC θ ∈ interior π.U :=
  π.gu6_Θ_sub_interior (π.gu6_seg_mC_sub_Θ ⟨θ, h0, h1, rfl⟩)
theorem gu6_edgePoint_X₁_mB_interior (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    edgePoint π.X₁ π.mB θ ∈ interior π.U :=
  π.gu6_Θ_sub_interior (π.gu6_seg_X₁_mB_sub_Θ ⟨θ, h0, h1, rfl⟩)
theorem gu6_edgePoint_X₁_mC_interior (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    edgePoint π.X₁ π.mC θ ∈ interior π.U :=
  π.gu6_Θ_sub_interior (π.gu6_seg_X₁_mC_sub_Θ ⟨θ, h0, h1, rfl⟩)

theorem gu6_p'_val : π.p'.val < C.m.val ∨ C.m.val + 3 < π.p'.val := by
  have h := gu6_lab_val C.m C.p
  have hpm : C.p.val ≠ C.m.val := fun h' => gu6_p_ne_m (C := C) (ZMod.val_injective k h')
  change (G11_lab C.m C.p).val < C.m.val ∨ C.m.val + 3 < (G11_lab C.m C.p).val
  rw [h]
  split_ifs with hle
  · left; omega
  · right; omega
theorem gu6_q'_val : π.q'.val < C.m.val ∨ C.m.val + 3 < π.q'.val := by
  have h := gu6_lab_val C.m C.q
  have hqm : C.q.val ≠ C.m.val := fun h' => gu6_q_ne_m (C := C) (ZMod.val_injective k h')
  change (G11_lab C.m C.q).val < C.m.val ∨ C.m.val + 3 < (G11_lab C.m C.q).val
  rw [h]
  split_ifs with hle
  · left; omega
  · right; omega
theorem gu6_p'_ne_q' : π.p' ≠ π.q' := by
  intro h
  have h' := congrArg ZMod.val h
  change (G11_lab C.m C.p).val = (G11_lab C.m C.q).val at h'
  rw [gu6_lab_val, gu6_lab_val] at h'
  have hpq : C.p.val ≠ C.q.val := fun e => gu6_p_ne_q (C := C) (ZMod.val_injective k e)
  split_ifs at h' <;> omega

/-! the crossing points of the local occurrences lie in the open disc -/

theorem gu6_xmp_mem_Δ : crossingPoint (xPair C.hmp) ∈ G11_triangle C.X C.hmp C.hmq C.hpq :=
  subset_convexHull ℝ _ (by simp)
theorem gu6_xmq_mem_Δ : crossingPoint (xPair C.hmq) ∈ G11_triangle C.X C.hmp C.hmq C.hpq :=
  subset_convexHull ℝ _ (by simp)
theorem gu6_xpq_mem_Δ : crossingPoint (xPair C.hpq) ∈ G11_triangle C.X C.hmp C.hmq C.hpq :=
  subset_convexHull ℝ _ (by simp)

/-- points of `p` between `x_mp` and `x_pq` lie in the open disc -/
theorem gu6_p_between_interior {θ : ℝ}
    (hθ : (π.gu6_s_pm ≤ θ ∧ θ ≤ π.gu6_s_pq) ∨ (π.gu6_s_pq ≤ θ ∧ θ ≤ π.gu6_s_pm)) :
    edgePoint C.X C.p θ ∈ interior π.U := by
  apply π.triangle_sub_interior
  have h1 : edgePoint C.X C.p π.gu6_s_pm ∈ G11_triangle C.X C.hmp C.hmq C.hpq := by
    rw [← gu6_edgePoint_X₀_p', ← gu6_s_pm_spec, gu6_cp0_mp]; exact gu6_xmp_mem_Δ (C := C)
  have h2 : edgePoint C.X C.p π.gu6_s_pq ∈ G11_triangle C.X C.hmp C.hmq C.hpq := by
    rw [← gu6_edgePoint_X₀_p', ← gu6_s_pq_spec, gu6_cp0_pq]; exact gu6_xpq_mem_Δ (C := C)
  rcases eq_or_ne π.gu6_s_pm π.gu6_s_pq with heq | hne
  · have : θ = π.gu6_s_pm := by rcases hθ with ⟨h, h'⟩ | ⟨h, h'⟩ <;> linarith
    rw [this]; exact h1
  rw [gu6_edgePoint_comb C.X C.p hne θ]
  refine (convex_convexHull ℝ _).add_smul_sub_mem h1 h2 ⟨?_, ?_⟩
  · rcases hθ with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact div_nonneg (by linarith) (by linarith)
    · rw [← neg_sub π.gu6_s_pm θ, ← neg_sub π.gu6_s_pm π.gu6_s_pq, neg_div_neg_eq]
      exact div_nonneg (by linarith) (by linarith)
  · rcases hθ with ⟨h, h'⟩ | ⟨h, h'⟩
    · have hlt : π.gu6_s_pm < π.gu6_s_pq := lt_of_le_of_ne (by linarith) hne
      exact (div_le_one (by linarith)).mpr (by linarith)
    · have hlt : π.gu6_s_pq < π.gu6_s_pm := lt_of_le_of_ne (by linarith) hne.symm
      rw [← neg_sub π.gu6_s_pm θ, ← neg_sub π.gu6_s_pm π.gu6_s_pq, neg_div_neg_eq]
      exact (div_le_one (by linarith)).mpr (by linarith)

theorem gu6_q_between_interior {θ : ℝ}
    (hθ : (π.gu6_s_qm ≤ θ ∧ θ ≤ π.gu6_s_qp) ∨ (π.gu6_s_qp ≤ θ ∧ θ ≤ π.gu6_s_qm)) :
    edgePoint C.X C.q θ ∈ interior π.U := by
  apply π.triangle_sub_interior
  have h1 : edgePoint C.X C.q π.gu6_s_qm ∈ G11_triangle C.X C.hmp C.hmq C.hpq := by
    rw [← gu6_edgePoint_X₀_q', ← gu6_s_qm_spec, gu6_cp0_mq]; exact gu6_xmq_mem_Δ (C := C)
  have h2 : edgePoint C.X C.q π.gu6_s_qp ∈ G11_triangle C.X C.hmp C.hmq C.hpq := by
    rw [← gu6_edgePoint_X₀_q', ← gu6_s_qp_spec, gu6_cp0_pq]; exact gu6_xpq_mem_Δ (C := C)
  rcases eq_or_ne π.gu6_s_qm π.gu6_s_qp with heq | hne
  · have : θ = π.gu6_s_qm := by rcases hθ with ⟨h, h'⟩ | ⟨h, h'⟩ <;> linarith
    rw [this]; exact h1
  rw [gu6_edgePoint_comb C.X C.q hne θ]
  refine (convex_convexHull ℝ _).add_smul_sub_mem h1 h2 ⟨?_, ?_⟩
  · rcases hθ with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact div_nonneg (by linarith) (by linarith)
    · rw [← neg_sub π.gu6_s_qm θ, ← neg_sub π.gu6_s_qm π.gu6_s_qp, neg_div_neg_eq]
      exact div_nonneg (by linarith) (by linarith)
  · rcases hθ with ⟨h, h'⟩ | ⟨h, h'⟩
    · have hlt : π.gu6_s_qm < π.gu6_s_qp := lt_of_le_of_ne (by linarith) hne
      exact (div_le_one (by linarith)).mpr (by linarith)
    · have hlt : π.gu6_s_qp < π.gu6_s_qm := lt_of_le_of_ne (by linarith) hne.symm
      rw [← neg_sub π.gu6_s_qm θ, ← neg_sub π.gu6_s_qm π.gu6_s_qp, neg_div_neg_eq]
      exact (div_le_one (by linarith)).mpr (by linarith)

theorem gu6_xpq_interior : crossingPoint (xPair C.hpq) ∈ interior π.U :=
  π.triangle_sub_interior (gu6_xpq_mem_Δ (C := C))
theorem gu6_xmp_interior : crossingPoint (xPair C.hmp) ∈ interior π.U :=
  π.triangle_sub_interior (gu6_xmp_mem_Δ (C := C))
theorem gu6_xmq_interior : crossingPoint (xPair C.hmq) ∈ interior π.U :=
  π.triangle_sub_interior (gu6_xmq_mem_Δ (C := C))
theorem gu6_xpC_interior : crossingPoint (xPair π.X₁_cross_pC) ∈ interior π.U := by
  rw [gu6_s'_Cp_spec]; exact π.gu6_edgePoint_X₁_mC_interior _ π.gu6_s'_Cp_pos.le π.gu6_s'_Cp_lt_one.le
theorem gu6_xqB_interior : crossingPoint (xPair π.X₁_cross_qB) ∈ interior π.U := by
  rw [gu6_s'_Bq_spec]; exact π.gu6_edgePoint_X₁_mB_interior _ π.gu6_s'_Bq_pos.le π.gu6_s'_Bq_lt_one.le

/-! generic arc facts for a diagram -/

/-- an arc of `U` with inner points on two edges such that both cyclic paths between them pass
through a vertex outside `U`: impossible -/
theorem gu6_arc_ne_of_paths (A : π.M₀.Γ.Arc) (hA : π.M₀.Γ.IsArc π.U A) {r s : TraversalPoint (k + 3)}
    (hr : A.Inner ⟨A.i, r⟩) (hs : A.Inner ⟨A.i, s⟩) {zf zb : TraversalPoint (k + 3)}
    (hf : traversalBetween r zf s) (hzf : edgePoint π.X₀ zf.1 zf.2.val ∉ π.U)
    (hb : traversalBetween s zb r) (hzb : edgePoint π.X₀ zb.1 zb.2.val ∉ π.U) : False := by
  have hrs : r ≠ s := by
    rintro rfl
    exact not_cycBetween_self_right _ _ hf
  rcases gu6_arc_two_paths hr hs hrs with h | h
  · exact hzf (interior_subset (hA.inner_interior _ (h zf hf)))
  · exact hzb (interior_subset (hA.inner_interior _ (h zb hb)))

/-- rewriting statements about a visit's traversal point through `Fin 1` eta -/
theorem gu6_inner_pt₀ (A : π.M₀.Γ.Arc) (v : π.M₀.Γ.Visit) :
    A.Inner (π.M₀.visitPt v) ↔ A.Inner ⟨A.i, (π.M₀.visitPt v).2⟩ :=
  Iff.of_eq (congrArg A.Inner (gu6_single_pt_eta _ _))
theorem gu6_inner_pt₁ (A : π.M₁.Γ.Arc) (v : π.M₁.Γ.Visit) :
    A.Inner (π.M₁.visitPt v) ↔ A.Inner ⟨A.i, (π.M₁.visitPt v).2⟩ :=
  Iff.of_eq (congrArg A.Inner (gu6_single_pt_eta _ _))
theorem gu6_mem_pt₀ (A : π.M₀.Γ.Arc) (v : π.M₀.Γ.Visit) :
    A.Mem (π.M₀.visitPt v) ↔ A.Mem ⟨A.i, (π.M₀.visitPt v).2⟩ :=
  Iff.of_eq (congrArg A.Mem (gu6_single_pt_eta _ _))
theorem gu6_mem_pt₁ (A : π.M₁.Γ.Arc) (v : π.M₁.Γ.Visit) :
    A.Mem (π.M₁.visitPt v) ↔ A.Mem ⟨A.i, (π.M₁.visitPt v).2⟩ :=
  Iff.of_eq (congrArg A.Mem (gu6_single_pt_eta _ _))
theorem gu6_before_pt₀ (A : π.M₀.Γ.Arc) (v w : π.M₀.Γ.Visit) :
    A.Before (π.M₀.visitPt v) (π.M₀.visitPt w) ↔
      A.Before ⟨A.i, (π.M₀.visitPt v).2⟩ ⟨A.i, (π.M₀.visitPt w).2⟩ :=
  Iff.of_eq (congrArg₂ A.Before (gu6_single_pt_eta _ _) (gu6_single_pt_eta _ _))
theorem gu6_before_pt₁ (A : π.M₁.Γ.Arc) (v w : π.M₁.Γ.Visit) :
    A.Before (π.M₁.visitPt v) (π.M₁.visitPt w) ↔
      A.Before ⟨A.i, (π.M₁.visitPt v).2⟩ ⟨A.i, (π.M₁.visitPt w).2⟩ :=
  Iff.of_eq (congrArg₂ A.Before (gu6_single_pt_eta _ _) (gu6_single_pt_eta _ _))

/-! path lemmas over `TraversalPoint (k + 3)` (the arc API states its points at the definitionally
equal type `TraversalPoint (Γ.comp a.i).k`; the lemmas below are applied by `exact`) -/

theorem gu6_path_mB_mC (z : TraversalPoint (k + 3))
    (hz : traversalBetween (π.mB, ⟨π.gu6_s_mp, π.gu6_s_mp_pos.le, π.gu6_s_mp_lt_one⟩) z
      (π.mC, ⟨π.gu6_s_mq, π.gu6_s_mq_pos.le, π.gu6_s_mq_lt_one⟩)) :
    edgePoint π.X₀ z.1 z.2.val ∈ interior π.U := by
  rw [gu6_tb_span_one π.mB π.mC (by rw [gu6_mB_val, gu6_mC_val])] at hz
  rcases hz with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h1]; exact π.gu6_edgePoint_mB_interior _ z.2.2.1 z.2.2.2.le
  · rw [h1]; exact π.gu6_edgePoint_mC_interior _ z.2.2.1 z.2.2.2.le

theorem gu6_path_p_fwd (hlt : π.gu6_s_pm < π.gu6_s_pq) (z : TraversalPoint (k + 3))
    (hz : traversalBetween (π.p', ⟨π.gu6_s_pm, π.gu6_s_pm_pos.le, π.gu6_s_pm_lt_one⟩) z
      (π.p', ⟨π.gu6_s_pq, π.gu6_s_pq_pos.le, π.gu6_s_pq_lt_one⟩)) :
    edgePoint π.X₀ z.1 z.2.val ∈ interior π.U := by
  rw [gu6_tb_same_edge π.p' _ _ hlt] at hz
  obtain ⟨h1, h2, h3⟩ := hz
  rw [h1, gu6_edgePoint_X₀_p']
  exact π.gu6_p_between_interior (Or.inl ⟨h2.le, h3.le⟩)

theorem gu6_path_p_bwd (hgt : π.gu6_s_pq < π.gu6_s_pm) (z : TraversalPoint (k + 3))
    (hz : traversalBetween (π.p', ⟨π.gu6_s_pq, π.gu6_s_pq_pos.le, π.gu6_s_pq_lt_one⟩) z
      (π.p', ⟨π.gu6_s_pm, π.gu6_s_pm_pos.le, π.gu6_s_pm_lt_one⟩)) :
    edgePoint π.X₀ z.1 z.2.val ∈ interior π.U := by
  rw [gu6_tb_same_edge π.p' _ _ hgt] at hz
  obtain ⟨h1, h2, h3⟩ := hz
  rw [h1, gu6_edgePoint_X₀_p']
  exact π.gu6_p_between_interior (Or.inr ⟨h2.le, h3.le⟩)

theorem gu6_path_q_fwd (hlt : π.gu6_s_qm < π.gu6_s_qp) (z : TraversalPoint (k + 3))
    (hz : traversalBetween (π.q', ⟨π.gu6_s_qm, π.gu6_s_qm_pos.le, π.gu6_s_qm_lt_one⟩) z
      (π.q', ⟨π.gu6_s_qp, π.gu6_s_qp_pos.le, π.gu6_s_qp_lt_one⟩)) :
    edgePoint π.X₀ z.1 z.2.val ∈ interior π.U := by
  rw [gu6_tb_same_edge π.q' _ _ hlt] at hz
  obtain ⟨h1, h2, h3⟩ := hz
  rw [h1, gu6_edgePoint_X₀_q']
  exact π.gu6_q_between_interior (Or.inl ⟨h2.le, h3.le⟩)

theorem gu6_path_q_bwd (hgt : π.gu6_s_qp < π.gu6_s_qm) (z : TraversalPoint (k + 3))
    (hz : traversalBetween (π.q', ⟨π.gu6_s_qp, π.gu6_s_qp_pos.le, π.gu6_s_qp_lt_one⟩) z
      (π.q', ⟨π.gu6_s_qm, π.gu6_s_qm_pos.le, π.gu6_s_qm_lt_one⟩)) :
    edgePoint π.X₀ z.1 z.2.val ∈ interior π.U := by
  rw [gu6_tb_same_edge π.q' _ _ hgt] at hz
  obtain ⟨h1, h2, h3⟩ := hz
  rw [h1, gu6_edgePoint_X₀_q']
  exact π.gu6_q_between_interior (Or.inr ⟨h2.le, h3.le⟩)

theorem gu6_decode_start_m (r : TraversalPoint (k + 3))
    (hb : traversalBetween (π.mA, ⟨0, le_rfl, zero_lt_one⟩) r
      (π.mB, ⟨π.gu6_s_mp, π.gu6_s_mp_pos.le, π.gu6_s_mp_lt_one⟩))
    (hfr : edgePoint π.X₀ r.1 r.2.val ∉ interior π.U) :
    ∃ θ : Set.Ico (0:ℝ) 1, 0 < θ.val ∧ r = (π.mA, θ) := by
  rw [gu6_tb_span_one π.mA π.mB (by rw [gu6_mA_val, gu6_mB_val])] at hb
  rcases hb with ⟨h1, h2⟩ | ⟨h1, -⟩
  · exact ⟨r.2, h2, Prod.ext h1 rfl⟩
  · exfalso
    apply hfr
    rw [h1]
    exact π.gu6_edgePoint_mB_interior _ r.2.2.1 r.2.2.2.le

theorem gu6_path_M₁_mA (θ : Set.Ico (0:ℝ) 1) (hfr : edgePoint π.X₁ π.mA θ.val ∈ π.U)
    (z : TraversalPoint (k + 3)) (h1 : z.1 = π.mA) (h2 : θ.val < z.2.val) :
    edgePoint π.X₁ z.1 z.2.val ∈ interior π.U := by
  have hin : edgePoint π.X₁ π.mA 1 ∈ interior π.U := by
    have : edgePoint π.X₁ π.mA 1 = edgePoint π.X₁ π.mB 0 := by
      simp only [edgePoint, edge, gu6_mA_add_one, one_smul, zero_smul, add_zero]; abel
    rw [this]; exact π.gu6_edgePoint_X₁_mB_interior 0 le_rfl zero_le_one
  rw [h1]
  exact gu6_edge_interior_of_convex π.gu6_U_convex π.X₁ π.mA hfr hin (Or.inl ⟨h2, z.2.2.2.le⟩)

theorem gu6_path_M₁_m_B (θ : Set.Ico (0:ℝ) 1) (hfr : edgePoint π.X₁ π.mA θ.val ∈ π.U)
    (z : TraversalPoint (k + 3))
    (hz : traversalBetween (π.mA, θ) z (π.mB, ⟨π.gu6_s'_Bq, π.gu6_s'_Bq_pos.le, π.gu6_s'_Bq_lt_one⟩)) :
    edgePoint π.X₁ z.1 z.2.val ∈ interior π.U := by
  rw [gu6_tb_span_one π.mA π.mB (by rw [gu6_mA_val, gu6_mB_val])] at hz
  rcases hz with ⟨h1, h2⟩ | ⟨h1, -⟩
  · exact π.gu6_path_M₁_mA θ hfr z h1 h2
  · rw [h1]; exact π.gu6_edgePoint_X₁_mB_interior _ z.2.2.1 z.2.2.2.le

theorem gu6_path_M₁_m_C (θ : Set.Ico (0:ℝ) 1) (hfr : edgePoint π.X₁ π.mA θ.val ∈ π.U)
    (z : TraversalPoint (k + 3))
    (hz : traversalBetween (π.mA, θ) z (π.mC, ⟨π.gu6_s'_Cp, π.gu6_s'_Cp_pos.le, π.gu6_s'_Cp_lt_one⟩)) :
    edgePoint π.X₁ z.1 z.2.val ∈ interior π.U := by
  rw [gu6_tb_span_two π.mA π.mB π.mC (by rw [gu6_mA_val, gu6_mB_val]) (by rw [gu6_mB_val, gu6_mC_val])] at hz
  rcases hz with ⟨h1, h2⟩ | h1 | ⟨h1, -⟩
  · exact π.gu6_path_M₁_mA θ hfr z h1 h2
  · rw [h1]; exact π.gu6_edgePoint_X₁_mB_interior _ z.2.2.1 z.2.2.2.le
  · rw [h1]; exact π.gu6_edgePoint_X₁_mC_interior _ z.2.2.1 z.2.2.2.le

theorem gu6_path_M₁_same (j : ZMod (k + 3)) (θ s : Set.Ico (0:ℝ) 1) (hfr : edgePoint π.X₁ j θ.val ∈ π.U)
    (hs : edgePoint π.X₁ j s.val ∈ interior π.U) (hθ : θ.val < s.val) (z : TraversalPoint (k + 3))
    (hz : traversalBetween (j, θ) z (j, s)) : edgePoint π.X₁ z.1 z.2.val ∈ interior π.U := by
  rw [gu6_tb_same_edge j _ _ hθ] at hz
  obtain ⟨h1, h2, h3⟩ := hz
  rw [h1]
  exact gu6_edge_interior_of_convex π.gu6_U_convex π.X₁ j hfr hs (Or.inl ⟨h2, h3.le⟩)

/-! the `M₀` arcs: start location, the second inner point, distinctness -/

/-- an arc of `U` with an inner point on the edge `j` whose tail vertex is outside `U` starts on `j`,
strictly before that point -/
theorem gu6_arc_start_same_edge (A : π.M₀.Γ.Arc) (hA : π.M₀.Γ.IsArc π.U A) {j : ZMod (k + 3)}
    (hj : π.X₀ j ∉ π.U) {s : Set.Ico (0:ℝ) 1} (hr : A.Inner ⟨A.i, (j, s)⟩) :
    ∃ θ : Set.Ico (0:ℝ) 1, 0 < θ.val ∧ θ.val < s.val ∧ A.start = (j, θ) := by
  have hz : π.M₀.Γ.eval ⟨A.i, (j, ⟨0, le_rfl, zero_lt_one⟩)⟩ ∉ π.U := by
    show edgePoint π.X₀ j 0 ∉ π.U
    rw [edgePoint_zero]; exact hj
  have hb := gu6_arc_start_between hA π.gu6_U_closed hr hz
  have hs0 : (0 : ℝ) < s.val := by
    rcases s.2.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have : A.Inner ⟨A.i, (j, ⟨0, le_rfl, zero_lt_one⟩)⟩ := by
        convert hr using 3
        exact Subtype.ext h
      exact hz (interior_subset (hA.inner_interior _ this))
  exact gu6_decode_start_same j s hs0 A.start hb

/-- an arc starting on the edge `j` (with tail outside `U`) at `θ₀` has its inner points of `j` after
`θ₀` -/
theorem gu6_arc_start_lt (A : π.M₀.Γ.Arc) (hA : π.M₀.Γ.IsArc π.U A) {j : ZMod (k + 3)}
    (hj : π.X₀ j ∉ π.U) {θ₀ : Set.Ico (0:ℝ) 1} (hstart : A.start = (j, θ₀)) {s : Set.Ico (0:ℝ) 1}
    (hr : A.Inner ⟨A.i, (j, s)⟩) : θ₀.val < s.val := by
  obtain ⟨θ, -, h2, h3⟩ := π.gu6_arc_start_same_edge A hA hj hr
  rw [hstart] at h3
  have := congrArg Prod.snd h3
  simp only at this
  rw [this]; exact h2

/-- the `m`-arc starts on `mA` -/
theorem gu6_arc_m_start (A : π.M₀.Γ.Arc) (hA : π.M₀.Γ.IsArc π.U A)
    (hr : A.Inner ⟨A.i, (π.mB, ⟨π.gu6_s_mp, π.gu6_s_mp_pos.le, π.gu6_s_mp_lt_one⟩)⟩) :
    ∃ θ : Set.Ico (0:ℝ) 1, 0 < θ.val ∧ A.start = (π.mA, θ) := by
  have hz : π.M₀.Γ.eval ⟨A.i, (π.mA, ⟨0, le_rfl, zero_lt_one⟩)⟩ ∉ π.U := by
    show edgePoint π.X₀ π.mA 0 ∉ π.U
    rw [edgePoint_zero]; exact π.gu6_X₀_mA_not_mem
  have hb := gu6_arc_start_between hA π.gu6_U_closed hr hz
  exact π.gu6_decode_start_m A.start hb hA.start_frontier.2

/-- the `m`-arc through `x_mp` on `mB` contains `x_mq` on `mC` -/
theorem gu6_arc_m_inner_mC (A : π.M₀.Γ.Arc) (hA : π.M₀.Γ.IsArc π.U A)
    (hr : A.Inner ⟨A.i, (π.mB, ⟨π.gu6_s_mp, π.gu6_s_mp_pos.le, π.gu6_s_mp_lt_one⟩)⟩) :
    A.Inner ⟨A.i, (π.mC, ⟨π.gu6_s_mq, π.gu6_s_mq_pos.le, π.gu6_s_mq_lt_one⟩)⟩ := by
  refine gu6_arc_inner_of_path_fwd hA hr (s := (π.mC, ⟨π.gu6_s_mq, π.gu6_s_mq_pos.le, π.gu6_s_mq_lt_one⟩))
    (π.gu6_edgePoint_mC_interior _ π.gu6_s_mq_pos.le π.gu6_s_mq_lt_one.le) ?_
  intro z hz
  exact π.gu6_path_mB_mC z hz

/-- the `p`-arc through `x_mp` on `p'` contains `x_pq` -/
theorem gu6_arc_p_inner_pq (A : π.M₀.Γ.Arc) (hA : π.M₀.Γ.IsArc π.U A)
    (hr : A.Inner ⟨A.i, (π.p', ⟨π.gu6_s_pm, π.gu6_s_pm_pos.le, π.gu6_s_pm_lt_one⟩)⟩) :
    A.Inner ⟨A.i, (π.p', ⟨π.gu6_s_pq, π.gu6_s_pq_pos.le, π.gu6_s_pq_lt_one⟩)⟩ := by
  have hin : edgePoint π.X₀ π.p' π.gu6_s_pq ∈ interior π.U := by
    rw [← gu6_s_pq_spec, gu6_cp0_pq]; exact π.gu6_xpq_interior
  rcases lt_trichotomy π.gu6_s_pm π.gu6_s_pq with hlt | heq | hgt
  · exact gu6_arc_inner_of_path_fwd hA hr
      (s := (π.p', ⟨π.gu6_s_pq, π.gu6_s_pq_pos.le, π.gu6_s_pq_lt_one⟩)) hin
      (fun z hz => π.gu6_path_p_fwd hlt z hz)
  · have : (⟨π.gu6_s_pq, π.gu6_s_pq_pos.le, π.gu6_s_pq_lt_one⟩ : Set.Ico (0:ℝ) 1) =
        ⟨π.gu6_s_pm, π.gu6_s_pm_pos.le, π.gu6_s_pm_lt_one⟩ := Subtype.ext heq.symm
    rw [this]; exact hr
  · exact gu6_arc_inner_of_path_bwd hA hr
      (s := (π.p', ⟨π.gu6_s_pq, π.gu6_s_pq_pos.le, π.gu6_s_pq_lt_one⟩)) hin
      (fun z hz => π.gu6_path_p_bwd hgt z hz)

/-- the `q`-arc through `x_mq` on `q'` contains `x_pq` -/
theorem gu6_arc_q_inner_pq (A : π.M₀.Γ.Arc) (hA : π.M₀.Γ.IsArc π.U A)
    (hr : A.Inner ⟨A.i, (π.q', ⟨π.gu6_s_qm, π.gu6_s_qm_pos.le, π.gu6_s_qm_lt_one⟩)⟩) :
    A.Inner ⟨A.i, (π.q', ⟨π.gu6_s_qp, π.gu6_s_qp_pos.le, π.gu6_s_qp_lt_one⟩)⟩ := by
  have hin : edgePoint π.X₀ π.q' π.gu6_s_qp ∈ interior π.U := by
    rw [← gu6_s_qp_spec, gu6_cp0_pq]; exact π.gu6_xpq_interior
  rcases lt_trichotomy π.gu6_s_qm π.gu6_s_qp with hlt | heq | hgt
  · exact gu6_arc_inner_of_path_fwd hA hr
      (s := (π.q', ⟨π.gu6_s_qp, π.gu6_s_qp_pos.le, π.gu6_s_qp_lt_one⟩)) hin
      (fun z hz => π.gu6_path_q_fwd hlt z hz)
  · have : (⟨π.gu6_s_qp, π.gu6_s_qp_pos.le, π.gu6_s_qp_lt_one⟩ : Set.Ico (0:ℝ) 1) =
        ⟨π.gu6_s_qm, π.gu6_s_qm_pos.le, π.gu6_s_qm_lt_one⟩ := Subtype.ext heq.symm
    rw [this]; exact hr
  · exact gu6_arc_inner_of_path_bwd hA hr
      (s := (π.q', ⟨π.gu6_s_qp, π.gu6_s_qp_pos.le, π.gu6_s_qp_lt_one⟩)) hin
      (fun z hz => π.gu6_path_q_bwd hgt z hz)

/-- the three `M₀` arcs are distinct -/
theorem gu6_arc_m_ne_p (Am Ap : π.M₀.Γ.Arc) (hAm : π.M₀.Γ.IsArc π.U Am)
    (hm : Am.Inner ⟨Am.i, (π.mB, ⟨π.gu6_s_mp, π.gu6_s_mp_pos.le, π.gu6_s_mp_lt_one⟩)⟩)
    (hp : Ap.Inner ⟨Ap.i, (π.p', ⟨π.gu6_s_pm, π.gu6_s_pm_pos.le, π.gu6_s_pm_lt_one⟩)⟩) : Am ≠ Ap := by
  rintro rfl
  refine π.gu6_arc_ne_of_paths Am hAm hm hp (zf := (π.p', ⟨0, le_rfl, zero_lt_one⟩))
    (zb := (π.mA, ⟨0, le_rfl, zero_lt_one⟩)) ?_ ?_ ?_ ?_
  · exact gu6_tb_edge_start (π.gu6_lab_ne_mB C.p).symm _ _ π.gu6_s_pm_pos
  · show edgePoint π.X₀ π.p' 0 ∉ π.U
    rw [edgePoint_zero]; exact π.gu6_X₀_p'_not_mem
  · refine gu6_tb_vertex_between (by rw [gu6_mA_val, gu6_mB_val]; omega) ?_ _ _
    rw [gu6_mA_val, gu6_mB_val]
    rcases π.gu6_p'_val with h | h
    · left; exact h
    · right; omega
  · show edgePoint π.X₀ π.mA 0 ∉ π.U
    rw [edgePoint_zero]; exact π.gu6_X₀_mA_not_mem

theorem gu6_arc_m_ne_q (Am Aq : π.M₀.Γ.Arc) (hAm : π.M₀.Γ.IsArc π.U Am)
    (hm : Am.Inner ⟨Am.i, (π.mC, ⟨π.gu6_s_mq, π.gu6_s_mq_pos.le, π.gu6_s_mq_lt_one⟩)⟩)
    (hq : Aq.Inner ⟨Aq.i, (π.q', ⟨π.gu6_s_qm, π.gu6_s_qm_pos.le, π.gu6_s_qm_lt_one⟩)⟩) : Am ≠ Aq := by
  rintro rfl
  refine π.gu6_arc_ne_of_paths Am hAm hm hq (zf := (π.q', ⟨0, le_rfl, zero_lt_one⟩))
    (zb := (π.mA, ⟨0, le_rfl, zero_lt_one⟩)) ?_ ?_ ?_ ?_
  · exact gu6_tb_edge_start (π.gu6_lab_ne_mC C.q).symm _ _ π.gu6_s_qm_pos
  · show edgePoint π.X₀ π.q' 0 ∉ π.U
    rw [edgePoint_zero]; exact π.gu6_X₀_q'_not_mem
  · refine gu6_tb_vertex_between (by rw [gu6_mA_val, gu6_mC_val]; omega) ?_ _ _
    rw [gu6_mA_val, gu6_mC_val]
    rcases π.gu6_q'_val with h | h
    · left; exact h
    · right; omega
  · show edgePoint π.X₀ π.mA 0 ∉ π.U
    rw [edgePoint_zero]; exact π.gu6_X₀_mA_not_mem

theorem gu6_arc_p_ne_q (Ap Aq : π.M₀.Γ.Arc) (hAp : π.M₀.Γ.IsArc π.U Ap)
    (hp : Ap.Inner ⟨Ap.i, (π.p', ⟨π.gu6_s_pm, π.gu6_s_pm_pos.le, π.gu6_s_pm_lt_one⟩)⟩)
    (hq : Aq.Inner ⟨Aq.i, (π.q', ⟨π.gu6_s_qm, π.gu6_s_qm_pos.le, π.gu6_s_qm_lt_one⟩)⟩) : Ap ≠ Aq := by
  rintro rfl
  refine π.gu6_arc_ne_of_paths Ap hAp hp hq (zf := (π.q', ⟨0, le_rfl, zero_lt_one⟩))
    (zb := (π.p', ⟨0, le_rfl, zero_lt_one⟩)) ?_ ?_ ?_ ?_
  · exact gu6_tb_edge_start π.gu6_p'_ne_q' _ _ π.gu6_s_qm_pos
  · show edgePoint π.X₀ π.q' 0 ∉ π.U
    rw [edgePoint_zero]; exact π.gu6_X₀_q'_not_mem
  · exact gu6_tb_edge_start π.gu6_p'_ne_q'.symm _ _ π.gu6_s_pm_pos
  · show edgePoint π.X₀ π.p' 0 ∉ π.U
    rw [edgePoint_zero]; exact π.gu6_X₀_p'_not_mem

/-! the `M₁` arcs: the partner of an `M₀` arc has the same start, and contains the two local
occurrences of its strand -/

/-- the partner arc starts at the same traversal point (frontier injectivity of `M₁`) -/
theorem gu6_partner_start (A : π.M₀.Γ.Arc) (A' : π.M₁.Γ.Arc) (hA' : π.M₁.Γ.IsArc π.U A')
    (heq : π.M₁.Γ.eval A'.startPt = π.M₀.Γ.eval A.startPt) {j : ZMod (k + 3)} {θ : Set.Ico (0:ℝ) 1}
    (hstart : A.start = (j, θ)) (hj : edgePoint π.X₁ j θ.val = edgePoint π.X₀ j θ.val) :
    A'.start = (j, θ) := by
  have h1 : π.M₁.Γ.eval ⟨A'.i, (j, θ)⟩ = π.M₁.Γ.eval A'.startPt := by
    rw [heq]
    show edgePoint π.X₁ j θ.val = edgePoint π.X₀ A.start.1 A.start.2.val
    rw [hstart]; exact hj
  have hfr : π.M₁.Γ.eval A'.startPt ∈ frontier π.U := hA'.start_frontier
  have h2 := π.clean_M₁.frontier_injOn (show π.M₁.Γ.eval ⟨A'.i, (j, θ)⟩ ∈ frontier π.U by
    rw [h1]; exact hfr) hfr h1
  exact (eq_of_heq (Sigma.mk.inj_iff.mp h2).2).symm

theorem gu6_edgePoint_X₁_mA (θ : ℝ) : edgePoint π.X₁ π.mA θ = edgePoint π.X₀ π.mA θ := by
  simp only [edgePoint, edge, gu6_mA_add_one, gu6_X₁_mA, gu6_X₁_mB, gu6_X₀_mA, gu6_X₀_mB]

/-- the `M₁` arc starting on `mA` contains the two bent-strand occurrences -/
theorem gu6_M₁_inner_m (A' : π.M₁.Γ.Arc) (hA' : π.M₁.Γ.IsArc π.U A') {θ : Set.Ico (0:ℝ) 1}
    (hstart : A'.start = (π.mA, θ)) :
    A'.Inner ⟨A'.i, (π.mB, ⟨π.gu6_s'_Bq, π.gu6_s'_Bq_pos.le, π.gu6_s'_Bq_lt_one⟩)⟩ ∧
      A'.Inner ⟨A'.i, (π.mC, ⟨π.gu6_s'_Cp, π.gu6_s'_Cp_pos.le, π.gu6_s'_Cp_lt_one⟩)⟩ := by
  have hfr : edgePoint π.X₁ π.mA θ.val ∈ π.U := by
    have := π.gu6_U_closed.frontier_subset hA'.start_frontier
    change edgePoint π.X₁ A'.start.1 A'.start.2.val ∈ π.U at this
    rw [hstart] at this; exact this
  constructor
  · refine gu6_arc_inner_of_path_start hA'
      (s := (π.mB, ⟨π.gu6_s'_Bq, π.gu6_s'_Bq_pos.le, π.gu6_s'_Bq_lt_one⟩))
      (π.gu6_edgePoint_X₁_mB_interior _ π.gu6_s'_Bq_pos.le π.gu6_s'_Bq_lt_one.le) ?_
    intro z hz
    rw [hstart] at hz
    exact π.gu6_path_M₁_m_B θ hfr z hz
  · refine gu6_arc_inner_of_path_start hA'
      (s := (π.mC, ⟨π.gu6_s'_Cp, π.gu6_s'_Cp_pos.le, π.gu6_s'_Cp_lt_one⟩))
      (π.gu6_edgePoint_X₁_mC_interior _ π.gu6_s'_Cp_pos.le π.gu6_s'_Cp_lt_one.le) ?_
    intro z hz
    rw [hstart] at hz
    exact π.gu6_path_M₁_m_C θ hfr z hz

/-- the `M₁` arc starting on `p'` at `θ < s_pq` contains `x_pq` and `x_mp'` -/
theorem gu6_M₁_inner_p (A' : π.M₁.Γ.Arc) (hA' : π.M₁.Γ.IsArc π.U A') {θ : Set.Ico (0:ℝ) 1}
    (hstart : A'.start = (π.p', θ)) (hθ : θ.val < π.gu6_s_pq) :
    A'.Inner ⟨A'.i, (π.p', ⟨π.gu6_s'_pq, π.gu6_s'_pq_pos.le, π.gu6_s'_pq_lt_one⟩)⟩ ∧
      A'.Inner ⟨A'.i, (π.p', ⟨π.gu6_s'_pC, π.gu6_s'_pC_pos.le, π.gu6_s'_pC_lt_one⟩)⟩ ∧
      θ.val < π.gu6_s'_pC := by
  have hfr' : edgePoint π.X₁ π.p' θ.val ∈ frontier π.U := by
    have := hA'.start_frontier
    change edgePoint π.X₁ A'.start.1 A'.start.2.val ∈ frontier π.U at this
    rw [hstart] at this; exact this
  have hfr : edgePoint π.X₁ π.p' θ.val ∈ π.U := π.gu6_U_closed.frontier_subset hfr'
  have hpq_in : edgePoint π.X₁ π.p' π.gu6_s'_pq ∈ interior π.U := by
    rw [← gu6_s'_pq_spec, gu6_cp1_pq]; exact π.gu6_xpq_interior
  have hpC_in : edgePoint π.X₁ π.p' π.gu6_s'_pC ∈ interior π.U := by
    rw [← gu6_s'_pC_spec]; exact π.gu6_xpC_interior
  have hθ' : θ.val < π.gu6_s'_pq := by rw [gu6_s'_pq_eq]; exact hθ
  have hθC : θ.val < π.gu6_s'_pC := by
    by_contra hcon
    push Not at hcon
    rcases hcon.lt_or_eq with hlt | heq
    · exact hfr'.2 (gu6_edge_interior_of_convex' π.gu6_U_convex π.X₁ π.p' hpC_in hpq_in
        (Or.inl ⟨hlt.le, hθ'.le⟩))
    · rw [heq] at hpC_in
      exact hfr'.2 hpC_in
  refine ⟨?_, ?_, hθC⟩
  · refine gu6_arc_inner_of_path_start hA'
      (s := (π.p', ⟨π.gu6_s'_pq, π.gu6_s'_pq_pos.le, π.gu6_s'_pq_lt_one⟩)) hpq_in ?_
    intro z hz
    rw [hstart] at hz
    exact π.gu6_path_M₁_same π.p' θ _ hfr hpq_in hθ' z hz
  · refine gu6_arc_inner_of_path_start hA'
      (s := (π.p', ⟨π.gu6_s'_pC, π.gu6_s'_pC_pos.le, π.gu6_s'_pC_lt_one⟩)) hpC_in ?_
    intro z hz
    rw [hstart] at hz
    exact π.gu6_path_M₁_same π.p' θ _ hfr hpC_in hθC z hz

/-- the `M₁` arc starting on `q'` at `θ < s_qp` contains `x_pq` and `x_mq'` -/
theorem gu6_M₁_inner_q (A' : π.M₁.Γ.Arc) (hA' : π.M₁.Γ.IsArc π.U A') {θ : Set.Ico (0:ℝ) 1}
    (hstart : A'.start = (π.q', θ)) (hθ : θ.val < π.gu6_s_qp) :
    A'.Inner ⟨A'.i, (π.q', ⟨π.gu6_s'_qp, π.gu6_s'_qp_pos.le, π.gu6_s'_qp_lt_one⟩)⟩ ∧
      A'.Inner ⟨A'.i, (π.q', ⟨π.gu6_s'_qB, π.gu6_s'_qB_pos.le, π.gu6_s'_qB_lt_one⟩)⟩ ∧
      θ.val < π.gu6_s'_qB := by
  have hfr' : edgePoint π.X₁ π.q' θ.val ∈ frontier π.U := by
    have := hA'.start_frontier
    change edgePoint π.X₁ A'.start.1 A'.start.2.val ∈ frontier π.U at this
    rw [hstart] at this; exact this
  have hfr : edgePoint π.X₁ π.q' θ.val ∈ π.U := π.gu6_U_closed.frontier_subset hfr'
  have hqp_in : edgePoint π.X₁ π.q' π.gu6_s'_qp ∈ interior π.U := by
    rw [← gu6_s'_qp_spec, gu6_cp1_pq]; exact π.gu6_xpq_interior
  have hqB_in : edgePoint π.X₁ π.q' π.gu6_s'_qB ∈ interior π.U := by
    rw [← gu6_s'_qB_spec]; exact π.gu6_xqB_interior
  have hθ' : θ.val < π.gu6_s'_qp := by rw [gu6_s'_qp_eq]; exact hθ
  have hθB : θ.val < π.gu6_s'_qB := by
    by_contra hcon
    push Not at hcon
    rcases hcon.lt_or_eq with hlt | heq
    · exact hfr'.2 (gu6_edge_interior_of_convex' π.gu6_U_convex π.X₁ π.q' hqB_in hqp_in
        (Or.inl ⟨hlt.le, hθ'.le⟩))
    · rw [heq] at hqB_in
      exact hfr'.2 hqB_in
  refine ⟨?_, ?_, hθB⟩
  · refine gu6_arc_inner_of_path_start hA'
      (s := (π.q', ⟨π.gu6_s'_qp, π.gu6_s'_qp_pos.le, π.gu6_s'_qp_lt_one⟩)) hqp_in ?_
    intro z hz
    rw [hstart] at hz
    exact π.gu6_path_M₁_same π.q' θ _ hfr hqp_in hθ' z hz
  · refine gu6_arc_inner_of_path_start hA'
      (s := (π.q', ⟨π.gu6_s'_qB, π.gu6_s'_qB_pos.le, π.gu6_s'_qB_lt_one⟩)) hqB_in ?_
    intro z hz
    rw [hstart] at hz
    exact π.gu6_path_M₁_same π.q' θ _ hfr hqB_in hθB z hz

/-! #### U6 helpers for D8 (g): the assembly of the Reidemeister-III site -/

/-! the inner crossings of `M₀`, `M₁` and the over/under occurrences -/

noncomputable def gu6_y_mp : π.M₀.Γ.Crossing :=
  (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩).symm (xPair π.X₀_cross_mp)
noncomputable def gu6_y_mq : π.M₀.Γ.Crossing :=
  (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩).symm (xPair π.X₀_cross_mq)
noncomputable def gu6_y_pq : π.M₀.Γ.Crossing :=
  (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩).symm (xPair π.X₀_cross_pq)
noncomputable def gu6_y'_pC : π.M₁.Γ.Crossing :=
  (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm (xPair π.X₁_cross_pC)
noncomputable def gu6_y'_qB : π.M₁.Γ.Crossing :=
  (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm (xPair π.X₁_cross_qB)
noncomputable def gu6_y'_pq : π.M₁.Γ.Crossing :=
  (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm (xPair π.X₁_cross_pq)

theorem gu6_inner0 (y : π.M₀.Γ.Crossing) :
    π.M₀.Γ.crossingPoint y ∈ interior π.U ↔ y = π.gu6_y_mp ∨ y = π.gu6_y_mq ∨ y = π.gu6_y_pq := by
  rw [π.inner_M₀ y]
  exact or_congr (Equiv.eq_symm_apply _).symm
    (or_congr (Equiv.eq_symm_apply _).symm (Equiv.eq_symm_apply _).symm)
theorem gu6_inner1 (y : π.M₁.Γ.Crossing) :
    π.M₁.Γ.crossingPoint y ∈ interior π.U ↔ y = π.gu6_y'_pC ∨ y = π.gu6_y'_qB ∨ y = π.gu6_y'_pq := by
  rw [π.inner_M₁ y]
  exact or_congr (Equiv.eq_symm_apply _).symm
    (or_congr (Equiv.eq_symm_apply _).symm (Equiv.eq_symm_apply _).symm)

theorem gu6_w_mp_fst : π.w_mp.1 = π.gu6_y_mp := gu6_sv_fst_eq _ _
theorem gu6_w_pm_fst : π.w_pm.1 = π.gu6_y_mp := gu6_sv_fst_eq _ _
theorem gu6_w_mq_fst : π.w_mq.1 = π.gu6_y_mq := gu6_sv_fst_eq _ _
theorem gu6_w_qm_fst : π.w_qm.1 = π.gu6_y_mq := gu6_sv_fst_eq _ _
theorem gu6_w_pq_fst : π.w_pq.1 = π.gu6_y_pq := gu6_sv_fst_eq _ _
theorem gu6_w_qp_fst : π.w_qp.1 = π.gu6_y_pq := gu6_sv_fst_eq _ _
theorem gu6_w'_pC_fst : π.gu6_w'_pC.1 = π.gu6_y'_pC := gu6_sv_fst_eq _ _
theorem gu6_w'_Cp_fst : π.gu6_w'_Cp.1 = π.gu6_y'_pC := gu6_sv_fst_eq _ _
theorem gu6_w'_qB_fst : π.gu6_w'_qB.1 = π.gu6_y'_qB := gu6_sv_fst_eq _ _
theorem gu6_w'_Bq_fst : π.gu6_w'_Bq.1 = π.gu6_y'_qB := gu6_sv_fst_eq _ _
theorem gu6_w'_pq_fst : π.gu6_w'_pq.1 = π.gu6_y'_pq := gu6_sv_fst_eq _ _
theorem gu6_w'_qp_fst : π.gu6_w'_qp.1 = π.gu6_y'_pq := gu6_sv_fst_eq _ _

theorem gu6_y_mp_ne_mq : π.gu6_y_mp ≠ π.gu6_y_mq :=
  gu6_xPair_ne_of_not_mem _ _ π.gu6_mB_ne_mC (π.gu6_lab_ne_mB C.q).symm
theorem gu6_y_mp_ne_pq : π.gu6_y_mp ≠ π.gu6_y_pq :=
  gu6_xPair_ne_of_not_mem _ _ (π.gu6_lab_ne_mB C.p).symm (π.gu6_lab_ne_mB C.q).symm
theorem gu6_y_mq_ne_pq : π.gu6_y_mq ≠ π.gu6_y_pq :=
  gu6_xPair_ne_of_not_mem _ _ (π.gu6_lab_ne_mC C.p).symm (π.gu6_lab_ne_mC C.q).symm
theorem gu6_y'_pC_ne_qB : π.gu6_y'_pC ≠ π.gu6_y'_qB :=
  gu6_xPair_ne_of_not_mem _ _ π.gu6_p'_ne_q' (π.gu6_lab_ne_mB C.p)
theorem gu6_y'_pC_ne_pq : π.gu6_y'_pC ≠ π.gu6_y'_pq := by
  intro e
  have e1 := (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm.injective e
  have e2 := congrArg Subtype.val e1
  change ({π.p', π.mC} : Finset (ZMod (k + 3))) = {π.p', π.q'} at e2
  have : π.mC ∈ ({π.p', π.q'} : Finset (ZMod (k + 3))) := by rw [← e2]; exact mem_pair_right _ _
  rw [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h
  · exact π.gu6_lab_ne_mC C.p h.symm
  · exact π.gu6_lab_ne_mC C.q h.symm
theorem gu6_y'_qB_ne_pq : π.gu6_y'_qB ≠ π.gu6_y'_pq := by
  intro e
  have e1 := (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm.injective e
  have e2 := congrArg Subtype.val e1
  change ({π.q', π.mB} : Finset (ZMod (k + 3))) = {π.p', π.q'} at e2
  have : π.mB ∈ ({π.p', π.q'} : Finset (ZMod (k + 3))) := by rw [← e2]; exact mem_pair_right _ _
  rw [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h' | h'
  · exact π.gu6_lab_ne_mB C.p h'.symm
  · exact π.gu6_lab_ne_mB C.q h'.symm

/-! the over relations and the over/under occurrences -/

theorem gu6_lab_ne_mA {i : ZMod k} (hi : i ≠ C.m) : G11_lab C.m i ≠ π.mA := fun h => by
  have := congrArg ZMod.val h
  rw [gu6_lab_val, gu6_mA_val] at this
  have him : i.val ≠ C.m.val := fun h' => hi (ZMod.val_injective k h')
  split_ifs at this <;> omega

theorem gu6_edge_p' : edge π.X₀ π.p' = edge C.X C.p := gu6_edge_lab π (gu6_p_ne_m (C := C))
theorem gu6_edge_q' : edge π.X₀ π.q' = edge C.X C.q := gu6_edge_lab π (gu6_q_ne_m (C := C))
theorem gu6_edge_X₁_p' : edge π.X₁ π.p' = edge C.X C.p := gu6_edge_X₁_lab π (gu6_p_ne_m (C := C))
theorem gu6_edge_X₁_q' : edge π.X₁ π.q' = edge C.X C.q := gu6_edge_X₁_lab π (gu6_q_ne_m (C := C))

theorem gu6_det_mB_p' :
    det (edge π.X₀ π.mB) (edge π.X₀ π.p') = (π.t₂ - π.t₁) * det (edge C.X C.m) (edge C.X C.p) := by
  rw [gu6_edge_mB, gu6_edge_p', CV.det_smul_left']
theorem gu6_det_mC_q' :
    det (edge π.X₀ π.mC) (edge π.X₀ π.q') = (π.t₃ - π.t₂) * det (edge C.X C.m) (edge C.X C.q) := by
  rw [gu6_edge_mC, gu6_edge_q', CV.det_smul_left']
theorem gu6_det_p'_q' : det (edge π.X₀ π.p') (edge π.X₀ π.q') = det (edge C.X C.p) (edge C.X C.q) := by
  rw [gu6_edge_p', gu6_edge_q']
theorem gu6_det_X₁_p'_q' : det (edge π.X₁ π.p') (edge π.X₁ π.q') = det (edge C.X C.p) (edge C.X C.q) := by
  rw [gu6_edge_X₁_p', gu6_edge_X₁_q']

theorem gu6_Rmp_iff : 0 < det (edge C.X C.m) (edge C.X C.p) ↔ 0 < det (edge π.X₀ π.mB) (edge π.X₀ π.p') := by
  rw [gu6_det_mB_p']
  exact (mul_pos_iff_of_pos_left (sub_pos.mpr π.gu6_t₁_lt_t₂)).symm
theorem gu6_Rmq_iff : 0 < det (edge C.X C.m) (edge C.X C.q) ↔ 0 < det (edge π.X₀ π.mC) (edge π.X₀ π.q') := by
  rw [gu6_det_mC_q']
  exact (mul_pos_iff_of_pos_left (sub_pos.mpr π.gu6_t₂_lt_t₃)).symm
theorem gu6_Rpq_iff : 0 < det (edge C.X C.p) (edge C.X C.q) ↔ 0 < det (edge π.X₀ π.p') (edge π.X₀ π.q') := by
  rw [gu6_det_p'_q']
theorem gu6_Rpq_iff' : 0 < det (edge C.X C.p) (edge C.X C.q) ↔ 0 < det (edge π.X₁ π.p') (edge π.X₁ π.q') := by
  rw [gu6_det_X₁_p'_q']
/-- the sign at the new crossing of `p` with `[w, p_out]`: `p` over `m`, i.e. `¬ Rmp` -/
theorem gu6_R_pC_iff : 0 < det (edge π.X₁ π.p') (edge π.X₁ π.mC) ↔ det (edge C.X C.m) (edge C.X C.p) < 0 := by
  have h := π.X₁_sign_pC
  unfold crossingSign at h
  rw [← GT_det_pos_iff_of_sign h, det_swap (edge C.X C.m), neg_pos]
theorem gu6_R_qB_iff : 0 < det (edge π.X₁ π.q') (edge π.X₁ π.mB) ↔ det (edge C.X C.m) (edge C.X C.q) < 0 := by
  have h := π.X₁_sign_qB
  unfold crossingSign at h
  rw [← GT_det_pos_iff_of_sign h, det_swap (edge C.X C.m), neg_pos]

theorem gu6_det_mp_ne : det (edge C.X C.m) (edge C.X C.p) ≠ 0 := gu6_det_ne_zero_single C.gen C.hmp
theorem gu6_det_mq_ne : det (edge C.X C.m) (edge C.X C.q) ≠ 0 := gu6_det_ne_zero_single C.gen C.hmq
theorem gu6_det_pq_ne : det (edge C.X C.p) (edge C.X C.q) ≠ 0 := gu6_det_ne_zero_single C.gen C.hpq

/-- over/under occurrences at the six inner crossings -/
theorem gu6_ov_mp_pos (h : 0 < det (edge C.X C.m) (edge C.X C.p)) :
    π.M₀.overVisit π.gu6_y_mp = π.w_mp ∧ π.M₀.underVisit π.gu6_y_mp = π.w_pm :=
  gu6_over_under_of_pos π.X₀_generic π.X₀_cross_mp (π.gu6_Rmp_iff.mp h)
theorem gu6_ov_mp_neg (h : ¬ 0 < det (edge C.X C.m) (edge C.X C.p)) :
    π.M₀.overVisit π.gu6_y_mp = π.w_pm ∧ π.M₀.underVisit π.gu6_y_mp = π.w_mp :=
  gu6_over_under_of_neg π.X₀_generic π.X₀_cross_mp
    (lt_of_le_of_ne (not_lt.mp (fun h' => h (π.gu6_Rmp_iff.mpr h')))
      (gu6_det_ne_zero_single π.X₀_generic π.X₀_cross_mp))
theorem gu6_ov_mq_pos (h : 0 < det (edge C.X C.m) (edge C.X C.q)) :
    π.M₀.overVisit π.gu6_y_mq = π.w_mq ∧ π.M₀.underVisit π.gu6_y_mq = π.w_qm :=
  gu6_over_under_of_pos π.X₀_generic π.X₀_cross_mq (π.gu6_Rmq_iff.mp h)
theorem gu6_ov_mq_neg (h : ¬ 0 < det (edge C.X C.m) (edge C.X C.q)) :
    π.M₀.overVisit π.gu6_y_mq = π.w_qm ∧ π.M₀.underVisit π.gu6_y_mq = π.w_mq :=
  gu6_over_under_of_neg π.X₀_generic π.X₀_cross_mq
    (lt_of_le_of_ne (not_lt.mp (fun h' => h (π.gu6_Rmq_iff.mpr h')))
      (gu6_det_ne_zero_single π.X₀_generic π.X₀_cross_mq))
theorem gu6_ov_pq_pos (h : 0 < det (edge C.X C.p) (edge C.X C.q)) :
    π.M₀.overVisit π.gu6_y_pq = π.w_pq ∧ π.M₀.underVisit π.gu6_y_pq = π.w_qp :=
  gu6_over_under_of_pos π.X₀_generic π.X₀_cross_pq (π.gu6_Rpq_iff.mp h)
theorem gu6_ov_pq_neg (h : ¬ 0 < det (edge C.X C.p) (edge C.X C.q)) :
    π.M₀.overVisit π.gu6_y_pq = π.w_qp ∧ π.M₀.underVisit π.gu6_y_pq = π.w_pq :=
  gu6_over_under_of_neg π.X₀_generic π.X₀_cross_pq
    (lt_of_le_of_ne (not_lt.mp (fun h' => h (π.gu6_Rpq_iff.mpr h')))
      (gu6_det_ne_zero_single π.X₀_generic π.X₀_cross_pq))
theorem gu6_ov_pC_pos (h : 0 < det (edge C.X C.m) (edge C.X C.p)) :
    π.M₁.overVisit π.gu6_y'_pC = π.gu6_w'_Cp ∧ π.M₁.underVisit π.gu6_y'_pC = π.gu6_w'_pC :=
  gu6_over_under_of_neg π.X₁_generic π.X₁_cross_pC
    (lt_of_le_of_ne (not_lt.mp (fun h' => (lt_asymm h) (π.gu6_R_pC_iff.mp h')))
      (gu6_det_ne_zero_single π.X₁_generic π.X₁_cross_pC))
theorem gu6_ov_pC_neg (h : ¬ 0 < det (edge C.X C.m) (edge C.X C.p)) :
    π.M₁.overVisit π.gu6_y'_pC = π.gu6_w'_pC ∧ π.M₁.underVisit π.gu6_y'_pC = π.gu6_w'_Cp :=
  gu6_over_under_of_pos π.X₁_generic π.X₁_cross_pC
    (π.gu6_R_pC_iff.mpr (lt_of_le_of_ne (not_lt.mp h) (gu6_det_mp_ne (C := C))))
theorem gu6_ov_qB_pos (h : 0 < det (edge C.X C.m) (edge C.X C.q)) :
    π.M₁.overVisit π.gu6_y'_qB = π.gu6_w'_Bq ∧ π.M₁.underVisit π.gu6_y'_qB = π.gu6_w'_qB :=
  gu6_over_under_of_neg π.X₁_generic π.X₁_cross_qB
    (lt_of_le_of_ne (not_lt.mp (fun h' => (lt_asymm h) (π.gu6_R_qB_iff.mp h')))
      (gu6_det_ne_zero_single π.X₁_generic π.X₁_cross_qB))
theorem gu6_ov_qB_neg (h : ¬ 0 < det (edge C.X C.m) (edge C.X C.q)) :
    π.M₁.overVisit π.gu6_y'_qB = π.gu6_w'_qB ∧ π.M₁.underVisit π.gu6_y'_qB = π.gu6_w'_Bq :=
  gu6_over_under_of_pos π.X₁_generic π.X₁_cross_qB
    (π.gu6_R_qB_iff.mpr (lt_of_le_of_ne (not_lt.mp h) (gu6_det_mq_ne (C := C))))
theorem gu6_ov_pq'_pos (h : 0 < det (edge C.X C.p) (edge C.X C.q)) :
    π.M₁.overVisit π.gu6_y'_pq = π.gu6_w'_pq ∧ π.M₁.underVisit π.gu6_y'_pq = π.gu6_w'_qp :=
  gu6_over_under_of_pos π.X₁_generic π.X₁_cross_pq (π.gu6_Rpq_iff'.mp h)
theorem gu6_ov_pq'_neg (h : ¬ 0 < det (edge C.X C.p) (edge C.X C.q)) :
    π.M₁.overVisit π.gu6_y'_pq = π.gu6_w'_qp ∧ π.M₁.underVisit π.gu6_y'_pq = π.gu6_w'_pq :=
  gu6_over_under_of_neg π.X₁_generic π.X₁_cross_pq
    (lt_of_le_of_ne (not_lt.mp (fun h' => h (π.gu6_Rpq_iff'.mpr h')))
      (gu6_det_ne_zero_single π.X₁_generic π.X₁_cross_pq))

/-! ### Unit E leaves — the record of `M₁` -/

/-! #### U6 helpers for E1 (a): the occurrence bijection `Ψ₁ : M₀ ≃ M₁` -/

/-- U6 helper: on a visit of the strand `m`, `σ` is the swap `x_mp ↔ x_mq`. -/
theorem gu6_σ_on_m {k : ℕ} [NeZero k] (C : G11_ConfigSw k) (x : Visit C.X) (hx : x.2.val = C.m) :
    C.σ x = Equiv.swap C.vmp C.vmq x := by
  have hmp : C.m ≠ C.p := P1.ne_of_isCrossing_pair C.hmp
  have hmq : C.m ≠ C.q := P1.ne_of_isCrossing_pair C.hmq
  have h1 : x ≠ C.vqm := gu6_visit_ne_of_edge (by rw [hx]; exact hmq)
  have h2 : x ≠ C.vqp := gu6_visit_ne_of_edge (by rw [hx]; exact hmq)
  have h3 : x ≠ C.vpm := gu6_visit_ne_of_edge (by rw [hx]; exact hmp)
  have h4 : x ≠ C.vpq := gu6_visit_ne_of_edge (by rw [hx]; exact hmp)
  unfold G11_ConfigSw.σ
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2,
    Equiv.swap_apply_of_ne_of_ne h3 h4]

/-- U6 helper: on a visit of the strand `p`, `σ` is the swap `x_pm ↔ x_pq`. -/
theorem gu6_σ_on_p {k : ℕ} [NeZero k] (C : G11_ConfigSw k) (x : Visit C.X) (hx : x.2.val = C.p) :
    C.σ x = Equiv.swap C.vpm C.vpq x := by
  have hmp : C.m ≠ C.p := P1.ne_of_isCrossing_pair C.hmp
  have hpq : C.p ≠ C.q := P1.ne_of_isCrossing_pair C.hpq
  have h1 : x ≠ C.vqm := gu6_visit_ne_of_edge (by rw [hx]; exact hpq)
  have h2 : x ≠ C.vqp := gu6_visit_ne_of_edge (by rw [hx]; exact hpq)
  have h3 : Equiv.swap C.vpm C.vpq x ≠ C.vmp :=
    gu6_visit_ne_of_edge (by rw [gu6_swap_edge C.vpm C.vpq rfl, hx]; exact hmp.symm)
  have h4 : Equiv.swap C.vpm C.vpq x ≠ C.vmq :=
    gu6_visit_ne_of_edge (by rw [gu6_swap_edge C.vpm C.vpq rfl, hx]; exact hmp.symm)
  unfold G11_ConfigSw.σ
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2,
    Equiv.swap_apply_of_ne_of_ne h3 h4]

/-- U6 helper: on a visit of the strand `q`, `σ` is the swap `x_qm ↔ x_qp`. -/
theorem gu6_σ_on_q {k : ℕ} [NeZero k] (C : G11_ConfigSw k) (x : Visit C.X) (hx : x.2.val = C.q) :
    C.σ x = Equiv.swap C.vqm C.vqp x := by
  have hmq : C.m ≠ C.q := P1.ne_of_isCrossing_pair C.hmq
  have hpq : C.p ≠ C.q := P1.ne_of_isCrossing_pair C.hpq
  have h3 : Equiv.swap C.vqm C.vqp x ≠ C.vpm :=
    gu6_visit_ne_of_edge (by rw [gu6_swap_edge C.vqm C.vqp rfl, hx]; exact hpq.symm)
  have h4 : Equiv.swap C.vqm C.vqp x ≠ C.vpq :=
    gu6_visit_ne_of_edge (by rw [gu6_swap_edge C.vqm C.vqp rfl, hx]; exact hpq.symm)
  have h1 : Equiv.swap C.vqm C.vqp x ≠ C.vmp :=
    gu6_visit_ne_of_edge (by rw [gu6_swap_edge C.vqm C.vqp rfl, hx]; exact hmq.symm)
  have h2 : Equiv.swap C.vqm C.vqp x ≠ C.vmq :=
    gu6_visit_ne_of_edge (by rw [gu6_swap_edge C.vqm C.vqp rfl, hx]; exact hmq.symm)
  unfold G11_ConfigSw.σ
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h3 h4,
    Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- U6 helper: the six values of `σ` on the local visits. -/
theorem gu6_σ_vmp {k : ℕ} [NeZero k] (C : G11_ConfigSw k) : C.σ C.vmp = C.vmq := by
  rw [gu6_σ_on_m C _ rfl, Equiv.swap_apply_left]

theorem gu6_σ_vmq {k : ℕ} [NeZero k] (C : G11_ConfigSw k) : C.σ C.vmq = C.vmp := by
  rw [gu6_σ_on_m C _ rfl, Equiv.swap_apply_right]

theorem gu6_σ_vpm {k : ℕ} [NeZero k] (C : G11_ConfigSw k) : C.σ C.vpm = C.vpq := by
  rw [gu6_σ_on_p C _ rfl, Equiv.swap_apply_left]

theorem gu6_σ_vpq {k : ℕ} [NeZero k] (C : G11_ConfigSw k) : C.σ C.vpq = C.vpm := by
  rw [gu6_σ_on_p C _ rfl, Equiv.swap_apply_right]

theorem gu6_σ_vqm {k : ℕ} [NeZero k] (C : G11_ConfigSw k) : C.σ C.vqm = C.vqp := by
  rw [gu6_σ_on_q C _ rfl, Equiv.swap_apply_left]

theorem gu6_σ_vqp {k : ℕ} [NeZero k] (C : G11_ConfigSw k) : C.σ C.vqp = C.vqm := by
  rw [gu6_σ_on_q C _ rfl, Equiv.swap_apply_right]

/-- U6 helper: `σ` fixes every visit other than the six local ones. -/
theorem gu6_σ_of_not_local {k : ℕ} [NeZero k] (C : G11_ConfigSw k) (x : Visit C.X)
    (h1 : x ≠ C.vmp) (h2 : x ≠ C.vmq) (h3 : x ≠ C.vpm) (h4 : x ≠ C.vpq) (h5 : x ≠ C.vqm)
    (h6 : x ≠ C.vqp) : C.σ x = x := by
  unfold G11_ConfigSw.σ
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h5 h6,
    Equiv.swap_apply_of_ne_of_ne h3 h4, Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- U6 helper: `σD` read through `singleVisitEquiv`. -/
theorem gu6_σD_apply {k : ℕ} [NeZero k] (C : G11_ConfigSw k) (x : Visit C.X) :
    C.σD ((Shadow.singleVisitEquiv C.comp).symm x) = (Shadow.singleVisitEquiv C.comp).symm (C.σ x) := by
  have h := Equiv.permCongr_apply (Shadow.singleVisitEquiv C.comp).symm C.σ
    ((Shadow.singleVisitEquiv C.comp).symm x)
  have h2 : (Shadow.singleVisitEquiv C.comp).symm.symm ((Shadow.singleVisitEquiv C.comp).symm x) = x :=
    Equiv.apply_symm_apply _ _
  rw [h2] at h
  exact h


/-! the crossings of `X₀`, `X₁` through the inner pieces `mB`, `mC` are the local ones -/

theorem gu6_X₀_cross_mB (y : Crossing π.X₀) (hmB : π.mB ∈ y.val) : y.val = {π.mB, π.p'} := by
  have hin : π.M₀.Γ.crossingPoint ((Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩).symm y) ∈
      interior π.U := by
    show (Shadow.single ⟨k + 3, π.hk₃, π.X₀⟩).crossingPoint _ ∈ interior π.U
    rw [Shadow.single_crossingPoint _ π.X₀_generic, Equiv.apply_symm_apply]
    obtain ⟨t, h0, h1, ht⟩ := crossingPoint_mem y π.mB hmB
    rw [ht]
    exact π.gu6_edgePoint_mB_interior t h0 h1
  rcases (π.gu6_inner0 _).mp hin with h1 | h1 | h1
  · exact congrArg Subtype.val ((Shadow.singleCrossingEquiv _).symm.injective h1)
  · exfalso
    have := congrArg Subtype.val ((Shadow.singleCrossingEquiv _).symm.injective h1)
    change y.val = {π.mC, π.q'} at this
    rw [this, Finset.mem_insert, Finset.mem_singleton] at hmB
    rcases hmB with e | e
    · exact π.gu6_mB_ne_mC e
    · exact π.gu6_lab_ne_mB C.q e.symm
  · exfalso
    have := congrArg Subtype.val ((Shadow.singleCrossingEquiv _).symm.injective h1)
    change y.val = {π.p', π.q'} at this
    rw [this, Finset.mem_insert, Finset.mem_singleton] at hmB
    rcases hmB with e | e
    · exact π.gu6_lab_ne_mB C.p e.symm
    · exact π.gu6_lab_ne_mB C.q e.symm

theorem gu6_X₀_cross_mC (y : Crossing π.X₀) (hmC : π.mC ∈ y.val) : y.val = {π.mC, π.q'} := by
  have hin : π.M₀.Γ.crossingPoint ((Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩).symm y) ∈
      interior π.U := by
    show (Shadow.single ⟨k + 3, π.hk₃, π.X₀⟩).crossingPoint _ ∈ interior π.U
    rw [Shadow.single_crossingPoint _ π.X₀_generic, Equiv.apply_symm_apply]
    obtain ⟨t, h0, h1, ht⟩ := crossingPoint_mem y π.mC hmC
    rw [ht]
    exact π.gu6_edgePoint_mC_interior t h0 h1
  rcases (π.gu6_inner0 _).mp hin with h1 | h1 | h1
  · exfalso
    have := congrArg Subtype.val ((Shadow.singleCrossingEquiv _).symm.injective h1)
    change y.val = {π.mB, π.p'} at this
    rw [this, Finset.mem_insert, Finset.mem_singleton] at hmC
    rcases hmC with e | e
    · exact π.gu6_mB_ne_mC e.symm
    · exact π.gu6_lab_ne_mC C.p e.symm
  · exact congrArg Subtype.val ((Shadow.singleCrossingEquiv _).symm.injective h1)
  · exfalso
    have := congrArg Subtype.val ((Shadow.singleCrossingEquiv _).symm.injective h1)
    change y.val = {π.p', π.q'} at this
    rw [this, Finset.mem_insert, Finset.mem_singleton] at hmC
    rcases hmC with e | e
    · exact π.gu6_lab_ne_mC C.p e.symm
    · exact π.gu6_lab_ne_mC C.q e.symm

theorem gu6_X₁_cross_mB (y : Crossing π.X₁) (hmB : π.mB ∈ y.val) : y.val = {π.q', π.mB} := by
  have hin : π.M₁.Γ.crossingPoint ((Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm y) ∈
      interior π.U := by
    show (Shadow.single ⟨k + 3, π.hk₃, π.X₁⟩).crossingPoint _ ∈ interior π.U
    rw [Shadow.single_crossingPoint _ π.X₁_generic, Equiv.apply_symm_apply]
    obtain ⟨t, h0, h1, ht⟩ := crossingPoint_mem y π.mB hmB
    rw [ht]
    exact π.gu6_edgePoint_X₁_mB_interior t h0 h1
  rcases (π.gu6_inner1 _).mp hin with h1 | h1 | h1
  · exfalso
    have := congrArg Subtype.val ((Shadow.singleCrossingEquiv _).symm.injective h1)
    change y.val = {π.p', π.mC} at this
    rw [this, Finset.mem_insert, Finset.mem_singleton] at hmB
    rcases hmB with e | e
    · exact π.gu6_lab_ne_mB C.p e.symm
    · exact π.gu6_mB_ne_mC e
  · exact congrArg Subtype.val ((Shadow.singleCrossingEquiv _).symm.injective h1)
  · exfalso
    have := congrArg Subtype.val ((Shadow.singleCrossingEquiv _).symm.injective h1)
    change y.val = {π.p', π.q'} at this
    rw [this, Finset.mem_insert, Finset.mem_singleton] at hmB
    rcases hmB with e | e
    · exact π.gu6_lab_ne_mB C.p e.symm
    · exact π.gu6_lab_ne_mB C.q e.symm

theorem gu6_X₁_cross_mC (y : Crossing π.X₁) (hmC : π.mC ∈ y.val) : y.val = {π.p', π.mC} := by
  have hin : π.M₁.Γ.crossingPoint ((Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm y) ∈
      interior π.U := by
    show (Shadow.single ⟨k + 3, π.hk₃, π.X₁⟩).crossingPoint _ ∈ interior π.U
    rw [Shadow.single_crossingPoint _ π.X₁_generic, Equiv.apply_symm_apply]
    obtain ⟨t, h0, h1, ht⟩ := crossingPoint_mem y π.mC hmC
    rw [ht]
    exact π.gu6_edgePoint_X₁_mC_interior t h0 h1
  rcases (π.gu6_inner1 _).mp hin with h1 | h1 | h1
  · exact congrArg Subtype.val ((Shadow.singleCrossingEquiv _).symm.injective h1)
  · exfalso
    have := congrArg Subtype.val ((Shadow.singleCrossingEquiv _).symm.injective h1)
    change y.val = {π.q', π.mB} at this
    rw [this, Finset.mem_insert, Finset.mem_singleton] at hmC
    rcases hmC with e | e
    · exact π.gu6_lab_ne_mC C.q e.symm
    · exact π.gu6_mB_ne_mC e.symm
  · exfalso
    have := congrArg Subtype.val ((Shadow.singleCrossingEquiv _).symm.injective h1)
    change y.val = {π.p', π.q'} at this
    rw [this, Finset.mem_insert, Finset.mem_singleton] at hmC
    rcases hmC with e | e
    · exact π.gu6_lab_ne_mC C.p e.symm
    · exact π.gu6_lab_ne_mC C.q e.symm

/-! the strand relabelling `mB ↔ mC` -/

/-- the strand relabelling of the move: `mB ↔ mC`, every other label fixed -/
noncomputable def gu6_σ₁ : Equiv.Perm (ZMod (k + 3)) := Equiv.swap π.mB π.mC

theorem gu6_σ₁_mB : π.gu6_σ₁ π.mB = π.mC := Equiv.swap_apply_left _ _
theorem gu6_σ₁_mC : π.gu6_σ₁ π.mC = π.mB := Equiv.swap_apply_right _ _
theorem gu6_σ₁_of_ne {i : ZMod (k + 3)} (h1 : i ≠ π.mB) (h2 : i ≠ π.mC) : π.gu6_σ₁ i = i :=
  Equiv.swap_apply_of_ne_of_ne h1 h2
theorem gu6_σ₁_p' : π.gu6_σ₁ π.p' = π.p' := π.gu6_σ₁_of_ne (π.gu6_lab_ne_mB C.p) (π.gu6_lab_ne_mC C.p)
theorem gu6_σ₁_q' : π.gu6_σ₁ π.q' = π.q' := π.gu6_σ₁_of_ne (π.gu6_lab_ne_mB C.q) (π.gu6_lab_ne_mC C.q)
theorem gu6_σ₁_σ₁ (i : ZMod (k + 3)) : π.gu6_σ₁ (π.gu6_σ₁ i) = i := Equiv.swap_apply_self _ _ _

theorem gu6_map_pair (i j : ZMod (k + 3)) :
    ({i, j} : Finset (ZMod (k + 3))).map π.gu6_σ₁.toEmbedding = {π.gu6_σ₁ i, π.gu6_σ₁ j} := by
  rw [Finset.map_insert, Finset.map_singleton]; rfl

theorem gu6_map_map (s : Finset (ZMod (k + 3))) :
    (s.map π.gu6_σ₁.toEmbedding).map π.gu6_σ₁.toEmbedding = s := by
  rw [Finset.map_map]
  have : π.gu6_σ₁.toEmbedding.trans π.gu6_σ₁.toEmbedding = Function.Embedding.refl _ :=
    Function.Embedding.ext fun x => π.gu6_σ₁_σ₁ x
  rw [this, Finset.map_refl]

theorem gu6_map_of_not_mem {s : Finset (ZMod (k + 3))} (hB : π.mB ∉ s) (hC : π.mC ∉ s) :
    s.map π.gu6_σ₁.toEmbedding = s := by
  ext x
  rw [Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h1 : a ≠ π.mB := fun e => hB (e ▸ ha)
    have h2 : a ≠ π.mC := fun e => hC (e ▸ ha)
    change π.gu6_σ₁ a ∈ s
    rw [π.gu6_σ₁_of_ne h1 h2]; exact ha
  · intro hx
    have h1 : x ≠ π.mB := fun e => hB (e ▸ hx)
    have h2 : x ≠ π.mC := fun e => hC (e ▸ hx)
    exact ⟨x, hx, π.gu6_σ₁_of_ne h1 h2⟩

/-- the crossing supports of `X₀` correspond to those of `X₁` under the relabelling -/
theorem gu6_cross_map_iff (s : Finset (ZMod (k + 3))) :
    IsCrossing π.X₀ s ↔ IsCrossing π.X₁ (s.map π.gu6_σ₁.toEmbedding) := by
  by_cases hB : π.mB ∈ s
  · constructor
    · intro h
      have hs := π.gu6_X₀_cross_mB ⟨s, h⟩ hB
      change s = {π.mB, π.p'} at hs
      rw [hs, gu6_map_pair, gu6_σ₁_mB, gu6_σ₁_p', Finset.pair_comm]
      exact π.X₁_cross_pC
    · intro h
      have hC : π.mC ∈ s.map π.gu6_σ₁.toEmbedding := by
        have := (Finset.mem_map' π.gu6_σ₁.toEmbedding).mpr hB
        rwa [show π.gu6_σ₁.toEmbedding π.mB = π.mC from π.gu6_σ₁_mB] at this
      have h2 := π.gu6_X₁_cross_mC ⟨_, h⟩ hC
      change s.map π.gu6_σ₁.toEmbedding = {π.p', π.mC} at h2
      have h3 : s = ({π.p', π.mC} : Finset _).map π.gu6_σ₁.toEmbedding := by
        rw [← h2, gu6_map_map]
      rw [h3, gu6_map_pair, gu6_σ₁_p', gu6_σ₁_mC, Finset.pair_comm]
      exact π.X₀_cross_mp
  · by_cases hC : π.mC ∈ s
    · constructor
      · intro h
        have hs := π.gu6_X₀_cross_mC ⟨s, h⟩ hC
        change s = {π.mC, π.q'} at hs
        rw [hs, gu6_map_pair, gu6_σ₁_mC, gu6_σ₁_q', Finset.pair_comm]
        exact π.X₁_cross_qB
      · intro h
        have hB' : π.mB ∈ s.map π.gu6_σ₁.toEmbedding := by
          have := (Finset.mem_map' π.gu6_σ₁.toEmbedding).mpr hC
          rwa [show π.gu6_σ₁.toEmbedding π.mC = π.mB from π.gu6_σ₁_mC] at this
        have h2 := π.gu6_X₁_cross_mB ⟨_, h⟩ hB'
        change s.map π.gu6_σ₁.toEmbedding = {π.q', π.mB} at h2
        have h3 : s = ({π.q', π.mB} : Finset _).map π.gu6_σ₁.toEmbedding := by
          rw [← h2, gu6_map_map]
        rw [h3, gu6_map_pair, gu6_σ₁_q', gu6_σ₁_mB, Finset.pair_comm]
        exact π.X₀_cross_mq
    · rw [π.gu6_map_of_not_mem hB hC]
      exact (π.X₁_cross_iff s hB hC).symm

/-- the crossing bijection `X₀ ≃ X₁` -/
noncomputable def gu6_κ : Crossing π.X₀ ≃ Crossing π.X₁ :=
  (Equiv.Finset.congr π.gu6_σ₁).subtypeEquiv π.gu6_cross_map_iff

theorem gu6_κ_val (y : Crossing π.X₀) : (π.gu6_κ y).val = y.val.map π.gu6_σ₁.toEmbedding := rfl

/-- the visit bijection of the polygons -/
noncomputable def gu6_ΨX : Visit π.X₀ ≃ Visit π.X₁ :=
  Equiv.sigmaCongr π.gu6_κ fun y => π.gu6_σ₁.subtypeEquiv fun i => by
    rw [gu6_κ_val]
    exact (Finset.mem_map' _).symm

theorem gu6_ΨX_fst (u : Visit π.X₀) : (π.gu6_ΨX u).1 = π.gu6_κ u.1 := rfl
theorem gu6_ΨX_snd (u : Visit π.X₀) : (π.gu6_ΨX u).2.val = π.gu6_σ₁ u.2.val := rfl

/-- **the occurrence bijection `Ψ₁ : M₀ ≃ M₁`** -/
noncomputable def gu6_Ψ₁ : π.M₀.Γ.Visit ≃ π.M₁.Γ.Visit :=
  (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₀⟩).trans
    (π.gu6_ΨX.trans (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm)

theorem gu6_Ψ₁_apply (v : π.M₀.Γ.Visit) :
    π.gu6_Ψ₁ v = (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm
      (π.gu6_ΨX (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₀⟩ v)) := rfl

theorem gu6_Ψ₁_symm_apply (y : Crossing π.X₀) (i : ZMod (k + 3)) (hi : i ∈ y.val) :
    π.gu6_Ψ₁ ((Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₀⟩).symm ⟨y, ⟨i, hi⟩⟩) =
      (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm
        ⟨π.gu6_κ y, ⟨π.gu6_σ₁ i, (Finset.mem_map' _).mpr hi⟩⟩ := by
  exact congrArg (fun u => (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm (π.gu6_ΨX u))
    (Equiv.apply_symm_apply _ _)

theorem gu6_κ_mp : π.gu6_κ (xPair π.X₀_cross_mp) = xPair π.X₁_cross_pC :=
  Subtype.ext (by
    rw [gu6_κ_val, P1.xPair_val, P1.xPair_val, gu6_map_pair, gu6_σ₁_mB, gu6_σ₁_p', Finset.pair_comm])
theorem gu6_κ_mq : π.gu6_κ (xPair π.X₀_cross_mq) = xPair π.X₁_cross_qB :=
  Subtype.ext (by
    rw [gu6_κ_val, P1.xPair_val, P1.xPair_val, gu6_map_pair, gu6_σ₁_mC, gu6_σ₁_q', Finset.pair_comm])
theorem gu6_κ_pq : π.gu6_κ (xPair π.X₀_cross_pq) = xPair π.X₁_cross_pq :=
  Subtype.ext (by rw [gu6_κ_val, P1.xPair_val, P1.xPair_val, gu6_map_pair, gu6_σ₁_p', gu6_σ₁_q'])

/-- `Ψ₁` on the six local occurrences -/
theorem gu6_Ψ₁_w_mp : π.gu6_Ψ₁ π.w_mp = π.gu6_w'_Cp := by
  show π.gu6_Ψ₁ ((Shadow.singleVisitEquiv _).symm ⟨xPair π.X₀_cross_mp, ⟨π.mB, mem_pair_left _ _⟩⟩) =
    (Shadow.singleVisitEquiv _).symm ⟨xPair π.X₁_cross_pC, ⟨π.mC, mem_pair_right _ _⟩⟩
  exact (π.gu6_Ψ₁_symm_apply _ _ _).trans (congrArg _ (gu6_visit_ext π.gu6_κ_mp π.gu6_σ₁_mB))
theorem gu6_Ψ₁_w_pm : π.gu6_Ψ₁ π.w_pm = π.gu6_w'_pC := by
  show π.gu6_Ψ₁ ((Shadow.singleVisitEquiv _).symm ⟨xPair π.X₀_cross_mp, ⟨π.p', mem_pair_right _ _⟩⟩) =
    (Shadow.singleVisitEquiv _).symm ⟨xPair π.X₁_cross_pC, ⟨π.p', mem_pair_left _ _⟩⟩
  exact (π.gu6_Ψ₁_symm_apply _ _ _).trans (congrArg _ (gu6_visit_ext π.gu6_κ_mp π.gu6_σ₁_p'))
theorem gu6_Ψ₁_w_mq : π.gu6_Ψ₁ π.w_mq = π.gu6_w'_Bq := by
  show π.gu6_Ψ₁ ((Shadow.singleVisitEquiv _).symm ⟨xPair π.X₀_cross_mq, ⟨π.mC, mem_pair_left _ _⟩⟩) =
    (Shadow.singleVisitEquiv _).symm ⟨xPair π.X₁_cross_qB, ⟨π.mB, mem_pair_right _ _⟩⟩
  exact (π.gu6_Ψ₁_symm_apply _ _ _).trans (congrArg _ (gu6_visit_ext π.gu6_κ_mq π.gu6_σ₁_mC))
theorem gu6_Ψ₁_w_qm : π.gu6_Ψ₁ π.w_qm = π.gu6_w'_qB := by
  show π.gu6_Ψ₁ ((Shadow.singleVisitEquiv _).symm ⟨xPair π.X₀_cross_mq, ⟨π.q', mem_pair_right _ _⟩⟩) =
    (Shadow.singleVisitEquiv _).symm ⟨xPair π.X₁_cross_qB, ⟨π.q', mem_pair_left _ _⟩⟩
  exact (π.gu6_Ψ₁_symm_apply _ _ _).trans (congrArg _ (gu6_visit_ext π.gu6_κ_mq π.gu6_σ₁_q'))
theorem gu6_Ψ₁_w_pq : π.gu6_Ψ₁ π.w_pq = π.gu6_w'_pq := by
  show π.gu6_Ψ₁ ((Shadow.singleVisitEquiv _).symm ⟨xPair π.X₀_cross_pq, ⟨π.p', mem_pair_left _ _⟩⟩) =
    (Shadow.singleVisitEquiv _).symm ⟨xPair π.X₁_cross_pq, ⟨π.p', mem_pair_left _ _⟩⟩
  exact (π.gu6_Ψ₁_symm_apply _ _ _).trans (congrArg _ (gu6_visit_ext π.gu6_κ_pq π.gu6_σ₁_p'))
theorem gu6_Ψ₁_w_qp : π.gu6_Ψ₁ π.w_qp = π.gu6_w'_qp := by
  show π.gu6_Ψ₁ ((Shadow.singleVisitEquiv _).symm ⟨xPair π.X₀_cross_pq, ⟨π.q', mem_pair_right _ _⟩⟩) =
    (Shadow.singleVisitEquiv _).symm ⟨xPair π.X₁_cross_pq, ⟨π.q', mem_pair_right _ _⟩⟩
  exact (π.gu6_Ψ₁_symm_apply _ _ _).trans (congrArg _ (gu6_visit_ext π.gu6_κ_pq π.gu6_σ₁_q'))

/-! #### U6 helpers for E1 (b): twins, over bits and signs under `Ψ₁` -/

theorem gu6_edge_X₁_of_ne {i : ZMod (k + 3)} (hB : i ≠ π.mB) (hC : i ≠ π.mC) :
    edge π.X₁ i = edge π.X₀ i := by
  have h1 : i + 1 ≠ π.mC := by
    intro h
    apply hB
    rw [← gu6_mB_add_one] at h
    exact add_right_cancel h
  rw [edge, edge, gu6_X₁_of_ne π hC, gu6_X₁_of_ne π h1]

/-- the strand of `Ψ₁ v` is the relabelled strand of `v` -/
theorem gu6_Ψ₁_strand (v : π.M₀.Γ.Visit) :
    (π.gu6_Ψ₁ v).2.val = (⟨0, π.gu6_σ₁ v.2.val.2⟩ : (Shadow.single ⟨k + 3, π.hk₃, π.X₁⟩).Strand) := by
  rw [gu6_Ψ₁_apply, gu6_sv_strand', gu6_ΨX_snd]
  rfl

theorem gu6_ΨX_twin (u : Visit π.X₀) : π.gu6_ΨX (visitTwin u) = visitTwin (π.gu6_ΨX u) := by
  apply visitTwin_unique
  · rfl
  · intro h
    exact visitTwin_ne u (π.gu6_ΨX.injective h)

theorem gu6_Ψ₁_twin (v : π.M₀.Γ.Visit) : π.gu6_Ψ₁ (π.M₀.twin v) = π.M₁.twin (π.gu6_Ψ₁ v) := by
  show (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm
      (π.gu6_ΨX ((Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₀⟩) (π.M₀.twin v))) =
    π.M₁.twin ((Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₁⟩).symm
      (π.gu6_ΨX ((Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₀⟩) v)))
  have h1 : (Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₀⟩) (π.M₀.twin v) =
      visitTwin ((Shadow.singleVisitEquiv ⟨k + 3, π.hk₃, π.X₀⟩) v) :=
    Shadow.singleVisitEquiv_otherVisit _ v
  rw [h1, gu6_ΨX_twin]
  exact Shadow.singleVisitEquiv_symm_visitTwin _ _

theorem gu6_Ψ₁_sign (v : π.M₀.Γ.Visit) : π.M₁.sign (π.gu6_Ψ₁ v).1 = π.M₀.sign v.1 :=
  (Shadow.positiveDiagram_sign _ _ _).trans (Shadow.positiveDiagram_sign _ _ _).symm

/-! the over bit through the divide sign -/

/-- the sign at `{mC, p'}` of `X₁` is the sign at `{mB, p'}` of `X₀` -/
theorem gu6_key_p : 0 < det (edge π.X₁ π.mC) (edge π.X₁ π.p') ↔ 0 < det (edge π.X₀ π.mB) (edge π.X₀ π.p') := by
  rw [det_swap (edge π.X₁ π.p'), neg_pos, ← gu6_Rmp_iff]
  have hne1 : det (edge π.X₁ π.p') (edge π.X₁ π.mC) ≠ 0 :=
    gu6_det_ne_zero_single π.X₁_generic π.X₁_cross_pC
  have hne2 : det (edge C.X C.m) (edge C.X C.p) ≠ 0 := gu6_det_mp_ne (C := C)
  constructor
  · intro h1
    rcases lt_trichotomy 0 (det (edge C.X C.m) (edge C.X C.p)) with h | h | h
    · exact h
    · exact absurd h.symm hne2
    · exact absurd (π.gu6_R_pC_iff.mpr h) (lt_asymm h1)
  · intro h1
    rcases lt_trichotomy (det (edge π.X₁ π.p') (edge π.X₁ π.mC)) 0 with h | h | h
    · exact h
    · exact absurd h hne1
    · exact absurd (π.gu6_R_pC_iff.mp h) (lt_asymm h1)

/-- the sign at `{mB, q'}` of `X₁` is the sign at `{mC, q'}` of `X₀` -/
theorem gu6_key_q : 0 < det (edge π.X₁ π.mB) (edge π.X₁ π.q') ↔ 0 < det (edge π.X₀ π.mC) (edge π.X₀ π.q') := by
  rw [det_swap (edge π.X₁ π.q'), neg_pos, ← gu6_Rmq_iff]
  have hne1 : det (edge π.X₁ π.q') (edge π.X₁ π.mB) ≠ 0 :=
    gu6_det_ne_zero_single π.X₁_generic π.X₁_cross_qB
  have hne2 : det (edge C.X C.m) (edge C.X C.q) ≠ 0 := gu6_det_mq_ne (C := C)
  constructor
  · intro h1
    rcases lt_trichotomy 0 (det (edge C.X C.m) (edge C.X C.q)) with h | h | h
    · exact h
    · exact absurd h.symm hne2
    · exact absurd (π.gu6_R_qB_iff.mpr h) (lt_asymm h1)
  · intro h1
    rcases lt_trichotomy (det (edge π.X₁ π.q') (edge π.X₁ π.mB)) 0 with h | h | h
    · exact h
    · exact absurd h hne1
    · exact absurd (π.gu6_R_qB_iff.mp h) (lt_asymm h1)

/-- the divide sign is carried by the relabelling at every crossing of `X₀` -/
theorem gu6_det_sign_iff {a b : ZMod (k + 3)} (h : IsCrossing π.X₀ {a, b}) :
    0 < det (edge π.X₁ (π.gu6_σ₁ a)) (edge π.X₁ (π.gu6_σ₁ b)) ↔ 0 < det (edge π.X₀ a) (edge π.X₀ b) := by
  have hab : a ≠ b := P1.ne_of_isCrossing_pair h
  by_cases hB : π.mB ∈ ({a, b} : Finset (ZMod (k + 3)))
  · have hs := π.gu6_X₀_cross_mB ⟨_, h⟩ hB
    change ({a, b} : Finset (ZMod (k + 3))) = {π.mB, π.p'} at hs
    have hmem : a ∈ ({π.mB, π.p'} : Finset (ZMod (k + 3))) := by rw [← hs]; exact mem_pair_left _ _
    have hmem' : b ∈ ({π.mB, π.p'} : Finset (ZMod (k + 3))) := by rw [← hs]; exact mem_pair_right _ _
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem hmem'
    have hneA : det (edge π.X₁ π.mC) (edge π.X₁ π.p') ≠ 0 :=
      gu6_det_ne_zero_single π.X₁_generic (by rw [Finset.pair_comm]; exact π.X₁_cross_pC)
    have hneB : det (edge π.X₀ π.mB) (edge π.X₀ π.p') ≠ 0 :=
      gu6_det_ne_zero_single π.X₀_generic π.X₀_cross_mp
    rcases hmem with rfl | rfl <;> rcases hmem' with rfl | rfl
    · exact absurd rfl hab
    · rw [gu6_σ₁_mB, gu6_σ₁_p']; exact π.gu6_key_p
    · rw [gu6_σ₁_mB, gu6_σ₁_p', det_swap (edge π.X₁ π.mC), det_swap (edge π.X₀ π.mB), neg_pos, neg_pos]
      exact gu6_neg_iff_of_pos_iff hneA hneB π.gu6_key_p
    · exact absurd rfl hab
  · by_cases hC : π.mC ∈ ({a, b} : Finset (ZMod (k + 3)))
    · have hs := π.gu6_X₀_cross_mC ⟨_, h⟩ hC
      change ({a, b} : Finset (ZMod (k + 3))) = {π.mC, π.q'} at hs
      have hmem : a ∈ ({π.mC, π.q'} : Finset (ZMod (k + 3))) := by rw [← hs]; exact mem_pair_left _ _
      have hmem' : b ∈ ({π.mC, π.q'} : Finset (ZMod (k + 3))) := by rw [← hs]; exact mem_pair_right _ _
      rw [Finset.mem_insert, Finset.mem_singleton] at hmem hmem'
      have hneA : det (edge π.X₁ π.mB) (edge π.X₁ π.q') ≠ 0 :=
        gu6_det_ne_zero_single π.X₁_generic (by rw [Finset.pair_comm]; exact π.X₁_cross_qB)
      have hneB : det (edge π.X₀ π.mC) (edge π.X₀ π.q') ≠ 0 :=
        gu6_det_ne_zero_single π.X₀_generic π.X₀_cross_mq
      rcases hmem with rfl | rfl <;> rcases hmem' with rfl | rfl
      · exact absurd rfl hab
      · rw [gu6_σ₁_mC, gu6_σ₁_q']; exact π.gu6_key_q
      · rw [gu6_σ₁_mC, gu6_σ₁_q', det_swap (edge π.X₁ π.mB), det_swap (edge π.X₀ π.mC), neg_pos, neg_pos]
        exact gu6_neg_iff_of_pos_iff hneA hneB π.gu6_key_q
      · exact absurd rfl hab
    · rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hB hC
      have ha1 : a ≠ π.mB := fun e => hB.1 e.symm
      have ha2 : a ≠ π.mC := fun e => hC.1 e.symm
      have hb1 : b ≠ π.mB := fun e => hB.2 e.symm
      have hb2 : b ≠ π.mC := fun e => hC.2 e.symm
      rw [π.gu6_σ₁_of_ne ha1 ha2, π.gu6_σ₁_of_ne hb1 hb2, gu6_edge_X₁_of_ne π ha1 ha2,
        gu6_edge_X₁_of_ne π hb1 hb2]

/-- the support of the crossing of an occurrence -/
theorem gu6_sCE_val (v : π.M₀.Γ.Visit) :
    (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ v.1).val = {v.2.val.2, (π.M₀.twin v).2.val.2} := by
  ext l
  have h1 : l ∈ (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ v.1).val ↔
      (⟨0, l⟩ : (Shadow.single ⟨k + 3, π.hk₃, π.X₀⟩).Strand) ∈ v.1.val :=
    Shadow.mem_singleCrossingEquiv_iff _ v.1 ⟨0, l⟩
  have h2 : l ∈ ({v.2.val.2, (π.M₀.twin v).2.val.2} : Finset (ZMod (k + 3))) ↔
      l = v.2.val.2 ∨ l = (π.M₀.twin v).2.val.2 :=
    Finset.mem_insert.trans (or_congr Iff.rfl Finset.mem_singleton)
  exact h1.trans ((((Shadow.single ⟨k + 3, π.hk₃, π.X₀⟩).mem_iff_eq_or_other v.1 v.2.2 _).trans
    (or_congr (gu6_strand_eq_iff _ _) (gu6_strand_eq_iff _ _))).trans h2.symm)

/-- the crossing of an occurrence, as a crossing of the polygon -/
theorem gu6_cross_of_visit (v : π.M₀.Γ.Visit) :
    IsCrossing π.X₀ {v.2.val.2, (π.M₀.twin v).2.val.2} := by
  have h := (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ v.1).2
  rw [← π.gu6_sCE_val v]
  exact h

/-- **over bits are carried by `Ψ₁`** -/
theorem gu6_Ψ₁_overBit (v : π.M₀.Γ.Visit) : π.M₁.overBit (π.gu6_Ψ₁ v) = π.M₀.overBit v := by
  apply Bool.eq_iff_iff.mpr
  refine (gu6_overBit_iff_det π.X₁_generic (π.gu6_Ψ₁ v)).trans
    (Iff.trans ?_ (gu6_overBit_iff_det π.X₀_generic v).symm)
  have e1 := π.gu6_Ψ₁_strand v
  have e2 : (π.M₁.twin (π.gu6_Ψ₁ v)).2.val =
      (⟨0, π.gu6_σ₁ (π.M₀.twin v).2.val.2⟩ : (Shadow.single ⟨k + 3, π.hk₃, π.X₁⟩).Strand) := by
    rw [← gu6_Ψ₁_twin]; exact π.gu6_Ψ₁_strand _
  change 0 < det (π.M₁.Γ.dir (π.gu6_Ψ₁ v).2.val) (π.M₁.Γ.dir (π.M₁.twin (π.gu6_Ψ₁ v)).2.val) ↔
    0 < det (π.M₀.Γ.dir v.2.val) (π.M₀.Γ.dir (π.M₀.twin v).2.val)
  rw [e1, e2]
  exact π.gu6_det_sign_iff (π.gu6_cross_of_visit v)

/-! #### U6 helpers for E1 (c): coordinates -/

theorem gu6_label₀ (v : π.M₀.Γ.Visit) : (π.M₀.visitPt v).2.1 = v.2.val.2 := rfl
theorem gu6_label₁ (v : π.M₁.Γ.Visit) : (π.M₁.visitPt v).2.1 = v.2.val.2 := rfl

theorem gu6_Ψ₁_label (v : π.M₀.Γ.Visit) : (π.M₁.visitPt (π.gu6_Ψ₁ v)).2.1 = π.gu6_σ₁ v.2.val.2 :=
  congrArg (Shadow.singleStrandEquiv ⟨k + 3, π.hk₃, π.X₁⟩) (π.gu6_Ψ₁_strand v)

theorem gu6_Ψ₁_fst (v : π.M₀.Γ.Visit) :
    Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩ (π.gu6_Ψ₁ v).1 =
      π.gu6_κ (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ v.1) := by
  rw [gu6_Ψ₁_apply, gu6_sv_fst']
  rfl

/-- the parameter of an occurrence, through the double point -/
theorem gu6_param_spec₀ (v : π.M₀.Γ.Visit) :
    crossingPoint (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ v.1) =
      edgePoint π.X₀ v.2.val.2 (π.M₀.visitPt v).2.2.val := by
  have h : π.M₀.Γ.crossingPoint v.1 = edgePoint π.X₀ v.2.val.2 (π.M₀.visitPt v).2.2.val :=
    (π.M₀.crossingParam_spec v.1 v.2.2).2.2
  exact (Shadow.single_crossingPoint _ π.X₀_generic v.1).symm.trans h
theorem gu6_param_spec₁ (v : π.M₁.Γ.Visit) :
    crossingPoint (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩ v.1) =
      edgePoint π.X₁ v.2.val.2 (π.M₁.visitPt v).2.2.val := by
  have h : π.M₁.Γ.crossingPoint v.1 = edgePoint π.X₁ v.2.val.2 (π.M₁.visitPt v).2.2.val :=
    (π.M₁.crossingParam_spec v.1 v.2.2).2.2
  exact (Shadow.single_crossingPoint _ π.X₁_generic v.1).symm.trans h

/-! non-local occurrences -/

theorem gu6_nonlocal_not_mem (v : π.M₀.Γ.Visit)
    (hv : v.1 ≠ π.gu6_y_mp ∧ v.1 ≠ π.gu6_y_mq ∧ v.1 ≠ π.gu6_y_pq) :
    π.mB ∉ (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ v.1).val ∧
      π.mC ∉ (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ v.1).val := by
  constructor
  · intro h
    apply hv.1
    show v.1 = (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩).symm (xPair π.X₀_cross_mp)
    exact (Equiv.eq_symm_apply _).mpr (Subtype.ext (π.gu6_X₀_cross_mB _ h))
  · intro h
    apply hv.2.1
    show v.1 = (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩).symm (xPair π.X₀_cross_mq)
    exact (Equiv.eq_symm_apply _).mpr (Subtype.ext (π.gu6_X₀_cross_mC _ h))

theorem gu6_mem_sCE (v : π.M₀.Γ.Visit) :
    v.2.val.2 ∈ (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ v.1).val :=
  (Shadow.mem_singleCrossingEquiv_iff _ _ _).mpr v.2.2

theorem gu6_nonlocal_ne (v : π.M₀.Γ.Visit)
    (hv : v.1 ≠ π.gu6_y_mp ∧ v.1 ≠ π.gu6_y_mq ∧ v.1 ≠ π.gu6_y_pq) :
    v.2.val.2 ≠ π.mB ∧ v.2.val.2 ≠ π.mC :=
  ⟨fun h => (π.gu6_nonlocal_not_mem v hv).1 (h ▸ π.gu6_mem_sCE v),
   fun h => (π.gu6_nonlocal_not_mem v hv).2 (h ▸ π.gu6_mem_sCE v)⟩

theorem gu6_twin_nonlocal (v : π.M₀.Γ.Visit)
    (hv : v.1 ≠ π.gu6_y_mp ∧ v.1 ≠ π.gu6_y_mq ∧ v.1 ≠ π.gu6_y_pq) :
    (π.M₀.twin v).1 ≠ π.gu6_y_mp ∧ (π.M₀.twin v).1 ≠ π.gu6_y_mq ∧ (π.M₀.twin v).1 ≠ π.gu6_y_pq := hv

theorem gu6_edgeSegment_X₁_of_ne {i : ZMod (k + 3)} (hB : i ≠ π.mB) (hC : i ≠ π.mC) :
    edgeSegment π.X₁ i = edgeSegment π.X₀ i := by
  simp only [edgeSegment, edgePoint, gu6_edge_X₁_of_ne π hB hC, gu6_X₁_of_ne π hC]

/-- for a non-local occurrence the relabelled crossing has the same support and the same double
point -/
theorem gu6_κ_val_nonlocal (v : π.M₀.Γ.Visit)
    (hv : v.1 ≠ π.gu6_y_mp ∧ v.1 ≠ π.gu6_y_mq ∧ v.1 ≠ π.gu6_y_pq) :
    (π.gu6_κ (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ v.1)).val =
      (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ v.1).val := by
  rw [gu6_κ_val]
  exact π.gu6_map_of_not_mem (π.gu6_nonlocal_not_mem v hv).1 (π.gu6_nonlocal_not_mem v hv).2

theorem gu6_cp_nonlocal (v : π.M₀.Γ.Visit)
    (hv : v.1 ≠ π.gu6_y_mp ∧ v.1 ≠ π.gu6_y_mq ∧ v.1 ≠ π.gu6_y_pq) :
    crossingPoint (π.gu6_κ (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ v.1)) =
      crossingPoint (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ v.1) := by
  have hval := π.gu6_sCE_val v
  have hne := π.gu6_nonlocal_ne v hv
  have hne' := π.gu6_nonlocal_ne (π.M₀.twin v) (π.gu6_twin_nonlocal v hv)
  have hκ := π.gu6_κ_val_nonlocal v hv
  have h := π.gu6_cross_of_visit v
  have ha : crossingPoint (π.gu6_κ (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ v.1)) ∈
      edgeSegment π.X₀ v.2.val.2 := by
    rw [← gu6_edgeSegment_X₁_of_ne π hne.1 hne.2]
    exact crossingPoint_mem _ _ (by rw [hκ, hval]; exact mem_pair_left _ _)
  have hb : crossingPoint (π.gu6_κ (Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ v.1)) ∈
      edgeSegment π.X₀ (π.M₀.twin v).2.val.2 := by
    rw [← gu6_edgeSegment_X₁_of_ne π hne'.1 hne'.2]
    exact crossingPoint_mem _ _ (by rw [hκ, hval]; exact mem_pair_right _ _)
  rw [gu6_common_eq_single π.X₀_generic h ha hb]
  congr 1
  exact Subtype.ext hval.symm

/-- for a non-local occurrence the coordinate is unchanged -/
theorem gu6_coord_nonlocal (v : π.M₀.Γ.Visit)
    (hv : v.1 ≠ π.gu6_y_mp ∧ v.1 ≠ π.gu6_y_mq ∧ v.1 ≠ π.gu6_y_pq) :
    (π.M₁.visitPt (π.gu6_Ψ₁ v)).2.1 = (π.M₀.visitPt v).2.1 ∧
      (π.M₁.visitPt (π.gu6_Ψ₁ v)).2.2.val = (π.M₀.visitPt v).2.2.val := by
  have hne := π.gu6_nonlocal_ne v hv
  have hl : (π.M₁.visitPt (π.gu6_Ψ₁ v)).2.1 = v.2.val.2 := by
    rw [gu6_Ψ₁_label]; exact π.gu6_σ₁_of_ne hne.1 hne.2
  refine ⟨hl, ?_⟩
  apply edgePoint_injective (π.gu6_edge_X₀_ne_zero v.2.val.2)
  have h1 := π.gu6_param_spec₁ (π.gu6_Ψ₁ v)
  rw [gu6_Ψ₁_fst, gu6_cp_nonlocal π v hv] at h1
  have h2 := π.gu6_param_spec₀ v
  have hl' : (π.gu6_Ψ₁ v).2.val.2 = v.2.val.2 := hl
  rw [hl'] at h1
  have h3 : edgePoint π.X₁ v.2.val.2 (π.M₁.visitPt (π.gu6_Ψ₁ v)).2.2.val =
      edgePoint π.X₀ v.2.val.2 (π.M₁.visitPt (π.gu6_Ψ₁ v)).2.2.val := by
    simp only [edgePoint, gu6_edge_X₁_of_ne π hne.1 hne.2, gu6_X₁_of_ne π hne.2]
  rw [h3] at h1
  exact h1.symm.trans h2

/-! labels and parameters of the twelve local occurrences -/

theorem gu6_w_mp_label : (π.M₀.visitPt π.w_mp).2.1 = π.mB := congrArg Prod.fst π.gu6_w_mp_pt
theorem gu6_w_pm_label : (π.M₀.visitPt π.w_pm).2.1 = π.p' := congrArg Prod.fst π.gu6_w_pm_pt
theorem gu6_w_mq_label : (π.M₀.visitPt π.w_mq).2.1 = π.mC := congrArg Prod.fst π.gu6_w_mq_pt
theorem gu6_w_qm_label : (π.M₀.visitPt π.w_qm).2.1 = π.q' := congrArg Prod.fst π.gu6_w_qm_pt
theorem gu6_w_pq_label : (π.M₀.visitPt π.w_pq).2.1 = π.p' := congrArg Prod.fst π.gu6_w_pq_pt
theorem gu6_w_qp_label : (π.M₀.visitPt π.w_qp).2.1 = π.q' := congrArg Prod.fst π.gu6_w_qp_pt
theorem gu6_w'_pC_label : (π.M₁.visitPt π.gu6_w'_pC).2.1 = π.p' := congrArg Prod.fst π.gu6_w'_pC_pt
theorem gu6_w'_Cp_label : (π.M₁.visitPt π.gu6_w'_Cp).2.1 = π.mC := congrArg Prod.fst π.gu6_w'_Cp_pt
theorem gu6_w'_qB_label : (π.M₁.visitPt π.gu6_w'_qB).2.1 = π.q' := congrArg Prod.fst π.gu6_w'_qB_pt
theorem gu6_w'_Bq_label : (π.M₁.visitPt π.gu6_w'_Bq).2.1 = π.mB := congrArg Prod.fst π.gu6_w'_Bq_pt
theorem gu6_w'_pq_label : (π.M₁.visitPt π.gu6_w'_pq).2.1 = π.p' := congrArg Prod.fst π.gu6_w'_pq_pt
theorem gu6_w'_qp_label : (π.M₁.visitPt π.gu6_w'_qp).2.1 = π.q' := congrArg Prod.fst π.gu6_w'_qp_pt

theorem gu6_w_mp_param : (π.M₀.visitPt π.w_mp).2.2.val = π.gu6_s_mp :=
  congrArg (fun q : TraversalPoint (k + 3) => q.2.val) π.gu6_w_mp_pt
theorem gu6_w_pm_param : (π.M₀.visitPt π.w_pm).2.2.val = π.gu6_s_pm :=
  congrArg (fun q : TraversalPoint (k + 3) => q.2.val) π.gu6_w_pm_pt
theorem gu6_w_mq_param : (π.M₀.visitPt π.w_mq).2.2.val = π.gu6_s_mq :=
  congrArg (fun q : TraversalPoint (k + 3) => q.2.val) π.gu6_w_mq_pt
theorem gu6_w_qm_param : (π.M₀.visitPt π.w_qm).2.2.val = π.gu6_s_qm :=
  congrArg (fun q : TraversalPoint (k + 3) => q.2.val) π.gu6_w_qm_pt
theorem gu6_w_pq_param : (π.M₀.visitPt π.w_pq).2.2.val = π.gu6_s_pq :=
  congrArg (fun q : TraversalPoint (k + 3) => q.2.val) π.gu6_w_pq_pt
theorem gu6_w_qp_param : (π.M₀.visitPt π.w_qp).2.2.val = π.gu6_s_qp :=
  congrArg (fun q : TraversalPoint (k + 3) => q.2.val) π.gu6_w_qp_pt
theorem gu6_w'_pC_param : (π.M₁.visitPt π.gu6_w'_pC).2.2.val = π.gu6_s'_pC :=
  congrArg (fun q : TraversalPoint (k + 3) => q.2.val) π.gu6_w'_pC_pt
theorem gu6_w'_Cp_param : (π.M₁.visitPt π.gu6_w'_Cp).2.2.val = π.gu6_s'_Cp :=
  congrArg (fun q : TraversalPoint (k + 3) => q.2.val) π.gu6_w'_Cp_pt
theorem gu6_w'_qB_param : (π.M₁.visitPt π.gu6_w'_qB).2.2.val = π.gu6_s'_qB :=
  congrArg (fun q : TraversalPoint (k + 3) => q.2.val) π.gu6_w'_qB_pt
theorem gu6_w'_Bq_param : (π.M₁.visitPt π.gu6_w'_Bq).2.2.val = π.gu6_s'_Bq :=
  congrArg (fun q : TraversalPoint (k + 3) => q.2.val) π.gu6_w'_Bq_pt
theorem gu6_w'_pq_param : (π.M₁.visitPt π.gu6_w'_pq).2.2.val = π.gu6_s'_pq :=
  congrArg (fun q : TraversalPoint (k + 3) => q.2.val) π.gu6_w'_pq_pt
theorem gu6_w'_qp_param : (π.M₁.visitPt π.gu6_w'_qp).2.2.val = π.gu6_s'_qp :=
  congrArg (fun q : TraversalPoint (k + 3) => q.2.val) π.gu6_w'_qp_pt

/-! the D9 reversal in the form used for the gap argument -/

theorem gu6_s_pm_ne_pq : π.gu6_s_pm ≠ π.gu6_s_pq := by
  intro h
  have h1 := π.gu6_s_pm_spec
  rw [h, ← gu6_s_pq_spec] at h1
  have h2 := congrArg Subtype.val (gu6_cp_injective_single π.X₀_generic h1)
  change ({π.mB, π.p'} : Finset (ZMod (k + 3))) = {π.p', π.q'} at h2
  have : π.mB ∈ ({π.p', π.q'} : Finset (ZMod (k + 3))) := by rw [← h2]; exact mem_pair_left _ _
  rw [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with e | e
  · exact π.gu6_lab_ne_mB C.p e.symm
  · exact π.gu6_lab_ne_mB C.q e.symm

theorem gu6_s_pq_ne_pC : π.gu6_s_pq ≠ π.gu6_s'_pC := by
  intro h
  have h1 := π.gu6_s'_pq_spec
  rw [gu6_s'_pq_eq, h, ← gu6_s'_pC_spec] at h1
  have h2 := congrArg Subtype.val (gu6_cp_injective_single π.X₁_generic h1)
  change ({π.p', π.q'} : Finset (ZMod (k + 3))) = {π.p', π.mC} at h2
  have : π.q' ∈ ({π.p', π.mC} : Finset (ZMod (k + 3))) := by rw [← h2]; exact mem_pair_right _ _
  rw [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with e | e
  · exact π.gu6_p'_ne_q' e.symm
  · exact π.gu6_lab_ne_mC C.q e

theorem gu6_s_qm_ne_qp : π.gu6_s_qm ≠ π.gu6_s_qp := by
  intro h
  have h1 := π.gu6_s_qm_spec
  rw [h, ← gu6_s_qp_spec] at h1
  have h2 := congrArg Subtype.val (gu6_cp_injective_single π.X₀_generic h1)
  change ({π.mC, π.q'} : Finset (ZMod (k + 3))) = {π.p', π.q'} at h2
  have : π.mC ∈ ({π.p', π.q'} : Finset (ZMod (k + 3))) := by rw [← h2]; exact mem_pair_left _ _
  rw [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with e | e
  · exact π.gu6_lab_ne_mC C.p e.symm
  · exact π.gu6_lab_ne_mC C.q e.symm

theorem gu6_s_qp_ne_qB : π.gu6_s_qp ≠ π.gu6_s'_qB := by
  intro h
  have h1 := π.gu6_s'_qp_spec
  rw [gu6_s'_qp_eq, h, ← gu6_s'_qB_spec] at h1
  have h2 := congrArg Subtype.val (gu6_cp_injective_single π.X₁_generic h1)
  change ({π.p', π.q'} : Finset (ZMod (k + 3))) = {π.q', π.mB} at h2
  have : π.p' ∈ ({π.q', π.mB} : Finset (ZMod (k + 3))) := by rw [← h2]; exact mem_pair_left _ _
  rw [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with e | e
  · exact π.gu6_p'_ne_q' e
  · exact π.gu6_lab_ne_mB C.p e

theorem gu6_D9_p' : π.gu6_s'_pC < π.gu6_s_pq ↔ π.gu6_s_pq < π.gu6_s_pm := by
  have h := π.gu6_D9_p
  have h1 := π.gu6_s_pm_ne_pq
  have h2 := π.gu6_s_pq_ne_pC
  constructor
  · intro hlt
    rcases lt_trichotomy π.gu6_s_pq π.gu6_s_pm with h3 | h3 | h3
    · exact h3
    · exact absurd h3.symm h1
    · exact absurd (h.mp h3) (lt_asymm hlt)
  · intro hlt
    rcases lt_trichotomy π.gu6_s'_pC π.gu6_s_pq with h3 | h3 | h3
    · exact h3
    · exact absurd h3.symm h2
    · exact absurd (h.mpr h3) (lt_asymm hlt)

theorem gu6_D9_q' : π.gu6_s'_qB < π.gu6_s_qp ↔ π.gu6_s_qp < π.gu6_s_qm := by
  have h := π.gu6_D9_q
  have h1 := π.gu6_s_qm_ne_qp
  have h2 := π.gu6_s_qp_ne_qB
  constructor
  · intro hlt
    rcases lt_trichotomy π.gu6_s_qp π.gu6_s_qm with h3 | h3 | h3
    · exact h3
    · exact absurd h3.symm h1
    · exact absurd (h.mp h3) (lt_asymm hlt)
  · intro hlt
    rcases lt_trichotomy π.gu6_s'_qB π.gu6_s_qp with h3 | h3 | h3
    · exact h3
    · exact absurd h3.symm h2
    · exact absurd (h.mpr h3) (lt_asymm hlt)

/-! twins of the local occurrences and the case split -/

theorem gu6_w_mp_ne_pm : π.w_mp ≠ π.w_pm := gu6_sv_ne _ _ _ (π.gu6_lab_ne_mB C.p).symm
theorem gu6_w_mq_ne_qm : π.w_mq ≠ π.w_qm := gu6_sv_ne _ _ _ (π.gu6_lab_ne_mC C.q).symm
theorem gu6_w_pq_ne_qp : π.w_pq ≠ π.w_qp := gu6_sv_ne _ _ _ π.gu6_p'_ne_q'
theorem gu6_w'_pC_ne_Cp : π.gu6_w'_pC ≠ π.gu6_w'_Cp := gu6_sv_ne _ _ _ (π.gu6_lab_ne_mC C.p)
theorem gu6_w'_qB_ne_Bq : π.gu6_w'_qB ≠ π.gu6_w'_Bq := gu6_sv_ne _ _ _ (π.gu6_lab_ne_mB C.q)
theorem gu6_w'_pq_ne_qp : π.gu6_w'_pq ≠ π.gu6_w'_qp := gu6_sv_ne _ _ _ π.gu6_p'_ne_q'

theorem gu6_twin_w_mp : π.M₀.twin π.w_mp = π.w_pm :=
  (π.M₀.twin_unique _ _ (π.gu6_w_pm_fst.trans π.gu6_w_mp_fst.symm) π.gu6_w_mp_ne_pm.symm).symm
theorem gu6_twin_w_mq : π.M₀.twin π.w_mq = π.w_qm :=
  (π.M₀.twin_unique _ _ (π.gu6_w_qm_fst.trans π.gu6_w_mq_fst.symm) π.gu6_w_mq_ne_qm.symm).symm
theorem gu6_twin_w_pq : π.M₀.twin π.w_pq = π.w_qp :=
  (π.M₀.twin_unique _ _ (π.gu6_w_qp_fst.trans π.gu6_w_pq_fst.symm) π.gu6_w_pq_ne_qp.symm).symm

/-- every occurrence of `M₀` is one of the six local ones or off the three local crossings -/
theorem gu6_M₀_cases (x : π.M₀.Γ.Visit) :
    (x = π.w_mp ∨ x = π.w_pm ∨ x = π.w_mq ∨ x = π.w_qm ∨ x = π.w_pq ∨ x = π.w_qp) ∨
      (x.1 ≠ π.gu6_y_mp ∧ x.1 ≠ π.gu6_y_mq ∧ x.1 ≠ π.gu6_y_pq) := by
  by_cases h1 : x.1 = π.gu6_y_mp
  · left
    rcases π.M₀.eq_or_eq_twin π.w_mp x (h1.trans π.gu6_w_mp_fst.symm) with h | h
    · exact Or.inl h
    · rw [gu6_twin_w_mp] at h
      exact Or.inr (Or.inl h)
  by_cases h2 : x.1 = π.gu6_y_mq
  · left
    rcases π.M₀.eq_or_eq_twin π.w_mq x (h2.trans π.gu6_w_mq_fst.symm) with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · rw [gu6_twin_w_mq] at h
      exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  by_cases h3 : x.1 = π.gu6_y_pq
  · left
    rcases π.M₀.eq_or_eq_twin π.w_pq x (h3.trans π.gu6_w_pq_fst.symm) with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · rw [gu6_twin_w_pq] at h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exact Or.inr ⟨h1, h2, h3⟩

/-- the double point of a non-local occurrence is not in the open disc -/
theorem gu6_nonlocal_not_interior (v : π.M₀.Γ.Visit)
    (hv : v.1 ≠ π.gu6_y_mp ∧ v.1 ≠ π.gu6_y_mq ∧ v.1 ≠ π.gu6_y_pq) :
    edgePoint π.X₀ v.2.val.2 (π.M₀.visitPt v).2.2.val ∉ interior π.U := by
  intro h
  have h' : π.M₀.Γ.crossingPoint v.1 ∈ interior π.U := by
    have e : π.M₀.Γ.crossingPoint v.1 = edgePoint π.X₀ v.2.val.2 (π.M₀.visitPt v).2.2.val :=
      (π.M₀.crossingParam_spec v.1 v.2.2).2.2
    rw [e]; exact h
  rcases (π.gu6_inner0 v.1).mp h' with e | e | e
  · exact hv.1 e
  · exact hv.2.1 e
  · exact hv.2.2 e

/-! #### U6 helpers for E1 (d): the transpositions on the lift, and the twisted key comparison -/

theorem gu6_σD_v_mp : C.σD C.v_mp = C.v_mq := by
  unfold G11_ConfigSw.v_mp G11_ConfigSw.v_mq
  rw [gu6_σD_apply, gu6_σ_vmp]
theorem gu6_σD_v_mq : C.σD C.v_mq = C.v_mp := by
  unfold G11_ConfigSw.v_mq G11_ConfigSw.v_mp
  rw [gu6_σD_apply, gu6_σ_vmq]
theorem gu6_σD_v_pm : C.σD C.v_pm = C.v_pq := by
  unfold G11_ConfigSw.v_pm G11_ConfigSw.v_pq
  rw [gu6_σD_apply, gu6_σ_vpm]
theorem gu6_σD_v_pq : C.σD C.v_pq = C.v_pm := by
  unfold G11_ConfigSw.v_pq G11_ConfigSw.v_pm
  rw [gu6_σD_apply, gu6_σ_vpq]
theorem gu6_σD_v_qm : C.σD C.v_qm = C.v_qp := by
  unfold G11_ConfigSw.v_qm G11_ConfigSw.v_qp
  rw [gu6_σD_apply, gu6_σ_vqm]
theorem gu6_σD_v_qp : C.σD C.v_qp = C.v_qm := by
  unfold G11_ConfigSw.v_qp G11_ConfigSw.v_qm
  rw [gu6_σD_apply, gu6_σ_vqp]

theorem gu6_σD_of_not_local (u : C.D₀.Γ.Visit) (h1 : u ≠ C.v_mp) (h2 : u ≠ C.v_pm) (h3 : u ≠ C.v_mq)
    (h4 : u ≠ C.v_qm) (h5 : u ≠ C.v_pq) (h6 : u ≠ C.v_qp) : C.σD u = u := by
  have hu : (Shadow.singleVisitEquiv C.comp).symm (Shadow.singleVisitEquiv C.comp u) = u :=
    Equiv.symm_apply_apply _ _
  have key : ∀ x : Visit C.X, u ≠ (Shadow.singleVisitEquiv C.comp).symm x →
      Shadow.singleVisitEquiv C.comp u ≠ x := fun x hne e => hne (by rw [← e]; exact hu.symm)
  have e1 : C.σD u = C.σD ((Shadow.singleVisitEquiv C.comp).symm (Shadow.singleVisitEquiv C.comp u)) :=
    (congrArg (fun z => C.σD z) hu).symm
  have e2 := gu6_σD_apply C (Shadow.singleVisitEquiv C.comp u)
  rw [e1, e2, gu6_σ_of_not_local C _ (key _ h1) (key _ h3) (key _ h2) (key _ h5) (key _ h4) (key _ h6)]
  exact hu

/-! the six local parameters are inside the open disc -/

theorem gu6_in_pC : edgePoint π.X₀ π.p' π.gu6_s'_pC ∈ interior π.U := by
  rw [gu6_edgePoint_X₀_p', ← gu6_edgePoint_X₁_p', ← gu6_s'_pC_spec]; exact π.gu6_xpC_interior
theorem gu6_in_pq : edgePoint π.X₀ π.p' π.gu6_s_pq ∈ interior π.U := by
  rw [← gu6_s_pq_spec, gu6_cp0_pq]; exact π.gu6_xpq_interior
theorem gu6_in_pm : edgePoint π.X₀ π.p' π.gu6_s_pm ∈ interior π.U := by
  rw [← gu6_s_pm_spec, gu6_cp0_mp]; exact π.gu6_xmp_interior
theorem gu6_in_qB : edgePoint π.X₀ π.q' π.gu6_s'_qB ∈ interior π.U := by
  rw [gu6_edgePoint_X₀_q', ← gu6_edgePoint_X₁_q', ← gu6_s'_qB_spec]; exact π.gu6_xqB_interior
theorem gu6_in_qp : edgePoint π.X₀ π.q' π.gu6_s_qp ∈ interior π.U := by
  rw [← gu6_s_qp_spec, gu6_cp0_pq]; exact π.gu6_xpq_interior
theorem gu6_in_qm : edgePoint π.X₀ π.q' π.gu6_s_qm ∈ interior π.U := by
  rw [← gu6_s_qm_spec, gu6_cp0_mq]; exact π.gu6_xmq_interior

/-- **(L)** the strand label of `Ψ₁ x` is the strand label of `σ₀ x` -/
theorem gu6_label_eq (σ₀ : π.M₀.Γ.Visit → π.M₀.Γ.Visit)
    (h1 : σ₀ π.w_mp = π.w_mq) (h2 : σ₀ π.w_mq = π.w_mp) (h3 : σ₀ π.w_pm = π.w_pq) (h4 : σ₀ π.w_pq = π.w_pm)
    (h5 : σ₀ π.w_qm = π.w_qp) (h6 : σ₀ π.w_qp = π.w_qm)
    (h0 : ∀ x, x.1 ≠ π.gu6_y_mp ∧ x.1 ≠ π.gu6_y_mq ∧ x.1 ≠ π.gu6_y_pq → σ₀ x = x) (x : π.M₀.Γ.Visit) :
    (π.M₁.visitPt (π.gu6_Ψ₁ x)).2.1 = (π.M₀.visitPt (σ₀ x)).2.1 := by
  rcases π.gu6_M₀_cases x with (rfl | rfl | rfl | rfl | rfl | rfl) | hx
  · rw [h1, gu6_Ψ₁_w_mp, gu6_w'_Cp_label, gu6_w_mq_label]
  · rw [h3, gu6_Ψ₁_w_pm, gu6_w'_pC_label, gu6_w_pq_label]
  · rw [h2, gu6_Ψ₁_w_mq, gu6_w'_Bq_label, gu6_w_mp_label]
  · rw [h5, gu6_Ψ₁_w_qm, gu6_w'_qB_label, gu6_w_qp_label]
  · rw [h4, gu6_Ψ₁_w_pq, gu6_w'_pq_label, gu6_w_pm_label]
  · rw [h6, gu6_Ψ₁_w_qp, gu6_w'_qp_label, gu6_w_qm_label]
  · rw [h0 x hx]; exact (π.gu6_coord_nonlocal x hx).1

/-- **(P)** for occurrences whose `σ₀`-images share the strand, the parameters of the `Ψ₁`-images
compare as the parameters of the `σ₀`-images (the gap argument: same edges keep their parameters,
the two local parameters of `p'` (resp. `q'`) are reversed (D9), and an outside parameter compares
alike with all inside parameters) -/
theorem gu6_param_iff (σ₀ : π.M₀.Γ.Visit → π.M₀.Γ.Visit)
    (h1 : σ₀ π.w_mp = π.w_mq) (h2 : σ₀ π.w_mq = π.w_mp) (h3 : σ₀ π.w_pm = π.w_pq) (h4 : σ₀ π.w_pq = π.w_pm)
    (h5 : σ₀ π.w_qm = π.w_qp) (h6 : σ₀ π.w_qp = π.w_qm)
    (h0 : ∀ x, x.1 ≠ π.gu6_y_mp ∧ x.1 ≠ π.gu6_y_mq ∧ x.1 ≠ π.gu6_y_pq → σ₀ x = x) (x y : π.M₀.Γ.Visit)
    (hL : (π.M₀.visitPt (σ₀ x)).2.1 = (π.M₀.visitPt (σ₀ y)).2.1) :
    (π.M₁.visitPt (π.gu6_Ψ₁ x)).2.2.val < (π.M₁.visitPt (π.gu6_Ψ₁ y)).2.2.val ↔
      (π.M₀.visitPt (σ₀ x)).2.2.val < (π.M₀.visitPt (σ₀ y)).2.2.val := by
  have hmBC := π.gu6_mB_ne_mC
  have hpB := π.gu6_lab_ne_mB C.p
  have hpC := π.gu6_lab_ne_mC C.p
  have hqB := π.gu6_lab_ne_mB C.q
  have hqC := π.gu6_lab_ne_mC C.q
  have hpq := π.gu6_p'_ne_q'
  rcases π.gu6_M₀_cases x with (rfl | rfl | rfl | rfl | rfl | rfl) | hx <;>
    rcases π.gu6_M₀_cases y with (rfl | rfl | rfl | rfl | rfl | rfl) | hy
  -- x = w_mp (label mC)
  · exact iff_of_false (lt_irrefl _) (lt_irrefl _)
  · rw [h1, h3, gu6_w_mq_label, gu6_w_pq_label] at hL; exact absurd hL.symm hpC
  · rw [h1, h2, gu6_w_mq_label, gu6_w_mp_label] at hL; exact absurd hL.symm hmBC
  · rw [h1, h5, gu6_w_mq_label, gu6_w_qp_label] at hL; exact absurd hL.symm hqC
  · rw [h1, h4, gu6_w_mq_label, gu6_w_pm_label] at hL; exact absurd hL.symm hpC
  · rw [h1, h6, gu6_w_mq_label, gu6_w_qm_label] at hL; exact absurd hL.symm hqC
  · rw [h1, h0 y hy, gu6_w_mq_label, gu6_label₀] at hL; exact absurd hL.symm (π.gu6_nonlocal_ne y hy).2
  -- x = w_pm (label p')
  · rw [h3, h1, gu6_w_pq_label, gu6_w_mq_label] at hL; exact absurd hL hpC
  · exact iff_of_false (lt_irrefl _) (lt_irrefl _)
  · rw [h3, h2, gu6_w_pq_label, gu6_w_mp_label] at hL; exact absurd hL hpB
  · rw [h3, h5, gu6_w_pq_label, gu6_w_qp_label] at hL; exact absurd hL hpq
  · rw [h3, h4, gu6_Ψ₁_w_pm, gu6_Ψ₁_w_pq, gu6_w'_pC_param, gu6_w'_pq_param, gu6_w_pq_param,
      gu6_w_pm_param, gu6_s'_pq_eq]
    exact π.gu6_D9_p'
  · rw [h3, h6, gu6_w_pq_label, gu6_w_qm_label] at hL; exact absurd hL hpq
  · rw [h3, h0 y hy, gu6_w_pq_label, gu6_label₀] at hL
    rw [h3, h0 y hy, gu6_Ψ₁_w_pm, gu6_w'_pC_param, gu6_w_pq_param, (π.gu6_coord_nonlocal y hy).2]
    have hz := π.gu6_nonlocal_not_interior y hy
    rw [← hL] at hz
    exact (gu6_outside_cmp π.gu6_U_convex π.X₀ π.p' π.gu6_in_pC π.gu6_in_pq hz).1
  -- x = w_mq (label mB)
  · rw [h2, h1, gu6_w_mp_label, gu6_w_mq_label] at hL; exact absurd hL hmBC
  · rw [h2, h3, gu6_w_mp_label, gu6_w_pq_label] at hL; exact absurd hL.symm hpB
  · exact iff_of_false (lt_irrefl _) (lt_irrefl _)
  · rw [h2, h5, gu6_w_mp_label, gu6_w_qp_label] at hL; exact absurd hL.symm hqB
  · rw [h2, h4, gu6_w_mp_label, gu6_w_pm_label] at hL; exact absurd hL.symm hpB
  · rw [h2, h6, gu6_w_mp_label, gu6_w_qm_label] at hL; exact absurd hL.symm hqB
  · rw [h2, h0 y hy, gu6_w_mp_label, gu6_label₀] at hL; exact absurd hL.symm (π.gu6_nonlocal_ne y hy).1
  -- x = w_qm (label q')
  · rw [h5, h1, gu6_w_qp_label, gu6_w_mq_label] at hL; exact absurd hL hqC
  · rw [h5, h3, gu6_w_qp_label, gu6_w_pq_label] at hL; exact absurd hL.symm hpq
  · rw [h5, h2, gu6_w_qp_label, gu6_w_mp_label] at hL; exact absurd hL hqB
  · exact iff_of_false (lt_irrefl _) (lt_irrefl _)
  · rw [h5, h4, gu6_w_qp_label, gu6_w_pm_label] at hL; exact absurd hL.symm hpq
  · rw [h5, h6, gu6_Ψ₁_w_qm, gu6_Ψ₁_w_qp, gu6_w'_qB_param, gu6_w'_qp_param, gu6_w_qp_param,
      gu6_w_qm_param, gu6_s'_qp_eq]
    exact π.gu6_D9_q'
  · rw [h5, h0 y hy, gu6_w_qp_label, gu6_label₀] at hL
    rw [h5, h0 y hy, gu6_Ψ₁_w_qm, gu6_w'_qB_param, gu6_w_qp_param, (π.gu6_coord_nonlocal y hy).2]
    have hz := π.gu6_nonlocal_not_interior y hy
    rw [← hL] at hz
    exact (gu6_outside_cmp π.gu6_U_convex π.X₀ π.q' π.gu6_in_qB π.gu6_in_qp hz).1
  -- x = w_pq (label p')
  · rw [h4, h1, gu6_w_pm_label, gu6_w_mq_label] at hL; exact absurd hL hpC
  · rw [h4, h3, gu6_Ψ₁_w_pq, gu6_Ψ₁_w_pm, gu6_w'_pq_param, gu6_w'_pC_param, gu6_w_pm_param,
      gu6_w_pq_param, gu6_s'_pq_eq]
    exact π.gu6_D9_p.symm
  · rw [h4, h2, gu6_w_pm_label, gu6_w_mp_label] at hL; exact absurd hL hpB
  · rw [h4, h5, gu6_w_pm_label, gu6_w_qp_label] at hL; exact absurd hL hpq
  · exact iff_of_false (lt_irrefl _) (lt_irrefl _)
  · rw [h4, h6, gu6_w_pm_label, gu6_w_qm_label] at hL; exact absurd hL hpq
  · rw [h4, h0 y hy, gu6_w_pm_label, gu6_label₀] at hL
    rw [h4, h0 y hy, gu6_Ψ₁_w_pq, gu6_w'_pq_param, gu6_w_pm_param, (π.gu6_coord_nonlocal y hy).2,
      gu6_s'_pq_eq]
    have hz := π.gu6_nonlocal_not_interior y hy
    rw [← hL] at hz
    exact (gu6_outside_cmp π.gu6_U_convex π.X₀ π.p' π.gu6_in_pq π.gu6_in_pm hz).1
  -- x = w_qp (label q')
  · rw [h6, h1, gu6_w_qm_label, gu6_w_mq_label] at hL; exact absurd hL hqC
  · rw [h6, h3, gu6_w_qm_label, gu6_w_pq_label] at hL; exact absurd hL.symm hpq
  · rw [h6, h2, gu6_w_qm_label, gu6_w_mp_label] at hL; exact absurd hL hqB
  · rw [h6, h5, gu6_Ψ₁_w_qp, gu6_Ψ₁_w_qm, gu6_w'_qp_param, gu6_w'_qB_param, gu6_w_qm_param,
      gu6_w_qp_param, gu6_s'_qp_eq]
    exact π.gu6_D9_q.symm
  · rw [h6, h4, gu6_w_qm_label, gu6_w_pm_label] at hL; exact absurd hL.symm hpq
  · exact iff_of_false (lt_irrefl _) (lt_irrefl _)
  · rw [h6, h0 y hy, gu6_w_qm_label, gu6_label₀] at hL
    rw [h6, h0 y hy, gu6_Ψ₁_w_qp, gu6_w'_qp_param, gu6_w_qm_param, (π.gu6_coord_nonlocal y hy).2,
      gu6_s'_qp_eq]
    have hz := π.gu6_nonlocal_not_interior y hy
    rw [← hL] at hz
    exact (gu6_outside_cmp π.gu6_U_convex π.X₀ π.q' π.gu6_in_qp π.gu6_in_qm hz).1
  -- x non-local
  · rw [h0 x hx, h1, gu6_label₀, gu6_w_mq_label] at hL; exact absurd hL (π.gu6_nonlocal_ne x hx).2
  · rw [h0 x hx, h3, gu6_label₀, gu6_w_pq_label] at hL
    rw [h0 x hx, h3, gu6_Ψ₁_w_pm, gu6_w'_pC_param, gu6_w_pq_param, (π.gu6_coord_nonlocal x hx).2]
    have hz := π.gu6_nonlocal_not_interior x hx
    rw [hL] at hz
    exact (gu6_outside_cmp π.gu6_U_convex π.X₀ π.p' π.gu6_in_pC π.gu6_in_pq hz).2
  · rw [h0 x hx, h2, gu6_label₀, gu6_w_mp_label] at hL; exact absurd hL (π.gu6_nonlocal_ne x hx).1
  · rw [h0 x hx, h5, gu6_label₀, gu6_w_qp_label] at hL
    rw [h0 x hx, h5, gu6_Ψ₁_w_qm, gu6_w'_qB_param, gu6_w_qp_param, (π.gu6_coord_nonlocal x hx).2]
    have hz := π.gu6_nonlocal_not_interior x hx
    rw [hL] at hz
    exact (gu6_outside_cmp π.gu6_U_convex π.X₀ π.q' π.gu6_in_qB π.gu6_in_qp hz).2
  · rw [h0 x hx, h4, gu6_label₀, gu6_w_pm_label] at hL
    rw [h0 x hx, h4, gu6_Ψ₁_w_pq, gu6_w'_pq_param, gu6_w_pm_param, (π.gu6_coord_nonlocal x hx).2,
      gu6_s'_pq_eq]
    have hz := π.gu6_nonlocal_not_interior x hx
    rw [hL] at hz
    exact (gu6_outside_cmp π.gu6_U_convex π.X₀ π.p' π.gu6_in_pq π.gu6_in_pm hz).2
  · rw [h0 x hx, h6, gu6_label₀, gu6_w_qm_label] at hL
    rw [h0 x hx, h6, gu6_Ψ₁_w_qp, gu6_w'_qp_param, gu6_w_qm_param, (π.gu6_coord_nonlocal x hx).2,
      gu6_s'_qp_eq]
    have hz := π.gu6_nonlocal_not_interior x hx
    rw [hL] at hz
    exact (gu6_outside_cmp π.gu6_U_convex π.X₀ π.q' π.gu6_in_qp π.gu6_in_qm hz).2
  · rw [h0 x hx, h0 y hy, (π.gu6_coord_nonlocal x hx).2, (π.gu6_coord_nonlocal y hy).2]

/-- **the twisted key comparison** -/
theorem gu6_key_lt (σ₀ : π.M₀.Γ.Visit → π.M₀.Γ.Visit)
    (h1 : σ₀ π.w_mp = π.w_mq) (h2 : σ₀ π.w_mq = π.w_mp) (h3 : σ₀ π.w_pm = π.w_pq) (h4 : σ₀ π.w_pq = π.w_pm)
    (h5 : σ₀ π.w_qm = π.w_qp) (h6 : σ₀ π.w_qp = π.w_qm)
    (h0 : ∀ x, x.1 ≠ π.gu6_y_mp ∧ x.1 ≠ π.gu6_y_mq ∧ x.1 ≠ π.gu6_y_pq → σ₀ x = x) (x y : π.M₀.Γ.Visit) :
    π.M₁.visitCoord (π.gu6_Ψ₁ x) < π.M₁.visitCoord (π.gu6_Ψ₁ y) ↔
      π.M₀.visitCoord (σ₀ x) < π.M₀.visitCoord (σ₀ y) := by
  have e1 := traversalKey_lt_iff (n := k + 3) (π.M₁.visitPt (π.gu6_Ψ₁ x)).2 (π.M₁.visitPt (π.gu6_Ψ₁ y)).2
  have e2 := traversalKey_lt_iff (n := k + 3) (π.M₀.visitPt (σ₀ x)).2 (π.M₀.visitPt (σ₀ y)).2
  refine e1.trans (Iff.trans ?_ e2.symm)
  rw [π.gu6_label_eq σ₀ h1 h2 h3 h4 h5 h6 h0 x, π.gu6_label_eq σ₀ h1 h2 h3 h4 h5 h6 h0 y]
  exact or_congr Iff.rfl (and_congr_right fun hL => π.gu6_param_iff σ₀ h1 h2 h3 h4 h5 h6 h0 x y hL)

/-- **E1.** The occurrence bijection `M₀ ≃ M₁`: the identity on crossings not involving `mB, mC`
(`X₁_cross_iff`), `x_mp ↦ x_mp' = {p', mC}`, `x_mq ↦ x_mq' = {q', mB}` (keeping the strand `p'`, resp.
`q'`, and sending the `m`-piece to the other bent edge); twins, over bits (`X₁_sign_*`) and signs (all
`+1`) carried; and **the cyclic order twisted by the three transpositions** — the gap argument: every
occurrence off the three local strands keeps its traversal key; the two occurrences on `p'` (resp. `q'`)
stay in the gap of `p'` (resp. `q'`) inside `U`, which contains no other occurrence (`inner_M₀`,
`inner_M₁`), and their order is reversed (`BeforeOn` reversal); on the `m`-arc the pieces `mB`, `mC` each
carry exactly one occurrence on each side, exchanged. -/
theorem exists_Ψ₁ (Ψ₀ : C.D₀.Γ.Visit ≃ π.M₀.Γ.Visit)
    (h₀ : ∀ u v w, π.M₀.VisitBetween (Ψ₀ u) (Ψ₀ v) (Ψ₀ w) ↔ C.D₀.VisitBetween u v w)
    (hmp : Ψ₀ C.v_mp = π.w_mp) (hpm : Ψ₀ C.v_pm = π.w_pm) (hmq : Ψ₀ C.v_mq = π.w_mq)
    (hqm : Ψ₀ C.v_qm = π.w_qm) (hpq : Ψ₀ C.v_pq = π.w_pq) (hqp : Ψ₀ C.v_qp = π.w_qp) :
    ∃ Ψ₁ : π.M₀.Γ.Visit ≃ π.M₁.Γ.Visit,
      (∀ v, Ψ₁ (π.M₀.twin v) = π.M₁.twin (Ψ₁ v)) ∧
      (∀ v, π.M₁.overBit (Ψ₁ v) = π.M₀.overBit v) ∧
      (∀ v, π.M₁.sign (Ψ₁ v).1 = π.M₀.sign v.1) ∧
      (∀ u v w : C.D₀.Γ.Visit, π.M₁.VisitBetween (Ψ₁ (Ψ₀ u)) (Ψ₁ (Ψ₀ v)) (Ψ₁ (Ψ₀ w)) ↔
        C.D₀.VisitBetween (C.σD u) (C.σD v) (C.σD w)) := by
  refine ⟨π.gu6_Ψ₁, π.gu6_Ψ₁_twin, π.gu6_Ψ₁_overBit, π.gu6_Ψ₁_sign, ?_⟩
  intro u v w
  let σ₀ : π.M₀.Γ.Visit → π.M₀.Γ.Visit := fun x => Ψ₀ (C.σD (Ψ₀.symm x))
  have e_mp : σ₀ π.w_mp = π.w_mq := by
    show Ψ₀ (C.σD (Ψ₀.symm π.w_mp)) = π.w_mq
    rw [← hmp, Equiv.symm_apply_apply, gu6_σD_v_mp, hmq]
  have e_mq : σ₀ π.w_mq = π.w_mp := by
    show Ψ₀ (C.σD (Ψ₀.symm π.w_mq)) = π.w_mp
    rw [← hmq, Equiv.symm_apply_apply, gu6_σD_v_mq, hmp]
  have e_pm : σ₀ π.w_pm = π.w_pq := by
    show Ψ₀ (C.σD (Ψ₀.symm π.w_pm)) = π.w_pq
    rw [← hpm, Equiv.symm_apply_apply, gu6_σD_v_pm, hpq]
  have e_pq : σ₀ π.w_pq = π.w_pm := by
    show Ψ₀ (C.σD (Ψ₀.symm π.w_pq)) = π.w_pm
    rw [← hpq, Equiv.symm_apply_apply, gu6_σD_v_pq, hpm]
  have e_qm : σ₀ π.w_qm = π.w_qp := by
    show Ψ₀ (C.σD (Ψ₀.symm π.w_qm)) = π.w_qp
    rw [← hqm, Equiv.symm_apply_apply, gu6_σD_v_qm, hqp]
  have e_qp : σ₀ π.w_qp = π.w_qm := by
    show Ψ₀ (C.σD (Ψ₀.symm π.w_qp)) = π.w_qm
    rw [← hqp, Equiv.symm_apply_apply, gu6_σD_v_qp, hqm]
  have e0 : ∀ x, x.1 ≠ π.gu6_y_mp ∧ x.1 ≠ π.gu6_y_mq ∧ x.1 ≠ π.gu6_y_pq → σ₀ x = x := by
    intro x hx
    show Ψ₀ (C.σD (Ψ₀.symm x)) = x
    rw [gu6_σD_of_not_local (C := C) (Ψ₀.symm x) ?_ ?_ ?_ ?_ ?_ ?_, Equiv.apply_symm_apply]
    · intro e; apply hx.1
      rw [← π.gu6_w_mp_fst, ← hmp, ← e, Equiv.apply_symm_apply]
    · intro e; apply hx.1
      rw [← π.gu6_w_pm_fst, ← hpm, ← e, Equiv.apply_symm_apply]
    · intro e; apply hx.2.1
      rw [← π.gu6_w_mq_fst, ← hmq, ← e, Equiv.apply_symm_apply]
    · intro e; apply hx.2.1
      rw [← π.gu6_w_qm_fst, ← hqm, ← e, Equiv.apply_symm_apply]
    · intro e; apply hx.2.2
      rw [← π.gu6_w_pq_fst, ← hpq, ← e, Equiv.apply_symm_apply]
    · intro e; apply hx.2.2
      rw [← π.gu6_w_qp_fst, ← hqp, ← e, Equiv.apply_symm_apply]
  have hcyc : ∀ x y z, π.M₁.VisitBetween (π.gu6_Ψ₁ x) (π.gu6_Ψ₁ y) (π.gu6_Ψ₁ z) ↔
      π.M₀.VisitBetween (σ₀ x) (σ₀ y) (σ₀ z) := by
    intro x y z
    exact GT_cyc_congr_of_lt (π.gu6_key_lt σ₀ e_mp e_mq e_pm e_pq e_qm e_qp e0 x y)
      (π.gu6_key_lt σ₀ e_mp e_mq e_pm e_pq e_qm e_qp e0 y z)
      (π.gu6_key_lt σ₀ e_mp e_mq e_pm e_pq e_qm e_qp e0 z x)
  rw [hcyc]
  have hσ : ∀ u, σ₀ (Ψ₀ u) = Ψ₀ (C.σD u) := fun u => by
    show Ψ₀ (C.σD (Ψ₀.symm (Ψ₀ u))) = _
    rw [Equiv.symm_apply_apply]
  rw [hσ, hσ, hσ]
  exact h₀ _ _ _


/-! #### W3-A1-DE new material: `withOver` transport of the move data (generic in `D D'`), the strands of
the twelve local occurrences, and the two unit theorems `w3de_riii_param` (the parametrised D8) and
`w3de_exists_Ψ₁` (E1 + crossing correspondence), whose `w3a_` connectors are one `exact` each. -/

omit [NeZero k] in
theorem w3de_overVisit_withOver {D : Diagram} (f : D.Γ.Crossing → D.Γ.Strand) (hf : ∀ y, f y ∈ y.val)
    {y : D.Γ.Crossing} {v : D.Γ.Visit} (h1 : v.1 = y) (h2 : v.2.val = f y) :
    (D.withOver f hf).overVisit y = v :=
  gu6_svisit_ext h1.symm h2.symm

omit [NeZero k] in
theorem w3de_underVisit_withOver {D : Diagram} (f : D.Γ.Crossing → D.Γ.Strand) (hf : ∀ y, f y ∈ y.val)
    {y : D.Γ.Crossing} {w : D.Γ.Visit} (h1 : w.1 = y) (h2 : w.2.val ≠ f y) :
    (D.withOver f hf).underVisit y = w := by
  apply gu6_svisit_ext h1.symm
  show D.Γ.other y (hf y) = w.2.val
  have hw : w.2.val ∈ y.val := by rw [← h1]; exact w.2.property
  exact (D.Γ.eq_other_of_mem_of_ne y (hf y) hw h2).symm

omit [NeZero k] in
theorem w3de_overVisit_withOver_of_eq {D : Diagram} (f : D.Γ.Crossing → D.Γ.Strand) (hf : ∀ y, f y ∈ y.val)
    {y : D.Γ.Crossing} (h : f y = D.overStrand y) : (D.withOver f hf).overVisit y = D.overVisit y :=
  gu6_svisit_ext rfl h

omit [NeZero k] in
theorem w3de_underVisit_withOver_of_eq {D : Diagram} (f : D.Γ.Crossing → D.Γ.Strand) (hf : ∀ y, f y ∈ y.val)
    {y : D.Γ.Crossing} (h : f y = D.overStrand y) : (D.withOver f hf).underVisit y = D.underVisit y :=
  w3de_underVisit_withOver f hf rfl (by rw [h]; exact D.under_ne_over y)

omit [NeZero k] in
/-- an outside match transports to new over data that agree with the old ones at every outer crossing -/
def w3de_outsideMatch_withOver {D D' : Diagram} {U : Set Plane} (m : OutsideMatch U D D')
    (f : D.Γ.Crossing → D.Γ.Strand) (hf : ∀ y, f y ∈ y.val)
    (f' : D'.Γ.Crossing → D'.Γ.Strand) (hf' : ∀ y, f' y ∈ y.val)
    (hout : ∀ y : D.Γ.Crossing, D.Γ.crossingPoint y ∉ interior U → f y = D.overStrand y)
    (hout' : ∀ y : D'.Γ.Crossing, D'.Γ.crossingPoint y ∉ interior U → f' y = D'.overStrand y) :
    OutsideMatch U (D.withOver f hf) (D'.withOver f' hf') where
  φ := m.φ
  eval_eq := m.eval_eq
  dir_pos := m.dir_pos
  dir_pos_before := m.dir_pos_before
  ψ := m.ψ
  over_eq := fun y => by
    refine (congrArg m.φ (Subtype.ext ?_)).trans ((m.over_eq y).trans (Subtype.ext ?_))
    · show (D.withOver f hf).visitPt ((D.withOver f hf).overVisit y.1) = D.visitPt (D.overVisit y.1)
      rw [w3de_overVisit_withOver_of_eq f hf (hout y.1 y.2)]
      rfl
    · show D'.visitPt (D'.overVisit (m.ψ y).1) =
        (D'.withOver f' hf').visitPt ((D'.withOver f' hf').overVisit (m.ψ y).1)
      rw [w3de_overVisit_withOver_of_eq f' hf' (hout' _ (m.ψ y).2)]
      rfl
  under_eq := fun y => by
    refine (congrArg m.φ (Subtype.ext ?_)).trans ((m.under_eq y).trans (Subtype.ext ?_))
    · show (D.withOver f hf).visitPt ((D.withOver f hf).underVisit y.1) = D.visitPt (D.underVisit y.1)
      rw [w3de_underVisit_withOver_of_eq f hf (hout y.1 y.2)]
      rfl
    · show D'.visitPt (D'.underVisit (m.ψ y).1) =
        (D'.withOver f' hf').visitPt ((D'.withOver f' hf').underVisit (m.ψ y).1)
      rw [w3de_underVisit_withOver_of_eq f' hf' (hout' _ (m.ψ y).2)]
      rfl

omit [NeZero k] in
def w3de_moveMatch_withOver {D D' : Diagram} {U : Set Plane} (m : MoveMatch U D D')
    (f : D.Γ.Crossing → D.Γ.Strand) (hf : ∀ y, f y ∈ y.val)
    (f' : D'.Γ.Crossing → D'.Γ.Strand) (hf' : ∀ y, f' y ∈ y.val)
    (hout : ∀ y : D.Γ.Crossing, D.Γ.crossingPoint y ∉ interior U → f y = D.overStrand y)
    (hout' : ∀ y : D'.Γ.Crossing, D'.Γ.crossingPoint y ∉ interior U → f' y = D'.overStrand y) :
    MoveMatch U (D.withOver f hf) (D'.withOver f' hf') :=
  { w3de_outsideMatch_withOver m.toOutsideMatch f hf f' hf' hout hout' with
    e := m.e
    comp_eq := m.comp_eq }

omit [NeZero k] in
theorem w3de_localFrame_withOver {D D' : Diagram} {U : Set Plane} (fr : LocalFrame U D D')
    (f : D.Γ.Crossing → D.Γ.Strand) (hf : ∀ y, f y ∈ y.val)
    (f' : D'.Γ.Crossing → D'.Γ.Strand) (hf' : ∀ y, f' y ∈ y.val) :
    LocalFrame U (D.withOver f hf) (D'.withOver f' hf') :=
  ⟨fr.disc, ⟨fr.clean.frontier_injOn, fr.clean.exits⟩, ⟨fr.clean'.frontier_injOn, fr.clean'.exits⟩⟩

/-- the strands of the twelve local occurrences (`gu6_sv_strand`, read through `st₀`/`st₁`) -/
theorem w3de_w_mp_strand : π.w_mp.2.val = π.st₀ π.mB := gu6_sv_strand _ _
theorem w3de_w_pm_strand : π.w_pm.2.val = π.st₀ π.p' := gu6_sv_strand _ _
theorem w3de_w_mq_strand : π.w_mq.2.val = π.st₀ π.mC := gu6_sv_strand _ _
theorem w3de_w_qm_strand : π.w_qm.2.val = π.st₀ π.q' := gu6_sv_strand _ _
theorem w3de_w_pq_strand : π.w_pq.2.val = π.st₀ π.p' := gu6_sv_strand _ _
theorem w3de_w_qp_strand : π.w_qp.2.val = π.st₀ π.q' := gu6_sv_strand _ _
theorem w3de_w'_pC_strand : π.gu6_w'_pC.2.val = π.st₁ π.p' := gu6_sv_strand _ _
theorem w3de_w'_Cp_strand : π.gu6_w'_Cp.2.val = π.st₁ π.mC := gu6_sv_strand _ _
theorem w3de_w'_qB_strand : π.gu6_w'_qB.2.val = π.st₁ π.q' := gu6_sv_strand _ _
theorem w3de_w'_Bq_strand : π.gu6_w'_Bq.2.val = π.st₁ π.mB := gu6_sv_strand _ _
theorem w3de_w'_pq_strand : π.gu6_w'_pq.2.val = π.st₁ π.p' := gu6_sv_strand _ _
theorem w3de_w'_qp_strand : π.gu6_w'_qp.2.val = π.st₁ π.q' := gu6_sv_strand _ _

theorem w3de_st₀_ne {i j : ZMod (k + 3)} (h : i ≠ j) : π.st₀ i ≠ π.st₀ j := gu6_strand_ne h
theorem w3de_st₁_ne {i j : ZMod (k + 3)} (h : i ≠ j) : π.st₁ i ≠ π.st₁ j := gu6_strand_ne h
theorem w3de_mB_ne_p' : π.mB ≠ π.p' := P1.ne_of_isCrossing_pair π.X₀_cross_mp
theorem w3de_mC_ne_q' : π.mC ≠ π.q' := P1.ne_of_isCrossing_pair π.X₀_cross_mq
theorem w3de_p'_ne_q' : π.p' ≠ π.q' := P1.ne_of_isCrossing_pair π.X₀_cross_pq
theorem w3de_p'_ne_mC : π.p' ≠ π.mC := P1.ne_of_isCrossing_pair π.X₁_cross_pC
theorem w3de_q'_ne_mB : π.q' ≠ π.mB := P1.ne_of_isCrossing_pair π.X₁_cross_qB

/-- the skeleton's local crossings and occurrences are the copy's (`rfl`) -/
theorem w3de_y_mp_eq : π.y_mp = π.gu6_y_mp := rfl
theorem w3de_y_mq_eq : π.y_mq = π.gu6_y_mq := rfl
theorem w3de_y_pq_eq : π.y_pq = π.gu6_y_pq := rfl
theorem w3de_y'_pC_eq : π.y'_pC = π.gu6_y'_pC := rfl
theorem w3de_y'_qB_eq : π.y'_qB = π.gu6_y'_qB := rfl
theorem w3de_y'_pq_eq : π.y'_pq = π.gu6_y'_pq := rfl

/-- **The parametrised D8** (`w3a_riii_param` proved inside the copy's section): the accepted `riii` proof
with the move match and the frame transported to `withOver` (`w3de_moveMatch_withOver`, `w3de_localFrame_withOver`),
the six over/under memberships read from the hypotheses `hmp₀ … hpq₁` through `w3de_overVisit_withOver` /
`w3de_underVisit_withOver`, and `htrans` in place of `gu6_htrans`. -/
theorem w3de_riii_param (f₀ : π.M₀.Γ.Crossing → π.M₀.Γ.Strand) (hf₀ : ∀ y, f₀ y ∈ y.val)
    (f₁ : π.M₁.Γ.Crossing → π.M₁.Γ.Strand) (hf₁ : ∀ y, f₁ y ∈ y.val)
    (h₀ : ∀ y, y ≠ π.gu6_y_mp → y ≠ π.gu6_y_mq → y ≠ π.gu6_y_pq → f₀ y = π.M₀.overStrand y)
    (h₁ : ∀ y, y ≠ π.gu6_y'_pC → y ≠ π.gu6_y'_qB → y ≠ π.gu6_y'_pq → f₁ y = π.M₁.overStrand y)
    (Rmp Rmq Rpq : Prop)
    (hmp₀ : (Rmp → f₀ π.gu6_y_mp = π.st₀ π.mB) ∧ (¬ Rmp → f₀ π.gu6_y_mp = π.st₀ π.p'))
    (hmq₀ : (Rmq → f₀ π.gu6_y_mq = π.st₀ π.mC) ∧ (¬ Rmq → f₀ π.gu6_y_mq = π.st₀ π.q'))
    (hpq₀ : (Rpq → f₀ π.gu6_y_pq = π.st₀ π.p') ∧ (¬ Rpq → f₀ π.gu6_y_pq = π.st₀ π.q'))
    (hmp₁ : (Rmp → f₁ π.gu6_y'_pC = π.st₁ π.mC) ∧ (¬ Rmp → f₁ π.gu6_y'_pC = π.st₁ π.p'))
    (hmq₁ : (Rmq → f₁ π.gu6_y'_qB = π.st₁ π.mB) ∧ (¬ Rmq → f₁ π.gu6_y'_qB = π.st₁ π.q'))
    (hpq₁ : (Rpq → f₁ π.gu6_y'_pq = π.st₁ π.p') ∧ (¬ Rpq → f₁ π.gu6_y'_pq = π.st₁ π.q'))
    (htrans : ¬ (Rmp ∧ Rpq ∧ ¬ Rmq) ∧ ¬ (¬ Rmp ∧ ¬ Rpq ∧ Rmq)) :
    RIII (π.M₀.withOver f₀ hf₀) (π.M₁.withOver f₁ hf₁) := by
  classical
  have hout₀ : ∀ y : π.M₀.Γ.Crossing, π.M₀.Γ.crossingPoint y ∉ interior π.U → f₀ y = π.M₀.overStrand y :=
    fun y hy => h₀ y (fun e => hy ((π.gu6_inner0 y).mpr (Or.inl e)))
      (fun e => hy ((π.gu6_inner0 y).mpr (Or.inr (Or.inl e)))) (fun e => hy ((π.gu6_inner0 y).mpr (Or.inr (Or.inr e))))
  have hout₁ : ∀ y : π.M₁.Γ.Crossing, π.M₁.Γ.crossingPoint y ∉ interior π.U → f₁ y = π.M₁.overStrand y :=
    fun y hy => h₁ y (fun e => hy ((π.gu6_inner1 y).mpr (Or.inl e)))
      (fun e => hy ((π.gu6_inner1 y).mpr (Or.inr (Or.inl e)))) (fun e => hy ((π.gu6_inner1 y).mpr (Or.inr (Or.inr e))))
  obtain ⟨a, b, c, a', b', c', hab, hbc, hac, hab', hbc', hac', cover, cover',
    ha_s, ha_e, hb_s, hb_e, hc_s, hc_e⟩ := π.exists_arcCovers
  obtain ⟨mm⟩ := π.exists_moveMatch
  have mm' := w3de_moveMatch_withOver mm f₀ hf₀ f₁ hf₁ hout₀ hout₁
  -- the `M₀` arcs through the local occurrences
  obtain ⟨Am, hAm, hm1⟩ := gu6_exists_arc_of_interior cover π.w_mp
    (by rw [gu6_w_mp_fst]; exact (π.gu6_inner0 _).mpr (Or.inl rfl))
  obtain ⟨Ap, hAp, hp1⟩ := gu6_exists_arc_of_interior cover π.w_pm
    (by rw [gu6_w_pm_fst]; exact (π.gu6_inner0 _).mpr (Or.inl rfl))
  obtain ⟨Aq, hAq, hq1⟩ := gu6_exists_arc_of_interior cover π.w_qm
    (by rw [gu6_w_qm_fst]; exact (π.gu6_inner0 _).mpr (Or.inr (Or.inl rfl)))
  have isAm := cover.isArc Am hAm
  have isAp := cover.isArc Ap hAp
  have isAq := cover.isArc Aq hAq
  have hm1' : Am.Inner ⟨Am.i, (π.mB, ⟨π.gu6_s_mp, π.gu6_s_mp_pos.le, π.gu6_s_mp_lt_one⟩)⟩ := by
    have := (π.gu6_inner_pt₀ Am π.w_mp).mp hm1
    rwa [gu6_w_mp_pt] at this
  have hp1' : Ap.Inner ⟨Ap.i, (π.p', ⟨π.gu6_s_pm, π.gu6_s_pm_pos.le, π.gu6_s_pm_lt_one⟩)⟩ := by
    have := (π.gu6_inner_pt₀ Ap π.w_pm).mp hp1
    rwa [gu6_w_pm_pt] at this
  have hq1' : Aq.Inner ⟨Aq.i, (π.q', ⟨π.gu6_s_qm, π.gu6_s_qm_pos.le, π.gu6_s_qm_lt_one⟩)⟩ := by
    have := (π.gu6_inner_pt₀ Aq π.w_qm).mp hq1
    rwa [gu6_w_qm_pt] at this
  have hm2' := π.gu6_arc_m_inner_mC Am isAm hm1'
  have hp2' := π.gu6_arc_p_inner_pq Ap isAp hp1'
  have hq2' := π.gu6_arc_q_inner_pq Aq isAq hq1'
  have hm2 : Am.Inner (π.M₀.visitPt π.w_mq) := by
    rw [gu6_inner_pt₀, gu6_w_mq_pt]; exact hm2'
  have hp2 : Ap.Inner (π.M₀.visitPt π.w_pq) := by
    rw [gu6_inner_pt₀, gu6_w_pq_pt]; exact hp2'
  have hq2 : Aq.Inner (π.M₀.visitPt π.w_qp) := by
    rw [gu6_inner_pt₀, gu6_w_qp_pt]; exact hq2'
  have hmp : Am ≠ Ap := π.gu6_arc_m_ne_p Am Ap isAm hm1' hp1'
  have hmq : Am ≠ Aq := π.gu6_arc_m_ne_q Am Aq isAm hm2' hq1'
  have hpq : Ap ≠ Aq := π.gu6_arc_p_ne_q Ap Aq isAp hp1' hq1'
  -- their starts
  obtain ⟨θm, -, hstartm⟩ := π.gu6_arc_m_start Am isAm hm1'
  obtain ⟨θp, -, hθp1, hstartp⟩ := π.gu6_arc_start_same_edge Ap isAp π.gu6_X₀_p'_not_mem hp1'
  obtain ⟨θq, -, hθq1, hstartq⟩ := π.gu6_arc_start_same_edge Aq isAq π.gu6_X₀_q'_not_mem hq1'
  have hθp2 : θp.val < π.gu6_s_pq := π.gu6_arc_start_lt Ap isAp π.gu6_X₀_p'_not_mem hstartp hp2'
  have hθq2 : θq.val < π.gu6_s_qp := π.gu6_arc_start_lt Aq isAq π.gu6_X₀_q'_not_mem hstartq hq2'
  -- `{Am, Ap, Aq} = {a, b, c}`
  have hmem : ∀ A ∈ ({a, b, c} : Set π.M₀.Γ.Arc), A = a ∨ A = b ∨ A = c := fun A hA => by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hA
  have hset : ({Am, Ap, Aq} : Set π.M₀.Γ.Arc) = {a, b, c} :=
    gu6_triple_eq (hmem Am hAm) (hmem Ap hAp) (hmem Aq hAq) hmp hpq hmq
  have cover₀ : π.M₀.Γ.ArcCover π.U {Am, Ap, Aq} := by rw [hset]; exact cover
  -- the partner arcs of `M₁`
  have hpartner : ∀ A ∈ ({a, b, c} : Set π.M₀.Γ.Arc), ∃ A' ∈ ({a', b', c'} : Set π.M₁.Γ.Arc),
      π.M₁.Γ.eval A'.startPt = π.M₀.Γ.eval A.startPt ∧ π.M₁.Γ.eval A'.stopPt = π.M₀.Γ.eval A.stopPt := by
    intro A hA
    rcases hmem A hA with rfl | rfl | rfl
    · exact ⟨a', Set.mem_insert _ _, ha_s, ha_e⟩
    · exact ⟨b', Set.mem_insert_of_mem _ (Set.mem_insert _ _), hb_s, hb_e⟩
    · exact ⟨c', Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)), hc_s, hc_e⟩
  obtain ⟨Am', hAm', hm_s, hm_e⟩ := hpartner Am hAm
  obtain ⟨Ap', hAp', hp_s, hp_e⟩ := hpartner Ap hAp
  obtain ⟨Aq', hAq', hq_s, hq_e⟩ := hpartner Aq hAq
  have isAm' := cover'.isArc Am' hAm'
  have isAp' := cover'.isArc Ap' hAp'
  have isAq' := cover'.isArc Aq' hAq'
  have hstartm' : Am'.start = (π.mA, θm) :=
    π.gu6_partner_start Am Am' isAm' hm_s hstartm (π.gu6_edgePoint_X₁_mA _)
  have hstartp' : Ap'.start = (π.p', θp) :=
    π.gu6_partner_start Ap Ap' isAp' hp_s hstartp (by rw [gu6_edgePoint_X₁_p', gu6_edgePoint_X₀_p'])
  have hstartq' : Aq'.start = (π.q', θq) :=
    π.gu6_partner_start Aq Aq' isAq' hq_s hstartq (by rw [gu6_edgePoint_X₁_q', gu6_edgePoint_X₀_q'])
  obtain ⟨hBq', hCp'⟩ := π.gu6_M₁_inner_m Am' isAm' hstartm'
  obtain ⟨hpq'', hpC', hθpC⟩ := π.gu6_M₁_inner_p Ap' isAp' hstartp' hθp2
  obtain ⟨hqp'', hqB', hθqB⟩ := π.gu6_M₁_inner_q Aq' isAq' hstartq' hθq2
  have hmp' : Am' ≠ Ap' := by
    rintro rfl
    rw [hstartm'] at hstartp'
    exact π.gu6_lab_ne_mA (gu6_p_ne_m (C := C)) (congrArg Prod.fst hstartp').symm
  have hmq' : Am' ≠ Aq' := by
    rintro rfl
    rw [hstartm'] at hstartq'
    exact π.gu6_lab_ne_mA (gu6_q_ne_m (C := C)) (congrArg Prod.fst hstartq').symm
  have hpq' : Ap' ≠ Aq' := by
    rintro rfl
    rw [hstartp'] at hstartq'
    exact π.gu6_p'_ne_q' (congrArg Prod.fst hstartq')
  have hmem' : ∀ A ∈ ({a', b', c'} : Set π.M₁.Γ.Arc), A = a' ∨ A = b' ∨ A = c' := fun A hA => by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hA
  have hset' : ({Am', Ap', Aq'} : Set π.M₁.Γ.Arc) = {a', b', c'} :=
    gu6_triple_eq (hmem' Am' hAm') (hmem' Ap' hAp') (hmem' Aq' hAq') hmp' hpq' hmq'
  have cover₁ : π.M₁.Γ.ArcCover π.U {Am', Ap', Aq'} := by rw [hset']; exact cover'
  -- the twelve memberships
  have hBq : Am'.Inner (π.M₁.visitPt π.gu6_w'_Bq) := by rw [gu6_inner_pt₁, gu6_w'_Bq_pt]; exact hBq'
  have hCp : Am'.Inner (π.M₁.visitPt π.gu6_w'_Cp) := by rw [gu6_inner_pt₁, gu6_w'_Cp_pt]; exact hCp'
  have hpq2 : Ap'.Inner (π.M₁.visitPt π.gu6_w'_pq) := by rw [gu6_inner_pt₁, gu6_w'_pq_pt]; exact hpq''
  have hpC : Ap'.Inner (π.M₁.visitPt π.gu6_w'_pC) := by rw [gu6_inner_pt₁, gu6_w'_pC_pt]; exact hpC'
  have hqp2 : Aq'.Inner (π.M₁.visitPt π.gu6_w'_qp) := by rw [gu6_inner_pt₁, gu6_w'_qp_pt]; exact hqp''
  have hqB : Aq'.Inner (π.M₁.visitPt π.gu6_w'_qB) := by rw [gu6_inner_pt₁, gu6_w'_qB_pt]; exact hqB'
  -- over/under memberships
  have hov_mp : (Rmp → (π.M₀.withOver f₀ hf₀).OverOn Am π.gu6_y_mp ∧ (π.M₀.withOver f₀ hf₀).UnderOn Ap π.gu6_y_mp) ∧
      (¬ Rmp → (π.M₀.withOver f₀ hf₀).OverOn Ap π.gu6_y_mp ∧ (π.M₀.withOver f₀ hf₀).UnderOn Am π.gu6_y_mp) := by
    constructor
    · intro h
      have h1 := w3de_overVisit_withOver f₀ hf₀ π.gu6_w_mp_fst (by rw [hmp₀.1 h]; exact π.w3de_w_mp_strand)
      have h2 := w3de_underVisit_withOver f₀ hf₀ π.gu6_w_pm_fst (by rw [hmp₀.1 h, π.w3de_w_pm_strand]; exact π.w3de_st₀_ne π.w3de_mB_ne_p'.symm)
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hm1.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hp1.mem⟩
    · intro h
      have h1 := w3de_overVisit_withOver f₀ hf₀ π.gu6_w_pm_fst (by rw [hmp₀.2 h]; exact π.w3de_w_pm_strand)
      have h2 := w3de_underVisit_withOver f₀ hf₀ π.gu6_w_mp_fst (by rw [hmp₀.2 h, π.w3de_w_mp_strand]; exact π.w3de_st₀_ne π.w3de_mB_ne_p')
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hp1.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hm1.mem⟩
  have hov_mq : (Rmq → (π.M₀.withOver f₀ hf₀).OverOn Am π.gu6_y_mq ∧ (π.M₀.withOver f₀ hf₀).UnderOn Aq π.gu6_y_mq) ∧
      (¬ Rmq → (π.M₀.withOver f₀ hf₀).OverOn Aq π.gu6_y_mq ∧ (π.M₀.withOver f₀ hf₀).UnderOn Am π.gu6_y_mq) := by
    constructor
    · intro h
      have h1 := w3de_overVisit_withOver f₀ hf₀ π.gu6_w_mq_fst (by rw [hmq₀.1 h]; exact π.w3de_w_mq_strand)
      have h2 := w3de_underVisit_withOver f₀ hf₀ π.gu6_w_qm_fst (by rw [hmq₀.1 h, π.w3de_w_qm_strand]; exact π.w3de_st₀_ne π.w3de_mC_ne_q'.symm)
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hm2.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hq1.mem⟩
    · intro h
      have h1 := w3de_overVisit_withOver f₀ hf₀ π.gu6_w_qm_fst (by rw [hmq₀.2 h]; exact π.w3de_w_qm_strand)
      have h2 := w3de_underVisit_withOver f₀ hf₀ π.gu6_w_mq_fst (by rw [hmq₀.2 h, π.w3de_w_mq_strand]; exact π.w3de_st₀_ne π.w3de_mC_ne_q')
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hq1.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hm2.mem⟩
  have hov_pq : (Rpq → (π.M₀.withOver f₀ hf₀).OverOn Ap π.gu6_y_pq ∧ (π.M₀.withOver f₀ hf₀).UnderOn Aq π.gu6_y_pq) ∧
      (¬ Rpq → (π.M₀.withOver f₀ hf₀).OverOn Aq π.gu6_y_pq ∧ (π.M₀.withOver f₀ hf₀).UnderOn Ap π.gu6_y_pq) := by
    constructor
    · intro h
      have h1 := w3de_overVisit_withOver f₀ hf₀ π.gu6_w_pq_fst (by rw [hpq₀.1 h]; exact π.w3de_w_pq_strand)
      have h2 := w3de_underVisit_withOver f₀ hf₀ π.gu6_w_qp_fst (by rw [hpq₀.1 h, π.w3de_w_qp_strand]; exact π.w3de_st₀_ne π.w3de_p'_ne_q'.symm)
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hp2.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hq2.mem⟩
    · intro h
      have h1 := w3de_overVisit_withOver f₀ hf₀ π.gu6_w_qp_fst (by rw [hpq₀.2 h]; exact π.w3de_w_qp_strand)
      have h2 := w3de_underVisit_withOver f₀ hf₀ π.gu6_w_pq_fst (by rw [hpq₀.2 h, π.w3de_w_pq_strand]; exact π.w3de_st₀_ne π.w3de_p'_ne_q')
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hq2.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hp2.mem⟩
  have hov_mp' : (Rmp → (π.M₁.withOver f₁ hf₁).OverOn Am' π.gu6_y'_pC ∧ (π.M₁.withOver f₁ hf₁).UnderOn Ap' π.gu6_y'_pC) ∧
      (¬ Rmp → (π.M₁.withOver f₁ hf₁).OverOn Ap' π.gu6_y'_pC ∧ (π.M₁.withOver f₁ hf₁).UnderOn Am' π.gu6_y'_pC) := by
    constructor
    · intro h
      have h1 := w3de_overVisit_withOver f₁ hf₁ π.gu6_w'_Cp_fst (by rw [hmp₁.1 h]; exact π.w3de_w'_Cp_strand)
      have h2 := w3de_underVisit_withOver f₁ hf₁ π.gu6_w'_pC_fst (by rw [hmp₁.1 h, π.w3de_w'_pC_strand]; exact π.w3de_st₁_ne π.w3de_p'_ne_mC)
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hCp.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hpC.mem⟩
    · intro h
      have h1 := w3de_overVisit_withOver f₁ hf₁ π.gu6_w'_pC_fst (by rw [hmp₁.2 h]; exact π.w3de_w'_pC_strand)
      have h2 := w3de_underVisit_withOver f₁ hf₁ π.gu6_w'_Cp_fst (by rw [hmp₁.2 h, π.w3de_w'_Cp_strand]; exact π.w3de_st₁_ne π.w3de_p'_ne_mC.symm)
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hpC.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hCp.mem⟩
  have hov_mq' : (Rmq → (π.M₁.withOver f₁ hf₁).OverOn Am' π.gu6_y'_qB ∧ (π.M₁.withOver f₁ hf₁).UnderOn Aq' π.gu6_y'_qB) ∧
      (¬ Rmq → (π.M₁.withOver f₁ hf₁).OverOn Aq' π.gu6_y'_qB ∧ (π.M₁.withOver f₁ hf₁).UnderOn Am' π.gu6_y'_qB) := by
    constructor
    · intro h
      have h1 := w3de_overVisit_withOver f₁ hf₁ π.gu6_w'_Bq_fst (by rw [hmq₁.1 h]; exact π.w3de_w'_Bq_strand)
      have h2 := w3de_underVisit_withOver f₁ hf₁ π.gu6_w'_qB_fst (by rw [hmq₁.1 h, π.w3de_w'_qB_strand]; exact π.w3de_st₁_ne π.w3de_q'_ne_mB)
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hBq.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hqB.mem⟩
    · intro h
      have h1 := w3de_overVisit_withOver f₁ hf₁ π.gu6_w'_qB_fst (by rw [hmq₁.2 h]; exact π.w3de_w'_qB_strand)
      have h2 := w3de_underVisit_withOver f₁ hf₁ π.gu6_w'_Bq_fst (by rw [hmq₁.2 h, π.w3de_w'_Bq_strand]; exact π.w3de_st₁_ne π.w3de_q'_ne_mB.symm)
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hqB.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hBq.mem⟩
  have hov_pq' : (Rpq → (π.M₁.withOver f₁ hf₁).OverOn Ap' π.gu6_y'_pq ∧ (π.M₁.withOver f₁ hf₁).UnderOn Aq' π.gu6_y'_pq) ∧
      (¬ Rpq → (π.M₁.withOver f₁ hf₁).OverOn Aq' π.gu6_y'_pq ∧ (π.M₁.withOver f₁ hf₁).UnderOn Ap' π.gu6_y'_pq) := by
    constructor
    · intro h
      have h1 := w3de_overVisit_withOver f₁ hf₁ π.gu6_w'_pq_fst (by rw [hpq₁.1 h]; exact π.w3de_w'_pq_strand)
      have h2 := w3de_underVisit_withOver f₁ hf₁ π.gu6_w'_qp_fst (by rw [hpq₁.1 h, π.w3de_w'_qp_strand]; exact π.w3de_st₁_ne π.w3de_p'_ne_q'.symm)
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hpq2.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hqp2.mem⟩
    · intro h
      have h1 := w3de_overVisit_withOver f₁ hf₁ π.gu6_w'_qp_fst (by rw [hpq₁.2 h]; exact π.w3de_w'_qp_strand)
      have h2 := w3de_underVisit_withOver f₁ hf₁ π.gu6_w'_pq_fst (by rw [hpq₁.2 h, π.w3de_w'_pq_strand]; exact π.w3de_st₁_ne π.w3de_p'_ne_q')
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hqp2.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hpq2.mem⟩
  -- separations used for the reversal clauses
  have sepPM : (π.M₀.withOver f₀ hf₀).Separates Ap Am π.gu6_y_mp := by
    by_cases h : Rmp
    · exact Or.inr (hov_mp.1 h)
    · exact Or.inl (hov_mp.2 h)
  have sepPQ : (π.M₀.withOver f₀ hf₀).Separates Ap Aq π.gu6_y_pq := by
    by_cases h : Rpq
    · exact Or.inl (hov_pq.1 h)
    · exact Or.inr (hov_pq.2 h)
  have sepQM : (π.M₀.withOver f₀ hf₀).Separates Aq Am π.gu6_y_mq := by
    by_cases h : Rmq
    · exact Or.inr (hov_mq.1 h)
    · exact Or.inl (hov_mq.2 h)
  have sepQP : (π.M₀.withOver f₀ hf₀).Separates Aq Ap π.gu6_y_pq := sepPQ.symm
  have sepPM' : (π.M₁.withOver f₁ hf₁).Separates Ap' Am' π.gu6_y'_pC := by
    by_cases h : Rmp
    · exact Or.inr (hov_mp'.1 h)
    · exact Or.inl (hov_mp'.2 h)
  have sepPQ' : (π.M₁.withOver f₁ hf₁).Separates Ap' Aq' π.gu6_y'_pq := by
    by_cases h : Rpq
    · exact Or.inl (hov_pq'.1 h)
    · exact Or.inr (hov_pq'.2 h)
  have sepQM' : (π.M₁.withOver f₁ hf₁).Separates Aq' Am' π.gu6_y'_qB := by
    by_cases h : Rmq
    · exact Or.inr (hov_mq'.1 h)
    · exact Or.inl (hov_mq'.2 h)
  have sepQP' : (π.M₁.withOver f₁ hf₁).Separates Aq' Ap' π.gu6_y'_pq := sepPQ'.symm
  -- the reversal along `m`: both orders hold
  have hbef_m : Am.Before (π.M₀.visitPt π.w_mp) (π.M₀.visitPt π.w_mq) := by
    rw [gu6_before_pt₀, gu6_w_mp_pt, gu6_w_mq_pt]
    refine (gu6_before_iff Am _ _ hm1' hm2').mpr ?_
    rw [hstartm]
    exact (gu6_tb_span_two π.mA π.mB π.mC (by rw [gu6_mA_val, gu6_mB_val])
      (by rw [gu6_mB_val, gu6_mC_val]) _ _ _).mpr (Or.inr (Or.inl rfl))
  have hbef_m' : Am'.Before (π.M₁.visitPt π.gu6_w'_Bq) (π.M₁.visitPt π.gu6_w'_Cp) := by
    rw [gu6_before_pt₁, gu6_w'_Bq_pt, gu6_w'_Cp_pt]
    refine (gu6_before_iff Am' _ _ hBq' hCp').mpr ?_
    rw [hstartm']
    exact (gu6_tb_span_two π.mA π.mB π.mC (by rw [gu6_mA_val, gu6_mB_val])
      (by rw [gu6_mB_val, gu6_mC_val]) _ _ _).mpr (Or.inr (Or.inl rfl))
  have rev_m : (π.M₀.withOver f₀ hf₀).BeforeOn Am π.gu6_y_mp π.gu6_y_mq ↔ (π.M₁.withOver f₁ hf₁).BeforeOn Am' π.gu6_y'_qB π.gu6_y'_pC :=
    iff_of_true ⟨π.w_mp, π.w_mq, π.gu6_w_mp_fst, π.gu6_w_mq_fst, hbef_m⟩
      ⟨π.gu6_w'_Bq, π.gu6_w'_Cp, π.gu6_w'_Bq_fst, π.gu6_w'_Cp_fst, hbef_m'⟩
  -- the reversal along `p` (D9)
  have hbp : (π.M₀.withOver f₀ hf₀).BeforeOn Ap π.gu6_y_mp π.gu6_y_pq ↔
      Ap.Before (π.M₀.visitPt π.w_pm) (π.M₀.visitPt π.w_pq) :=
    (π.M₀.withOver f₀ hf₀).beforeOn_iff_before cover hAp hAm hAq hmp.symm hpq sepPM sepPQ π.gu6_w_pm_fst π.gu6_w_pq_fst
      hp1.mem hp2.mem
  have hbp' : (π.M₁.withOver f₁ hf₁).BeforeOn Ap' π.gu6_y'_pq π.gu6_y'_pC ↔
      Ap'.Before (π.M₁.visitPt π.gu6_w'_pq) (π.M₁.visitPt π.gu6_w'_pC) :=
    (π.M₁.withOver f₁ hf₁).beforeOn_iff_before cover' hAp' hAq' hAm' hpq' hmp'.symm sepPQ' sepPM' π.gu6_w'_pq_fst
      π.gu6_w'_pC_fst hpq2.mem hpC.mem
  have hbp2 : Ap.Before (π.M₀.visitPt π.w_pm) (π.M₀.visitPt π.w_pq) ↔ π.gu6_s_pm < π.gu6_s_pq := by
    rw [gu6_before_pt₀, gu6_w_pm_pt, gu6_w_pq_pt]
    refine (gu6_before_iff Ap _ _ hp1' hp2').trans ?_
    rw [hstartp]
    exact gu6_tb_same_edge_of_start π.p' θp _ _ hθp1 hθp2
  have hbp2' : Ap'.Before (π.M₁.visitPt π.gu6_w'_pq) (π.M₁.visitPt π.gu6_w'_pC) ↔
      π.gu6_s'_pq < π.gu6_s'_pC := by
    rw [gu6_before_pt₁, gu6_w'_pq_pt, gu6_w'_pC_pt]
    refine (gu6_before_iff Ap' _ _ hpq'' hpC').trans ?_
    rw [hstartp']
    exact gu6_tb_same_edge_of_start π.p' θp _ _ (by show θp.val < π.gu6_s'_pq; rw [gu6_s'_pq_eq]; exact hθp2) hθpC
  have rev_p : (π.M₀.withOver f₀ hf₀).BeforeOn Ap π.gu6_y_mp π.gu6_y_pq ↔ (π.M₁.withOver f₁ hf₁).BeforeOn Ap' π.gu6_y'_pq π.gu6_y'_pC := by
    rw [hbp, hbp', hbp2, hbp2', gu6_s'_pq_eq]
    exact π.gu6_D9_p
  -- the reversal along `q` (D9)
  have hbq : (π.M₀.withOver f₀ hf₀).BeforeOn Aq π.gu6_y_mq π.gu6_y_pq ↔
      Aq.Before (π.M₀.visitPt π.w_qm) (π.M₀.visitPt π.w_qp) :=
    (π.M₀.withOver f₀ hf₀).beforeOn_iff_before cover hAq hAm hAp hmq.symm hpq.symm sepQM sepQP π.gu6_w_qm_fst
      π.gu6_w_qp_fst hq1.mem hq2.mem
  have hbq' : (π.M₁.withOver f₁ hf₁).BeforeOn Aq' π.gu6_y'_pq π.gu6_y'_qB ↔
      Aq'.Before (π.M₁.visitPt π.gu6_w'_qp) (π.M₁.visitPt π.gu6_w'_qB) :=
    (π.M₁.withOver f₁ hf₁).beforeOn_iff_before cover' hAq' hAp' hAm' hpq'.symm hmq'.symm sepQP' sepQM' π.gu6_w'_qp_fst
      π.gu6_w'_qB_fst hqp2.mem hqB.mem
  have hbq2 : Aq.Before (π.M₀.visitPt π.w_qm) (π.M₀.visitPt π.w_qp) ↔ π.gu6_s_qm < π.gu6_s_qp := by
    rw [gu6_before_pt₀, gu6_w_qm_pt, gu6_w_qp_pt]
    refine (gu6_before_iff Aq _ _ hq1' hq2').trans ?_
    rw [hstartq]
    exact gu6_tb_same_edge_of_start π.q' θq _ _ hθq1 hθq2
  have hbq2' : Aq'.Before (π.M₁.visitPt π.gu6_w'_qp) (π.M₁.visitPt π.gu6_w'_qB) ↔
      π.gu6_s'_qp < π.gu6_s'_qB := by
    rw [gu6_before_pt₁, gu6_w'_qp_pt, gu6_w'_qB_pt]
    refine (gu6_before_iff Aq' _ _ hqp'' hqB').trans ?_
    rw [hstartq']
    exact gu6_tb_same_edge_of_start π.q' θq _ _ (by show θq.val < π.gu6_s'_qp; rw [gu6_s'_qp_eq]; exact hθq2) hθqB
  have rev_q : (π.M₀.withOver f₀ hf₀).BeforeOn Aq π.gu6_y_mq π.gu6_y_pq ↔ (π.M₁.withOver f₁ hf₁).BeforeOn Aq' π.gu6_y'_pq π.gu6_y'_qB := by
    rw [hbq, hbq', hbq2, hbq2', gu6_s'_qp_eq]
    exact π.gu6_D9_q
  -- assembly
  exact ⟨π.U, Or.inl (gu6_riii_of_strands (w3de_localFrame_withOver ⟨π.disc_isDisc, π.clean_M₀, π.clean_M₁⟩ f₀ hf₀ f₁ hf₁) mm' Am Ap Aq Am' Ap' Aq'
    hmp hmq hpq hmp' hmq' hpq' cover₀ cover₁ hm_s hm_e hp_s hp_e hq_s hq_e
    π.gu6_y_mp π.gu6_y_mq π.gu6_y_pq π.gu6_y_mp_ne_mq π.gu6_y_mp_ne_pq π.gu6_y_mq_ne_pq π.gu6_inner0
    π.gu6_y'_pC π.gu6_y'_qB π.gu6_y'_pq π.gu6_y'_pC_ne_qB π.gu6_y'_pC_ne_pq π.gu6_y'_qB_ne_pq π.gu6_inner1
    Rmp Rmq Rpq hov_mp hov_mq hov_pq hov_mp' hov_mq' hov_pq' htrans rev_m rev_p rev_q)⟩

/-- **E1 + the crossing correspondence** (`w3a_exists_Ψ₁` proved inside the copy's section): the accepted
`exists_Ψ₁` proof (`gu6_Ψ₁`, its twin/over-bit/sign clauses, the twisted key comparison) plus the three clauses
`(Ψ₁ v).1 = y' ↔ v.1 = y` from `w3b_fst_eq_iff_of_twin` and the six images `gu6_Ψ₁_w_*`. -/
theorem w3de_exists_Ψ₁ (Ψ₀ : C.D₀.Γ.Visit ≃ π.M₀.Γ.Visit)
    (h₀ : ∀ u v w, π.M₀.VisitBetween (Ψ₀ u) (Ψ₀ v) (Ψ₀ w) ↔ C.D₀.VisitBetween u v w)
    (hmp : Ψ₀ C.v_mp = π.w_mp) (hpm : Ψ₀ C.v_pm = π.w_pm) (hmq : Ψ₀ C.v_mq = π.w_mq)
    (hqm : Ψ₀ C.v_qm = π.w_qm) (hpq : Ψ₀ C.v_pq = π.w_pq) (hqp : Ψ₀ C.v_qp = π.w_qp) :
    ∃ Ψ₁ : π.M₀.Γ.Visit ≃ π.M₁.Γ.Visit,
      (∀ v, Ψ₁ (π.M₀.twin v) = π.M₁.twin (Ψ₁ v)) ∧
      (∀ v, π.M₁.overBit (Ψ₁ v) = π.M₀.overBit v) ∧
      (∀ v, π.M₁.sign (Ψ₁ v).1 = π.M₀.sign v.1) ∧
      (∀ u v w : C.D₀.Γ.Visit, π.M₁.VisitBetween (Ψ₁ (Ψ₀ u)) (Ψ₁ (Ψ₀ v)) (Ψ₁ (Ψ₀ w)) ↔
        C.D₀.VisitBetween (C.σD u) (C.σD v) (C.σD w)) ∧
      (∀ v, (Ψ₁ v).1 = π.gu6_y'_pC ↔ v.1 = π.gu6_y_mp) ∧ (∀ v, (Ψ₁ v).1 = π.gu6_y'_qB ↔ v.1 = π.gu6_y_mq) ∧
      (∀ v, (Ψ₁ v).1 = π.gu6_y'_pq ↔ v.1 = π.gu6_y_pq) := by
  refine ⟨π.gu6_Ψ₁, π.gu6_Ψ₁_twin, π.gu6_Ψ₁_overBit, π.gu6_Ψ₁_sign, ?_, ?_, ?_, ?_⟩
  rotate_left
  · intro v
    have e := w3b_fst_eq_iff_of_twin π.gu6_Ψ₁ π.gu6_Ψ₁_twin v π.w_mp
    rwa [gu6_Ψ₁_w_mp, gu6_w'_Cp_fst, gu6_w_mp_fst] at e
  · intro v
    have e := w3b_fst_eq_iff_of_twin π.gu6_Ψ₁ π.gu6_Ψ₁_twin v π.w_mq
    rwa [gu6_Ψ₁_w_mq, gu6_w'_Bq_fst, gu6_w_mq_fst] at e
  · intro v
    have e := w3b_fst_eq_iff_of_twin π.gu6_Ψ₁ π.gu6_Ψ₁_twin v π.w_pq
    rwa [gu6_Ψ₁_w_pq, gu6_w'_pq_fst, gu6_w_pq_fst] at e
  intro u v w
  let σ₀ : π.M₀.Γ.Visit → π.M₀.Γ.Visit := fun x => Ψ₀ (C.σD (Ψ₀.symm x))
  have e_mp : σ₀ π.w_mp = π.w_mq := by
    show Ψ₀ (C.σD (Ψ₀.symm π.w_mp)) = π.w_mq
    rw [← hmp, Equiv.symm_apply_apply, gu6_σD_v_mp, hmq]
  have e_mq : σ₀ π.w_mq = π.w_mp := by
    show Ψ₀ (C.σD (Ψ₀.symm π.w_mq)) = π.w_mp
    rw [← hmq, Equiv.symm_apply_apply, gu6_σD_v_mq, hmp]
  have e_pm : σ₀ π.w_pm = π.w_pq := by
    show Ψ₀ (C.σD (Ψ₀.symm π.w_pm)) = π.w_pq
    rw [← hpm, Equiv.symm_apply_apply, gu6_σD_v_pm, hpq]
  have e_pq : σ₀ π.w_pq = π.w_pm := by
    show Ψ₀ (C.σD (Ψ₀.symm π.w_pq)) = π.w_pm
    rw [← hpq, Equiv.symm_apply_apply, gu6_σD_v_pq, hpm]
  have e_qm : σ₀ π.w_qm = π.w_qp := by
    show Ψ₀ (C.σD (Ψ₀.symm π.w_qm)) = π.w_qp
    rw [← hqm, Equiv.symm_apply_apply, gu6_σD_v_qm, hqp]
  have e_qp : σ₀ π.w_qp = π.w_qm := by
    show Ψ₀ (C.σD (Ψ₀.symm π.w_qp)) = π.w_qm
    rw [← hqp, Equiv.symm_apply_apply, gu6_σD_v_qp, hqm]
  have e0 : ∀ x, x.1 ≠ π.gu6_y_mp ∧ x.1 ≠ π.gu6_y_mq ∧ x.1 ≠ π.gu6_y_pq → σ₀ x = x := by
    intro x hx
    show Ψ₀ (C.σD (Ψ₀.symm x)) = x
    rw [gu6_σD_of_not_local (C := C) (Ψ₀.symm x) ?_ ?_ ?_ ?_ ?_ ?_, Equiv.apply_symm_apply]
    · intro e; apply hx.1
      rw [← π.gu6_w_mp_fst, ← hmp, ← e, Equiv.apply_symm_apply]
    · intro e; apply hx.1
      rw [← π.gu6_w_pm_fst, ← hpm, ← e, Equiv.apply_symm_apply]
    · intro e; apply hx.2.1
      rw [← π.gu6_w_mq_fst, ← hmq, ← e, Equiv.apply_symm_apply]
    · intro e; apply hx.2.1
      rw [← π.gu6_w_qm_fst, ← hqm, ← e, Equiv.apply_symm_apply]
    · intro e; apply hx.2.2
      rw [← π.gu6_w_pq_fst, ← hpq, ← e, Equiv.apply_symm_apply]
    · intro e; apply hx.2.2
      rw [← π.gu6_w_qp_fst, ← hqp, ← e, Equiv.apply_symm_apply]
  have hcyc : ∀ x y z, π.M₁.VisitBetween (π.gu6_Ψ₁ x) (π.gu6_Ψ₁ y) (π.gu6_Ψ₁ z) ↔
      π.M₀.VisitBetween (σ₀ x) (σ₀ y) (σ₀ z) := by
    intro x y z
    exact GT_cyc_congr_of_lt (π.gu6_key_lt σ₀ e_mp e_mq e_pm e_pq e_qm e_qp e0 x y)
      (π.gu6_key_lt σ₀ e_mp e_mq e_pm e_pq e_qm e_qp e0 y z)
      (π.gu6_key_lt σ₀ e_mp e_mq e_pm e_pq e_qm e_qp e0 z x)
  rw [hcyc]
  have hσ : ∀ u, σ₀ (Ψ₀ u) = Ψ₀ (C.σD u) := fun u => by
    show Ψ₀ (C.σD (Ψ₀.symm (Ψ₀ u))) = _
    rw [Equiv.symm_apply_apply]
  rw [hσ, hσ, hσ]
  exact h₀ _ _ _

end W3DECopy


/-- **W3-A1 helper (C-free):** the over/under STRANDS of a positive one-component diagram at a crossing
`{i, j}` with `det(edge i, edge j) > 0` (`gu6_over_under_of_pos` read on strands through `gu6_sv_strand`). -/
theorem w3bc_over_under_pos {Cp : PolyComp} (hΓ : (Shadow.single Cp).Generic) {i j : ZMod Cp.k}
    (h : IsCrossing Cp.P {i, j}) (hpos : 0 < det (edge Cp.P i) (edge Cp.P j)) :
    ((Shadow.single Cp).positiveDiagram hΓ).overStrand ((Shadow.singleCrossingEquiv Cp).symm (xPair h)) =
        (⟨0, i⟩ : (Shadow.single Cp).Strand) ∧
      ((Shadow.single Cp).positiveDiagram hΓ).underStrand ((Shadow.singleCrossingEquiv Cp).symm (xPair h)) =
        (⟨0, j⟩ : (Shadow.single Cp).Strand) := by
  obtain ⟨h1, h2⟩ := RProof.G11_Params.gu6_over_under_of_pos hΓ h hpos
  exact ⟨(congrArg (fun v : ((Shadow.single Cp).positiveDiagram hΓ).Γ.Visit => v.2.val) h1).trans
      (RProof.G11_Params.gu6_sv_strand _ _),
    (congrArg (fun v : ((Shadow.single Cp).positiveDiagram hΓ).Γ.Visit => v.2.val) h2).trans
      (RProof.G11_Params.gu6_sv_strand _ _)⟩

/-- … and with `det(edge i, edge j) < 0`: `j` is over. -/
theorem w3bc_over_under_neg {Cp : PolyComp} (hΓ : (Shadow.single Cp).Generic) {i j : ZMod Cp.k}
    (h : IsCrossing Cp.P {i, j}) (hneg : det (edge Cp.P i) (edge Cp.P j) < 0) :
    ((Shadow.single Cp).positiveDiagram hΓ).overStrand ((Shadow.singleCrossingEquiv Cp).symm (xPair h)) =
        (⟨0, j⟩ : (Shadow.single Cp).Strand) ∧
      ((Shadow.single Cp).positiveDiagram hΓ).underStrand ((Shadow.singleCrossingEquiv Cp).symm (xPair h)) =
        (⟨0, i⟩ : (Shadow.single Cp).Strand) := by
  obtain ⟨h1, h2⟩ := RProof.G11_Params.gu6_over_under_of_neg hΓ h hneg
  exact ⟨(congrArg (fun v : ((Shadow.single Cp).positiveDiagram hΓ).Γ.Visit => v.2.val) h1).trans
      (RProof.G11_Params.gu6_sv_strand _ _),
    (congrArg (fun v : ((Shadow.single Cp).positiveDiagram hΓ).Γ.Visit => v.2.val) h2).trans
      (RProof.G11_Params.gu6_sv_strand _ _)⟩

/-- an equality of crossing signs transports the positivity of the determinant -/
theorem w3bc_det_pos_iff_of_sign_eq {n n' : ℕ} [NeZero n] [NeZero n'] {P : LabelledTuple n}
    {P' : LabelledTuple n'} {i j : ZMod n} {i' j' : ZMod n'} (h : crossingSign P i j = crossingSign P' i' j') :
    0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i') (edge P' j') := by
  unfold crossingSign at h
  exact (GT_det_pos_iff_of_sign h).symm

/-- **(a) sub-leaves** (copies of `gu6_y_mp_ne_mq` … :7016–7044 via `gu6_xPair_ne_of_not_mem` and the
label facts `gu3_remote_*`): the three local crossings are distinct on each side. -/
theorem w3a_y_ne : π.y_mp ≠ π.y_mq ∧ π.y_mp ≠ π.y_pq ∧ π.y_mq ≠ π.y_pq := by
  exact ⟨RProof.G11_Params.gu6_xPair_ne_of_not_mem _ _ π.gu5_mB_ne_mC π.gu5_q'_ne.2.1.symm,
    RProof.G11_Params.gu6_xPair_ne_of_not_mem _ _ π.gu5_p'_ne.2.1.symm π.gu5_q'_ne.2.1.symm,
    RProof.G11_Params.gu6_xPair_ne_of_not_mem _ _ π.gu5_p'_ne.2.2.1.symm π.gu5_q'_ne.2.2.1.symm⟩
theorem w3a_y'_ne : π.y'_pC ≠ π.y'_qB ∧ π.y'_pC ≠ π.y'_pq ∧ π.y'_qB ≠ π.y'_pq := by
  refine ⟨RProof.G11_Params.gu6_xPair_ne_of_not_mem _ _ π.gu5_p'_ne_q' π.gu5_p'_ne.2.1, ?_, ?_⟩
  · intro e
    have e1 := (Shadow.singleCrossingEquiv π.comp₁).symm.injective e
    have e2 := congrArg Subtype.val e1
    change ({π.p', π.mC} : Finset (ZMod (k + 3))) = {π.p', π.q'} at e2
    have : π.mC ∈ ({π.p', π.q'} : Finset (ZMod (k + 3))) := by rw [← e2]; exact mem_pair_right _ _
    rw [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact π.gu5_p'_ne.2.2.1 h.symm
    · exact π.gu5_q'_ne.2.2.1 h.symm
  · intro e
    have e1 := (Shadow.singleCrossingEquiv π.comp₁).symm.injective e
    have e2 := congrArg Subtype.val e1
    change ({π.q', π.mB} : Finset (ZMod (k + 3))) = {π.p', π.q'} at e2
    have : π.mB ∈ ({π.p', π.q'} : Finset (ZMod (k + 3))) := by rw [← e2]; exact mem_pair_right _ _
    rw [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact π.gu5_p'_ne.2.1 h.symm
    · exact π.gu5_q'_ne.2.1 h.symm

/-- **(a) sub-leaves — the over data of the POSITIVE `M₀`, `M₁` at the six local crossings**, by the
determinant sign of the ORIGINAL configuration (copies of `gu6_ov_mp_pos/neg` … :7115–7162 through
`gu6_Rmp_iff`/`gu6_R_pC_iff` :7069–7087 and `gu6_over_under_of_pos/neg` :5879–5926, read on strands).
These are the "six local over bits" of PLAN §5 (a): the positive instance of the parametrised D8. -/
theorem w3a_over_mp₀ :
    (0 < det (edge C.X C.m) (edge C.X C.p) →
      π.M₀.overStrand π.y_mp = π.st₀ π.mB ∧ π.M₀.underStrand π.y_mp = π.st₀ π.p') ∧
    (¬ 0 < det (edge C.X C.m) (edge C.X C.p) →
      π.M₀.overStrand π.y_mp = π.st₀ π.p' ∧ π.M₀.underStrand π.y_mp = π.st₀ π.mB) := by
  have hX : edge π.X₀ π.mB = (π.t₂ - π.t₁) • edge C.X C.m := π.gu4_edge_X₀_mB
  have e : det (edge π.X₀ π.mB) (edge π.X₀ π.p') = (π.t₂ - π.t₁) * det (edge C.X C.m) (edge C.X C.p) := by
    rw [hX, π.gu4_edge_X₀_p', CV.det_smul_left']
  have ht : 0 < π.t₂ - π.t₁ := sub_pos.mpr (π.h₁.trans π.h₂)
  constructor
  · intro h
    have hp : 0 < det (edge π.X₀ π.mB) (edge π.X₀ π.p') := by rw [e]; exact mul_pos ht h
    exact w3bc_over_under_pos π.X₀_generic π.X₀_cross_mp hp
  · intro h
    have h' : det (edge C.X C.m) (edge C.X C.p) < 0 := lt_of_le_of_ne (not_lt.mp h) C.det_mp_ne
    have hn : det (edge π.X₀ π.mB) (edge π.X₀ π.p') < 0 := by rw [e]; exact mul_neg_of_pos_of_neg ht h'
    exact w3bc_over_under_neg π.X₀_generic π.X₀_cross_mp hn
theorem w3a_over_mq₀ :
    (0 < det (edge C.X C.m) (edge C.X C.q) →
      π.M₀.overStrand π.y_mq = π.st₀ π.mC ∧ π.M₀.underStrand π.y_mq = π.st₀ π.q') ∧
    (¬ 0 < det (edge C.X C.m) (edge C.X C.q) →
      π.M₀.overStrand π.y_mq = π.st₀ π.q' ∧ π.M₀.underStrand π.y_mq = π.st₀ π.mC) := by
  have hX : edge π.X₀ π.mC = (π.t₃ - π.t₂) • edge C.X C.m := π.gu4_edge_X₀_mC
  have e : det (edge π.X₀ π.mC) (edge π.X₀ π.q') = (π.t₃ - π.t₂) * det (edge C.X C.m) (edge C.X C.q) := by
    rw [hX, π.gu4_edge_X₀_q', CV.det_smul_left']
  have ht : 0 < π.t₃ - π.t₂ := sub_pos.mpr (π.h₃.trans π.h₄)
  constructor
  · intro h
    have hp : 0 < det (edge π.X₀ π.mC) (edge π.X₀ π.q') := by rw [e]; exact mul_pos ht h
    exact w3bc_over_under_pos π.X₀_generic π.X₀_cross_mq hp
  · intro h
    have h' : det (edge C.X C.m) (edge C.X C.q) < 0 := lt_of_le_of_ne (not_lt.mp h) C.det_mq_ne
    have hn : det (edge π.X₀ π.mC) (edge π.X₀ π.q') < 0 := by rw [e]; exact mul_neg_of_pos_of_neg ht h'
    exact w3bc_over_under_neg π.X₀_generic π.X₀_cross_mq hn
theorem w3a_over_pq₀ :
    (0 < det (edge C.X C.p) (edge C.X C.q) →
      π.M₀.overStrand π.y_pq = π.st₀ π.p' ∧ π.M₀.underStrand π.y_pq = π.st₀ π.q') ∧
    (¬ 0 < det (edge C.X C.p) (edge C.X C.q) →
      π.M₀.overStrand π.y_pq = π.st₀ π.q' ∧ π.M₀.underStrand π.y_pq = π.st₀ π.p') := by
  have e : det (edge π.X₀ π.p') (edge π.X₀ π.q') = det (edge C.X C.p) (edge C.X C.q) := by
    rw [π.gu4_edge_X₀_p', π.gu4_edge_X₀_q']
  constructor
  · intro h
    have hp : 0 < det (edge π.X₀ π.p') (edge π.X₀ π.q') := by rw [e]; exact h
    exact w3bc_over_under_pos π.X₀_generic π.X₀_cross_pq hp
  · intro h
    have hn : det (edge π.X₀ π.p') (edge π.X₀ π.q') < 0 := by
      rw [e]; exact lt_of_le_of_ne (not_lt.mp h) C.det_pq_ne
    exact w3bc_over_under_neg π.X₀_generic π.X₀_cross_pq hn
theorem w3a_over_mp₁ :
    (0 < det (edge C.X C.m) (edge C.X C.p) →
      π.M₁.overStrand π.y'_pC = π.st₁ π.mC ∧ π.M₁.underStrand π.y'_pC = π.st₁ π.p') ∧
    (¬ 0 < det (edge C.X C.m) (edge C.X C.p) →
      π.M₁.overStrand π.y'_pC = π.st₁ π.p' ∧ π.M₁.underStrand π.y'_pC = π.st₁ π.mC) := by
  have e : 0 < det (edge π.X₁ π.p') (edge π.X₁ π.mC) ↔ 0 < det (edge C.X C.p) (edge C.X C.m) :=
    w3bc_det_pos_iff_of_sign_eq π.X₁_sign_pC
  constructor
  · intro h
    have hne : det (edge π.X₁ π.p') (edge π.X₁ π.mC) ≠ 0 :=
      RProof.G11_Params.gu6_det_ne_zero_single π.X₁_generic π.X₁_cross_pC
    have hn : det (edge π.X₁ π.p') (edge π.X₁ π.mC) < 0 := by
      refine lt_of_le_of_ne (not_lt.mp fun h' => ?_) hne
      have := e.mp h'
      rw [det_swap] at this
      linarith
    exact w3bc_over_under_neg π.X₁_generic π.X₁_cross_pC hn
  · intro h
    have h' : det (edge C.X C.m) (edge C.X C.p) < 0 := lt_of_le_of_ne (not_lt.mp h) C.det_mp_ne
    have hp : 0 < det (edge π.X₁ π.p') (edge π.X₁ π.mC) := e.mpr (by rw [det_swap]; linarith)
    exact w3bc_over_under_pos π.X₁_generic π.X₁_cross_pC hp
theorem w3a_over_mq₁ :
    (0 < det (edge C.X C.m) (edge C.X C.q) →
      π.M₁.overStrand π.y'_qB = π.st₁ π.mB ∧ π.M₁.underStrand π.y'_qB = π.st₁ π.q') ∧
    (¬ 0 < det (edge C.X C.m) (edge C.X C.q) →
      π.M₁.overStrand π.y'_qB = π.st₁ π.q' ∧ π.M₁.underStrand π.y'_qB = π.st₁ π.mB) := by
  have e : 0 < det (edge π.X₁ π.q') (edge π.X₁ π.mB) ↔ 0 < det (edge C.X C.q) (edge C.X C.m) :=
    w3bc_det_pos_iff_of_sign_eq π.X₁_sign_qB
  constructor
  · intro h
    have hne : det (edge π.X₁ π.q') (edge π.X₁ π.mB) ≠ 0 :=
      RProof.G11_Params.gu6_det_ne_zero_single π.X₁_generic π.X₁_cross_qB
    have hn : det (edge π.X₁ π.q') (edge π.X₁ π.mB) < 0 := by
      refine lt_of_le_of_ne (not_lt.mp fun h' => ?_) hne
      have := e.mp h'
      rw [det_swap] at this
      linarith
    exact w3bc_over_under_neg π.X₁_generic π.X₁_cross_qB hn
  · intro h
    have h' : det (edge C.X C.m) (edge C.X C.q) < 0 := lt_of_le_of_ne (not_lt.mp h) C.det_mq_ne
    have hp : 0 < det (edge π.X₁ π.q') (edge π.X₁ π.mB) := e.mpr (by rw [det_swap]; linarith)
    exact w3bc_over_under_pos π.X₁_generic π.X₁_cross_qB hp
theorem w3a_over_pq₁ :
    (0 < det (edge C.X C.p) (edge C.X C.q) →
      π.M₁.overStrand π.y'_pq = π.st₁ π.p' ∧ π.M₁.underStrand π.y'_pq = π.st₁ π.q') ∧
    (¬ 0 < det (edge C.X C.p) (edge C.X C.q) →
      π.M₁.overStrand π.y'_pq = π.st₁ π.q' ∧ π.M₁.underStrand π.y'_pq = π.st₁ π.p') := by
  have e : det (edge π.X₁ π.p') (edge π.X₁ π.q') = det (edge C.X C.p) (edge C.X C.q) := by
    rw [π.gu4_edge_X₁_eq _ π.gu4_p'_ne.2.1 π.gu4_p'_ne.2.2.1, π.gu4_edge_X₁_eq _ π.gu4_q'_ne.2.1 π.gu4_q'_ne.2.2.1,
      π.gu4_edge_X₀_p', π.gu4_edge_X₀_q']
  constructor
  · intro h
    have hp : 0 < det (edge π.X₁ π.p') (edge π.X₁ π.q') := by rw [e]; exact h
    exact w3bc_over_under_pos π.X₁_generic π.X₁_cross_pq hp
  · intro h
    have hn : det (edge π.X₁ π.p') (edge π.X₁ π.q') < 0 := by
      rw [e]; exact lt_of_le_of_ne (not_lt.mp h) C.det_pq_ne
    exact w3bc_over_under_neg π.X₁_generic π.X₁_cross_pq hn

/-- **(a) sub-leaf B4′** (copy of `G11_Params.exists_Ψ₀` :1403 + the crossing correspondence): the record
of `M₀` is the record of `D₀` — an occurrence bijection carrying twins, over bits, signs and the cyclic
order (`gu3_visitIso_of_reparam` along the five reparametrizations `gu3_reparam₁…₅`, copied over
`G11_ConfigSw`), sending the six local occurrences to the six local occurrences (`gu3_image_eq`), hence
matching the three local crossings. -/
theorem w3a_exists_Ψ₀ : ∃ Ψ₀ : C.D₀.Γ.Visit ≃ π.M₀.Γ.Visit,
    (∀ v, Ψ₀ (C.D₀.twin v) = π.M₀.twin (Ψ₀ v)) ∧
    (∀ v, π.M₀.overBit (Ψ₀ v) = C.D₀.overBit v) ∧
    (∀ v, π.M₀.sign (Ψ₀ v).1 = C.D₀.sign v.1) ∧
    (∀ u v w, π.M₀.VisitBetween (Ψ₀ u) (Ψ₀ v) (Ψ₀ w) ↔ C.D₀.VisitBetween u v w) ∧
    Ψ₀ C.v_mp = π.w_mp ∧ Ψ₀ C.v_pm = π.w_pm ∧ Ψ₀ C.v_mq = π.w_mq ∧
    Ψ₀ C.v_qm = π.w_qm ∧ Ψ₀ C.v_pq = π.w_pq ∧ Ψ₀ C.v_qp = π.w_qp ∧
    (∀ v, (Ψ₀ v).1 = π.y_mp ↔ v.1 = C.x_mp) ∧ (∀ v, (Ψ₀ v).1 = π.y_mq ↔ v.1 = C.x_mq) ∧
    (∀ v, (Ψ₀ v).1 = π.y_pq ↔ v.1 = C.x_pq) := by
  obtain ⟨Ψ₀, htw, hbit, hsgn, hcyc, hmp, hpm, hmq, hqm, hpq, hqp⟩ := π.exists_Ψ₀
  refine ⟨Ψ₀, htw, hbit, hsgn, hcyc, hmp, hpm, hmq, hqm, hpq, hqp, ?_, ?_, ?_⟩
  · intro v
    have := w3b_fst_eq_iff_of_twin Ψ₀ htw v C.v_mp
    rwa [hmp, π.w_mp_fst, C.v_mp_fst] at this
  · intro v
    have := w3b_fst_eq_iff_of_twin Ψ₀ htw v C.v_mq
    rwa [hmq, π.w_mq_fst, C.v_mq_fst] at this
  · intro v
    have := w3b_fst_eq_iff_of_twin Ψ₀ htw v C.v_pq
    rwa [hpq, π.w_pq_fst, C.v_pq_fst] at this

/-- **(a) THE parametrised D8** (statement-neutral generalisation of `G11_Params.riii` :7172): the RIII
site between the diagrams on the shadows of `X₀` and `X₁` with ARBITRARY over data `f₀`, `f₁` that (i) are
positive away from the three local crossings, (ii) agree on the three local over relations `Rmp Rmq Rpq`
("`m` over `p`": `mB` over `p'` on `X₀`, `mC` over `p'` on `X₁`; etc.), (iii) form a transitive height
order.  Positive instance: `f₀ := M₀.overStrand`, `f₁ := M₁.overStrand`, `Rmp := 0 < det (edge X m) (edge X p)`
… with `htrans := gu6_htrans` — that IS the accepted `riii`.  Proof = the accepted `riii` proof (270 lines)
verbatim: the frame (`disc_isDisc`, `clean_M₀/₁` transported to `withOver` as `⟨h.frontier_injOn, h.exits⟩`),
the move match (`gu5_moveMatch` with `over_eq` from (i) and `inner_M₀/₁`), the arcs and covers (`exists_arcCovers`,
shadow-level), the twelve memberships, the over/under memberships from (ii) in place of `gu6_ov_*`, the
reversals (`gu6_D9_p/q`, shadow-level), then `gu6_riii_of_strands` (accepted, general in `D D'`) with (iii).
Requires the Units B–D copies for `G11_ParamsSw` (≈ 8.5k lines of mechanical copy, see the report). -/
theorem w3a_riii_param (f₀ : π.M₀.Γ.Crossing → π.M₀.Γ.Strand) (hf₀ : ∀ y, f₀ y ∈ y.val)
    (f₁ : π.M₁.Γ.Crossing → π.M₁.Γ.Strand) (hf₁ : ∀ y, f₁ y ∈ y.val)
    (h₀ : ∀ y, y ≠ π.y_mp → y ≠ π.y_mq → y ≠ π.y_pq → f₀ y = π.M₀.overStrand y)
    (h₁ : ∀ y, y ≠ π.y'_pC → y ≠ π.y'_qB → y ≠ π.y'_pq → f₁ y = π.M₁.overStrand y)
    (Rmp Rmq Rpq : Prop)
    (hmp₀ : (Rmp → f₀ π.y_mp = π.st₀ π.mB) ∧ (¬ Rmp → f₀ π.y_mp = π.st₀ π.p'))
    (hmq₀ : (Rmq → f₀ π.y_mq = π.st₀ π.mC) ∧ (¬ Rmq → f₀ π.y_mq = π.st₀ π.q'))
    (hpq₀ : (Rpq → f₀ π.y_pq = π.st₀ π.p') ∧ (¬ Rpq → f₀ π.y_pq = π.st₀ π.q'))
    (hmp₁ : (Rmp → f₁ π.y'_pC = π.st₁ π.mC) ∧ (¬ Rmp → f₁ π.y'_pC = π.st₁ π.p'))
    (hmq₁ : (Rmq → f₁ π.y'_qB = π.st₁ π.mB) ∧ (¬ Rmq → f₁ π.y'_qB = π.st₁ π.q'))
    (hpq₁ : (Rpq → f₁ π.y'_pq = π.st₁ π.p') ∧ (¬ Rpq → f₁ π.y'_pq = π.st₁ π.q'))
    (htrans : ¬ (Rmp ∧ Rpq ∧ ¬ Rmq) ∧ ¬ (¬ Rmp ∧ ¬ Rpq ∧ Rmq)) :
    RIII (π.M₀.withOver f₀ hf₀) (π.M₁.withOver f₁ hf₁) := by
  exact π.w3de_riii_param f₀ hf₀ f₁ hf₁ h₀ h₁ Rmp Rmq Rpq hmp₀ hmq₀ hpq₀ hmp₁ hmq₁ hpq₁ htrans

/-- **(a) sub-leaf E1′** (copy of `G11_Params.exists_Ψ₁` :8552 + the crossing correspondence): the record
of the POSITIVE `M₁` is the record of `M₀` twisted by the three transpositions — `Ψ₁ := gu6_Ψ₁` (the strand
relabelling `mB ↔ mC` on the local crossings, `gu6_ΨX`), twins (`gu6_Ψ₁_twin`), over bits
(`gu6_Ψ₁_overBit`, the divide sign — positivity used HERE, for the positive pair only), signs
(`positiveDiagram_sign`), the twisted key comparison `gu6_key_lt` + `GT_cyc_congr_of_lt`; the six images
`gu6_Ψ₁_w_*` :7786–7810 give the crossing correspondence `{m,p} ↦ {p',mC}`, `{m,q} ↦ {q',mB}`, `{p,q} ↦ {p',q'}`. -/
theorem w3a_exists_Ψ₁ (Ψ₀ : C.D₀.Γ.Visit ≃ π.M₀.Γ.Visit)
    (h₀ : ∀ u v w, π.M₀.VisitBetween (Ψ₀ u) (Ψ₀ v) (Ψ₀ w) ↔ C.D₀.VisitBetween u v w)
    (hmp : Ψ₀ C.v_mp = π.w_mp) (hpm : Ψ₀ C.v_pm = π.w_pm) (hmq : Ψ₀ C.v_mq = π.w_mq)
    (hqm : Ψ₀ C.v_qm = π.w_qm) (hpq : Ψ₀ C.v_pq = π.w_pq) (hqp : Ψ₀ C.v_qp = π.w_qp) :
    ∃ Ψ₁ : π.M₀.Γ.Visit ≃ π.M₁.Γ.Visit,
      (∀ v, Ψ₁ (π.M₀.twin v) = π.M₁.twin (Ψ₁ v)) ∧
      (∀ v, π.M₁.overBit (Ψ₁ v) = π.M₀.overBit v) ∧
      (∀ v, π.M₁.sign (Ψ₁ v).1 = π.M₀.sign v.1) ∧
      (∀ u v w : C.D₀.Γ.Visit, π.M₁.VisitBetween (Ψ₁ (Ψ₀ u)) (Ψ₁ (Ψ₀ v)) (Ψ₁ (Ψ₀ w)) ↔
        C.D₀.VisitBetween (C.σD u) (C.σD v) (C.σD w)) ∧
      (∀ v, (Ψ₁ v).1 = π.y'_pC ↔ v.1 = π.y_mp) ∧ (∀ v, (Ψ₁ v).1 = π.y'_qB ↔ v.1 = π.y_mq) ∧
      (∀ v, (Ψ₁ v).1 = π.y'_pq ↔ v.1 = π.y_pq) := by
  exact π.w3de_exists_Ψ₁ Ψ₀ h₀ hmp hpm hmq hqm hpq hqp

/-! ### W3-(c) D8′ — the RIII site of the switched diagrams (PROVED from `w3a_riii_param` and the
positive over data: the "one more instantiation table" of PLAN §5 (c)) -/

theorem sw_cases (C : G11_ConfigSw k) : C.sw = 0 ∨ C.sw = 1 ∨ C.sw = 2 := by
  generalize C.sw = s
  fin_cases s <;> simp

theorem x₀_eq0 (h : C.sw = 0) : π.x₀ = π.y_mp := by unfold x₀; rw [if_pos h]
theorem x₀_eq1 (h : C.sw = 1) : π.x₀ = π.y_mq := by
  unfold x₀; rw [if_neg (by rw [h]; decide), if_pos h]
theorem x₀_eq2 (h : C.sw = 2) : π.x₀ = π.y_pq := by
  unfold x₀; rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide)]
theorem x₁_eq0 (h : C.sw = 0) : π.x₁ = π.y'_pC := by unfold x₁; rw [if_pos h]
theorem x₁_eq1 (h : C.sw = 1) : π.x₁ = π.y'_qB := by
  unfold x₁; rw [if_neg (by rw [h]; decide), if_pos h]
theorem x₁_eq2 (h : C.sw = 2) : π.x₁ = π.y'_pq := by
  unfold x₁; rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide)]

theorem x₀_cases : π.x₀ = π.y_mp ∨ π.x₀ = π.y_mq ∨ π.x₀ = π.y_pq := by
  rcases sw_cases C with h | h | h
  · exact Or.inl (π.x₀_eq0 h)
  · exact Or.inr (Or.inl (π.x₀_eq1 h))
  · exact Or.inr (Or.inr (π.x₀_eq2 h))

theorem x₁_cases : π.x₁ = π.y'_pC ∨ π.x₁ = π.y'_qB ∨ π.x₁ = π.y'_pq := by
  rcases sw_cases C with h | h | h
  · exact Or.inl (π.x₁_eq0 h)
  · exact Or.inr (Or.inl (π.x₁_eq1 h))
  · exact Or.inr (Or.inr (π.x₁_eq2 h))

/-- which local crossing is switched, as an `iff` on `sw` (uses the distinctness of the three) -/
theorem x₀_eq_mp_iff : π.x₀ = π.y_mp ↔ ¬ C.sw ≠ 0 := by
  obtain ⟨n1, n2, -⟩ := π.w3a_y_ne
  rw [not_not]
  rcases sw_cases C with h | h | h
  · exact ⟨fun _ => h, fun _ => π.x₀_eq0 h⟩
  · rw [π.x₀_eq1 h, h]; exact ⟨fun e => absurd e.symm n1, fun e => absurd e (by decide)⟩
  · rw [π.x₀_eq2 h, h]; exact ⟨fun e => absurd e.symm n2, fun e => absurd e (by decide)⟩
theorem x₀_eq_mq_iff : π.x₀ = π.y_mq ↔ ¬ C.sw ≠ 1 := by
  obtain ⟨n1, -, n3⟩ := π.w3a_y_ne
  rw [not_not]
  rcases sw_cases C with h | h | h
  · rw [π.x₀_eq0 h, h]; exact ⟨fun e => absurd e n1, fun e => absurd e (by decide)⟩
  · exact ⟨fun _ => h, fun _ => π.x₀_eq1 h⟩
  · rw [π.x₀_eq2 h, h]; exact ⟨fun e => absurd e.symm n3, fun e => absurd e (by decide)⟩
theorem x₀_eq_pq_iff : π.x₀ = π.y_pq ↔ ¬ C.sw ≠ 2 := by
  obtain ⟨-, n2, n3⟩ := π.w3a_y_ne
  rw [not_not]
  rcases sw_cases C with h | h | h
  · rw [π.x₀_eq0 h, h]; exact ⟨fun e => absurd e n2, fun e => absurd e (by decide)⟩
  · rw [π.x₀_eq1 h, h]; exact ⟨fun e => absurd e n3, fun e => absurd e (by decide)⟩
  · exact ⟨fun _ => h, fun _ => π.x₀_eq2 h⟩
theorem x₁_eq_pC_iff : π.x₁ = π.y'_pC ↔ ¬ C.sw ≠ 0 := by
  obtain ⟨n1, n2, -⟩ := π.w3a_y'_ne
  rw [not_not]
  rcases sw_cases C with h | h | h
  · exact ⟨fun _ => h, fun _ => π.x₁_eq0 h⟩
  · rw [π.x₁_eq1 h, h]; exact ⟨fun e => absurd e.symm n1, fun e => absurd e (by decide)⟩
  · rw [π.x₁_eq2 h, h]; exact ⟨fun e => absurd e.symm n2, fun e => absurd e (by decide)⟩
theorem x₁_eq_qB_iff : π.x₁ = π.y'_qB ↔ ¬ C.sw ≠ 1 := by
  obtain ⟨n1, -, n3⟩ := π.w3a_y'_ne
  rw [not_not]
  rcases sw_cases C with h | h | h
  · rw [π.x₁_eq0 h, h]; exact ⟨fun e => absurd e n1, fun e => absurd e (by decide)⟩
  · exact ⟨fun _ => h, fun _ => π.x₁_eq1 h⟩
  · rw [π.x₁_eq2 h, h]; exact ⟨fun e => absurd e.symm n3, fun e => absurd e (by decide)⟩
theorem x₁_eq_pq_iff : π.x₁ = π.y'_pq ↔ ¬ C.sw ≠ 2 := by
  obtain ⟨-, n2, n3⟩ := π.w3a_y'_ne
  rw [not_not]
  rcases sw_cases C with h | h | h
  · rw [π.x₁_eq0 h, h]; exact ⟨fun e => absurd e n2, fun e => absurd e (by decide)⟩
  · rw [π.x₁_eq1 h, h]; exact ⟨fun e => absurd e n3, fun e => absurd e (by decide)⟩
  · exact ⟨fun _ => h, fun _ => π.x₁_eq2 h⟩

/-- **the local table at one crossing** (generic): switching `x` flips the over strand at `y` iff `x = y`;
with the positive data `hpos`/`hneg` this is the parametrised D8's local clause for the relation `d ↔ s`. -/
theorem w3c_table_aux {E : Diagram} (x y : E.Γ.Crossing) (a b : E.Γ.Strand) (d s : Prop)
    (hpos : d → E.overStrand y = a ∧ E.underStrand y = b)
    (hneg : ¬ d → E.overStrand y = b ∧ E.underStrand y = a)
    (hxy : x = y ↔ ¬ s) :
    ((d ↔ s) → (E.switch x).overStrand y = a) ∧ (¬ (d ↔ s) → (E.switch x).overStrand y = b) := by
  by_cases hx : x = y
  · subst hx
    have hs : ¬ s := hxy.mp rfl
    rw [E.switch_overStrand_self]
    constructor
    · intro h
      exact (hneg (fun hd => hs (h.mp hd))).2
    · intro h
      have hd : d := by
        by_contra hd
        exact h ⟨fun x => absurd x hd, fun x => absurd x hs⟩
      exact (hpos hd).2
  · have hs : s := by
      by_contra hs
      exact hx (hxy.mpr hs)
    rw [E.switch_overStrand_of_ne (Ne.symm hx)]
    constructor
    · intro h
      exact (hpos (h.mpr hs)).1
    · intro h
      exact (hneg (fun hd => h ⟨fun _ => hs, fun _ => hd⟩)).1

/-- **(c) D8′ (PROVED):** `RIII M₀^{sw} M₁^{sw}` — the parametrised D8 at the switched over data
`Rmp_sw Rmq_sw Rpq_sw` (the local table: at the switched pair the roles of over and under are exchanged,
elsewhere the positive data), transitivity from `trans_sw` (`w3c_htrans_sw`). -/
theorem w3c_riii_sw : RIII π.M₀sw π.M₁sw := by
  refine π.w3a_riii_param (π.M₀.switch π.x₀).overStrand (π.M₀.switch π.x₀).over_mem
    (π.M₁.switch π.x₁).overStrand (π.M₁.switch π.x₁).over_mem ?_ ?_ C.Rmp_sw C.Rmq_sw C.Rpq_sw
    (w3c_table_aux π.x₀ π.y_mp _ _ _ _ π.w3a_over_mp₀.1 π.w3a_over_mp₀.2 π.x₀_eq_mp_iff)
    (w3c_table_aux π.x₀ π.y_mq _ _ _ _ π.w3a_over_mq₀.1 π.w3a_over_mq₀.2 π.x₀_eq_mq_iff)
    (w3c_table_aux π.x₀ π.y_pq _ _ _ _ π.w3a_over_pq₀.1 π.w3a_over_pq₀.2 π.x₀_eq_pq_iff)
    (w3c_table_aux π.x₁ π.y'_pC _ _ _ _ π.w3a_over_mp₁.1 π.w3a_over_mp₁.2 π.x₁_eq_pC_iff)
    (w3c_table_aux π.x₁ π.y'_qB _ _ _ _ π.w3a_over_mq₁.1 π.w3a_over_mq₁.2 π.x₁_eq_qB_iff)
    (w3c_table_aux π.x₁ π.y'_pq _ _ _ _ π.w3a_over_pq₁.1 π.w3a_over_pq₁.2 π.x₁_eq_pq_iff)
    C.w3c_htrans_sw
  · intro y h1 h2 h3
    apply π.M₀.switch_overStrand_of_ne
    rcases π.x₀_cases with h | h | h <;> rw [h] <;> assumption
  · intro y h1 h2 h3
    apply π.M₁.switch_overStrand_of_ne
    rcases π.x₁_cases with h | h | h <;> rw [h] <;> assumption

/-- `P(M₁^{sw}) = P(M₀^{sw})` by `ax:homfly` (accepted `homfly_reidemeister_III`) -/
theorem w3c_homfly_M₁sw : homfly π.M₁sw = homfly π.M₀sw :=
  (homfly_reidemeister_III π.w3c_riii_sw).symm

/-! ### W3-(d) E′ — the record of `M₁^{sw}` (PROVED from E1′ and the switch transport: the over bits at
the six local occurrences are flipped at the switched pair on BOTH sides, everything else is shadow-level) -/

/-- the switched crossings correspond under a bijection matching the three local crossings -/
theorem x₁_iff_of_local (Ψ₁ : π.M₀.Γ.Visit ≃ π.M₁.Γ.Visit)
    (hmp : ∀ v, (Ψ₁ v).1 = π.y'_pC ↔ v.1 = π.y_mp) (hmq : ∀ v, (Ψ₁ v).1 = π.y'_qB ↔ v.1 = π.y_mq)
    (hpq : ∀ v, (Ψ₁ v).1 = π.y'_pq ↔ v.1 = π.y_pq) (v : π.M₀.Γ.Visit) :
    (Ψ₁ v).1 = π.x₁ ↔ v.1 = π.x₀ := by
  unfold x₀ x₁
  split_ifs
  · exact hmp v
  · exact hmq v
  · exact hpq v

/-- the switched crossing of `D₀` corresponds to `x₀` under a bijection matching the local crossings -/
theorem x₀_iff_of_local (Ψ₀ : C.D₀.Γ.Visit ≃ π.M₀.Γ.Visit)
    (hmp : ∀ v, (Ψ₀ v).1 = π.y_mp ↔ v.1 = C.x_mp) (hmq : ∀ v, (Ψ₀ v).1 = π.y_mq ↔ v.1 = C.x_mq)
    (hpq : ∀ v, (Ψ₀ v).1 = π.y_pq ↔ v.1 = C.x_pq) (v : C.D₀.Γ.Visit) :
    (Ψ₀ v).1 = π.x₀ ↔ v.1 = C.xs := by
  rw [C.xs_eq]
  unfold x₀
  split_ifs
  · exact hmp v
  · exact hmq v
  · exact hpq v

/-- **(d) E′ (PROVED):** the occurrence bijection `M₀^{sw} ≃ M₁^{sw}` with twins, over bits, signs and the
`σ`-twisted cyclic order — `Ψ₁` of E1′ with the two local switches transported by `w3b_*`. -/
theorem w3d_exists_Ψ₁_sw (Ψ₀ : C.D₀.Γ.Visit ≃ π.M₀.Γ.Visit)
    (h₀ : ∀ u v w, π.M₀.VisitBetween (Ψ₀ u) (Ψ₀ v) (Ψ₀ w) ↔ C.D₀.VisitBetween u v w)
    (hmp : Ψ₀ C.v_mp = π.w_mp) (hpm : Ψ₀ C.v_pm = π.w_pm) (hmq : Ψ₀ C.v_mq = π.w_mq)
    (hqm : Ψ₀ C.v_qm = π.w_qm) (hpq : Ψ₀ C.v_pq = π.w_pq) (hqp : Ψ₀ C.v_qp = π.w_qp) :
    ∃ Ψ₁ : π.M₀.Γ.Visit ≃ π.M₁.Γ.Visit,
      (∀ v, Ψ₁ (π.M₀sw.twin v) = π.M₁sw.twin (Ψ₁ v)) ∧
      (∀ v, π.M₁sw.overBit (Ψ₁ v) = π.M₀sw.overBit v) ∧
      (∀ v, π.M₁sw.sign (Ψ₁ v).1 = π.M₀sw.sign v.1) ∧
      (∀ u v w : C.D₀sw.Γ.Visit, π.M₁sw.VisitBetween (Ψ₁ (Ψ₀ u)) (Ψ₁ (Ψ₀ v)) (Ψ₁ (Ψ₀ w)) ↔
        C.D₀sw.VisitBetween (C.σD u) (C.σD v) (C.σD w)) := by
  obtain ⟨Ψ₁, htw, hbit, hsgn, hcyc, hc_mp, hc_mq, hc_pq⟩ := π.w3a_exists_Ψ₁ Ψ₀ h₀ hmp hpm hmq hqm hpq hqp
  have hx := π.x₁_iff_of_local Ψ₁ hc_mp hc_mq hc_pq
  exact ⟨Ψ₁, htw, w3b_overBit_switch_of_visitIso Ψ₁ π.x₀ π.x₁ hx hbit,
    w3b_sign_switch_of_visitIso Ψ₁ π.x₀ π.x₁ hx hsgn, hcyc⟩

end G11_ParamsSw

/-- **W3-A1 helper** (copy of `RProof.gu3_exists_small` :8650 over `G11_ConfigSw`): the three flat vertices
and the apex can be chosen `η`-close to the three double points. -/
theorem w3bc_exists_small {k : ℕ} [NeZero k] (C : G11_ConfigSw k) {η : ℝ} (hη : 0 < η) :
    ∃ t₁ t₂ t₃ lam : ℝ, 0 < t₁ ∧
      t₁ < crossingParameter (xPair C.hmp) C.m (mem_pair_left _ _) ∧
      crossingParameter (xPair C.hmp) C.m (mem_pair_left _ _) < t₂ ∧
      t₂ < crossingParameter (xPair C.hmq) C.m (mem_pair_left _ _) ∧
      crossingParameter (xPair C.hmq) C.m (mem_pair_left _ _) < t₃ ∧ t₃ < 1 ∧ 1 < lam ∧
      dist (edgePoint C.X C.m t₁) (crossingPoint (xPair C.hmp)) < η ∧
      dist (edgePoint C.X C.m t₂ + lam • (crossingPoint (xPair C.hpq) - edgePoint C.X C.m t₂))
        (crossingPoint (xPair C.hpq)) < η ∧
      dist (edgePoint C.X C.m t₃) (crossingPoint (xPair C.hmq)) < η := by
  have h0 := (G11_ParamsSw.gu3_param_interior C C.hmp).1
  have h1 := (G11_ParamsSw.gu3_param_interior C C.hmq).2
  have hord := C.order
  have ha := (crossingParameter_spec (xPair C.hmp) C.m (mem_pair_left _ _)).2.2
  have hb := (crossingParameter_spec (xPair C.hmq) C.m (mem_pair_left _ _)).2.2
  set tmp := crossingParameter (xPair C.hmp) C.m (mem_pair_left _ _) with htmp
  set tmq := crossingParameter (xPair C.hmq) C.m (mem_pair_left _ _) with htmq
  have hNpos : 0 < ‖edge C.X C.m‖ + 1 := by positivity
  set N := ‖edge C.X C.m‖ + 1 with hN
  set δ := min (min (tmp / 2) ((1 - tmq) / 2)) (η / (2 * N)) with hδ
  have hδpos : 0 < δ := lt_min (lt_min (by linarith) (by linarith)) (by positivity)
  have hδ1 : δ ≤ tmp / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ (1 - tmq) / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ η / (2 * N) := min_le_right _ _
  have hsmall : ∀ t s : ℝ, |t - s| ≤ δ →
      dist (edgePoint C.X C.m t) (edgePoint C.X C.m s) < η := by
    intro t s hts
    rw [dist_eq_norm, RProof.G11_Params.gu3_edgePoint_sub, norm_smul, Real.norm_eq_abs]
    calc |t - s| * ‖edge C.X C.m‖ ≤ δ * N := mul_le_mul hts (by linarith) (norm_nonneg _) hδpos.le
      _ ≤ η / (2 * N) * N := mul_le_mul_of_nonneg_right hδ3 hNpos.le
      _ = η / 2 := by rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hNpos.ne']
      _ < η := by linarith
  have hM : 0 ≤ ‖crossingPoint (xPair C.hpq) - edgePoint C.X C.m ((tmp + tmq) / 2)‖ :=
    norm_nonneg _
  set N₂ := ‖crossingPoint (xPair C.hpq) - edgePoint C.X C.m ((tmp + tmq) / 2)‖ with hN₂
  have hlpos : 0 < η / (2 * (N₂ + 1)) := by positivity
  refine ⟨tmp - δ, (tmp + tmq) / 2, tmq + δ, 1 + η / (2 * (N₂ + 1)), by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, ?_, ?_, ?_⟩
  · rw [ha]
    exact hsmall _ _ (by rw [abs_of_nonpos (by linarith)]; linarith)
  · have e : edgePoint C.X C.m ((tmp + tmq) / 2) + (1 + η / (2 * (N₂ + 1))) •
        (crossingPoint (xPair C.hpq) - edgePoint C.X C.m ((tmp + tmq) / 2)) -
        crossingPoint (xPair C.hpq) =
        (η / (2 * (N₂ + 1))) • (crossingPoint (xPair C.hpq) - edgePoint C.X C.m ((tmp + tmq) / 2)) := by
      module
    rw [dist_eq_norm, e, norm_smul, Real.norm_of_nonneg hlpos.le, div_mul_eq_mul_div,
      div_lt_iff₀ (by positivity)]
    nlinarith
  · rw [hb]
    exact hsmall _ _ (by rw [abs_of_nonneg (by linarith)]; linarith)

/-- **(a) sub-leaf (Units B–D, the choice of parameters)** — copy of `G11_exists_params` :8705 over
`G11_ConfigSw` (`G11_ConfigSw.clear_edge` in place of `G11_Config.clear_edge`; `gu3_triangle_compact`,
`gu3_disc_convex`, `gu3_triangle_sub_interior_disc`, `gu3_exists_small` re-stated for `G11_discOfSw`). -/
theorem w3a_exists_params {k : ℕ} [NeZero k] (C : G11_ConfigSw k) : Nonempty (G11_ParamsSw C) := by
  classical
  -- the closed set of the foreign edges and of the vertices
  let K : Set Plane :=
    (⋃ h ∈ {h : ZMod k | h ≠ C.m ∧ h ≠ C.p ∧ h ≠ C.q}, edgeSegment C.X h) ∪ Set.range C.X
  have hKc : IsClosed K :=
    ((Set.toFinite _).isClosed_biUnion fun h _ => RProof.gu3_edgeSegment_isClosed C.X h).union
      (Set.finite_range C.X).isClosed
  have hΔK : G11_triangle C.X C.hmp C.hmq C.hpq ⊆ Kᶜ := by
    intro y hy hyK
    rcases hyK with hyK | ⟨i, rfl⟩
    · rw [Set.mem_iUnion₂] at hyK
      obtain ⟨h, ⟨hm, hp, hq⟩, hyh⟩ := hyK
      exact C.clear_edge h hm hp hq y hyh hy
    · exact C.clear_vertex i hy
  obtain ⟨δ, hδ, hδK⟩ := (G11_ParamsSw.gu3_triangle_compact C).exists_thickening_subset_open
    hKc.isOpen_compl hΔK
  -- the radius of the triangle about its centroid
  have hMpos : 0 < dist (crossingPoint (xPair C.hmp)) (G11_centroidSw C) +
      dist (crossingPoint (xPair C.hmq)) (G11_centroidSw C) +
      dist (crossingPoint (xPair C.hpq)) (G11_centroidSw C) + 1 := by positivity
  set M := dist (crossingPoint (xPair C.hmp)) (G11_centroidSw C) +
    dist (crossingPoint (xPair C.hmq)) (G11_centroidSw C) +
    dist (crossingPoint (xPair C.hpq)) (G11_centroidSw C) + 1 with hM
  have hΔM : ∀ y ∈ G11_triangle C.X C.hmp C.hmq C.hpq, dist y (G11_centroidSw C) ≤ M := by
    intro y hy
    have hsub : G11_triangle C.X C.hmp C.hmq C.hpq ⊆ Metric.closedBall (G11_centroidSw C) M := by
      apply convexHull_min _ (convex_closedBall _ M)
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rw [Metric.mem_closedBall]
      have d1 := dist_nonneg (x := crossingPoint (xPair C.hmp)) (y := G11_centroidSw C)
      have d2 := dist_nonneg (x := crossingPoint (xPair C.hmq)) (y := G11_centroidSw C)
      have d3 := dist_nonneg (x := crossingPoint (xPair C.hpq)) (y := G11_centroidSw C)
      rcases hz with rfl | rfl | rfl <;> linarith
    exact hsub hy
  have hrpos : 0 < δ / (2 * M) := by positivity
  set r := δ / (2 * M) with hr
  have hU : G11_discOfSw C r ⊆ Kᶜ := by
    rintro _ ⟨y, hy, rfl⟩
    apply hδK
    rw [Metric.mem_thickening_iff]
    refine ⟨y, hy, ?_⟩
    show dist (G11_centroidSw C + (1 + r) • (y - G11_centroidSw C)) y < δ
    have hyz : G11_centroidSw C + (1 + r) • (y - G11_centroidSw C) - y = r • (y - G11_centroidSw C) := by
      module
    rw [dist_eq_norm, hyz, norm_smul, Real.norm_of_nonneg hrpos.le, ← dist_eq_norm]
    calc r * dist y (G11_centroidSw C) ≤ r * M := mul_le_mul_of_nonneg_left (hΔM y hy) hrpos.le
      _ = δ / 2 := by rw [hr, div_mul_eq_mul_div, mul_div_mul_right _ _ hMpos.ne']
      _ < δ := by linarith
  obtain ⟨η, hη, hηU⟩ := (G11_ParamsSw.gu3_triangle_compact C).exists_thickening_subset_open
    isOpen_interior (G11_ParamsSw.gu3_triangle_sub_interior_disc C hrpos)
  obtain ⟨t₁, t₂, t₃, lam, ht₁, h₁, h₂, h₃, h₄, ht₃, hlam, hd₁, hd₂, hd₃⟩ := w3bc_exists_small C hη
  refine ⟨⟨t₁, t₂, t₃, lam, r, ht₁, h₁, h₂, h₃, h₄, ht₃, hlam, hrpos, ?_, ?_, ?_⟩⟩
  · apply convexHull_min _ (G11_ParamsSw.gu3_disc_convex C r).interior
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    apply hηU
    rw [Metric.mem_thickening_iff]
    rcases hz with rfl | rfl | rfl
    · exact ⟨crossingPoint (xPair C.hmp), subset_convexHull ℝ _ (by simp), hd₁⟩
    · exact ⟨crossingPoint (xPair C.hpq), subset_convexHull ℝ _ (by simp), hd₂⟩
    · exact ⟨crossingPoint (xPair C.hmq), subset_convexHull ℝ _ (by simp), hd₃⟩
  · intro h hm hp hq x hx hxU
    exact hU hxU (Or.inl (Set.mem_biUnion
      (show h ∈ {h : ZMod k | h ≠ C.m ∧ h ≠ C.p ∧ h ≠ C.q} from ⟨hm, hp, hq⟩) hx))
  · intro i hxU
    exact hU hxU (Or.inr ⟨i, rfl⟩)

/-- **Leaf (Wave 3, ≈ 4.5–6.5k lines).** -/
theorem G11_core_sw {k : ℕ} [NeZero k] (C : G11_ConfigSw k) : G11_core_sw_statement C := by
  obtain ⟨π⟩ := w3a_exists_params C
  obtain ⟨Ψ₀, htw₀, hbit₀, hsgn₀, hcyc₀, hmp, hpm, hmq, hqm, hpq, hqp, hc_mp, hc_mq, hc_pq⟩ :=
    π.w3a_exists_Ψ₀
  obtain ⟨Ψ₁, htw₁, hbit₁, hsgn₁, hcyc₁⟩ := π.w3d_exists_Ψ₁_sw Ψ₀ hcyc₀ hmp hpm hmq hqm hpq hqp
  have hx₀ := π.x₀_iff_of_local Ψ₀ hc_mp hc_mq hc_pq
  have hhom : homfly (π.M₀.switch π.x₀) = homfly (C.D₀.switch C.xs) :=
    (w3b_homfly_switch_of_clauses (D := C.D₀) (D' := π.M₀) rfl rfl Ψ₀ C.xs π.x₀ hx₀ htw₀ hbit₀
      hsgn₀ hcyc₀).symm
  refine ⟨π.M₁sw, Ψ₀.trans Ψ₁, rfl, π.w3c_homfly_M₁sw.trans hhom, ?_, ?_, ?_, ?_⟩
  · intro v
    exact (congrArg Ψ₁ (htw₀ v)).trans (htw₁ (Ψ₀ v))
  · intro v
    exact (hbit₁ (Ψ₀ v)).trans (w3b_overBit_switch_of_visitIso Ψ₀ C.xs π.x₀ hx₀ hbit₀ v)
  · intro v
    exact (hsgn₁ (Ψ₀ v)).trans (w3b_sign_switch_of_visitIso Ψ₀ C.xs π.x₀ hx₀ hsgn₀ v)
  · intro u v w
    exact hcyc₁ u v w


/-! ### W3-(e) A′ + F′ — the configuration extraction at the K3 side (with `trans_sw` in place of
`trans`) and the transposition record isomorphism against `D_L.switch x_L`; the row-level assembly
`w3e_strong_case_sw` (the switched `G11_strong_case`) is PROVED from the leaf and the sub-leaves. -/

section W3E

open SM.GeoCarrier SM.Carrier

variable {n : ℕ} [NeZero n]

/-- flipping one entry of a NONZERO alternating sign triple makes it non-alternating (PROVED by `decide`;
`IsAlternating 0 0 0` holds and is flip-invariant, hence the hypothesis `a ≠ 0` — the transverse signs of
the consumer are nonzero: `crossingSign`/`strandSign` of a crossing of a generic polygon) -/
theorem w3e_alt_flip (a b c : SignType) (ha : a ≠ 0) (h : IsAlternating a b c) :
    ¬ IsAlternating (-a) b c ∧ ¬ IsAlternating a (-b) c ∧ ¬ IsAlternating a b (-c) := by
  unfold IsAlternating at *
  revert a b c
  decide

/-- the `trans_sw` clause of `G11_ConfigSw` from a nonzero alternating triple, for every choice of the
switched pair (PROVED by `decide`) -/
theorem w3e_trans_sw_of_alt (a b c : SignType) (ha : a ≠ 0) (h : IsAlternating a b c) (sw : Fin 3) :
    ¬ IsAlternating (if sw = 0 then -a else a) (if sw = 1 then -b else b) (if sw = 2 then -c else c) := by
  unfold IsAlternating at *
  revert a b c sw
  decide

/-- **A′ (PROVED): the K3 side is alternating** — `CompleteLocal → ExtremeLocal` (`extremeLocal_iff`) and
`GenericTableData.extreme_iff_alternating`.  NOTE (executor decision): `GenericTableData` (or
`G1.GoodRadius`) is NOT among the hypotheses of the frozen `esc_interface` (RALedgers.lean:2027, which
passes only `LocalizationData`); the ledger `esc_couple` has `hE : E.IsSimpleRIII …` from which
`generic_table` yields it — the interface must be extended (F-177-2), see the report. -/
theorem w3e_alt_of_completeLocal {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hGT : GenericTableData E e f g δ) (t : E.Parameter) (ht : Punctured E δ t)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) (hK : CompleteLocal (geomAt E t ht.1) hef heg hfg) :
    IsAlternating (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) (strandSign (E.curve t) f g) :=
  (hGT.extreme_iff_alternating t ht hef heg hfg).mp ((extremeLocal_iff _ hef heg hfg).mpr (Or.inl hK))

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {e f g : ZMod n}
  {T : Finset (Crossing P)} {T' : Finset (Crossing P')}
  (hT : GeoIndependent hG.cg T) (hT' : GeoIndependent hG'.cg T')
  (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T')

/-- the parent triangle crossing of the switched pair: `0 ↦ x_ef`, `1 ↦ x_eg`, `2 ↦ x_fg` -/
def w3e_swPair (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (sw : Fin 3) : Crossing P :=
  if sw = 0 then xPair hcef else if sw = 1 then xPair hceg else xPair hcfg

/-- **A14′ (PROVED, the copy of `G11_cfg_trans` :10040 with the flip)**: the switched over-order of the
configuration's three strands is transitive when the strand-sign triple of `P` flipped at `sw` is
non-alternating (`G11_carrierSign` ×3, `strandSign_eq_crossingSign`). -/
theorem w3e_cfg_trans_sw (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g})
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q) (sw : Fin 3)
    (hsw : ¬ IsAlternating (if sw = 0 then -strandSign P e f else strandSign P e f)
      (if sw = 1 then -strandSign P e g else strandSign P e g)
      (if sw = 2 then -strandSign P f g else strandSign P f g)) :
    ¬ IsAlternating
      (if sw = 0 then -crossingSign (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri)
          (G11_pE hn hG hT q hcef htri)
        else crossingSign (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) (G11_pE hn hG hT q hcef htri))
      (if sw = 1 then -crossingSign (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri)
          (G11_qE hn hG hT q hceg htri)
        else crossingSign (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) (G11_qE hn hG hT q hceg htri))
      (if sw = 2 then -crossingSign (geoCornerPolygon hG.cg T q) (G11_pE hn hG hT q hcef htri)
          (G11_qE hn hG hT q hceg htri)
        else crossingSign (geoCornerPolygon hG.cg T q) (G11_pE hn hG hT q hcef htri) (G11_qE hn hG hT q hceg htri)) := by
  have h1 := G11_carrierSign hn hG hT q (G11_vef hcef) (G11_vfe hcef) (G11_mem_tri_ef hG q hcef htri)
    (G11_mem_tri_ef hG q hcef htri)
  have h2 := G11_carrierSign hn hG hT q (G11_vef hcef) (G11_vge hceg) (G11_mem_tri_ef hG q hcef htri)
    (G11_mem_tri_eg hG q hceg htri)
  have h3 := G11_carrierSign hn hG hT q (G11_vfe hcef) (G11_vge hceg) (G11_mem_tri_ef hG q hcef htri)
    (G11_mem_tri_eg hG q hceg htri)
  unfold G11_mE G11_pE G11_qE
  rw [h1, h2, h3]
  exact hsw

/-- **A′: the configuration extraction at the K3 side** — `G11_configOf` (:10231) with `trans` replaced by
the switched pair `sw` and `trans_sw`; the twelve other fields are the accepted Unit A leaves (none of
which takes `halt`).  `D₀sw` is `(geoPositiveLift hn hG hT q).switch xs` by `rfl` (`w3e_configOfSw_D₀sw`). -/
def w3e_configOfSw (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q)
    (hord : crossingParameter (xPair hcef) e (mem_pair_left _ _) <
      crossingParameter (xPair hceg) e (mem_pair_left _ _))
    (sw : Fin 3)
    (hsw : ¬ IsAlternating (if sw = 0 then -strandSign P e f else strandSign P e f)
      (if sw = 1 then -strandSign P e g else strandSign P e g)
      (if sw = 2 then -strandSign P f g else strandSign P f g)) :
    G11_ConfigSw (geoCornerCount hG.cg T q) where
  hk := three_le_geoCornerCount hn hG hT q
  X := geoCornerPolygon hG.cg T q
  gen := geoCarrierShadow_generic hn hG hT q
  m := G11_mE hn hG hT q hcef htri
  p := G11_pE hn hG hT q hcef htri
  q := G11_qE hn hG hT q hceg htri
  hmp := G11_cfg_hmp hn hG hT q hcef htri
  hmq := G11_cfg_hmq hn hG hs hT q hcef hceg htri hX
  hpq := G11_cfg_hpq hn hG hs hT q hfg hcef hceg hcfg htri hX
  order := G11_cfg_order hn hG hs hT q hcef hceg htri hX hord
  clear_frontier := G11_cfg_clear_frontier hn hG hs hT q hcef hceg hcfg htri hef heg hfg hX
  clear_vertex := G11_cfg_clear_vertex hn hG hs hT q hcef hceg hcfg htri hef heg hfg hX
  sw := sw
  trans_sw := w3e_cfg_trans_sw hn hG hT q hcef hceg htri sw hsw

/-- Sanity: `D₀^{sw}` of the extracted configuration is the switched positive lift, definitionally. -/
theorem w3e_configOfSw_D₀sw (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q)
    (hord : crossingParameter (xPair hcef) e (mem_pair_left _ _) <
      crossingParameter (xPair hceg) e (mem_pair_left _ _))
    (sw : Fin 3)
    (hsw : ¬ IsAlternating (if sw = 0 then -strandSign P e f else strandSign P e f)
      (if sw = 1 then -strandSign P e g else strandSign P e g)
      (if sw = 2 then -strandSign P f g else strandSign P f g)) :
    (w3e_configOfSw hn hG hs hT q hef heg hfg hcef hceg hcfg hX htri hord sw hsw).D₀sw =
      (geoPositiveLift hn hG hT q).switch
        (w3e_configOfSw hn hG hs hT q hef heg hfg hcef hceg hcfg hX htri hord sw hsw).xs := rfl

/-- **(e) sub-leaf A′-pt**: the double point of the switched crossing `xs` of the extracted configuration
is the double point of the parent triangle crossing `w3e_swPair sw` (`gu3_crossingPoint_symm` on the
one-component lift + `G11_carrierEdge_crossingPoint` through `G11_cfg_hmp/hmq/hpq`; three cases on `sw`).
This is what identifies `xs` with the consumer's `x_H` (`esc_MoveData.switch_riii` names it by
`crossingPoint x_H = crossingPoint (xPair hef)`; `Shadow.Generic.crossingPoint_injective`). -/
theorem w3e_xs_point (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q)
    (hord : crossingParameter (xPair hcef) e (mem_pair_left _ _) <
      crossingParameter (xPair hceg) e (mem_pair_left _ _))
    (sw : Fin 3)
    (hsw : ¬ IsAlternating (if sw = 0 then -strandSign P e f else strandSign P e f)
      (if sw = 1 then -strandSign P e g else strandSign P e g)
      (if sw = 2 then -strandSign P f g else strandSign P f g)) :
    (geoPositiveLift hn hG hT q).Γ.crossingPoint
        (w3e_configOfSw hn hG hs hT q hef heg hfg hcef hceg hcfg hX htri hord sw hsw).xs =
      crossingPoint (w3e_swPair hcef hceg hcfg sw) := by
  set C := w3e_configOfSw hn hG hs hT q hef heg hfg hcef hceg hcfg hX htri hord sw hsw with hC
  have hmp : C.D₀.Γ.crossingPoint C.x_mp = crossingPoint (xPair hcef) := by
    have h := G11_ParamsSw.gu3_cp_v_mp (C := C)
    rw [C.v_mp_fst] at h
    exact h.trans (gu2_xmp_eq hn hG hT q hcef htri C.hmp)
  have hmq : C.D₀.Γ.crossingPoint C.x_mq = crossingPoint (xPair hceg) := by
    have h := G11_ParamsSw.gu3_cp_v_mq (C := C)
    rw [C.v_mq_fst] at h
    exact h.trans (gu2_xmq_eq hn hG hT q hcef hceg htri C.hmq)
  have hpq : C.D₀.Γ.crossingPoint C.x_pq = crossingPoint (xPair hcfg) := by
    have h := G11_ParamsSw.gu3_cp_v_pq (C := C)
    rw [C.v_pq_fst] at h
    exact h.trans (gu2_xpq_eq hn hG hT q hcef hceg hcfg htri C.hpq)
  have hsw' : C.sw = sw := rfl
  show C.D₀.Γ.crossingPoint C.xs = _
  rw [C.xs_eq, hsw']
  unfold w3e_swPair
  by_cases hs0 : sw = 0
  · rw [if_pos hs0, if_pos hs0]
    exact hmp
  · by_cases hs1 : sw = 1
    · rw [if_neg hs0, if_pos hs1, if_neg hs0, if_pos hs1]
      exact hmq
    · rw [if_neg hs0, if_neg hs1, if_neg hs0, if_neg hs1]
      exact hpq

/-- **(E) helper — the `halt`-free `gu6_lift_six` (:10758)**: the parents of the six local occurrences of
the lift of the distinguished carrier, read through the switched configuration `w3e_configOfSw`, are the
six local visits of `P` (`gu6_liftVisit_symm_eq` six times; nothing here depends on `sw`). -/
theorem w3be_lift_six (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q)
    (hord : crossingParameter (xPair hcef) e (mem_pair_left _ _) <
      crossingParameter (xPair hceg) e (mem_pair_left _ _))
    (sw : Fin 3)
    (hsw : ¬ IsAlternating (if sw = 0 then -strandSign P e f else strandSign P e f)
      (if sw = 1 then -strandSign P e g else strandSign P e g)
      (if sw = 2 then -strandSign P f g else strandSign P f g)) :
    let C := w3e_configOfSw hn hG hs hT q hef heg hfg hcef hceg hcfg hX htri hord sw hsw
    CV.liftVisit hn hG hT q ((Shadow.singleVisitEquiv C.comp).symm C.vmp) = G11_vef hcef ∧
    CV.liftVisit hn hG hT q ((Shadow.singleVisitEquiv C.comp).symm C.vpm) = G11_vfe hcef ∧
    CV.liftVisit hn hG hT q ((Shadow.singleVisitEquiv C.comp).symm C.vmq) = G11_veg hceg ∧
    CV.liftVisit hn hG hT q ((Shadow.singleVisitEquiv C.comp).symm C.vqm) = G11_vge hceg ∧
    CV.liftVisit hn hG hT q ((Shadow.singleVisitEquiv C.comp).symm C.vpq) = G11_vfg hcfg ∧
    CV.liftVisit hn hG hT q ((Shadow.singleVisitEquiv C.comp).symm C.vqp) = G11_vgf hcfg := by
  intro C
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gu6_liftVisit_symm_eq hn hG hT q C.vmp C.vpm rfl (G11_vef hcef) (G11_vfe hcef)
      (G11_mem_tri_ef hG q hcef htri) (G11_mem_tri_ef hG q hcef htri) rfl rfl hcef (G11_vef hcef) rfl rfl
  · exact gu6_liftVisit_symm_eq hn hG hT q C.vpm C.vmp rfl (G11_vfe hcef) (G11_vef hcef)
      (G11_mem_tri_ef hG q hcef htri) (G11_mem_tri_ef hG q hcef htri) rfl rfl (G11_Params.gu6_isCrossing_comm hcef)
      (G11_vfe hcef) (Subtype.ext (Finset.pair_comm e f)) rfl
  · exact gu6_liftVisit_symm_eq hn hG hT q C.vmq C.vqm rfl (G11_vef hcef) (G11_vge hceg)
      (G11_mem_tri_ef hG q hcef htri) (G11_mem_tri_eg hG q hceg htri) rfl rfl hceg (G11_veg hceg) rfl rfl
  · exact gu6_liftVisit_symm_eq hn hG hT q C.vqm C.vmq rfl (G11_vge hceg) (G11_vef hcef)
      (G11_mem_tri_eg hG q hceg htri) (G11_mem_tri_ef hG q hcef htri) rfl rfl (G11_Params.gu6_isCrossing_comm hceg)
      (G11_vge hceg) (Subtype.ext (Finset.pair_comm e g)) rfl
  · exact gu6_liftVisit_symm_eq hn hG hT q C.vpq C.vqp rfl (G11_vfe hcef) (G11_vge hceg)
      (G11_mem_tri_ef hG q hcef htri) (G11_mem_tri_eg hG q hceg htri) rfl rfl hcfg (G11_vfg hcfg) rfl rfl
  · exact gu6_liftVisit_symm_eq hn hG hT q C.vqp C.vpq rfl (G11_vge hceg) (G11_vfe hcef)
      (G11_mem_tri_eg hG q hceg htri) (G11_mem_tri_ef hG q hcef htri) rfl rfl (G11_Params.gu6_isCrossing_comm hcfg)
      (G11_vgf hcfg) (Subtype.ext (Finset.pair_comm f g)) rfl

/-- **(e) sub-leaf F2′** (copy of `G11_liftVisit_σD` :10793 over `w3e_configOfSw`; `gu6_lift_six` re-stated
without `halt`): the transpositions of the configuration lift to `σ_P` on the parent visits. -/
theorem w3e_liftVisit_σD_sw (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q)
    (hord : crossingParameter (xPair hcef) e (mem_pair_left _ _) <
      crossingParameter (xPair hceg) e (mem_pair_left _ _))
    (sw : Fin 3)
    (hsw : ¬ IsAlternating (if sw = 0 then -strandSign P e f else strandSign P e f)
      (if sw = 1 then -strandSign P e g else strandSign P e g)
      (if sw = 2 then -strandSign P f g else strandSign P f g))
    (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    CV.liftVisit hn hG hT q
        ((w3e_configOfSw hn hG hs hT q hef heg hfg hcef hceg hcfg hX htri hord sw hsw).σD v) =
      G11_σP hcef hceg hcfg (CV.liftVisit hn hG hT q v) := by
  obtain ⟨h_mp, h_pm, h_mq, h_qm, h_pq, h_qp⟩ :=
    w3be_lift_six hn hG hs hT q hef heg hfg hcef hceg hcfg hX htri hord sw hsw
  set C := w3e_configOfSw hn hG hs hT q hef heg hfg hcef hceg hcfg hX htri hord sw hsw with hC
  by_cases hloc : (CV.liftVisit hn hG hT q v).1.val ∈ triangleSupports e f g
  · rcases gu6_local_cases hcef hceg hcfg _ hloc with h | h | h | h | h | h
    · have hv := CV.liftVisit_injective hn hG hT q (h.trans h_mp.symm)
      rw [h, gu6_σP_vef hef heg hcef hceg hcfg, hv, G11_ParamsSw.gu6_σD_apply, G11_ParamsSw.gu6_σ_vmp, h_mq]
    · have hv := CV.liftVisit_injective hn hG hT q (h.trans h_pm.symm)
      rw [h, gu6_σP_vfe hef hfg hcef hceg hcfg, hv, G11_ParamsSw.gu6_σD_apply, G11_ParamsSw.gu6_σ_vpm, h_pq]
    · have hv := CV.liftVisit_injective hn hG hT q (h.trans h_mq.symm)
      rw [h, gu6_σP_veg hef heg hcef hceg hcfg, hv, G11_ParamsSw.gu6_σD_apply, G11_ParamsSw.gu6_σ_vmq, h_mp]
    · have hv := CV.liftVisit_injective hn hG hT q (h.trans h_qm.symm)
      rw [h, gu6_σP_vge heg hfg hcef hceg hcfg, hv, G11_ParamsSw.gu6_σD_apply, G11_ParamsSw.gu6_σ_vqm, h_qp]
    · have hv := CV.liftVisit_injective hn hG hT q (h.trans h_pq.symm)
      rw [h, gu6_σP_vfg hef hfg hcef hceg hcfg, hv, G11_ParamsSw.gu6_σD_apply, G11_ParamsSw.gu6_σ_vpq, h_pm]
    · have hv := CV.liftVisit_injective hn hG hT q (h.trans h_qp.symm)
      rw [h, gu6_σP_vgf heg hfg hcef hceg hcfg, hv, G11_ParamsSw.gu6_σD_apply, G11_ParamsSw.gu6_σ_vqp, h_qm]
  · rw [gu6_σP_of_not_local hcef hceg hcfg _ hloc]
    have hne : ∀ (x : Visit C.X) (w : Visit P),
        CV.liftVisit hn hG hT q ((Shadow.singleVisitEquiv C.comp).symm x) = w →
        w.1.val ∈ triangleSupports e f g → Shadow.singleVisitEquiv C.comp v ≠ x := by
      intro x w hw hwt h
      apply hloc
      rw [← Equiv.symm_apply_apply (Shadow.singleVisitEquiv C.comp) v, h, hw]
      exact hwt
    have hσ := G11_ParamsSw.gu6_σ_of_not_local C _
      (hne _ _ h_mp (by rw [P1.mem_triangleSupports]; exact Or.inl rfl))
      (hne _ _ h_mq (by rw [P1.mem_triangleSupports]; exact Or.inr (Or.inl rfl)))
      (hne _ _ h_pm (by rw [P1.mem_triangleSupports]; exact Or.inl rfl))
      (hne _ _ h_pq (by rw [P1.mem_triangleSupports]; exact Or.inr (Or.inr rfl)))
      (hne _ _ h_qm (by rw [P1.mem_triangleSupports]; exact Or.inr (Or.inl rfl)))
      (hne _ _ h_qp (by rw [P1.mem_triangleSupports]; exact Or.inr (Or.inr rfl)))
    have hfix : C.σD v = v := by
      have h1 : C.σD ((Shadow.singleVisitEquiv C.comp).symm ((Shadow.singleVisitEquiv C.comp) v)) =
          (Shadow.singleVisitEquiv C.comp).symm (C.σ ((Shadow.singleVisitEquiv C.comp) v)) :=
        G11_ParamsSw.gu6_σD_apply C _
      have h2 : (Shadow.singleVisitEquiv C.comp).symm ((Shadow.singleVisitEquiv C.comp) v) = v :=
        Equiv.symm_apply_apply _ _
      rw [h2, hσ, h2] at h1
      exact h1
    rw [hfix]

/-- **(E) helper — the crossing correspondence of the lift**: an occurrence of the lift sits at the crossing
`x` at the double point of the parent crossing `c` iff its parent visit is a visit of `c`
(`liftVisit_fst`, `crossingPoint_liftCrossing`, `Generic.crossingPoint_injective`,
`crossingPoint_injective_of_geometry`). -/
theorem w3be_liftVisit_fst_eq_iff (x : (geoPositiveLift hn hG hT q).Γ.Crossing) (c : Crossing P)
    (hx : (geoPositiveLift hn hG hT q).Γ.crossingPoint x = crossingPoint c)
    (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    (CV.liftVisit hn hG hT q v).1 = c ↔ v.1 = x := by
  rw [CV.liftVisit_fst]
  constructor
  · intro h
    apply (geoPositiveLift hn hG hT q).generic.crossingPoint_injective
    rw [hx, ← h, CV.crossingPoint_liftCrossing]
  · intro h
    apply crossingPoint_injective_of_geometry hG.cg
    rw [CV.crossingPoint_liftCrossing, h, hx]

/-- **(e) sub-leaf F3′ — the record isomorphism `D₁ ≅ D_L.switch x_L`** (the switched `G11_recordIsoData`
:10852): given the switched core's output on `D₀^{sw} = (geoPositiveLift q).switch x` and the twisted key
transport, `Φ := Ψ.symm.trans Λ` (`Λ` the parent-visit identification through `visitTransport`) satisfies
CV:def:record (a)–(d) against the EMPTY-side lift switched at the corresponding crossing `x'` (the crossing
at the double point of the transported parent crossing `c`): (a), (b) as in the accepted proof; (c) the
over bit of a positive lift is the divide sign carried by `hdet`, flipped at `x` and at `x'` alike
(`w3b_overBit_switch_of_visitIso` with the correspondence `(Λ v).1 = x' ↔ v.1 = x`, from
`liftVisit_fst`/`visitTransport` and `hx`, `hx'`); (d) the signs: `+1` everywhere except `−1` at `x`, `x'`
(`switch_sign`).  Route: prove the accepted-shape lemma with the explicit `Φ`-formula exposed (a copy of
:10852–10920 plus one clause), then `w3b_isRecordIsoData_switch` — or prove the switched clauses directly. -/
theorem w3e_recordIsoData_sw (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (hdet : ∀ i j : ZMod n, IsCrossing P {i, j} →
      (0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i) (edge P' j)))
    (hcarr : geoCarrierCrossings hG'.cg T' q' =
      (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q)
    (x : (geoPositiveLift hn hG hT q).Γ.Crossing) (x' : (geoPositiveLift hn hG' hT' q').Γ.Crossing)
    (c : Crossing P) (hx : (geoPositiveLift hn hG hT q).Γ.crossingPoint x = crossingPoint c)
    (hx' : (geoPositiveLift hn hG' hT' q').Γ.crossingPoint x' = crossingPoint (crossingTransport hs c))
    (D₁ : Diagram) (Ψ : (geoPositiveLift hn hG hT q).Γ.Visit ≃ D₁.Γ.Visit)
    (σ : Equiv.Perm (geoPositiveLift hn hG hT q).Γ.Visit)
    (hσ : ∀ v, CV.liftVisit hn hG hT q (σ v) = G11_σP hcef hceg hcfg (CV.liftVisit hn hG hT q v))
    (htw : ∀ v, Ψ ((geoPositiveLift hn hG hT q).twin v) = D₁.twin (Ψ v))
    (hbit : ∀ v, D₁.overBit (Ψ v) = ((geoPositiveLift hn hG hT q).switch x).overBit v)
    (hsgn : ∀ v, D₁.sign (Ψ v).1 = ((geoPositiveLift hn hG hT q).switch x).sign v.1)
    (hcyc : ∀ u v w, D₁.VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔
      (geoPositiveLift hn hG hT q).VisitBetween (σ u) (σ v) (σ w)) :
    ∃ Φ : D₁.Γ.Visit ≃ (geoPositiveLift hn hG' hT' q').Γ.Visit,
      CV.IsRecordIsoData D₁ ((geoPositiveLift hn hG' hT' q').switch x') Φ := by
  have _htri_used := htri
  let ψ : {w : Visit P // w.1 ∈ geoCarrierCrossings hG.cg T q} ≃
      {w : Visit P' // w.1 ∈ geoCarrierCrossings hG'.cg T' q'} :=
    (visitTransport hs).subtypeEquiv fun w => by
      rw [hcarr, visitTransport_crossing, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  let Λ : (geoPositiveLift hn hG hT q).Γ.Visit ≃ (geoPositiveLift hn hG' hT' q').Γ.Visit :=
    (CV.liftVisitEquiv hn hG hT q).trans (ψ.trans (CV.liftVisitEquiv hn hG' hT' q').symm)
  have hΛ : ∀ v, CV.liftVisit hn hG' hT' q' (Λ v) = visitTransport hs (CV.liftVisit hn hG hT q v) := by
    intro v
    show CV.liftVisit hn hG' hT' q'
      ((CV.liftVisitEquiv hn hG' hT' q').symm (ψ (CV.liftVisitEquiv hn hG hT q v))) = _
    rw [CV.liftVisit_symm]
    rfl
  have hΛtw : ∀ v, Λ ((geoPositiveLift hn hG hT q).twin v) = (geoPositiveLift hn hG' hT' q').twin (Λ v) := by
    intro v
    apply CV.liftVisit_injective hn hG' hT' q'
    rw [hΛ, CV.liftVisit_twin, CV.liftVisit_twin, hΛ, visitTransport_visitTwin]
  have hΨtw : ∀ v, Ψ.symm (D₁.twin v) = (geoPositiveLift hn hG hT q).twin (Ψ.symm v) := by
    intro v
    rw [Equiv.symm_apply_eq, htw, Equiv.apply_symm_apply]
  -- the crossing correspondence `x ↦ x'` of `Λ` (both crossings sit at the double point of `c`)
  have hΛx : ∀ v, (Λ v).1 = x' ↔ v.1 = x := by
    intro v
    rw [← w3be_liftVisit_fst_eq_iff hn hG' hT' q' x' (crossingTransport hs c) hx',
      ← w3be_liftVisit_fst_eq_iff hn hG hT q x c hx, hΛ, visitTransport_crossing]
    exact (crossingTransport hs).injective.eq_iff
  -- the unswitched bits (the divide sign, carried by `hdet`) and signs (`+1`) of `Λ`
  have hΛbit : ∀ v, (geoPositiveLift hn hG' hT' q').overBit (Λ v) =
      (geoPositiveLift hn hG hT q).overBit v := by
    intro v
    rw [Bool.eq_iff_iff, CV.overBit_eq_true_iff_parent, CV.overBit_eq_true_iff_parent, hΛ,
      visitTransport_edge, ← visitTransport_visitTwin, visitTransport_edge]
    exact (hdet _ _ (by rw [← visit_crossing_val_eq_pair]; exact (CV.liftVisit hn hG hT q _).1.property)).symm
  have hΛsgn : ∀ v, (geoPositiveLift hn hG' hT' q').sign (Λ v).1 =
      (geoPositiveLift hn hG hT q).sign v.1 := by
    intro v
    rw [geoPositiveLift_sign, geoPositiveLift_sign]
  refine ⟨Ψ.symm.trans Λ,
    { cyclic_order := ?_, double_points := ?_, over_under := ?_, signs := ?_ }⟩
  · intro v w u hb
    change ((geoPositiveLift hn hG' hT' q').switch x').VisitBetween (Λ (Ψ.symm v)) (Λ (Ψ.symm w))
      (Λ (Ψ.symm u))
    have hb' : D₁.VisitBetween (Ψ (Ψ.symm v)) (Ψ (Ψ.symm w)) (Ψ (Ψ.symm u)) := by
      rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [hcyc, CV.visitBetween_iff_key, hσ, hσ, hσ] at hb'
    rw [w3b_visitBetween_switch, CV.visitBetween_iff_key, hΛ, hΛ, hΛ]
    exact (GT_cyc_congr_of_lt
      (G11_twisted_key_lt hG hG' hs hef heg hfg hcef hceg hcfg hX _ _)
      (G11_twisted_key_lt hG hG' hs hef heg hfg hcef hceg hcfg hX _ _)
      (G11_twisted_key_lt hG hG' hs hef heg hfg hcef hceg hcfg hX _ _)).mp hb'
  · refine (CV.carriesDoublePoints_iff (ρ := D₁.record)
      (ρ' := ((geoPositiveLift hn hG' hT' q').switch x').record) (Ψ.symm.trans Λ)).2 fun v => ?_
    change Λ (Ψ.symm (D₁.twin v)) = (geoPositiveLift hn hG' hT' q').twin (Λ (Ψ.symm v))
    rw [hΨtw, hΛtw]
  · refine (CV.carriesOverUnder_iff (ρ := D₁.record)
      (ρ' := ((geoPositiveLift hn hG' hT' q').switch x').record) (Ψ.symm.trans Λ)).2 fun v => ?_
    change ((geoPositiveLift hn hG' hT' q').switch x').overBit (Λ (Ψ.symm v)) = D₁.overBit v
    conv_rhs => rw [← Equiv.apply_symm_apply Ψ v]
    rw [hbit]
    exact w3b_overBit_switch_of_visitIso Λ x x' hΛx hΛbit _
  · intro v
    change ((geoPositiveLift hn hG' hT' q').switch x').sign (Λ (Ψ.symm v)).1 = D₁.sign v.1
    conv_rhs => rw [← Equiv.apply_symm_apply Ψ v]
    rw [hsgn]
    exact w3b_sign_switch_of_visitIso Λ x x' hΛx hΛsgn _


/-- **The row-level assembly (PROVED from the leaf and the sub-leaves): the switched `G11_strong_case`.**
`(D_H)^{x−} = D₀^{sw} →(core) D₁ ≅ (D_L)^{x−}`: for the two lifts across the wall (`hX`, `hdet`, `hcarr`,
`htri` as in `GT_G11_strong`), the switched pair `sw` with the flipped strand-sign triple non-alternating
(on the K3 side: `w3e_trans_sw_of_alt` of `w3e_alt_of_completeLocal`), and the two crossings `x`, `x'` at the
double points of the parent crossing `w3e_swPair sw` and of its transport: `homfly (D_L^{sw}) = homfly (D_H^{sw})`.
The consumer (`esc_MoveData.switch_riii`, `carrierDiagram = geoPositiveLift`) supplies `sw := 0`
(`x = x_ef`) in the main case `hord`, or `sw := 1` after the relabelling `f ↔ g` (`G11_exact_swap`,
`G11_isCrossing_comm`, `G11_triangleCrossings_swap`, `G11_param_ne`), exactly as `GT_G11_strong_proof` does. -/
theorem w3e_strong_case_sw (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (hdet : ∀ i j : ZMod n, IsCrossing P {i, j} →
      (0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i) (edge P' j)))
    (hcarr : geoCarrierCrossings hG'.cg T' q' =
      (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q)
    (hord : crossingParameter (xPair hcef) e (mem_pair_left _ _) <
      crossingParameter (xPair hceg) e (mem_pair_left _ _))
    (sw : Fin 3)
    (hsw : ¬ IsAlternating (if sw = 0 then -strandSign P e f else strandSign P e f)
      (if sw = 1 then -strandSign P e g else strandSign P e g)
      (if sw = 2 then -strandSign P f g else strandSign P f g))
    (x : (geoPositiveLift hn hG hT q).Γ.Crossing) (x' : (geoPositiveLift hn hG' hT' q').Γ.Crossing)
    (hx : (geoPositiveLift hn hG hT q).Γ.crossingPoint x = crossingPoint (w3e_swPair hcef hceg hcfg sw))
    (hx' : (geoPositiveLift hn hG' hT' q').Γ.crossingPoint x' =
      crossingPoint (crossingTransport hs (w3e_swPair hcef hceg hcfg sw))) :
    homfly ((geoPositiveLift hn hG' hT' q').switch x') = homfly ((geoPositiveLift hn hG hT q).switch x) := by
  have hxC : x = (w3e_configOfSw hn hG hs hT q hef heg hfg hcef hceg hcfg hX htri hord sw hsw).xs :=
    (geoPositiveLift hn hG hT q).generic.crossingPoint_injective
      (hx.trans (w3e_xs_point hn hG hs hT q hef heg hfg hcef hceg hcfg hX htri hord sw hsw).symm)
  subst hxC
  obtain ⟨D₁, Ψ, hD₁, hhom, htw, hbit, hsgn, hcyc⟩ :=
    G11_core_sw (w3e_configOfSw hn hG hs hT q hef heg hfg hcef hceg hcfg hX htri hord sw hsw)
  obtain ⟨Φ, hΦ⟩ := w3e_recordIsoData_sw hn hG hG' hs hT hT' q q' hef heg hfg hcef hceg hcfg hX hdet hcarr
    htri _ x' _ hx hx' D₁ Ψ _ (w3e_liftVisit_σD_sw hn hG hs hT q hef heg hfg hcef hceg hcfg hX htri hord sw hsw)
    htw hbit hsgn hcyc
  have h1 : homfly D₁ = homfly ((geoPositiveLift hn hG' hT' q').switch x') :=
    CV.gausscode_polynomial D₁ _ hD₁ rfl (CV.recordIsoOfData hD₁ rfl Φ hΦ)
  exact h1.symm.trans hhom

end W3E

end RIIISw

/-- Row 177 (4) `esc_switch_riii` from the chain `D_H.switch x_H ≃_Reparam M₀ –RIII→ M₁ ≅_record
D_L.switch x_L` (G11's route): only `homfly M₁ = homfly (D_H.switch x_H)` and the record iso
`M₁ ≅ D_L.switch x_L` (G11 Unit F pattern with the switched bit) are consumed. -/
theorem esc_switch_riii_of_chain (D_H D_L M₁ : Diagram) (x_H : D_H.Γ.Crossing) (x_L : D_L.Γ.Crossing)
    (h1 : homfly M₁ = homfly (D_H.switch x_H)) (hc1 : M₁.componentCount = 1)
    (hcL : D_L.componentCount = 1) (hrec : Nonempty (RecordIso M₁.record (D_L.switch x_L).record)) :
    homfly (D_H.switch x_H) = homfly (D_L.switch x_L) := by
  rw [← h1]
  exact CV.gausscode_polynomial M₁ (D_L.switch x_L) hc1 hcL hrec.some

/-! ## 5. Row 177 (6): the two `j = 2` bigon sites on smoothing outputs and the reduced-smoothed-record
lemma (statements with proof sketches; PLAN_FINAL §4.4 (6), §5 Wave 3 "I-177b") -/

section Row177_6

open Smoothing

/-! ### Unit G (`w3bg_`): the corrected `j = 2` bigon sites on smoothing outputs.  The frozen statements
`w3g_bigonData_smooth_arcST/TS` are FALSE as stated (rule 3): `BigonData.hk : j + 3 ≤ k` needs `5 ≤ k` on the
component carrying the cut-start strand, and in the self model that component has only `4` strands when the
smoothed crossing is a kink (`t = s ∓ 2` on one component, one old strand between the two cut points).  The corrected
forms `w3bg_bigonData_smooth_arcST_of_five` / `_arcTS_of_five` add exactly that hypothesis and are PROVED; the
frozen sub-leaves are reduced to it (their remaining `sorry` is the hypothesis `hk5` alone).  Tools: the affine
determinant `det v (· − p)`, the half-plane / segment-union convexity lemmas and the line lemma
`w3bg_line_convexHull` (a line through two generators of a convex hull whose other generators lie strictly on one
side meets the hull only in the segment between them). -/

/-- (G) `det v (· − p)` is affine along a segment. -/
theorem w3bg_det_affine (v p q₁ q₂ : Plane) {a b : ℝ} (hab : a + b = 1) :
    det v (a • q₁ + b • q₂ - p) = a * det v (q₁ - p) + b * det v (q₂ - p) := by
  have hp : p = a • p + b • p := by rw [← add_smul, hab, one_smul]
  conv_lhs => rw [hp]
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul]
  ring

/-- (G) a closed half-plane `{q | 0 ≤ det v (q − p) * c}` is convex. -/
theorem w3bg_convex_halfPlane (v p : Plane) (c : ℝ) : Convex ℝ {q : Plane | 0 ≤ det v (q - p) * c} := by
  intro q₁ h₁ q₂ h₂ a b ha hb hab
  simp only [Set.mem_setOf_eq] at h₁ h₂ ⊢
  rw [w3bg_det_affine v p q₁ q₂ hab, add_mul, mul_assoc, mul_assoc]
  exact add_nonneg (mul_nonneg ha h₁) (mul_nonneg hb h₂)

/-- (G) the convex hull of four points lies in a closed half-plane containing them. -/
theorem w3bg_convexHull_subset_halfPlane (v p : Plane) (c : ℝ) (a b c' d : Plane)
    (ha : 0 ≤ det v (a - p) * c) (hb : 0 ≤ det v (b - p) * c) (hc : 0 ≤ det v (c' - p) * c)
    (hd : 0 ≤ det v (d - p) * c) :
    convexHull ℝ {a, b, c', d} ⊆ {q : Plane | 0 ≤ det v (q - p) * c} := by
  apply convexHull_min _ (w3bg_convex_halfPlane v p c)
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> assumption

/-- (G) a segment on the line `det v (· − p) = 0` together with an open half-plane of that line is convex. -/
theorem w3bg_convex_segment_union_open (v p a b : Plane) (c : ℝ) (ha : det v (a - p) = 0)
    (hb : det v (b - p) = 0) :
    Convex ℝ (segment ℝ a b ∪ {q : Plane | 0 < det v (q - p) * c}) := by
  have key : ∀ q ∈ segment ℝ a b, det v (q - p) = 0 := by
    rintro q ⟨γ, δ, hγ, hδ, hγδ, rfl⟩
    rw [w3bg_det_affine v p a b hγδ, ha, hb]; ring
  intro q₁ h₁ q₂ h₂ α β hα hβ hαβ
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact Or.inl (convex_segment a b h₁ h₂ hα hβ hαβ)
  · rcases hβ.lt_or_eq with hβ' | hβ'
    · right
      show 0 < det v (α • q₁ + β • q₂ - p) * c
      rw [w3bg_det_affine v p _ _ hαβ, key _ h₁, mul_zero, zero_add, mul_assoc]
      exact mul_pos hβ' h₂
    · left
      rw [← hβ', add_zero] at hαβ
      rw [← hβ', zero_smul, add_zero, hαβ, one_smul]
      exact h₁
  · rcases hα.lt_or_eq with hα' | hα'
    · right
      show 0 < det v (α • q₁ + β • q₂ - p) * c
      rw [w3bg_det_affine v p _ _ hαβ, key _ h₂, mul_zero, add_zero, mul_assoc]
      exact mul_pos hα' h₁
    · left
      rw [← hα', zero_add] at hαβ
      rw [← hα', zero_smul, zero_add, hαβ, one_smul]
      exact h₂
  · right
    show 0 < det v (α • q₁ + β • q₂ - p) * c
    rw [w3bg_det_affine v p _ _ hαβ, add_mul, mul_assoc, mul_assoc]
    rcases hα.lt_or_eq with hα' | hα'
    · exact add_pos_of_pos_of_nonneg (mul_pos hα' h₁) (mul_nonneg hβ h₂.le)
    · rw [← hα', zero_add] at hαβ
      rw [← hα', zero_mul, zero_add, hαβ, one_mul]
      exact h₂

/-- (G) **the line lemma**: if `a, b` lie on the line `det v (· − p) = 0` and `c, d` lie strictly on one
side of it (`0 < det v (· − p) * k`), the line meets `conv{a, b, c, d}` only in the segment `[a, b]`. -/
theorem w3bg_line_convexHull_four {v p a b c d q : Plane} {k : ℝ} (ha : det v (a - p) = 0)
    (hb : det v (b - p) = 0) (hc : 0 < det v (c - p) * k) (hd : 0 < det v (d - p) * k)
    (hq : det v (q - p) = 0) (hK : q ∈ convexHull ℝ {a, b, c, d}) : q ∈ segment ℝ a b := by
  have hsub : convexHull ℝ {a, b, c, d} ⊆ segment ℝ a b ∪ {q : Plane | 0 < det v (q - p) * k} := by
    apply convexHull_min _ (w3bg_convex_segment_union_open v p a b k ha hb)
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inl (right_mem_segment ℝ _ _)
    · exact Or.inr hc
    · exact Or.inr hd
  rcases hsub hK with h | h
  · exact h
  · exfalso
    have h' : 0 < det v (q - p) * k := h
    rw [hq, zero_mul] at h'
    exact lt_irrefl _ h'

/-- (G) the strand of `Γ₀` following the strand of an occurring kind carries the successor kind. -/
theorem w3bg_strandOf_succ {D : Diagram} {x : D.Γ.Crossing} {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (κ : StrandKind D x) (hκ : κ.Occurs) (hκ' : κ.succ.Occurs) :
    (⟨(M.strandOf κ hκ).1, (M.strandOf κ hκ).2 + 1⟩ : Γ₀.Strand) = M.strandOf κ.succ hκ' := by
  apply M.kind_injective
  rw [M.kind_succ, M.kind_strandOf, M.kind_strandOf]

/-- (G) `det` is linear in its second argument (scalars). -/
theorem w3bg_det_smul_right (u v : Plane) (c : ℝ) : det u (c • v) = c * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
theorem w3bg_det_self (u : Plane) : det u u = 0 := by simp only [det]; ring
theorem w3bg_det_add_right (u v w : Plane) : det u (v + w) = det u v + det u w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring
theorem w3bg_det_neg_right (u v : Plane) : det u (-v) = - det u v := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
theorem w3bg_det_comm (u v : Plane) : det u v = - det v u := by simp only [det]; ring

/-- (G) the convex hull of a set in a closed half-plane lies in that half-plane. -/
theorem w3bg_convexHull_subset_halfPlane' (v p : Plane) (c : ℝ) (S : Set Plane)
    (hS : ∀ z ∈ S, 0 ≤ det v (z - p) * c) : convexHull ℝ S ⊆ {q : Plane | 0 ≤ det v (q - p) * c} :=
  convexHull_min hS (w3bg_convex_halfPlane v p c)

/-- (G) **the line lemma, general form**: if every generator of `S` lies on the segment `[a, b]` of the line
`det v (· − p) = 0` or strictly on one side of it, the line meets `conv S` only in `[a, b]`. -/
theorem w3bg_line_convexHull {v p a b q : Plane} {k : ℝ} (ha : det v (a - p) = 0) (hb : det v (b - p) = 0)
    (S : Set Plane) (hS : ∀ z ∈ S, z ∈ segment ℝ a b ∨ 0 < det v (z - p) * k)
    (hq : det v (q - p) = 0) (hK : q ∈ convexHull ℝ S) : q ∈ segment ℝ a b := by
  have hsub : convexHull ℝ S ⊆ segment ℝ a b ∪ {q : Plane | 0 < det v (q - p) * k} :=
    convexHull_min hS (w3bg_convex_segment_union_open v p a b k ha hb)
  rcases hsub hK with h | h
  · exact h
  · exfalso
    have h' : 0 < det v (q - p) * k := h
    rw [hq, zero_mul] at h'
    exact lt_irrefl _ h'

/-- (G) `liftStrand` on `s` before the cut is the `cutStartS` strand. -/
theorem w3bg_liftStrand_s (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀)
    (y : D.Γ.Crossing) (hs : sS D x ∈ y.val) (h : D.crossingParam y hs < τs D x) :
    liftStrand D x M y (sS D x) hs = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS := by
  unfold liftStrand
  rw [dif_pos rfl, if_pos h]

/-- (G) `liftStrand` on `s` after the cut is the `cutEndS` strand. -/
theorem w3bg_liftStrand_s' (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀)
    (y : D.Γ.Crossing) (hs : sS D x ∈ y.val) (h : τs D x ≤ D.crossingParam y hs) :
    liftStrand D x M y (sS D x) hs = M.strandOf StrandKind.cutEndS StrandKind.occurs_cutEndS := by
  unfold liftStrand
  rw [dif_pos rfl, if_neg (not_lt.mpr h)]

/-- (G) `liftStrand` on `t` before the cut is the `cutStartT` strand. -/
theorem w3bg_liftStrand_t (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀)
    (y : D.Γ.Crossing) (ht : tS D x ∈ y.val) (h : D.crossingParam y ht < τt D x) :
    liftStrand D x M y (tS D x) ht = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT := by
  unfold liftStrand
  rw [dif_neg (sS_ne_tS D x).symm, dif_pos rfl, if_pos h]

/-- (G) `liftStrand` on `t` after the cut is the `cutEndT` strand. -/
theorem w3bg_liftStrand_t' (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀)
    (y : D.Γ.Crossing) (ht : tS D x ∈ y.val) (h : τt D x ≤ D.crossingParam y ht) :
    liftStrand D x M y (tS D x) ht = M.strandOf StrandKind.cutEndT StrandKind.occurs_cutEndT := by
  unfold liftStrand
  rw [dif_neg (sS_ne_tS D x).symm, dif_pos rfl, if_neg (not_lt.mpr h)]

/-- (G) `liftStrand` on a third strand is the old strand. -/
theorem w3bg_liftStrand_old (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀)
    (y : D.Γ.Crossing) (g : D.Γ.Strand) (hg : g ∈ y.val) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x) :
    liftStrand D x M y g hg = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) := by
  unfold liftStrand
  rw [dif_neg hgs, dif_neg hgt]

/-- (G) the strands of the lift of a crossing `y = {e, f}` are the lifts of `e` and `f`. -/
theorem w3bg_val_liftCrossing (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε) (y : D.Γ.Crossing) (hyx : y ≠ x)
    (e f : D.Γ.Strand) (hef : e ≠ f) (hy : y.val = {e, f}) (he : e ∈ y.val) (hf : f ∈ y.val) :
    (liftCrossing D x M hε y hyx).val = {liftStrand D x M y e he, liftStrand D x M y f hf} := by
  have key : ∀ (e' : D.Γ.Strand) (he' : e' ∈ y.val) (e'' : D.Γ.Strand) (he'' : e'' ∈ y.val), e' = e'' →
      liftStrand D x M y e' he' = liftStrand D x M y e'' he'' := by
    rintro e' he' e'' he'' rfl; rfl
  show ({liftStrand D x M y y.fst y.fst_mem, liftStrand D x M y y.snd y.snd_mem} : Finset Γ₀.Strand) = _
  have h1 := y.fst_mem
  have h2 := y.snd_mem
  rw [hy] at h1 h2
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  have hne : y.snd ≠ y.fst := D.Γ.other_ne y y.fst_mem
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h2.trans h1.symm) hne
  · rw [key _ _ e he h1, key _ _ f hf h2]
  · rw [key _ _ f hf h1, key _ _ e he h2, Finset.pair_comm]
  · exact absurd (h2.trans h1.symm) hne

/-- **(G) the corrected `arcST` site (rule 3): `w3g_bigonData_smooth_arcST` with the missing hypothesis
`hk5 : 5 ≤ k` on the component of `cutStartS`.**  Without it the statement is FALSE: in the self model with
`t = s − 2` on one component (a kink at `x`; `dd = kI − 2`) the component `B` carrying `cutStartS`, `arcST`,
`cutEndT` has `kI − dd + 2 = 4` strands, and `BigonData.hk : j + 3 ≤ k` needs `5` for `j = 2`; every other
hypothesis of the frozen statement is satisfiable there.  Everything else is proved: labels by `kind_succ`,
`hy/hz` by `liftCrossing`, `run_free` by `kind_ne_arc_of_mem`, `no_io` by `origCrossing_ne`, `same_over` by
`orig_overStrand₀`/`toDiagram_underStrand_orig` and the switch at `y₀`, `in_iff/out_iff/s_iff` by the line
lemma `w3bg_line_convexHull` (the strict sides come from the orientation `hys, hzt` and, for `s_iff`, from
the clearance `r₁`), `clear` by the half-planes `det es/et (· − p) · det es et ≥ 0` and `K ⊆ Δ`. -/
theorem w3bg_bigonData_smooth_arcST_of_five (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : D.crossingParam y hsy < τs D x) (hzt : τt D x < D.crossingParam z htz)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hk5 : 5 ≤ (Γ₀.comp (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1).k) :
    ∃ B : BigonData ((toDiagram D x M hε).switch y₀),
      B.j = 2 ∧ B.y = y₀ ∧ B.z = z₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} := by
  -- the four strands
  obtain ⟨uIn, huIn⟩ : ∃ u : Γ₀.Strand, u = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS :=
    ⟨_, rfl⟩
  obtain ⟨uArc, huArc⟩ : ∃ u : Γ₀.Strand, u = M.strandOf StrandKind.arcST StrandKind.occurs_arcST := ⟨_, rfl⟩
  obtain ⟨uOut, huOut⟩ : ∃ u : Γ₀.Strand, u = M.strandOf StrandKind.cutEndT StrandKind.occurs_cutEndT :=
    ⟨_, rfl⟩
  obtain ⟨uG, huG⟩ : ∃ u : Γ₀.Strand, u = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) :=
    ⟨_, rfl⟩
  rw [← huIn] at hk5
  have hkIn : M.kind uIn = StrandKind.cutStartS := by rw [huIn, M.kind_strandOf]
  have hkArc : M.kind uArc = StrandKind.arcST := by rw [huArc, M.kind_strandOf]
  have hkOut : M.kind uOut = StrandKind.cutEndT := by rw [huOut, M.kind_strandOf]
  have hkG : M.kind uG = StrandKind.old g := by rw [huG, M.kind_strandOf]
  -- labels
  have hArc : (⟨uIn.1, uIn.2 + 1⟩ : Γ₀.Strand) = uArc := by
    apply M.kind_injective
    rw [M.kind_succ, hkIn, hkArc]
    rfl
  have hOut : (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) = uOut := by
    apply M.kind_injective
    have h2 : uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k) = (uIn.2 + 1) + 1 := by push_cast; ring
    rw [h2]
    have h3 : M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩ = (M.kind ⟨uIn.1, uIn.2 + 1⟩).succ := M.kind_succ ⟨uIn.1, uIn.2 + 1⟩
    rw [h3, hArc, hkArc, hkOut]
    rfl
  -- the crossings and their lifts
  have hyx : y ≠ x := by rw [← hy₀]; exact origCrossing_ne D x M hε y₀
  have hzx : z ≠ x := by rw [← hz₀]; exact origCrossing_ne D x M hε z₀
  have hgy : g ∈ y.val := by rw [hy]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hgz : g ∈ z.val := by rw [hz]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hlift_y : liftCrossing D x M hε y hyx = y₀ := by
    have key : ∀ (y'' : D.Γ.Crossing) (h : y'' ≠ x), y'' = y →
        liftCrossing D x M hε y'' h = liftCrossing D x M hε y hyx := by
      rintro y'' h rfl; rfl
    exact (key _ _ hy₀).symm.trans (liftCrossing_origCrossing D x M hε y₀)
  have hlift_z : liftCrossing D x M hε z hzx = z₀ := by
    have key : ∀ (z'' : D.Γ.Crossing) (h : z'' ≠ x), z'' = z →
        liftCrossing D x M hε z'' h = liftCrossing D x M hε z hzx := by
      rintro z'' h rfl; rfl
    exact (key _ _ hz₀).symm.trans (liftCrossing_origCrossing D x M hε z₀)
  have hyv : y₀.val = {uIn, uG} := by
    rw [← hlift_y, w3bg_val_liftCrossing D x M hε y hyx (sS D x) g hgs.symm hy hsy hgy,
      w3bg_liftStrand_s D x M y hsy hys, w3bg_liftStrand_old D x M y g hgy hgs hgt, huIn, huG]
  have hzv : z₀.val = {uOut, uG} := by
    rw [← hlift_z, w3bg_val_liftCrossing D x M hε z hzx (tS D x) g hgt.symm hz htz hgz,
      w3bg_liftStrand_t' D x M z htz hzt.le, w3bg_liftStrand_old D x M z g hgz hgs hgt, huOut, huG]
  have huIn_y : uIn ∈ y₀.val := by rw [hyv]; exact Finset.mem_insert_self _ _
  have huG_y : uG ∈ y₀.val := by rw [hyv]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have huOut_z : uOut ∈ z₀.val := by rw [hzv]; exact Finset.mem_insert_self _ _
  have huG_z : uG ∈ z₀.val := by rw [hzv]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hyz₀ : z₀ ≠ y₀ := by
    intro h
    have h1 : z = y := by rw [← hz₀, ← hy₀, h]
    have h2 : sS D x ∈ z.val := by rw [h1]; exact hsy
    rw [hz] at h2
    rcases Finset.mem_insert.mp h2 with h3 | h3
    · exact sS_ne_tS D x h3
    · exact hgs (Finset.mem_singleton.mp h3).symm
  -- points and parameters in `D`
  have hpy : Γ₀.crossingPoint y₀ = D.Γ.crossingPoint y := by
    rw [crossingPoint_origCrossing D x M hε y₀, hy₀]
  have hpz : Γ₀.crossingPoint z₀ = D.Γ.crossingPoint z := by
    rw [crossingPoint_origCrossing D x M hε z₀, hz₀]
  have hYs : D.Γ.crossingPoint y = D.Γ.edgePt (sS D x) (D.crossingParam y hsy) :=
    (D.crossingParam_spec y hsy).2.2
  have hZt : D.Γ.crossingPoint z = D.Γ.edgePt (tS D x) (D.crossingParam z htz) :=
    (D.crossingParam_spec z htz).2.2
  have hYg : D.Γ.crossingPoint y = D.Γ.edgePt g (D.crossingParam y hgy) := (D.crossingParam_spec y hgy).2.2
  have hZg : D.Γ.crossingPoint z = D.Γ.edgePt g (D.crossingParam z hgz) := (D.crossingParam_spec z hgz).2.2
  have hpt_s : pt D x = D.Γ.edgePt (sS D x) (τs D x) := pt_eq_s D x
  have hpt_t : pt D x = D.Γ.edgePt (tS D x) (τt D x) := pt_eq_t D x
  have hYsub : D.Γ.crossingPoint y - pt D x = (D.crossingParam y hsy - τs D x) • es D x := by
    rw [hYs, hpt_s, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul]
  have hZsub : D.Γ.crossingPoint z - pt D x = (D.crossingParam z htz - τt D x) • et D x := by
    rw [hZt, hpt_t, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul]
  have hsm : sMinus D x ε - pt D x = -(ε • es D x) := by rw [sMinus, sub_sub_cancel_left]
  have htp : tPlus D x ε - pt D x = ε • et D x := by rw [tPlus, add_sub_cancel_left]
  have hsm' : sMinus D x ε = D.Γ.edgePt (sS D x) (τs D x - ε) := sMinus_eq_edgePoint D x ε
  have htp' : tPlus D x ε = D.Γ.edgePt (tS D x) (τt D x + ε) := tPlus_eq_edgePoint D x ε
  have hd : det (es D x) (et D x) ≠ 0 := det_es_et_ne_zero D x
  have hdd : 0 < det (es D x) (et D x) * det (es D x) (et D x) := mul_self_pos.mpr hd
  -- clearance: `y`, `z` are farther from `p` than the cut points
  have hεy : ε < τs D x - D.crossingParam y hsy := by
    have h1 := r₁_le_dist_crossingPoint D x hyx
    rw [hYs, hpt_s, D.Γ.dist_edgePt, abs_of_pos (sub_pos.mpr hys)] at h1
    have hes : 0 < ‖es D x‖ := norm_pos_iff.mpr (es_ne_zero D x)
    exact lt_of_mul_lt_mul_right (hε.mul_es_lt.trans_le h1) hes.le
  have hεz : ε < D.crossingParam z htz - τt D x := by
    have h1 := r₁_le_dist_crossingPoint D x hzx
    rw [hZt, hpt_t, D.Γ.dist_edgePt, abs_sub_comm, abs_of_pos (sub_pos.mpr hzt)] at h1
    have het : 0 < ‖et D x‖ := norm_pos_iff.mpr (et_ne_zero D x)
    exact lt_of_mul_lt_mul_right (hε.mul_et_lt.trans_le h1) het.le
  -- transversality of `g` with `s` at `y` and with `t` at `z`
  have hgs_det : det (D.Γ.dir g) (es D x) ≠ 0 := by
    have hspec := D.Γ.crossing_pair_spec y hgy hsy hgs
    exact D.generic.transverse _ _ hspec.1 hspec.2
  have hgt_det : det (D.Γ.dir g) (et D x) ≠ 0 := by
    have hspec := D.Γ.crossing_pair_spec z hgz htz hgt
    exact D.generic.transverse _ _ hspec.1 hspec.2
  -- edge points of the three local strands of `Γ₀`
  have heIn : ∀ θ : ℝ, Γ₀.edgePt uIn θ = pt D x + (θ * (τs D x - ε) - τs D x) • es D x + (0:ℝ) • et D x := by
    intro θ; rw [Γ₀.edgePt_eq, M.tail_eq, M.dir_eq, hkIn]; exact u3_cutStartS_pt D x θ
  have heOut : ∀ θ : ℝ, Γ₀.edgePt uOut θ = pt D x + (0:ℝ) • es D x + (ε + θ * (1 - τt D x - ε)) • et D x := by
    intro θ; rw [Γ₀.edgePt_eq, M.tail_eq, M.dir_eq, hkOut]; exact u3_cutEndT_pt D x θ
  have heG : ∀ θ : ℝ, Γ₀.edgePt uG θ = D.Γ.edgePt g θ := by
    intro θ; rw [Γ₀.edgePt_eq, M.tail_eq, M.dir_eq, hkG]; rfl
  have hIn1 : Γ₀.edgePt uIn 1 = sMinus D x ε := by rw [heIn, sMinus]; module
  have hOut0 : Γ₀.edgePt uOut 0 = tPlus D x ε := by rw [heOut, tPlus]; module
  have hsw : ∀ (w : Γ₀.Crossing) (u : Γ₀.Strand) (hu : u ∈ w.val),
      Γ₀.edgePt u (((toDiagram D x M hε).switch y₀).crossingParam w hu) = Γ₀.crossingPoint w :=
    fun w u hu => (((toDiagram D x M hε).switch y₀).crossingParam_spec w hu).2.2.symm
  have hEty : Γ₀.edgePt uIn (((toDiagram D x M hε).switch y₀).crossingParam y₀ huIn_y) = D.Γ.crossingPoint y := by
    rw [hsw, hpy]
  have hEtz : Γ₀.edgePt uOut (((toDiagram D x M hε).switch y₀).crossingParam z₀ huOut_z) = D.Γ.crossingPoint z := by
    rw [hsw, hpz]
  have hEtsy : Γ₀.edgePt uG (((toDiagram D x M hε).switch y₀).crossingParam y₀ huG_y) = D.Γ.crossingPoint y := by
    rw [hsw, hpy]
  have hEtsz : Γ₀.edgePt uG (((toDiagram D x M hε).switch y₀).crossingParam z₀ huG_z) = D.Γ.crossingPoint z := by
    rw [hsw, hpz]
  have hty1 : ((toDiagram D x M hε).switch y₀).crossingParam y₀ huIn_y ≤ 1 :=
    (((toDiagram D x M hε).switch y₀).crossingParam_spec y₀ huIn_y).2.1
  have htz0 : 0 ≤ ((toDiagram D x M hε).switch y₀).crossingParam z₀ huOut_z :=
    (((toDiagram D x M hε).switch y₀).crossingParam_spec z₀ huOut_z).1
  -- the half-plane data of the line `s`
  have hs_y : det (es D x) (D.Γ.crossingPoint y - pt D x) = 0 := by
    rw [hYsub, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  have hs_sm : det (es D x) (sMinus D x ε - pt D x) = 0 := by
    rw [hsm, w3bg_det_neg_right, w3bg_det_smul_right, w3bg_det_self, mul_zero, neg_zero]
  have hs_tp : 0 < det (es D x) (tPlus D x ε - pt D x) * det (es D x) (et D x) := by
    rw [htp, w3bg_det_smul_right, mul_assoc]; exact mul_pos hε.pos hdd
  have hs_z : 0 < det (es D x) (D.Γ.crossingPoint z - pt D x) * det (es D x) (et D x) := by
    rw [hZsub, w3bg_det_smul_right, mul_assoc]; exact mul_pos (sub_pos.mpr hzt) hdd
  -- the half-plane data of the line `t`
  have ht_y : 0 < det (et D x) (D.Γ.crossingPoint y - pt D x) * det (es D x) (et D x) := by
    rw [hYsub, w3bg_det_smul_right, w3bg_det_comm (et D x) (es D x)]
    have e : (D.crossingParam y hsy - τs D x) * -det (es D x) (et D x) * det (es D x) (et D x) =
        (τs D x - D.crossingParam y hsy) * (det (es D x) (et D x) * det (es D x) (et D x)) := by ring
    rw [e]; exact mul_pos (sub_pos.mpr hys) hdd
  have ht_sm : 0 < det (et D x) (sMinus D x ε - pt D x) * det (es D x) (et D x) := by
    rw [hsm, w3bg_det_neg_right, w3bg_det_smul_right, w3bg_det_comm (et D x) (es D x)]
    have e : -(ε * -det (es D x) (et D x)) * det (es D x) (et D x) =
        ε * (det (es D x) (et D x) * det (es D x) (et D x)) := by ring
    rw [e]; exact mul_pos hε.pos hdd
  have ht_tp : det (et D x) (tPlus D x ε - pt D x) = 0 := by
    rw [htp, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  have ht_z : det (et D x) (D.Γ.crossingPoint z - pt D x) = 0 := by
    rw [hZsub, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  -- the half-plane data of the line `g` (through `y`), sign constant `kg = det eg (p − y)`
  have hg_y : det (D.Γ.dir g) (D.Γ.crossingPoint y - D.Γ.crossingPoint y) = 0 := by
    rw [sub_self]; simp only [det, Prod.fst_zero, Prod.snd_zero, mul_zero, sub_zero]
  have hg_z : det (D.Γ.dir g) (D.Γ.crossingPoint z - D.Γ.crossingPoint y) = 0 := by
    rw [hZg, hYg, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul, w3bg_det_smul_right,
      w3bg_det_self, mul_zero]
  have hkg : det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint y) =
      (τs D x - D.crossingParam y hsy) * det (D.Γ.dir g) (es D x) := by
    rw [← neg_sub, hYsub, w3bg_det_neg_right, w3bg_det_smul_right]; ring
  have hg_sm : 0 < det (D.Γ.dir g) (sMinus D x ε - D.Γ.crossingPoint y) *
      det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint y) := by
    have e1 : sMinus D x ε - D.Γ.crossingPoint y = (τs D x - D.crossingParam y hsy - ε) • es D x := by
      rw [sMinus, pt_eq_s, hYs, D.Γ.edgePt_eq]; module
    rw [e1, hkg, w3bg_det_smul_right]
    have e2 : (τs D x - D.crossingParam y hsy - ε) * det (D.Γ.dir g) (es D x) *
        ((τs D x - D.crossingParam y hsy) * det (D.Γ.dir g) (es D x)) =
        ((τs D x - D.crossingParam y hsy - ε) * (τs D x - D.crossingParam y hsy)) *
          (det (D.Γ.dir g) (es D x) * det (D.Γ.dir g) (es D x)) := by ring
    rw [e2]
    exact mul_pos (mul_pos (by linarith) (sub_pos.mpr hys)) (mul_self_pos.mpr hgs_det)
  have hg_tp : 0 < det (D.Γ.dir g) (tPlus D x ε - D.Γ.crossingPoint y) *
      det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint y) := by
    have e3 : tPlus D x ε - D.Γ.crossingPoint y = ε • et D x + (pt D x - D.Γ.crossingPoint y) := by
      rw [tPlus]; abel
    have e4 : D.Γ.crossingPoint z - D.Γ.crossingPoint y =
        (D.crossingParam z htz - τt D x) • et D x + (pt D x - D.Γ.crossingPoint y) := by
      rw [← hZsub]; abel
    have h0 : (D.crossingParam z htz - τt D x) * det (D.Γ.dir g) (et D x) +
        det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint y) = 0 := by
      rw [← w3bg_det_smul_right, ← w3bg_det_add_right, ← e4]; exact hg_z
    rw [e3, w3bg_det_add_right, w3bg_det_smul_right]
    have hkg' : det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint y) =
        -((D.crossingParam z htz - τt D x) * det (D.Γ.dir g) (et D x)) := by linarith
    rw [hkg']
    have e5 : (ε * det (D.Γ.dir g) (et D x) + -((D.crossingParam z htz - τt D x) * det (D.Γ.dir g) (et D x))) *
        -((D.crossingParam z htz - τt D x) * det (D.Γ.dir g) (et D x)) =
        ((D.crossingParam z htz - τt D x - ε) * (D.crossingParam z htz - τt D x)) *
          (det (D.Γ.dir g) (et D x) * det (D.Γ.dir g) (et D x)) := by ring
    rw [e5]
    exact mul_pos (mul_pos (by linarith) (sub_pos.mpr hzt)) (mul_self_pos.mpr hgt_det)
  -- the generators
  have hgen : ∀ q ∈ ({D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} : Set Plane),
      q = D.Γ.crossingPoint y ∨ q = sMinus D x ε ∨ q = tPlus D x ε ∨ q = D.Γ.crossingPoint z := by
    intro q hq
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hq
  have hmem_y : D.Γ.crossingPoint y ∈
      ({D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} : Set Plane) := by simp
  have hmem_sm : sMinus D x ε ∈
      ({D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} : Set Plane) := by simp
  have hmem_tp : tPlus D x ε ∈
      ({D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} : Set Plane) := by simp
  have hmem_z : D.Γ.crossingPoint z ∈
      ({D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} : Set Plane) := by simp
  -- `K` inside the two closed half-planes at `p` and inside the triangle `Δ = conv{p, y, z}`
  have hKs : convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} ⊆
      {q : Plane | 0 ≤ det (es D x) (q - pt D x) * det (es D x) (et D x)} := by
    apply w3bg_convexHull_subset_halfPlane'
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · rw [hs_y, zero_mul]
    · rw [hs_sm, zero_mul]
    · exact hs_tp.le
    · exact hs_z.le
  have hKt : convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} ⊆
      {q : Plane | 0 ≤ det (et D x) (q - pt D x) * det (es D x) (et D x)} := by
    apply w3bg_convexHull_subset_halfPlane'
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact ht_y.le
    · exact ht_sm.le
    · rw [ht_tp, zero_mul]
    · rw [ht_z, zero_mul]
  have hKΔ : convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} ⊆
      convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z} := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact subset_convexHull ℝ _ (by simp)
    · refine segment_subset_convexHull (𝕜 := ℝ) (x := D.Γ.crossingPoint y) (y := D.Γ.crossingPoint x)
        (by simp) (by simp) ?_
      rw [hsm', hYs, show D.Γ.crossingPoint x = D.Γ.edgePt (sS D x) (τs D x) from hpt_s,
        um7_edgePt_mem_segment_iff D.generic, min_eq_left hys.le, max_eq_right hys.le]
      constructor <;> linarith [hε.pos]
    · refine segment_subset_convexHull (𝕜 := ℝ) (x := D.Γ.crossingPoint x) (y := D.Γ.crossingPoint z)
        (by simp) (by simp) ?_
      rw [htp', hZt, show D.Γ.crossingPoint x = D.Γ.edgePt (tS D x) (τt D x) from hpt_t,
        um7_edgePt_mem_segment_iff D.generic, min_eq_left hzt.le, max_eq_right hzt.le]
      constructor <;> linarith [hε.pos]
    · exact subset_convexHull ℝ _ (by simp)
  -- the three lines through `K`
  have hline_s : ∀ θ : ℝ, det (es D x) (Γ₀.edgePt uIn θ - pt D x) = 0 := by
    intro θ
    rw [heIn, zero_smul, add_zero, add_sub_cancel_left, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  have hline_t : ∀ θ : ℝ, det (et D x) (Γ₀.edgePt uOut θ - pt D x) = 0 := by
    intro θ
    rw [heOut, zero_smul, add_zero, add_sub_cancel_left, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  have hline_g : ∀ θ : ℝ, det (D.Γ.dir g) (Γ₀.edgePt uG θ - D.Γ.crossingPoint y) = 0 := by
    intro θ
    rw [heG, hYg, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul, w3bg_det_smul_right,
      w3bg_det_self, mul_zero]
  have hS_s : ∀ q ∈ ({D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} : Set Plane),
      q ∈ segment ℝ (D.Γ.crossingPoint y) (sMinus D x ε) ∨
        0 < det (es D x) (q - pt D x) * det (es D x) (et D x) := by
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inl (right_mem_segment ℝ _ _)
    · exact Or.inr hs_tp
    · exact Or.inr hs_z
  have hS_t : ∀ q ∈ ({D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} : Set Plane),
      q ∈ segment ℝ (tPlus D x ε) (D.Γ.crossingPoint z) ∨
        0 < det (et D x) (q - pt D x) * det (es D x) (et D x) := by
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact Or.inr ht_y
    · exact Or.inr ht_sm
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inl (right_mem_segment ℝ _ _)
  have hS_g : ∀ q ∈ ({D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} : Set Plane),
      q ∈ segment ℝ (D.Γ.crossingPoint y) (D.Γ.crossingPoint z) ∨
        0 < det (D.Γ.dir g) (q - D.Γ.crossingPoint y) * det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint y) := by
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr hg_sm
    · exact Or.inr hg_tp
    · exact Or.inl (right_mem_segment ℝ _ _)
  have hΓ₀ : Γ₀.Generic := generic D x M hε
  refine ⟨{
    i := uIn.1
    a := uIn.2
    j := 2
    hj := by norm_num
    hk := hk5
    s := uG
    y := y₀
    z := z₀
    hy := hyv
    hz := by
      show z₀.val = {(⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand), uG}
      rw [hOut]; exact hzv
    run_free := ?_
    no_io := ?_
    same_over := ?_
    ty := ((toDiagram D x M hε).switch y₀).crossingParam y₀ huIn_y
    tz := ((toDiagram D x M hε).switch y₀).crossingParam z₀ huOut_z
    tsy := ((toDiagram D x M hε).switch y₀).crossingParam y₀ huG_y
    tsz := ((toDiagram D x M hε).switch y₀).crossingParam z₀ huG_z
    hty := (((toDiagram D x M hε).switch y₀).crossingParam_spec y₀ huIn_y).2.2.symm
    htz := by
      show Γ₀.edgePt (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) _ = Γ₀.crossingPoint z₀
      rw [hOut]; exact hsw z₀ uOut huOut_z
    htsy := (((toDiagram D x M hε).switch y₀).crossingParam_spec y₀ huG_y).2.2.symm
    htsz := (((toDiagram D x M hε).switch y₀).crossingParam_spec z₀ huG_z).2.2.symm
    K := convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z}
    K_convex := convex_convexHull ℝ _
    K_compact := (Set.toFinite _).isCompact_convexHull ℝ
    run_mem := ?_
    in_iff := ?_
    out_iff := ?_
    s_iff := ?_
    clear := ?_ }, rfl, rfl, rfl, huG, huIn, rfl⟩
  · -- run_free: the only run edge is the arc `arcST`, which carries no crossing
    intro m h1 h2 x' hmem
    have hm : m = 1 := by omega
    subst hm
    have hmem' : (⟨uIn.1, uIn.2 + ((1 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) ∈ x'.val := hmem
    rw [Nat.cast_one, hArc] at hmem'
    exact (kind_ne_arc_of_mem D x M hε x' hmem').1 hkArc
  · -- no_io: a crossing of `cutStartS` with `cutEndT` would be a lift of `x`
    intro x' hx'
    have hx'' : uIn ∈ x'.val ∧ (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) ∈ x'.val := hx'
    rw [hOut] at hx''
    obtain ⟨h1, h2⟩ := hx''
    have horIn : M.orig uIn = sS D x := by unfold SpliceModel.orig; rw [hkIn]; rfl
    have horOut : M.orig uOut = tS D x := by unfold SpliceModel.orig; rw [hkOut]; rfl
    have hs' : sS D x ∈ (origCrossing D x M hε x').val := by
      have := orig_mem_origCrossing D x M hε h1; rwa [horIn] at this
    have ht' : tS D x ∈ (origCrossing D x M hε x').val := by
      have := orig_mem_origCrossing D x M hε h2; rwa [horOut] at this
    apply origCrossing_ne D x M hε x'
    apply Subtype.ext
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      rw [D.mem_iff] at he
      rcases he with rfl | rfl
      · exact hs'
      · exact ht'
    · rw [D.Γ.crossing_card_two, D.Γ.crossing_card_two]
  · -- same_over: the switch at `y₀` and `hover`
    have hov_y : ((toDiagram D x M hε).switch y₀).overStrand y₀ = (toDiagram D x M hε).underStrand y₀ :=
      (toDiagram D x M hε).switch_overStrand_self y₀
    have hov_z : ((toDiagram D x M hε).switch y₀).overStrand z₀ = (toDiagram D x M hε).overStrand z₀ :=
      (toDiagram D x M hε).switch_overStrand_of_ne hyz₀
    have hor_uy : M.orig ((toDiagram D x M hε).underStrand y₀) = D.underStrand y := by
      have h := toDiagram_underStrand_orig D x M hε y₀; rwa [hy₀] at h
    have hor_oz : M.orig ((toDiagram D x M hε).overStrand z₀) = D.overStrand z := by
      have h := orig_overStrand₀ D x M hε z₀; rwa [hz₀] at h
    have horG : M.orig uG = g := by unfold SpliceModel.orig; rw [hkG]; rfl
    have hA : (toDiagram D x M hε).underStrand y₀ = uG ↔ D.underStrand y = g := by
      constructor
      · intro h; rw [← hor_uy, h, horG]
      · intro h
        exact orig_injOn_crossing D x M hε y₀ ((toDiagram D x M hε).under_mem y₀) huG_y
          (by rw [hor_uy, horG, h])
    have hB : (toDiagram D x M hε).overStrand z₀ = uG ↔ D.overStrand z = g := by
      constructor
      · intro h; rw [← hor_oz, h, horG]
      · intro h
        exact orig_injOn_crossing D x M hε z₀ ((toDiagram D x M hε).over_mem z₀) huG_z
          (by rw [hor_oz, horG, h])
    have hC : D.underStrand y = g ↔ D.overStrand y ≠ g := by
      constructor
      · intro h h'; exact D.under_ne_over y (h.trans h'.symm)
      · intro h
        have hg' := hgy
        rw [D.mem_iff] at hg'
        rcases hg' with hg' | hg'
        · exact absurd hg'.symm h
        · exact hg'.symm
    rw [hov_y, hov_z]
    by_cases hz' : D.overStrand z = g
    · left
      exact ⟨hA.mpr (hC.mpr (fun h => hover.mp h hz')), hB.mpr hz'⟩
    · right
      exact ⟨fun h => (hC.mp (hA.mp h)) (hover.mpr hz'), fun h => hz' (hB.mp h)⟩
  · -- run_mem: the run vertices are `s⁻` and `t⁺`
    intro m h1 h2
    have hm : m = 1 ∨ m = 2 := by omega
    rcases hm with rfl | rfl
    · show Γ₀.tail ⟨uIn.1, uIn.2 + ((1 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ ∈ _
      rw [Nat.cast_one, hArc, M.tail_eq, hkArc]
      exact subset_convexHull ℝ _ hmem_sm
    · show Γ₀.tail ⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ ∈ _
      rw [hOut, M.tail_eq, hkOut]
      exact subset_convexHull ℝ _ hmem_tp
  · -- in_iff: `cutStartS ∩ K = [y, s⁻]`
    intro t h0 h1
    constructor
    · intro hmem
      have hseg := w3bg_line_convexHull hs_y hs_sm _ hS_s (hline_s t) hmem
      rw [← hEty, ← hIn1, um7_edgePt_mem_segment_iff hΓ₀, min_eq_left hty1] at hseg
      exact hseg.1
    · intro hle
      have hseg : Γ₀.edgePt uIn t ∈ segment ℝ
          (Γ₀.edgePt uIn (((toDiagram D x M hε).switch y₀).crossingParam y₀ huIn_y)) (Γ₀.edgePt uIn 1) := by
        rw [um7_edgePt_mem_segment_iff hΓ₀, min_eq_left hty1, max_eq_right hty1]
        exact ⟨hle, h1⟩
      rw [hEty, hIn1] at hseg
      exact segment_subset_convexHull hmem_y hmem_sm hseg
  · -- out_iff: `cutEndT ∩ K = [t⁺, z]`
    intro t h0 h1
    show Γ₀.edgePt (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) t ∈
      convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} ↔
      t ≤ ((toDiagram D x M hε).switch y₀).crossingParam z₀ huOut_z
    rw [hOut]
    constructor
    · intro hmem
      have hseg := w3bg_line_convexHull ht_tp ht_z _ hS_t (hline_t t) hmem
      rw [← hEtz, ← hOut0, um7_edgePt_mem_segment_iff hΓ₀, max_eq_right htz0] at hseg
      exact hseg.2
    · intro hle
      have hseg : Γ₀.edgePt uOut t ∈ segment ℝ (Γ₀.edgePt uOut 0)
          (Γ₀.edgePt uOut (((toDiagram D x M hε).switch y₀).crossingParam z₀ huOut_z)) := by
        rw [um7_edgePt_mem_segment_iff hΓ₀, min_eq_left htz0, max_eq_right htz0]
        exact ⟨h0, hle⟩
      rw [hEtz, hOut0] at hseg
      exact segment_subset_convexHull hmem_tp hmem_z hseg
  · -- s_iff: `g ∩ K = [y, z]`
    intro t h0 h1
    constructor
    · intro hmem
      have hseg := w3bg_line_convexHull hg_y hg_z _ hS_g (hline_g t) hmem
      rwa [← hEtsy, ← hEtsz, um7_edgePt_mem_segment_iff hΓ₀] at hseg
    · intro hbetween
      have hseg : Γ₀.edgePt uG t ∈ segment ℝ
          (Γ₀.edgePt uG (((toDiagram D x M hε).switch y₀).crossingParam y₀ huG_y))
          (Γ₀.edgePt uG (((toDiagram D x M hε).switch y₀).crossingParam z₀ huG_z)) := by
        rwa [um7_edgePt_mem_segment_iff hΓ₀]
      rw [hEtsy, hEtsz] at hseg
      exact segment_subset_convexHull hmem_y hmem_z hseg
  · -- clear: every other strand of `Γ₀` misses `K`
    intro u hu1 hu2 hu3 hrun
    have hu2' : u ≠ (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) := hu2
    rw [hOut] at hu2'
    have hu4 : u ≠ uArc := by
      have h := hrun 1 le_rfl one_lt_two
      have h' : u ≠ (⟨uIn.1, uIn.2 + ((1 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) := h
      rwa [Nat.cast_one, hArc] at h'
    rw [Set.disjoint_left]
    intro q hqu hqK
    have hqu' : q ∈ (M.kind u).seg ε := (M.seg_eq u).subset hqu
    obtain ⟨κ, hκ⟩ : ∃ κ, M.kind u = κ := ⟨_, rfl⟩
    have hocc : κ.Occurs := hκ ▸ M.kind_occurs u
    have hu_eq : u = M.strandOf κ hocc := by subst hκ; exact (M.strandOf_kind u).symm
    rw [hκ] at hqu'
    cases κ with
    | old e =>
      have hocc' := (u3_occurs_old_iff D x).mp hocc
      have heg : e ≠ g := by
        rintro rfl
        exact hu3 (hu_eq.trans huG.symm)
      have hsub : StrandKind.seg ε (StrandKind.old e) ⊆ D.Γ.seg e :=
        StrandKind.seg_subset_seg_orig ε hε _ (fun h => by cases h) (fun h => by cases h)
      exact Set.disjoint_left.mp (clear e hocc'.1 hocc'.2 heg) (hsub hqu') (hKΔ hqK)
    | cutStartS => exact hu1 (hu_eq.trans huIn.symm)
    | cutEndS =>
      obtain ⟨θ, h0, h1, rfl⟩ := hqu'
      have hq_eq : StrandKind.tail ε (StrandKind.cutEndS : StrandKind D x) +
          θ • StrandKind.dir ε (StrandKind.cutEndS : StrandKind D x) =
          D.Γ.edgePt (sS D x) (τs D x + (ε + θ * (1 - τs D x - ε))) := by
        rw [u3_cutEndS_pt D x θ, D.Γ.edgePt_eq, pt_eq_s]; module
      have hline : det (es D x) (D.Γ.edgePt (sS D x) (τs D x + (ε + θ * (1 - τs D x - ε))) - pt D x) = 0 := by
        rw [hpt_s, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul, w3bg_det_smul_right,
          w3bg_det_self, mul_zero]
      rw [hq_eq] at hqK
      have hseg := w3bg_line_convexHull hs_y hs_sm _ hS_s hline hqK
      rw [hYs, hsm', um7_edgePt_mem_segment_iff D.generic, max_eq_right (by linarith)] at hseg
      have hc : 0 ≤ θ * (1 - τs D x - ε) := mul_nonneg h0 (by linarith [hε.lt_one_sub_τs])
      linarith [hseg.2, hε.pos]
    | cutStartT =>
      obtain ⟨θ, h0, h1, rfl⟩ := hqu'
      have hq_eq : StrandKind.tail ε (StrandKind.cutStartT : StrandKind D x) +
          θ • StrandKind.dir ε (StrandKind.cutStartT : StrandKind D x) =
          D.Γ.edgePt (tS D x) (τt D x + (θ * (τt D x - ε) - τt D x)) := by
        rw [u3_cutStartT_pt D x θ, D.Γ.edgePt_eq, pt_eq_t]; module
      have hline : det (et D x) (D.Γ.edgePt (tS D x) (τt D x + (θ * (τt D x - ε) - τt D x)) - pt D x) = 0 := by
        rw [hpt_t, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul, w3bg_det_smul_right,
          w3bg_det_self, mul_zero]
      rw [hq_eq] at hqK
      have hseg := w3bg_line_convexHull ht_tp ht_z _ hS_t hline hqK
      rw [htp', hZt, um7_edgePt_mem_segment_iff D.generic] at hseg
      have hc : θ * (τt D x - ε) ≤ τt D x - ε := mul_le_of_le_one_left (by linarith [hε.lt_τt]) h1
      rcases min_le_iff.mp hseg.1 with h | h <;> linarith [hε.pos]
    | cutEndT => exact hu2' (hu_eq.trans huOut.symm)
    | arcST => exact hu4 (hu_eq.trans huArc.symm)
    | arcTS =>
      obtain ⟨θ, h0, h1, rfl⟩ := hqu'
      have hq1 : StrandKind.tail ε (StrandKind.arcTS : StrandKind D x) +
          θ • StrandKind.dir ε (StrandKind.arcTS : StrandKind D x) - pt D x =
          (θ * ε) • es D x + ((θ - 1) * ε) • et D x := by
        rw [u3_arcTS_pt D x θ]; abel
      have hA := hKs hqK
      have hB := hKt hqK
      simp only [Set.mem_setOf_eq] at hA hB
      rw [hq1, w3bg_det_add_right, w3bg_det_smul_right, w3bg_det_smul_right, w3bg_det_self] at hA hB
      rw [w3bg_det_comm (et D x) (es D x)] at hB
      have hP : 0 < ε * (det (es D x) (et D x) * det (es D x) (et D x)) := mul_pos hε.pos hdd
      have eA : (θ * ε * 0 + (θ - 1) * ε * det (es D x) (et D x)) * det (es D x) (et D x) =
          (θ - 1) * (ε * (det (es D x) (et D x) * det (es D x) (et D x))) := by ring
      have eB : (θ * ε * -det (es D x) (et D x) + (θ - 1) * ε * 0) * det (es D x) (et D x) =
          -θ * (ε * (det (es D x) (et D x) * det (es D x) (et D x))) := by ring
      rw [eA] at hA
      rw [eB] at hB
      nlinarith [hA, hB, hP]

/-- **(G) the corrected `arcTS` site (rule 3): `w3g_bigonData_smooth_arcTS` with the missing hypothesis
`hk5 : 5 ≤ k` on the component of `cutStartT`** (the same kink counterexample as for `arcST`, with `s ↔ t`:
component `A` has `dd + 2 = 4` strands when `dd = 2`).  The proof is `w3bg_bigonData_smooth_arcST_of_five` with the
roles `s ↔ t`, `y ↔ z` (entering crossing `z` on `cutStartT`, exiting crossing `y` on `cutEndS`, `B.y = z₀`,
`B.z = y₀`); the switch stays at `y₀ = B.z`. -/
theorem w3bg_bigonData_smooth_arcTS_of_five (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : τs D x < D.crossingParam y hsy) (hzt : D.crossingParam z htz < τt D x)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hk5 : 5 ≤ (Γ₀.comp (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1).k) :
    ∃ B : BigonData ((toDiagram D x M hε).switch y₀),
      B.j = 2 ∧ B.y = z₀ ∧ B.z = y₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} := by
  -- the four strands
  obtain ⟨uIn, huIn⟩ : ∃ u : Γ₀.Strand, u = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT :=
    ⟨_, rfl⟩
  obtain ⟨uArc, huArc⟩ : ∃ u : Γ₀.Strand, u = M.strandOf StrandKind.arcTS StrandKind.occurs_arcTS := ⟨_, rfl⟩
  obtain ⟨uOut, huOut⟩ : ∃ u : Γ₀.Strand, u = M.strandOf StrandKind.cutEndS StrandKind.occurs_cutEndS :=
    ⟨_, rfl⟩
  obtain ⟨uG, huG⟩ : ∃ u : Γ₀.Strand, u = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) :=
    ⟨_, rfl⟩
  rw [← huIn] at hk5
  have hkIn : M.kind uIn = StrandKind.cutStartT := by rw [huIn, M.kind_strandOf]
  have hkArc : M.kind uArc = StrandKind.arcTS := by rw [huArc, M.kind_strandOf]
  have hkOut : M.kind uOut = StrandKind.cutEndS := by rw [huOut, M.kind_strandOf]
  have hkG : M.kind uG = StrandKind.old g := by rw [huG, M.kind_strandOf]
  -- labels
  have hArc : (⟨uIn.1, uIn.2 + 1⟩ : Γ₀.Strand) = uArc := by
    apply M.kind_injective
    rw [M.kind_succ, hkIn, hkArc]
    rfl
  have hOut : (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) = uOut := by
    apply M.kind_injective
    have h2 : uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k) = (uIn.2 + 1) + 1 := by push_cast; ring
    rw [h2]
    have h3 : M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩ = (M.kind ⟨uIn.1, uIn.2 + 1⟩).succ := M.kind_succ ⟨uIn.1, uIn.2 + 1⟩
    rw [h3, hArc, hkArc, hkOut]
    rfl
  -- the crossings and their lifts
  have hzx : z ≠ x := by rw [← hz₀]; exact origCrossing_ne D x M hε z₀
  have hyx : y ≠ x := by rw [← hy₀]; exact origCrossing_ne D x M hε y₀
  have hgz : g ∈ z.val := by rw [hz]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hgy : g ∈ y.val := by rw [hy]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hlift_z : liftCrossing D x M hε z hzx = z₀ := by
    have key : ∀ (y'' : D.Γ.Crossing) (h : y'' ≠ x), y'' = z →
        liftCrossing D x M hε y'' h = liftCrossing D x M hε z hzx := by
      rintro y'' h rfl; rfl
    exact (key _ _ hz₀).symm.trans (liftCrossing_origCrossing D x M hε z₀)
  have hlift_y : liftCrossing D x M hε y hyx = y₀ := by
    have key : ∀ (z'' : D.Γ.Crossing) (h : z'' ≠ x), z'' = y →
        liftCrossing D x M hε z'' h = liftCrossing D x M hε y hyx := by
      rintro z'' h rfl; rfl
    exact (key _ _ hy₀).symm.trans (liftCrossing_origCrossing D x M hε y₀)
  have hzv : z₀.val = {uIn, uG} := by
    rw [← hlift_z, w3bg_val_liftCrossing D x M hε z hzx (tS D x) g hgt.symm hz htz hgz,
      w3bg_liftStrand_t D x M z htz hzt, w3bg_liftStrand_old D x M z g hgz hgs hgt, huIn, huG]
  have hyv : y₀.val = {uOut, uG} := by
    rw [← hlift_y, w3bg_val_liftCrossing D x M hε y hyx (sS D x) g hgs.symm hy hsy hgy,
      w3bg_liftStrand_s' D x M y hsy hys.le, w3bg_liftStrand_old D x M y g hgy hgs hgt, huOut, huG]
  have huIn_y : uIn ∈ z₀.val := by rw [hzv]; exact Finset.mem_insert_self _ _
  have huG_y : uG ∈ z₀.val := by rw [hzv]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have huOut_z : uOut ∈ y₀.val := by rw [hyv]; exact Finset.mem_insert_self _ _
  have huG_z : uG ∈ y₀.val := by rw [hyv]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hyz₀ : y₀ ≠ z₀ := by
    intro h
    have h1 : y = z := by rw [← hy₀, ← hz₀, h]
    have h2 : tS D x ∈ y.val := by rw [h1]; exact htz
    rw [hy] at h2
    rcases Finset.mem_insert.mp h2 with h3 | h3
    · exact sS_ne_tS D x h3.symm
    · exact hgt (Finset.mem_singleton.mp h3).symm
  -- points and parameters in `D`
  have hpz : Γ₀.crossingPoint z₀ = D.Γ.crossingPoint z := by
    rw [crossingPoint_origCrossing D x M hε z₀, hz₀]
  have hpy : Γ₀.crossingPoint y₀ = D.Γ.crossingPoint y := by
    rw [crossingPoint_origCrossing D x M hε y₀, hy₀]
  have hZt : D.Γ.crossingPoint z = D.Γ.edgePt (tS D x) (D.crossingParam z htz) :=
    (D.crossingParam_spec z htz).2.2
  have hYs : D.Γ.crossingPoint y = D.Γ.edgePt (sS D x) (D.crossingParam y hsy) :=
    (D.crossingParam_spec y hsy).2.2
  have hZg : D.Γ.crossingPoint z = D.Γ.edgePt g (D.crossingParam z hgz) := (D.crossingParam_spec z hgz).2.2
  have hYg : D.Γ.crossingPoint y = D.Γ.edgePt g (D.crossingParam y hgy) := (D.crossingParam_spec y hgy).2.2
  have hpt_t : pt D x = D.Γ.edgePt (tS D x) (τt D x) := pt_eq_t D x
  have hpt_s : pt D x = D.Γ.edgePt (sS D x) (τs D x) := pt_eq_s D x
  have hZsub : D.Γ.crossingPoint z - pt D x = (D.crossingParam z htz - τt D x) • et D x := by
    rw [hZt, hpt_t, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul]
  have hYsub : D.Γ.crossingPoint y - pt D x = (D.crossingParam y hsy - τs D x) • es D x := by
    rw [hYs, hpt_s, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul]
  have htp : tMinus D x ε - pt D x = -(ε • et D x) := by rw [tMinus, sub_sub_cancel_left]
  have hsm : sPlus D x ε - pt D x = ε • es D x := by rw [sPlus, add_sub_cancel_left]
  have htp' : tMinus D x ε = D.Γ.edgePt (tS D x) (τt D x - ε) := tMinus_eq_edgePoint D x ε
  have hsm' : sPlus D x ε = D.Γ.edgePt (sS D x) (τs D x + ε) := sPlus_eq_edgePoint D x ε
  have hd : det (et D x) (es D x) ≠ 0 := by rw [w3bg_det_comm]; exact neg_ne_zero.mpr (det_es_et_ne_zero D x)
  have hdd : 0 < det (et D x) (es D x) * det (et D x) (es D x) := mul_self_pos.mpr hd
  -- clearance: `z`, `y` are farther from `p` than the cut points
  have hεz : ε < τt D x - D.crossingParam z htz := by
    have h1 := r₁_le_dist_crossingPoint D x hzx
    rw [hZt, hpt_t, D.Γ.dist_edgePt, abs_of_pos (sub_pos.mpr hzt)] at h1
    have hes : 0 < ‖et D x‖ := norm_pos_iff.mpr (et_ne_zero D x)
    exact lt_of_mul_lt_mul_right (hε.mul_et_lt.trans_le h1) hes.le
  have hεy : ε < D.crossingParam y hsy - τs D x := by
    have h1 := r₁_le_dist_crossingPoint D x hyx
    rw [hYs, hpt_s, D.Γ.dist_edgePt, abs_sub_comm, abs_of_pos (sub_pos.mpr hys)] at h1
    have het : 0 < ‖es D x‖ := norm_pos_iff.mpr (es_ne_zero D x)
    exact lt_of_mul_lt_mul_right (hε.mul_es_lt.trans_le h1) het.le
  -- transversality of `g` with `s` at `z` and with `t` at `y`
  have hgt_det : det (D.Γ.dir g) (et D x) ≠ 0 := by
    have hspec := D.Γ.crossing_pair_spec z hgz htz hgt
    exact D.generic.transverse _ _ hspec.1 hspec.2
  have hgs_det : det (D.Γ.dir g) (es D x) ≠ 0 := by
    have hspec := D.Γ.crossing_pair_spec y hgy hsy hgs
    exact D.generic.transverse _ _ hspec.1 hspec.2
  -- edge points of the three local strands of `Γ₀`
  have heOut : ∀ θ : ℝ, Γ₀.edgePt uIn θ = pt D x + (0:ℝ) • es D x + (θ * (τt D x - ε) - τt D x) • et D x := by
    intro θ; rw [Γ₀.edgePt_eq, M.tail_eq, M.dir_eq, hkIn]; exact u3_cutStartT_pt D x θ
  have heIn : ∀ θ : ℝ, Γ₀.edgePt uOut θ = pt D x + (ε + θ * (1 - τs D x - ε)) • es D x + (0:ℝ) • et D x := by
    intro θ; rw [Γ₀.edgePt_eq, M.tail_eq, M.dir_eq, hkOut]; exact u3_cutEndS_pt D x θ
  have heG : ∀ θ : ℝ, Γ₀.edgePt uG θ = D.Γ.edgePt g θ := by
    intro θ; rw [Γ₀.edgePt_eq, M.tail_eq, M.dir_eq, hkG]; rfl
  have hOut0 : Γ₀.edgePt uIn 1 = tMinus D x ε := by rw [heOut, tMinus]; module
  have hIn1 : Γ₀.edgePt uOut 0 = sPlus D x ε := by rw [heIn, sPlus]; module
  have hsw : ∀ (w : Γ₀.Crossing) (u : Γ₀.Strand) (hu : u ∈ w.val),
      Γ₀.edgePt u (((toDiagram D x M hε).switch y₀).crossingParam w hu) = Γ₀.crossingPoint w :=
    fun w u hu => (((toDiagram D x M hε).switch y₀).crossingParam_spec w hu).2.2.symm
  have hEtz : Γ₀.edgePt uIn (((toDiagram D x M hε).switch y₀).crossingParam z₀ huIn_y) = D.Γ.crossingPoint z := by
    rw [hsw, hpz]
  have hEty : Γ₀.edgePt uOut (((toDiagram D x M hε).switch y₀).crossingParam y₀ huOut_z) = D.Γ.crossingPoint y := by
    rw [hsw, hpy]
  have hEtsz : Γ₀.edgePt uG (((toDiagram D x M hε).switch y₀).crossingParam z₀ huG_y) = D.Γ.crossingPoint z := by
    rw [hsw, hpz]
  have hEtsy : Γ₀.edgePt uG (((toDiagram D x M hε).switch y₀).crossingParam y₀ huG_z) = D.Γ.crossingPoint y := by
    rw [hsw, hpy]
  have htz0 : ((toDiagram D x M hε).switch y₀).crossingParam z₀ huIn_y ≤ 1 :=
    (((toDiagram D x M hε).switch y₀).crossingParam_spec z₀ huIn_y).2.1
  have hty1 : 0 ≤ ((toDiagram D x M hε).switch y₀).crossingParam y₀ huOut_z :=
    (((toDiagram D x M hε).switch y₀).crossingParam_spec y₀ huOut_z).1
  -- the half-plane data of the line `s`
  have ht_tp : det (et D x) (D.Γ.crossingPoint z - pt D x) = 0 := by
    rw [hZsub, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  have ht_z : det (et D x) (tMinus D x ε - pt D x) = 0 := by
    rw [htp, w3bg_det_neg_right, w3bg_det_smul_right, w3bg_det_self, mul_zero, neg_zero]
  have ht_y : 0 < det (et D x) (sPlus D x ε - pt D x) * det (et D x) (es D x) := by
    rw [hsm, w3bg_det_smul_right, mul_assoc]; exact mul_pos hε.pos hdd
  have ht_sm : 0 < det (et D x) (D.Γ.crossingPoint y - pt D x) * det (et D x) (es D x) := by
    rw [hYsub, w3bg_det_smul_right, mul_assoc]; exact mul_pos (sub_pos.mpr hys) hdd
  -- the half-plane data of the line `t`
  have hs_tp : 0 < det (es D x) (D.Γ.crossingPoint z - pt D x) * det (et D x) (es D x) := by
    rw [hZsub, w3bg_det_smul_right, w3bg_det_comm (es D x) (et D x)]
    have e : (D.crossingParam z htz - τt D x) * -det (et D x) (es D x) * det (et D x) (es D x) =
        (τt D x - D.crossingParam z htz) * (det (et D x) (es D x) * det (et D x) (es D x)) := by ring
    rw [e]; exact mul_pos (sub_pos.mpr hzt) hdd
  have hs_z : 0 < det (es D x) (tMinus D x ε - pt D x) * det (et D x) (es D x) := by
    rw [htp, w3bg_det_neg_right, w3bg_det_smul_right, w3bg_det_comm (es D x) (et D x)]
    have e : -(ε * -det (et D x) (es D x)) * det (et D x) (es D x) =
        ε * (det (et D x) (es D x) * det (et D x) (es D x)) := by ring
    rw [e]; exact mul_pos hε.pos hdd
  have hs_y : det (es D x) (sPlus D x ε - pt D x) = 0 := by
    rw [hsm, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  have hs_sm : det (es D x) (D.Γ.crossingPoint y - pt D x) = 0 := by
    rw [hYsub, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  -- the half-plane data of the line `g` (through `z`), sign constant `kg = det eg (p − z)`
  have hg_y : det (D.Γ.dir g) (D.Γ.crossingPoint z - D.Γ.crossingPoint z) = 0 := by
    rw [sub_self]; simp only [det, Prod.fst_zero, Prod.snd_zero, mul_zero, sub_zero]
  have hg_z : det (D.Γ.dir g) (D.Γ.crossingPoint y - D.Γ.crossingPoint z) = 0 := by
    rw [hYg, hZg, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul, w3bg_det_smul_right,
      w3bg_det_self, mul_zero]
  have hkg : det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint z) =
      (τt D x - D.crossingParam z htz) * det (D.Γ.dir g) (et D x) := by
    rw [← neg_sub, hZsub, w3bg_det_neg_right, w3bg_det_smul_right]; ring
  have hg_sm : 0 < det (D.Γ.dir g) (tMinus D x ε - D.Γ.crossingPoint z) *
      det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint z) := by
    have e1 : tMinus D x ε - D.Γ.crossingPoint z = (τt D x - D.crossingParam z htz - ε) • et D x := by
      rw [tMinus, pt_eq_t, hZt, D.Γ.edgePt_eq]; module
    rw [e1, hkg, w3bg_det_smul_right]
    have e2 : (τt D x - D.crossingParam z htz - ε) * det (D.Γ.dir g) (et D x) *
        ((τt D x - D.crossingParam z htz) * det (D.Γ.dir g) (et D x)) =
        ((τt D x - D.crossingParam z htz - ε) * (τt D x - D.crossingParam z htz)) *
          (det (D.Γ.dir g) (et D x) * det (D.Γ.dir g) (et D x)) := by ring
    rw [e2]
    exact mul_pos (mul_pos (by linarith) (sub_pos.mpr hzt)) (mul_self_pos.mpr hgt_det)
  have hg_tp : 0 < det (D.Γ.dir g) (sPlus D x ε - D.Γ.crossingPoint z) *
      det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint z) := by
    have e3 : sPlus D x ε - D.Γ.crossingPoint z = ε • es D x + (pt D x - D.Γ.crossingPoint z) := by
      rw [sPlus]; abel
    have e4 : D.Γ.crossingPoint y - D.Γ.crossingPoint z =
        (D.crossingParam y hsy - τs D x) • es D x + (pt D x - D.Γ.crossingPoint z) := by
      rw [← hYsub]; abel
    have h0 : (D.crossingParam y hsy - τs D x) * det (D.Γ.dir g) (es D x) +
        det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint z) = 0 := by
      rw [← w3bg_det_smul_right, ← w3bg_det_add_right, ← e4]; exact hg_z
    rw [e3, w3bg_det_add_right, w3bg_det_smul_right]
    have hkg' : det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint z) =
        -((D.crossingParam y hsy - τs D x) * det (D.Γ.dir g) (es D x)) := by linarith
    rw [hkg']
    have e5 : (ε * det (D.Γ.dir g) (es D x) + -((D.crossingParam y hsy - τs D x) * det (D.Γ.dir g) (es D x))) *
        -((D.crossingParam y hsy - τs D x) * det (D.Γ.dir g) (es D x)) =
        ((D.crossingParam y hsy - τs D x - ε) * (D.crossingParam y hsy - τs D x)) *
          (det (D.Γ.dir g) (es D x) * det (D.Γ.dir g) (es D x)) := by ring
    rw [e5]
    exact mul_pos (mul_pos (by linarith) (sub_pos.mpr hys)) (mul_self_pos.mpr hgs_det)
  -- the generators
  have hgen : ∀ q ∈ ({D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} : Set Plane),
      q = D.Γ.crossingPoint z ∨ q = tMinus D x ε ∨ q = sPlus D x ε ∨ q = D.Γ.crossingPoint y := by
    intro q hq
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hq
  have hmem_z : D.Γ.crossingPoint z ∈
      ({D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} : Set Plane) := by simp
  have hmem_tp : tMinus D x ε ∈
      ({D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} : Set Plane) := by simp
  have hmem_sm : sPlus D x ε ∈
      ({D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} : Set Plane) := by simp
  have hmem_y : D.Γ.crossingPoint y ∈
      ({D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} : Set Plane) := by simp
  -- `K` inside the two closed half-planes at `p` and inside the triangle `Δ = conv{p, z, y}`
  have hKt : convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} ⊆
      {q : Plane | 0 ≤ det (et D x) (q - pt D x) * det (et D x) (es D x)} := by
    apply w3bg_convexHull_subset_halfPlane'
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · rw [ht_tp, zero_mul]
    · rw [ht_z, zero_mul]
    · exact ht_y.le
    · exact ht_sm.le
  have hKs : convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} ⊆
      {q : Plane | 0 ≤ det (es D x) (q - pt D x) * det (et D x) (es D x)} := by
    apply w3bg_convexHull_subset_halfPlane'
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact hs_tp.le
    · exact hs_z.le
    · rw [hs_y, zero_mul]
    · rw [hs_sm, zero_mul]
  have hKΔ : convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} ⊆
      convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z} := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact subset_convexHull ℝ _ (by simp)
    · refine segment_subset_convexHull (𝕜 := ℝ) (x := D.Γ.crossingPoint z) (y := D.Γ.crossingPoint x)
        (by simp) (by simp) ?_
      rw [htp', hZt, show D.Γ.crossingPoint x = D.Γ.edgePt (tS D x) (τt D x) from hpt_t,
        um7_edgePt_mem_segment_iff D.generic, min_eq_left hzt.le, max_eq_right hzt.le]
      constructor <;> linarith [hε.pos]
    · refine segment_subset_convexHull (𝕜 := ℝ) (x := D.Γ.crossingPoint x) (y := D.Γ.crossingPoint y)
        (by simp) (by simp) ?_
      rw [hsm', hYs, show D.Γ.crossingPoint x = D.Γ.edgePt (sS D x) (τs D x) from hpt_s,
        um7_edgePt_mem_segment_iff D.generic, min_eq_left hys.le, max_eq_right hys.le]
      constructor <;> linarith [hε.pos]
    · exact subset_convexHull ℝ _ (by simp)
  -- the three lines through `K`
  have hline_t : ∀ θ : ℝ, det (et D x) (Γ₀.edgePt uIn θ - pt D x) = 0 := by
    intro θ
    rw [heOut, zero_smul, add_zero, add_sub_cancel_left, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  have hline_s : ∀ θ : ℝ, det (es D x) (Γ₀.edgePt uOut θ - pt D x) = 0 := by
    intro θ
    rw [heIn, zero_smul, add_zero, add_sub_cancel_left, w3bg_det_smul_right, w3bg_det_self, mul_zero]
  have hline_g : ∀ θ : ℝ, det (D.Γ.dir g) (Γ₀.edgePt uG θ - D.Γ.crossingPoint z) = 0 := by
    intro θ
    rw [heG, hZg, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul, w3bg_det_smul_right,
      w3bg_det_self, mul_zero]
  have hS_t : ∀ q ∈ ({D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} : Set Plane),
      q ∈ segment ℝ (D.Γ.crossingPoint z) (tMinus D x ε) ∨
        0 < det (et D x) (q - pt D x) * det (et D x) (es D x) := by
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inl (right_mem_segment ℝ _ _)
    · exact Or.inr ht_y
    · exact Or.inr ht_sm
  have hS_s : ∀ q ∈ ({D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} : Set Plane),
      q ∈ segment ℝ (sPlus D x ε) (D.Γ.crossingPoint y) ∨
        0 < det (es D x) (q - pt D x) * det (et D x) (es D x) := by
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact Or.inr hs_tp
    · exact Or.inr hs_z
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inl (right_mem_segment ℝ _ _)
  have hS_g : ∀ q ∈ ({D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} : Set Plane),
      q ∈ segment ℝ (D.Γ.crossingPoint z) (D.Γ.crossingPoint y) ∨
        0 < det (D.Γ.dir g) (q - D.Γ.crossingPoint z) * det (D.Γ.dir g) (pt D x - D.Γ.crossingPoint z) := by
    intro q hq
    rcases hgen q hq with rfl | rfl | rfl | rfl
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr hg_sm
    · exact Or.inr hg_tp
    · exact Or.inl (right_mem_segment ℝ _ _)
  have hΓ₀ : Γ₀.Generic := generic D x M hε
  refine ⟨{
    i := uIn.1
    a := uIn.2
    j := 2
    hj := by norm_num
    hk := hk5
    s := uG
    y := z₀
    z := y₀
    hy := hzv
    hz := by
      show y₀.val = {(⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand), uG}
      rw [hOut]; exact hyv
    run_free := ?_
    no_io := ?_
    same_over := ?_
    ty := ((toDiagram D x M hε).switch y₀).crossingParam z₀ huIn_y
    tz := ((toDiagram D x M hε).switch y₀).crossingParam y₀ huOut_z
    tsy := ((toDiagram D x M hε).switch y₀).crossingParam z₀ huG_y
    tsz := ((toDiagram D x M hε).switch y₀).crossingParam y₀ huG_z
    hty := (((toDiagram D x M hε).switch y₀).crossingParam_spec z₀ huIn_y).2.2.symm
    htz := by
      show Γ₀.edgePt (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) _ = Γ₀.crossingPoint y₀
      rw [hOut]; exact hsw y₀ uOut huOut_z
    htsy := (((toDiagram D x M hε).switch y₀).crossingParam_spec z₀ huG_y).2.2.symm
    htsz := (((toDiagram D x M hε).switch y₀).crossingParam_spec y₀ huG_z).2.2.symm
    K := convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y}
    K_convex := convex_convexHull ℝ _
    K_compact := (Set.toFinite _).isCompact_convexHull ℝ
    run_mem := ?_
    in_iff := ?_
    out_iff := ?_
    s_iff := ?_
    clear := ?_ }, rfl, rfl, rfl, huG, huIn, rfl⟩
  · -- run_free: the only run edge is the arc `arcTS`, which carries no crossing
    intro m h1 h2 x' hmem
    have hm : m = 1 := by omega
    subst hm
    have hmem' : (⟨uIn.1, uIn.2 + ((1 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) ∈ x'.val := hmem
    rw [Nat.cast_one, hArc] at hmem'
    exact (kind_ne_arc_of_mem D x M hε x' hmem').2 hkArc
  · -- no_io: a crossing of `cutStartT` with `cutEndS` would be a lift of `x`
    intro x' hx'
    have hx'' : uIn ∈ x'.val ∧ (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) ∈ x'.val := hx'
    rw [hOut] at hx''
    obtain ⟨h1, h2⟩ := hx''
    have horIn : M.orig uIn = tS D x := by unfold SpliceModel.orig; rw [hkIn]; rfl
    have horOut : M.orig uOut = sS D x := by unfold SpliceModel.orig; rw [hkOut]; rfl
    have hs' : tS D x ∈ (origCrossing D x M hε x').val := by
      have := orig_mem_origCrossing D x M hε h1; rwa [horIn] at this
    have ht' : sS D x ∈ (origCrossing D x M hε x').val := by
      have := orig_mem_origCrossing D x M hε h2; rwa [horOut] at this
    apply origCrossing_ne D x M hε x'
    apply Subtype.ext
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      rw [D.mem_iff] at he
      rcases he with rfl | rfl
      · exact ht'
      · exact hs'
    · rw [D.Γ.crossing_card_two, D.Γ.crossing_card_two]
  · -- same_over: the switch at `y₀` (= `B.z`) and `hover`
    have hov_y : ((toDiagram D x M hε).switch y₀).overStrand y₀ = (toDiagram D x M hε).underStrand y₀ :=
      (toDiagram D x M hε).switch_overStrand_self y₀
    have hov_z : ((toDiagram D x M hε).switch y₀).overStrand z₀ = (toDiagram D x M hε).overStrand z₀ :=
      (toDiagram D x M hε).switch_overStrand_of_ne hyz₀.symm
    have hor_uy : M.orig ((toDiagram D x M hε).underStrand y₀) = D.underStrand y := by
      have h := toDiagram_underStrand_orig D x M hε y₀; rwa [hy₀] at h
    have hor_oz : M.orig ((toDiagram D x M hε).overStrand z₀) = D.overStrand z := by
      have h := orig_overStrand₀ D x M hε z₀; rwa [hz₀] at h
    have horG : M.orig uG = g := by unfold SpliceModel.orig; rw [hkG]; rfl
    have hA : (toDiagram D x M hε).underStrand y₀ = uG ↔ D.underStrand y = g := by
      constructor
      · intro h; rw [← hor_uy, h, horG]
      · intro h
        exact orig_injOn_crossing D x M hε y₀ ((toDiagram D x M hε).under_mem y₀) huG_z
          (by rw [hor_uy, horG, h])
    have hB : (toDiagram D x M hε).overStrand z₀ = uG ↔ D.overStrand z = g := by
      constructor
      · intro h; rw [← hor_oz, h, horG]
      · intro h
        exact orig_injOn_crossing D x M hε z₀ ((toDiagram D x M hε).over_mem z₀) huG_y
          (by rw [hor_oz, horG, h])
    have hC : D.underStrand y = g ↔ D.overStrand y ≠ g := by
      constructor
      · intro h h'; exact D.under_ne_over y (h.trans h'.symm)
      · intro h
        have hg' := hgy
        rw [D.mem_iff] at hg'
        rcases hg' with hg' | hg'
        · exact absurd hg'.symm h
        · exact hg'.symm
    rw [hov_y, hov_z]
    by_cases hz' : D.overStrand z = g
    · left
      exact ⟨hB.mpr hz', hA.mpr (hC.mpr (fun h => hover.mp h hz'))⟩
    · right
      exact ⟨fun h => hz' (hB.mp h), fun h => (hC.mp (hA.mp h)) (hover.mpr hz')⟩
  · -- run_mem: the run vertices are `s⁻` and `t⁺`
    intro m h1 h2
    have hm : m = 1 ∨ m = 2 := by omega
    rcases hm with rfl | rfl
    · show Γ₀.tail ⟨uIn.1, uIn.2 + ((1 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ ∈ _
      rw [Nat.cast_one, hArc, M.tail_eq, hkArc]
      exact subset_convexHull ℝ _ hmem_tp
    · show Γ₀.tail ⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ ∈ _
      rw [hOut, M.tail_eq, hkOut]
      exact subset_convexHull ℝ _ hmem_sm
  · -- in_iff: `cutStartT ∩ K = [z, s⁻]`
    intro t h0 h1
    constructor
    · intro hmem
      have hseg := w3bg_line_convexHull ht_tp ht_z _ hS_t (hline_t t) hmem
      rw [← hEtz, ← hOut0, um7_edgePt_mem_segment_iff hΓ₀, min_eq_left htz0] at hseg
      exact hseg.1
    · intro hle
      have hseg : Γ₀.edgePt uIn t ∈ segment ℝ
          (Γ₀.edgePt uIn (((toDiagram D x M hε).switch y₀).crossingParam z₀ huIn_y)) (Γ₀.edgePt uIn 1) := by
        rw [um7_edgePt_mem_segment_iff hΓ₀, min_eq_left htz0, max_eq_right htz0]
        exact ⟨hle, h1⟩
      rw [hEtz, hOut0] at hseg
      exact segment_subset_convexHull hmem_z hmem_tp hseg
  · -- out_iff: `cutEndS ∩ K = [t⁺, y]`
    intro t h0 h1
    show Γ₀.edgePt (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) t ∈
      convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} ↔
      t ≤ ((toDiagram D x M hε).switch y₀).crossingParam y₀ huOut_z
    rw [hOut]
    constructor
    · intro hmem
      have hseg := w3bg_line_convexHull hs_y hs_sm _ hS_s (hline_s t) hmem
      rw [← hEty, ← hIn1, um7_edgePt_mem_segment_iff hΓ₀, max_eq_right hty1] at hseg
      exact hseg.2
    · intro hle
      have hseg : Γ₀.edgePt uOut t ∈ segment ℝ (Γ₀.edgePt uOut 0)
          (Γ₀.edgePt uOut (((toDiagram D x M hε).switch y₀).crossingParam y₀ huOut_z)) := by
        rw [um7_edgePt_mem_segment_iff hΓ₀, min_eq_left hty1, max_eq_right hty1]
        exact ⟨h0, hle⟩
      rw [hEty, hIn1] at hseg
      exact segment_subset_convexHull hmem_sm hmem_y hseg
  · -- s_iff: `g ∩ K = [z, y]`
    intro t h0 h1
    constructor
    · intro hmem
      have hseg := w3bg_line_convexHull hg_y hg_z _ hS_g (hline_g t) hmem
      rwa [← hEtsz, ← hEtsy, um7_edgePt_mem_segment_iff hΓ₀] at hseg
    · intro hbetween
      have hseg : Γ₀.edgePt uG t ∈ segment ℝ
          (Γ₀.edgePt uG (((toDiagram D x M hε).switch y₀).crossingParam z₀ huG_y))
          (Γ₀.edgePt uG (((toDiagram D x M hε).switch y₀).crossingParam y₀ huG_z)) := by
        rwa [um7_edgePt_mem_segment_iff hΓ₀]
      rw [hEtsz, hEtsy] at hseg
      exact segment_subset_convexHull hmem_z hmem_y hseg
  · -- clear: every other strand of `Γ₀` misses `K`
    intro u hu1 hu2 hu3 hrun
    have hu2' : u ≠ (⟨uIn.1, uIn.2 + ((2 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) := hu2
    rw [hOut] at hu2'
    have hu4 : u ≠ uArc := by
      have h := hrun 1 le_rfl one_lt_two
      have h' : u ≠ (⟨uIn.1, uIn.2 + ((1 : ℕ) : ZMod (Γ₀.comp uIn.1).k)⟩ : Γ₀.Strand) := h
      rwa [Nat.cast_one, hArc] at h'
    rw [Set.disjoint_left]
    intro q hqu hqK
    have hqu' : q ∈ (M.kind u).seg ε := (M.seg_eq u).subset hqu
    obtain ⟨κ, hκ⟩ : ∃ κ, M.kind u = κ := ⟨_, rfl⟩
    have hocc : κ.Occurs := hκ ▸ M.kind_occurs u
    have hu_eq : u = M.strandOf κ hocc := by subst hκ; exact (M.strandOf_kind u).symm
    rw [hκ] at hqu'
    cases κ with
    | old e =>
      have hocc' := (u3_occurs_old_iff D x).mp hocc
      have heg : e ≠ g := by
        rintro rfl
        exact hu3 (hu_eq.trans huG.symm)
      have hsub : StrandKind.seg ε (StrandKind.old e) ⊆ D.Γ.seg e :=
        StrandKind.seg_subset_seg_orig ε hε _ (fun h => by cases h) (fun h => by cases h)
      exact Set.disjoint_left.mp (clear e hocc'.1 hocc'.2 heg) (hsub hqu') (hKΔ hqK)
    | cutStartT => exact hu1 (hu_eq.trans huIn.symm)
    | cutEndT =>
      obtain ⟨θ, h0, h1, rfl⟩ := hqu'
      have hq_eq : StrandKind.tail ε (StrandKind.cutEndT : StrandKind D x) +
          θ • StrandKind.dir ε (StrandKind.cutEndT : StrandKind D x) =
          D.Γ.edgePt (tS D x) (τt D x + (ε + θ * (1 - τt D x - ε))) := by
        rw [u3_cutEndT_pt D x θ, D.Γ.edgePt_eq, pt_eq_t]; module
      have hline : det (et D x) (D.Γ.edgePt (tS D x) (τt D x + (ε + θ * (1 - τt D x - ε))) - pt D x) = 0 := by
        rw [hpt_t, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul, w3bg_det_smul_right,
          w3bg_det_self, mul_zero]
      rw [hq_eq] at hqK
      have hseg := w3bg_line_convexHull ht_tp ht_z _ hS_t hline hqK
      rw [hZt, htp', um7_edgePt_mem_segment_iff D.generic, max_eq_right (by linarith)] at hseg
      have hc : 0 ≤ θ * (1 - τt D x - ε) := mul_nonneg h0 (by linarith [hε.lt_one_sub_τt])
      linarith [hseg.2, hε.pos]
    | cutStartS =>
      obtain ⟨θ, h0, h1, rfl⟩ := hqu'
      have hq_eq : StrandKind.tail ε (StrandKind.cutStartS : StrandKind D x) +
          θ • StrandKind.dir ε (StrandKind.cutStartS : StrandKind D x) =
          D.Γ.edgePt (sS D x) (τs D x + (θ * (τs D x - ε) - τs D x)) := by
        rw [u3_cutStartS_pt D x θ, D.Γ.edgePt_eq, pt_eq_s]; module
      have hline : det (es D x) (D.Γ.edgePt (sS D x) (τs D x + (θ * (τs D x - ε) - τs D x)) - pt D x) = 0 := by
        rw [hpt_s, D.Γ.edgePt_eq, D.Γ.edgePt_eq, add_sub_add_left_eq_sub, ← sub_smul, w3bg_det_smul_right,
          w3bg_det_self, mul_zero]
      rw [hq_eq] at hqK
      have hseg := w3bg_line_convexHull hs_y hs_sm _ hS_s hline hqK
      rw [hsm', hYs, um7_edgePt_mem_segment_iff D.generic] at hseg
      have hc : θ * (τs D x - ε) ≤ τs D x - ε := mul_le_of_le_one_left (by linarith [hε.lt_τs]) h1
      rcases min_le_iff.mp hseg.1 with h | h <;> linarith [hε.pos]
    | cutEndS => exact hu2' (hu_eq.trans huOut.symm)
    | arcTS => exact hu4 (hu_eq.trans huArc.symm)
    | arcST =>
      obtain ⟨θ, h0, h1, rfl⟩ := hqu'
      have hq1 : StrandKind.tail ε (StrandKind.arcST : StrandKind D x) +
          θ • StrandKind.dir ε (StrandKind.arcST : StrandKind D x) - pt D x =
          (θ * ε) • et D x + ((θ - 1) * ε) • es D x := by
        rw [u3_arcST_pt D x θ]; abel
      have hA := hKt hqK
      have hB := hKs hqK
      simp only [Set.mem_setOf_eq] at hA hB
      rw [hq1, w3bg_det_add_right, w3bg_det_smul_right, w3bg_det_smul_right, w3bg_det_self] at hA hB
      rw [w3bg_det_comm (es D x) (et D x)] at hB
      have hP : 0 < ε * (det (et D x) (es D x) * det (et D x) (es D x)) := mul_pos hε.pos hdd
      have eA : (θ * ε * 0 + (θ - 1) * ε * det (et D x) (es D x)) * det (et D x) (es D x) =
          (θ - 1) * (ε * (det (et D x) (es D x) * det (et D x) (es D x))) := by ring
      have eB : (θ * ε * -det (et D x) (es D x) + (θ - 1) * ε * 0) * det (et D x) (es D x) =
          -θ * (ε * (det (et D x) (es D x) * det (et D x) (es D x))) := by ring
      rw [eA] at hA
      rw [eB] at hB
      nlinarith [hA, hB, hP]


/-- (G) **the missing `hk5` in `D`'s own terms (`arcST`)**: unless the strand before `s` IS the strand after `t`
(the kink at `x`: `⟨s.1, s.2 − 1⟩ = ⟨t.1, t.2 + 1⟩`), the component of `cutStartS` in ANY splice model has at least
five strands.  Proof from the model laws alone: the labels `a − 1, a, a + 1, a + 2, a + 3` of the component carry the
kinds `old ⟨s.1, s.2 − 1⟩, cutStartS, arcST, cutEndT, old ⟨t.1, t.2 + 1⟩` (`kind_pred`, `kind_succ`); `k = 3` would
identify the first with `cutEndT`, `k = 4` the first with the last. -/
theorem w3bg_hk5_arcST_of_not_kink (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀)
    (hkink : (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩) :
    5 ≤ (Γ₀.comp (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1).k := by
  obtain ⟨uIn, huIn⟩ : ∃ u : Γ₀.Strand, u = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS :=
    ⟨_, rfl⟩
  rw [← huIn]
  have hkIn : M.kind uIn = StrandKind.cutStartS := by rw [huIn, M.kind_strandOf]
  have hPrev : M.kind ⟨uIn.1, uIn.2 - 1⟩ = StrandKind.old ⟨(sS D x).1, (sS D x).2 - 1⟩ := by
    rw [M.kind_pred, hkIn]; rfl
  have h1 : M.kind ⟨uIn.1, uIn.2 + 1⟩ = StrandKind.arcST := by rw [M.kind_succ, hkIn]; rfl
  have h2 : M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩ = StrandKind.cutEndT := by
    have h : M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩ = (M.kind ⟨uIn.1, uIn.2 + 1⟩).succ := M.kind_succ ⟨uIn.1, uIn.2 + 1⟩
    rw [h, h1]; rfl
  have h3 : M.kind ⟨uIn.1, uIn.2 + 1 + 1 + 1⟩ = StrandKind.old ⟨(tS D x).1, (tS D x).2 + 1⟩ := by
    have h : M.kind ⟨uIn.1, uIn.2 + 1 + 1 + 1⟩ = (M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩).succ :=
      M.kind_succ ⟨uIn.1, uIn.2 + 1 + 1⟩
    rw [h, h2]; rfl
  by_contra hlt
  push Not at hlt
  have hk3 : 3 ≤ (Γ₀.comp uIn.1).k := (Γ₀.comp uIn.1).hk
  rcases (show (Γ₀.comp uIn.1).k = 3 ∨ (Γ₀.comp uIn.1).k = 4 by omega) with hk | hk
  · have hz : ((3 : ℕ) : ZMod (Γ₀.comp uIn.1).k) = 0 :=
      (congrArg (Nat.cast : ℕ → ZMod (Γ₀.comp uIn.1).k) hk.symm).trans (ZMod.natCast_self _)
    have hdiff : uIn.2 + 1 + 1 - (uIn.2 - 1) = ((3 : ℕ) : ZMod (Γ₀.comp uIn.1).k) := by push_cast; ring
    have e : uIn.2 - 1 = uIn.2 + 1 + 1 := (sub_eq_zero.mp (hdiff.trans hz)).symm
    have : M.kind ⟨uIn.1, uIn.2 - 1⟩ = M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩ := by rw [e]
    rw [hPrev, h2] at this
    simp at this
  · have hz : ((4 : ℕ) : ZMod (Γ₀.comp uIn.1).k) = 0 :=
      (congrArg (Nat.cast : ℕ → ZMod (Γ₀.comp uIn.1).k) hk.symm).trans (ZMod.natCast_self _)
    have hdiff : uIn.2 + 1 + 1 + 1 - (uIn.2 - 1) = ((4 : ℕ) : ZMod (Γ₀.comp uIn.1).k) := by push_cast; ring
    have e : uIn.2 - 1 = uIn.2 + 1 + 1 + 1 := (sub_eq_zero.mp (hdiff.trans hz)).symm
    have : M.kind ⟨uIn.1, uIn.2 - 1⟩ = M.kind ⟨uIn.1, uIn.2 + 1 + 1 + 1⟩ := by rw [e]
    rw [hPrev, h3] at this
    exact hkink (StrandKind.old.inj this)

/-- (G) the `arcTS` analogue: unless the strand before `t` is the strand after `s`, the component of `cutStartT`
has at least five strands. -/
theorem w3bg_hk5_arcTS_of_not_kink (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀)
    (hkink : (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩) :
    5 ≤ (Γ₀.comp (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1).k := by
  obtain ⟨uIn, huIn⟩ : ∃ u : Γ₀.Strand, u = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT :=
    ⟨_, rfl⟩
  rw [← huIn]
  have hkIn : M.kind uIn = StrandKind.cutStartT := by rw [huIn, M.kind_strandOf]
  have hPrev : M.kind ⟨uIn.1, uIn.2 - 1⟩ = StrandKind.old ⟨(tS D x).1, (tS D x).2 - 1⟩ := by
    rw [M.kind_pred, hkIn]; rfl
  have h1 : M.kind ⟨uIn.1, uIn.2 + 1⟩ = StrandKind.arcTS := by rw [M.kind_succ, hkIn]; rfl
  have h2 : M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩ = StrandKind.cutEndS := by
    have h : M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩ = (M.kind ⟨uIn.1, uIn.2 + 1⟩).succ := M.kind_succ ⟨uIn.1, uIn.2 + 1⟩
    rw [h, h1]; rfl
  have h3 : M.kind ⟨uIn.1, uIn.2 + 1 + 1 + 1⟩ = StrandKind.old ⟨(sS D x).1, (sS D x).2 + 1⟩ := by
    have h : M.kind ⟨uIn.1, uIn.2 + 1 + 1 + 1⟩ = (M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩).succ :=
      M.kind_succ ⟨uIn.1, uIn.2 + 1 + 1⟩
    rw [h, h2]; rfl
  by_contra hlt
  push Not at hlt
  have hk3 : 3 ≤ (Γ₀.comp uIn.1).k := (Γ₀.comp uIn.1).hk
  rcases (show (Γ₀.comp uIn.1).k = 3 ∨ (Γ₀.comp uIn.1).k = 4 by omega) with hk | hk
  · have hz : ((3 : ℕ) : ZMod (Γ₀.comp uIn.1).k) = 0 :=
      (congrArg (Nat.cast : ℕ → ZMod (Γ₀.comp uIn.1).k) hk.symm).trans (ZMod.natCast_self _)
    have hdiff : uIn.2 + 1 + 1 - (uIn.2 - 1) = ((3 : ℕ) : ZMod (Γ₀.comp uIn.1).k) := by push_cast; ring
    have e : uIn.2 - 1 = uIn.2 + 1 + 1 := (sub_eq_zero.mp (hdiff.trans hz)).symm
    have : M.kind ⟨uIn.1, uIn.2 - 1⟩ = M.kind ⟨uIn.1, uIn.2 + 1 + 1⟩ := by rw [e]
    rw [hPrev, h2] at this
    simp at this
  · have hz : ((4 : ℕ) : ZMod (Γ₀.comp uIn.1).k) = 0 :=
      (congrArg (Nat.cast : ℕ → ZMod (Γ₀.comp uIn.1).k) hk.symm).trans (ZMod.natCast_self _)
    have hdiff : uIn.2 + 1 + 1 + 1 - (uIn.2 - 1) = ((4 : ℕ) : ZMod (Γ₀.comp uIn.1).k) := by push_cast; ring
    have e : uIn.2 - 1 = uIn.2 + 1 + 1 + 1 := (sub_eq_zero.mp (hdiff.trans hz)).symm
    have : M.kind ⟨uIn.1, uIn.2 - 1⟩ = M.kind ⟨uIn.1, uIn.2 + 1 + 1 + 1⟩ := by rw [e]
    rw [hPrev, h3] at this
    exact hkink (StrandKind.old.inj this)

/-- (G) **the corrected `arcST` site in `D`'s terms**: the frozen `w3g_bigonData_smooth_arcST` plus the non-kink
hypothesis `⟨s.1, s.2 − 1⟩ ≠ ⟨t.1, t.2 + 1⟩` (which is exactly what the frozen statement lacks). -/
theorem w3bg_bigonData_smooth_arcST_of_not_kink (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : D.crossingParam y hsy < τs D x) (hzt : τt D x < D.crossingParam z htz)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hkink : (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩) :
    ∃ B : BigonData ((toDiagram D x M hε).switch y₀),
      B.j = 2 ∧ B.y = y₀ ∧ B.z = z₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} :=
  w3bg_bigonData_smooth_arcST_of_five D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀ hy₀ hz₀
    (w3bg_hk5_arcST_of_not_kink D x M hkink)

/-- (G) **the corrected `arcTS` site in `D`'s terms**: the frozen `w3g_bigonData_smooth_arcTS` plus the non-kink
hypothesis `⟨t.1, t.2 − 1⟩ ≠ ⟨s.1, s.2 + 1⟩`. -/
theorem w3bg_bigonData_smooth_arcTS_of_not_kink (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : τs D x < D.crossingParam y hsy) (hzt : D.crossingParam z htz < τt D x)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z)
    (hkink : (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩) :
    ∃ B : BigonData ((toDiagram D x M hε).switch y₀),
      B.j = 2 ∧ B.y = z₀ ∧ B.z = y₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} :=
  w3bg_bigonData_smooth_arcTS_of_five D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀ hy₀ hz₀
    (w3bg_hk5_arcTS_of_not_kink D x M hkink)

/-- (G) in the mixed case (`s`, `t` on different components) both non-kink conditions hold trivially, so the
corrected sites need no extra hypothesis there; only the self case (one component split into two) can be a kink. -/
theorem w3bg_not_kink_of_ne_comp (D : Diagram) (x : D.Γ.Crossing) (h : (sS D x).1 ≠ (tS D x).1) :
    (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩ ∧
    (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩ :=
  ⟨fun h' => h (Sigma.mk.inj h').1, fun h' => h.symm (Sigma.mk.inj h').1⟩

/-- **(g) sub-leaf — the `j = 2` bigon site on a smoothing output, case `arcST`** (the corner-cut arc on
the bigon side runs `s⁻ → t⁺`: `y` PRECEDES `x` on the over strand `s` and `z` FOLLOWS `x` on the under
strand `t`).  On the switched smoothing `(D^x)^{y−}` the run is the two arc ends `s⁻ = tail arcST`,
`t⁺ = tail cutEndT` (`StrandKind.tail`), the entering edge is `cutStartS` (carrying `y`), the exiting edge
`cutEndT` (carrying `z`), the remote strand is the old strand `g`, and `K = conv{y, s⁻, t⁺, z} ⊆ Δ`.
Sketch: labels of the three consecutive kinds from `SpliceModel.kind_succ` (`cutStartS → arcST → cutEndT`,
no wrap by `cut_val`), `hk` from `5 ≤ k` (the run + three); `run_free`: no crossing on `arcST`
(`eval_arc_mem_ball` + the clearance `r₁`); `no_io`: a crossing of `cutStartS` with `cutEndT` would be a
crossing of `s` with `t` other than `x` inside the triangle corner — excluded by `clear` (closed form);
`same_over` from `hover` through `orig_overStrand₀` (the smoothing pulls the over data back along
`orig`) and the switch at `y₀`; parameters `ty tz tsy tsz` rescaled through `origParam`; `in_iff`,
`out_iff`, `s_iff` from the quadrilateral's sides (`K ⊆ Δ`, `Δ` on one side of `line(s)`, `line(t)`,
`line(g)`; the affine-basis toolkit `gu2_mem_segment_*` of BigonDeletion §2a); `clear`: old kinds from
`clear` (their segments are sub-segments of the old edges), the three other new kinds `cutStartT`,
`arcTS`, `cutEndS` lie in the opposite cone at `x` (`sPlus`, `tMinus` on the far half-edges) and miss
`K ⊆ Δ ∩ {corner (−e_s, +e_t)}` — the cone geometry with `SmallEps.mul_es_lt / mul_et_lt`.  ≈ 1.2k lines. -/
theorem w3g_bigonData_smooth_arcST (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : D.crossingParam y hsy < τs D x) (hzt : τt D x < D.crossingParam z htz)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (clear_vertex : ∀ (i : Fin D.Γ.c) (a : ZMod (D.Γ.comp i).k),
      (D.Γ.comp i).P a ∉ convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z})
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z) :
    ∃ B : BigonData ((toDiagram D x M hε).switch y₀),
      B.j = 2 ∧ B.y = y₀ ∧ B.z = z₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} := by
  -- (G) everything but `hk5 : 5 ≤ k` is proved in `w3bg_bigonData_smooth_arcST_of_five`; `hk5` is NOT derivable
  -- from the hypotheses above (kink counterexample, see the docstring there) — rule 3, reported.
  exact w3bg_bigonData_smooth_arcST_of_five D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀ hy₀ hz₀
    (by sorry)

/-- **(g) sub-leaf — the `j = 2` bigon site, case `arcTS`** (the other orientation: `y` FOLLOWS `x` on
`s`, `z` PRECEDES `x` on `t`; the bigon path runs `z → t⁻ → s⁺ → y`, so the ENTERING edge is `cutStartT`
(carrying `z`, which is `B.y`), the run is `t⁻, s⁺`, the exiting edge `cutEndS` (carrying `y`, which is
`B.z`), `K = conv{z, t⁻, s⁺, y}`).  The consumer case-splits on the orientation (PLAN §4.4 (6)); in the two
remaining orientation combinations the oriented smoothing does not cut the triangle's corner at `x` and
NO bigon exists — the realiser must derive `(hys ∧ hzt) ∨ (hys' ∧ hzt')` from the 177 configuration (the
sign table (1c) / the coherent orientation of the triangle's corner at `x`), see the report.  Same
sketch as `w3g_bigonData_smooth_arcST` with `s ↔ t`. -/
theorem w3g_bigonData_smooth_arcTS (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : τs D x < D.crossingParam y hsy) (hzt : D.crossingParam z htz < τt D x)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (clear_vertex : ∀ (i : Fin D.Γ.c) (a : ZMod (D.Γ.comp i).k),
      (D.Γ.comp i).P a ∉ convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z})
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z) :
    ∃ B : BigonData ((toDiagram D x M hε).switch y₀),
      B.j = 2 ∧ B.y = z₀ ∧ B.z = y₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} := by
  -- (G) as for `arcST`: reduced to the missing `hk5 : 5 ≤ k` on the component of `cutStartT` (rule 3).
  exact w3bg_bigonData_smooth_arcTS_of_five D x M hε g hgs hgt y z hy hz hsy htz hys hzt clear hover y₀ z₀ hy₀ hz₀
    (by sorry)

/-- `w3bh_` helper: membership of `crossingOf v` in an occurrence-defined crossing set. -/
theorem w3bh_crossingOf_mem_setOf (ρ : Record) (P : ρ.M → Prop) (v : ρ.M) :
    ρ.crossingOf v ∈ {c : ρ.Crossing | ∀ w ∈ c.1, P w} ↔ P v ∧ P (ρ.pair v) := by
  show (∀ w ∈ ({v, ρ.pair v} : Finset ρ.M), P w) ↔ P v ∧ P (ρ.pair v)
  simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]

/-- `w3bh_` helper: two occurrences of a diagram name the same record crossing iff they lie over the
same crossing. -/
theorem w3bh_record_crossingOf_eq_iff (D : Diagram) (v w : D.Γ.Visit) :
    D.record.crossingOf v = D.record.crossingOf w ↔ v.1 = w.1 := by
  rw [Record.crossingOf_eq_iff]
  exact D.mem_pair_twin_iff w v

/-- `w3bh_` helper: a product of two commuting involutions is an involution. -/
theorem w3bh_invol_mul {G : Type*} [Group G] {f g : G} (hf : f * f = 1) (hg : g * g = 1)
    (hc : Commute f g) : (f * g) * (f * g) = 1 := by
  calc (f * g) * (f * g) = f * (g * f) * g := by simp only [mul_assoc]
    _ = f * (f * g) * g := by rw [hc.eq]
    _ = (f * f) * (g * g) := by simp only [mul_assoc]
    _ = 1 := by rw [hf, hg, one_mul]

/-- `w3bh_` helper: two swaps on disjoint pairs are disjoint permutations. -/
theorem w3bh_swap_disjoint {α : Type*} [DecidableEq α] {a b c d : α}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (Equiv.swap a b).Disjoint (Equiv.swap c d) := by
  intro x
  by_cases hxa : x = a
  · right; subst hxa; exact Equiv.swap_apply_of_ne_of_ne hac had
  by_cases hxb : x = b
  · right; subst hxb; exact Equiv.swap_apply_of_ne_of_ne hbc hbd
  · left; exact Equiv.swap_apply_of_ne_of_ne hxa hxb

/-- `w3bh_` helper: the twist `σ = (a₁ a₂)(b₁ b₂)(c₁ c₂)` on six distinct points is an involution. -/
theorem w3bh_swap3_sq {α : Type*} [DecidableEq α] (a₁ a₂ b₁ b₂ c₁ c₂ : α)
    (h13 : a₁ ≠ b₁) (h14 : a₁ ≠ b₂) (h23 : a₂ ≠ b₁) (h24 : a₂ ≠ b₂)
    (h15 : a₁ ≠ c₁) (h16 : a₁ ≠ c₂) (h25 : a₂ ≠ c₁) (h26 : a₂ ≠ c₂)
    (h35 : b₁ ≠ c₁) (h36 : b₁ ≠ c₂) (h45 : b₂ ≠ c₁) (h46 : b₂ ≠ c₂) :
    (Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) *
      (Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) = 1 := by
  have hBC : (Equiv.swap b₁ b₂).Disjoint (Equiv.swap c₁ c₂) := w3bh_swap_disjoint h35 h36 h45 h46
  have hAB : (Equiv.swap a₁ a₂).Disjoint (Equiv.swap b₁ b₂) := w3bh_swap_disjoint h13 h14 h23 h24
  have hAC : (Equiv.swap a₁ a₂).Disjoint (Equiv.swap c₁ c₂) := w3bh_swap_disjoint h15 h16 h25 h26
  apply w3bh_invol_mul (Equiv.swap_mul_self _ _)
  · exact w3bh_invol_mul (Equiv.swap_mul_self _ _) (Equiv.swap_mul_self _ _) hBC.commute
  · exact (hAB.mul_right hAC).commute

theorem w3bh_swap3_apply_apply {α : Type*} [DecidableEq α] (a₁ a₂ b₁ b₂ c₁ c₂ : α)
    (h13 : a₁ ≠ b₁) (h14 : a₁ ≠ b₂) (h23 : a₂ ≠ b₁) (h24 : a₂ ≠ b₂)
    (h15 : a₁ ≠ c₁) (h16 : a₁ ≠ c₂) (h25 : a₂ ≠ c₁) (h26 : a₂ ≠ c₂)
    (h35 : b₁ ≠ c₁) (h36 : b₁ ≠ c₂) (h45 : b₂ ≠ c₁) (h46 : b₂ ≠ c₂) (v : α) :
    (Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v) = v := by
  have h := w3bh_swap3_sq a₁ a₂ b₁ b₂ c₁ c₂ h13 h14 h23 h24 h15 h16 h25 h26 h35 h36 h45 h46
  have := congrArg (fun σ : Equiv.Perm α => σ v) h
  simpa [Equiv.Perm.mul_apply] using this

/-- `w3bh_` helper: on a one-component diagram every two occurrences share the component. -/
theorem w3bh_compOf_eq_of_one (D : Diagram) (h1 : D.componentCount = 1) (v w : D.Γ.Visit) :
    D.compOf v = D.compOf w := by
  have hc : D.Γ.c = 1 := h1
  apply Fin.ext
  have := (D.compOf v).isLt
  have := (D.compOf w).isLt
  omega


/-- `w3bh_` helper: an occurrence differs from both occurrences of `a` iff it lies over another crossing. -/
theorem w3bh_ne_ne_twin_iff (D : Diagram) (a w : D.Γ.Visit) :
    (w ≠ a ∧ w ≠ D.twin a) ↔ w.1 ≠ a.1 := by
  constructor
  · rintro ⟨h1, h2⟩ h
    rcases D.eq_or_eq_twin a w h with h' | h'
    · exact h1 h'
    · exact h2 h'
  · intro h
    exact ⟨fun h' => h (congrArg (fun w : D.Γ.Visit => w.1) h'),
      fun h' => h ((congrArg (fun w : D.Γ.Visit => w.1) h').trans (D.twin_fst a))⟩

/-- `w3bh_` helper: a twin-compatible bijection preserves "same crossing". -/
theorem w3bh_fst_eq_iff_of_twin {D D' : Diagram} (Ψ : D.Γ.Visit ≃ D'.Γ.Visit)
    (htw : ∀ v, Ψ (D.twin v) = D'.twin (Ψ v)) (u v : D.Γ.Visit) :
    (Ψ u).1 = (Ψ v).1 ↔ u.1 = v.1 := by
  constructor
  · intro h
    rcases D'.eq_or_eq_twin (Ψ v) (Ψ u) h with h' | h'
    · rw [Ψ.injective h']
    · rw [← htw, Ψ.apply_eq_iff_eq] at h'
      exact (congrArg (fun w : D.Γ.Visit => w.1) h').trans (D.twin_fst v)
  · intro h
    rcases D.eq_or_eq_twin v u h with h' | h'
    · rw [h']
    · rw [h', htw]
      exact D'.twin_fst (Ψ v)

/-- `w3bh_` copy of `w3bh_restrictCrossings_iso_of_recordIso` (SM/CBProducts.lean:1358; that module is not
in this file's import closure): a named record isomorphism restricts to corresponding crossing sets. -/
theorem w3bh_restrictCrossings_iso_of_recordIso {ρ ρ' : Record} (ι : RecordIso ρ ρ') (X : Set ρ.Crossing)
    (X' : Set ρ'.Crossing)
    (hX : ∀ v : ρ.M, ρ.crossingOf v ∈ X ↔ ρ'.crossingOf (ι.Φ v) ∈ X') :
    Nonempty (RecordIso (ρ.restrictCrossings X) (ρ'.restrictCrossings X')) :=
  have hk : ∀ v : ρ.M, ρ'.CrossKeep X' (ι.Φ v) ↔ ρ.CrossKeep X v := fun v => (hX v).symm
  ⟨{ e := ι.e
     Φ := Equiv.subtypeEquiv ι.Φ (fun v => (hk v).symm)
     comp_eq := fun v => ι.comp_eq v.1
     succ_eq := fun v =>
       Subtype.ext (firstReturn_map_val ι.Φ ρ.succ ρ'.succ (ρ.CrossKeep X) (ρ'.CrossKeep X')
         ι.succ_eq hk v).symm
     pair_eq := fun v => Subtype.ext (ι.pair_eq v.1)
     bit_eq := fun v => ι.bit_eq v.1
     sgn_eq := fun v => ι.sgn_eq v.1 }⟩

/-- `w3bh_` helper: `ρ.pair u ≠ a ↔ u ≠ b` when `ρ.pair a = b` (and symmetrically). -/
theorem w3bh_pair_ne_iff (ρ : Record) {a b : ρ.M} (h : ρ.pair a = b) (u : ρ.M) :
    (ρ.pair u = a ↔ u = b) ∧ (ρ.pair u = b ↔ u = a) := by
  constructor
  · rw [ρ.pair_eq_iff, h]
  · rw [ρ.pair_eq_iff, ← h, ρ.pair_invol]

/-- `w3bh_` helper: the retained predicate of the `{y, z}`-deletion on `ρ.smooth a₁`, read on the
underlying occurrence (the four deleted occurrences form a pair-closed set). -/
theorem w3bh_crossKeep_iff (ρ : Record) (a₁ a₂ b₂ c₁ c₂ : ρ.M) (hy : ρ.pair a₂ = c₁) (hz : ρ.pair b₂ = c₂)
    (w : (ρ.smooth a₁).M) :
    (ρ.smooth a₁).CrossKeep {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂} w ↔
      (w.1 ≠ a₂ ∧ w.1 ≠ c₁ ∧ w.1 ≠ b₂ ∧ w.1 ≠ c₂) := by
  show (ρ.smooth a₁).crossingOf w ∈ {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂} ↔ _
  rw [w3bh_crossingOf_mem_setOf]
  show (w.1 ≠ a₂ ∧ w.1 ≠ c₁ ∧ w.1 ≠ b₂ ∧ w.1 ≠ c₂) ∧
    (ρ.pair w.1 ≠ a₂ ∧ ρ.pair w.1 ≠ c₁ ∧ ρ.pair w.1 ≠ b₂ ∧ ρ.pair w.1 ≠ c₂) ↔ _
  have e := w3bh_pair_ne_iff ρ hy w.1
  have f := w3bh_pair_ne_iff ρ hz w.1
  simp only [Ne, e.1, e.2, f.1, f.2]
  tauto


/-- `w3bh_` helper: a bijection carries a transposition to the transposition of the images. -/
theorem w3bh_map_swap {α β : Type*} [DecidableEq α] [DecidableEq β] (Φ : α ≃ β) (a b u : α) :
    Φ (Equiv.swap a b u) = Equiv.swap (Φ a) (Φ b) (Φ u) := by
  by_cases h1 : u = a
  · subst h1; rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  by_cases h2 : u = b
  · subst h2; rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
  · rw [Equiv.swap_apply_of_ne_of_ne h1 h2,
      Equiv.swap_apply_of_ne_of_ne (Φ.injective.ne h1) (Φ.injective.ne h2)]

/-- `w3bh_` helper: a `k`-step chain (intermediate points outside `p`, end point in `p`) determines the first return. -/
theorem w3bh_fr_chain {α : Type*} [Fintype α] (f : Equiv.Perm α) (p : α → Prop) [DecidablePred p]
    (m : {m // p m}) (k : ℕ) (hk : 0 < k) (hmid : ∀ j, 0 < j → j < k → ¬ p ((f ^ j) m.1))
    (hend : p ((f ^ k) m.1)) : (firstReturn f p m).1 = (f ^ k) m.1 := by
  have h : returnTime f p m.1 m.2 = k :=
    (returnTime_eq_iff f p m.1 m.2).mpr ⟨⟨hk, hend⟩, fun j hj hj' => hmid j hj'.1 hj hj'.2⟩
  rw [firstReturn_apply, h]

theorem w3bh_pow2 {α : Type*} (f : Equiv.Perm α) (u : α) : (f ^ 2) u = f (f u) := by
  rw [pow_two, Equiv.Perm.mul_apply]
theorem w3bh_pow3 {α : Type*} (f : Equiv.Perm α) (u : α) : (f ^ 3) u = f (f (f u)) := by
  rw [pow_succ, Equiv.Perm.mul_apply, w3bh_pow2]
theorem w3bh_pow4 {α : Type*} (f : Equiv.Perm α) (u : α) : (f ^ 4) u = f (f (f (f u))) := by
  rw [pow_succ, Equiv.Perm.mul_apply, w3bh_pow3]

/-- `w3bh_` helper: on a one-circle record, a two-cycle `x ↦ y ↦ x` of the successor leaves no room for a third occurrence. -/
theorem w3bh_no_two_cycle (ρ : Record) (hρ : ρ.componentCount = 1) (x y v : ρ.M)
    (hxy : ρ.succ x = y) (hyx : ρ.succ y = x) (hv : v ≠ x) (hv' : v ≠ y) : False := by
  obtain ⟨n, hn⟩ := (ρ.sameCycle_of_one_circle hρ x v).exists_nat_pow_eq
  have key : ∀ n : ℕ, (ρ.succ ^ n) x = x ∨ (ρ.succ ^ n) x = y := by
    intro n
    induction n with
    | zero => left; rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with h | h
      · right; rw [h, hxy]
      · left; rw [h, hyx]
  rcases key n with h | h
  · exact hv (hn.symm.trans h)
  · exact hv' (hn.symm.trans h)

/-- `w3bh_` helper: on a one-circle record the successor has no fixed point next to another occurrence. -/
theorem w3bh_no_fixed (ρ : Record) (hρ : ρ.componentCount = 1) (x v : ρ.M)
    (hx : ρ.succ x = x) (hv : v ≠ x) : False := by
  obtain ⟨n, hn⟩ := (ρ.sameCycle_of_one_circle hρ x v).exists_nat_pow_eq
  have key : ∀ n : ℕ, (ρ.succ ^ n) x = x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hx]
  exact hv (hn.symm.trans (key n))

/-- `w3bh_` helper: `s u ≠ t` when `s w = t` and `u ≠ w`. -/
theorem w3bh_succ_ne (ρ : Record) {u w t : ρ.M} (hw : ρ.succ w = t) (hne : u ≠ w) : ρ.succ u ≠ t :=
  fun h => hne (ρ.succ.injective (h.trans hw.symm))

/-- **`w3bh_` the pure core on the four `x, y, z`-strand occurrences** (`c₁, c₂` peeled off): for a one-circle
record and four distinct occurrences with `a₁ ~ a₂`, `b₁ ~ b₂` adjacent, the first returns of `s ∘ (a₁ b₁)` and
`s ∘ (a₂ b₂)` to the complement of `{a₁, b₁, a₂, b₂}` agree.  PROVED (Unit H, 2026-09-15) by the chase: if `s v` is
retained both return `s v`; otherwise `s v` is an entry of the block and the two chains (`w3bh_fr_chain`, 2–4 steps)
end at the same exit, which is retained by predecessor uniqueness (`w3bh_succ_ne`) and one circle (`w3bh_no_two_cycle`,
`w3bh_no_fixed`): pattern `s a₁ = a₂, s b₁ = b₂`: entry `a₁`: `a₁ ↦ b₂ ↦ s b₂` vs `a₁ ↦ a₂ ↦ s b₂`, entry `b₁`:
`b₁ ↦ a₂ ↦ s a₂` vs `b₁ ↦ b₂ ↦ s a₂`; pattern `s a₁ = a₂, s b₂ = b₁`: entry `a₁`: `a₁ ↦ s b₁` vs `a₁ ↦ a₂ ↦ b₁ ↦ s b₁`,
entry `b₂`: `b₂ ↦ b₁ ↦ a₂ ↦ s a₂` vs `b₂ ↦ s a₂`; the two mirror patterns likewise.  Brute-force checked for all
one-circle records with `≤ 10` occurrences (`W3B_H_brute.py`).  `w3bh_core_pure` is derived from it. -/
theorem w3bh_core_pure₀ (ρ : Record) (hρ : ρ.componentCount = 1) (a₁ a₂ b₁ b₂ : ρ.M)
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ b₁) (h14 : a₁ ≠ b₂) (h23 : a₂ ≠ b₁) (h24 : a₂ ≠ b₂) (h34 : b₁ ≠ b₂)
    (hadj_e : ρ.succ a₁ = a₂ ∨ ρ.succ a₂ = a₁) (hadj_f : ρ.succ b₁ = b₂ ∨ ρ.succ b₂ = b₁)
    (v : ρ.M) (hv : v ≠ a₁ ∧ v ≠ b₁ ∧ v ≠ a₂ ∧ v ≠ b₂) :
    (firstReturn (ρ.succ * Equiv.swap a₁ b₁) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) ⟨v, hv⟩).1 =
      (firstReturn (ρ.succ * Equiv.swap a₂ b₂) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) ⟨v, hv⟩).1 := by
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
  -- evaluations of the two reconnections
  have e1 : ∀ u, u ≠ a₁ → u ≠ b₁ → (ρ.succ * Equiv.swap a₁ b₁) u = ρ.succ u := fun u h1 h2 => by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have e1a : (ρ.succ * Equiv.swap a₁ b₁) a₁ = ρ.succ b₁ := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have e1b : (ρ.succ * Equiv.swap a₁ b₁) b₁ = ρ.succ a₁ := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have e2 : ∀ u, u ≠ a₂ → u ≠ b₂ → (ρ.succ * Equiv.swap a₂ b₂) u = ρ.succ u := fun u h1 h2 => by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have e2a : (ρ.succ * Equiv.swap a₂ b₂) a₂ = ρ.succ b₂ := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have e2b : (ρ.succ * Equiv.swap a₂ b₂) b₂ = ρ.succ a₂ := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have hf1v : (ρ.succ * Equiv.swap a₁ b₁) v = ρ.succ v := e1 v hv1 hv2
  have hf2v : (ρ.succ * Equiv.swap a₂ b₂) v = ρ.succ v := e2 v hv3 hv4
  -- the four local points are not retained
  have nA₁ : ¬ (a₁ ≠ a₁ ∧ a₁ ≠ b₁ ∧ a₁ ≠ a₂ ∧ a₁ ≠ b₂) := fun h => h.1 rfl
  have nB₁ : ¬ (b₁ ≠ a₁ ∧ b₁ ≠ b₁ ∧ b₁ ≠ a₂ ∧ b₁ ≠ b₂) := fun h => h.2.1 rfl
  have nA₂ : ¬ (a₂ ≠ a₁ ∧ a₂ ≠ b₁ ∧ a₂ ≠ a₂ ∧ a₂ ≠ b₂) := fun h => h.2.2.1 rfl
  have nB₂ : ¬ (b₂ ≠ a₁ ∧ b₂ ≠ b₁ ∧ b₂ ≠ a₂ ∧ b₂ ≠ b₂) := fun h => h.2.2.2 rfl
  by_cases hw : ρ.succ v ≠ a₁ ∧ ρ.succ v ≠ b₁ ∧ ρ.succ v ≠ a₂ ∧ ρ.succ v ≠ b₂
  · -- the successor of `v` is retained: both first returns are `s v`
    rw [firstReturn_apply_of_mem _ _ ⟨v, ⟨hv1, hv2, hv3, hv4⟩⟩ (by rw [hf1v]; exact hw),
      firstReturn_apply_of_mem _ _ ⟨v, ⟨hv1, hv2, hv3, hv4⟩⟩ (by rw [hf2v]; exact hw)]
    exact hf1v.trans hf2v.symm
  · -- `s v` is one of the four local points: chase through the block
    have hw' : ρ.succ v = a₁ ∨ ρ.succ v = b₁ ∨ ρ.succ v = a₂ ∨ ρ.succ v = b₂ := by
      by_contra hc
      push Not at hc
      exact hw ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
    rcases hadj_e with hE | hE <;> rcases hadj_f with hF | hF <;>
      rcases hw' with hw | hw | hw | hw
    -- pattern E1 F1 (s a₁ = a₂, s b₁ = b₂)
    · -- entry a₁: f₁ : v a₁ b₂ (s b₂); f₂ : v a₁ a₂ (s b₂)
      have ex : ρ.succ b₂ ≠ a₁ ∧ ρ.succ b₂ ≠ b₁ ∧ ρ.succ b₂ ≠ a₂ ∧ ρ.succ b₂ ≠ b₂ :=
        ⟨w3bh_succ_ne ρ hw (Ne.symm hv4), fun h => w3bh_no_two_cycle ρ hρ b₁ b₂ v hF h hv2 hv4,
         w3bh_succ_ne ρ hE (Ne.symm h14), fun h => w3bh_no_fixed ρ hρ b₂ v h hv4⟩
      rw [w3bh_fr_chain _ _ _ 3 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf1v, hw]; exact nA₁
          · rw [w3bh_pow2, hf1v, hw, e1a, hF]; exact nB₂)
        (by rw [w3bh_pow3, hf1v, hw, e1a, hF, e1 b₂ (Ne.symm h14) (Ne.symm h34)]; exact ex),
        w3bh_fr_chain _ _ _ 3 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf2v, hw]; exact nA₁
          · rw [w3bh_pow2, hf2v, hw, e2 a₁ h12 h14, hE]; exact nA₂)
        (by rw [w3bh_pow3, hf2v, hw, e2 a₁ h12 h14, hE, e2a]; exact ex)]
      rw [w3bh_pow3, w3bh_pow3, hf1v, hf2v, hw, e1a, hF, e1 b₂ (Ne.symm h14) (Ne.symm h34),
        e2 a₁ h12 h14, hE, e2a]
    · -- entry b₁: f₁ : v b₁ a₂ (s a₂); f₂ : v b₁ b₂ (s a₂)
      have ex : ρ.succ a₂ ≠ a₁ ∧ ρ.succ a₂ ≠ b₁ ∧ ρ.succ a₂ ≠ a₂ ∧ ρ.succ a₂ ≠ b₂ :=
        ⟨fun h => w3bh_no_two_cycle ρ hρ a₁ a₂ v hE h hv1 hv3, w3bh_succ_ne ρ hw (Ne.symm hv3),
         fun h => w3bh_no_fixed ρ hρ a₂ v h hv3, w3bh_succ_ne ρ hF h23⟩
      rw [w3bh_fr_chain _ _ _ 3 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf1v, hw]; exact nB₁
          · rw [w3bh_pow2, hf1v, hw, e1b, hE]; exact nA₂)
        (by rw [w3bh_pow3, hf1v, hw, e1b, hE, e1 a₂ (Ne.symm h12) h23]; exact ex),
        w3bh_fr_chain _ _ _ 3 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf2v, hw]; exact nB₁
          · rw [w3bh_pow2, hf2v, hw, e2 b₁ (Ne.symm h23) h34, hF]; exact nB₂)
        (by rw [w3bh_pow3, hf2v, hw, e2 b₁ (Ne.symm h23) h34, hF, e2b]; exact ex)]
      rw [w3bh_pow3, w3bh_pow3, hf1v, hf2v, hw, e1b, hE, e1 a₂ (Ne.symm h12) h23,
        e2 b₁ (Ne.symm h23) h34, hF, e2b]
    · exact absurd (ρ.succ.injective (hw.trans hE.symm)) hv1
    · exact absurd (ρ.succ.injective (hw.trans hF.symm)) hv2
    -- pattern E1 F2 (s a₁ = a₂, s b₂ = b₁)
    · -- entry a₁: f₁ : v a₁ (s b₁); f₂ : v a₁ a₂ b₁ (s b₁)
      have ex : ρ.succ b₁ ≠ a₁ ∧ ρ.succ b₁ ≠ b₁ ∧ ρ.succ b₁ ≠ a₂ ∧ ρ.succ b₁ ≠ b₂ :=
        ⟨w3bh_succ_ne ρ hw (Ne.symm hv2), fun h => w3bh_no_fixed ρ hρ b₁ v h hv2,
         w3bh_succ_ne ρ hE (Ne.symm h13), fun h => w3bh_no_two_cycle ρ hρ b₂ b₁ v hF h hv4 hv2⟩
      rw [w3bh_fr_chain _ _ _ 2 (by norm_num) (by
          intro j hj hjk; interval_cases j
          rw [pow_one, hf1v, hw]; exact nA₁)
        (by rw [w3bh_pow2, hf1v, hw, e1a]; exact ex),
        w3bh_fr_chain _ _ _ 4 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf2v, hw]; exact nA₁
          · rw [w3bh_pow2, hf2v, hw, e2 a₁ h12 h14, hE]; exact nA₂
          · rw [w3bh_pow3, hf2v, hw, e2 a₁ h12 h14, hE, e2a, hF]; exact nB₁)
        (by rw [w3bh_pow4, hf2v, hw, e2 a₁ h12 h14, hE, e2a, hF, e2 b₁ (Ne.symm h23) h34]; exact ex)]
      rw [w3bh_pow2, w3bh_pow4, hf1v, hf2v, hw, e1a, e2 a₁ h12 h14, hE, e2a, hF, e2 b₁ (Ne.symm h23) h34]
    · exact absurd (ρ.succ.injective (hw.trans hF.symm)) hv4
    · exact absurd (ρ.succ.injective (hw.trans hE.symm)) hv1
    · -- entry b₂: f₁ : v b₂ b₁ a₂ (s a₂); f₂ : v b₂ (s a₂)
      have ex : ρ.succ a₂ ≠ a₁ ∧ ρ.succ a₂ ≠ b₁ ∧ ρ.succ a₂ ≠ a₂ ∧ ρ.succ a₂ ≠ b₂ :=
        ⟨fun h => w3bh_no_two_cycle ρ hρ a₁ a₂ v hE h hv1 hv3, w3bh_succ_ne ρ hF h24,
         fun h => w3bh_no_fixed ρ hρ a₂ v h hv3, w3bh_succ_ne ρ hw (Ne.symm hv3)⟩
      rw [w3bh_fr_chain _ _ _ 4 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf1v, hw]; exact nB₂
          · rw [w3bh_pow2, hf1v, hw, e1 b₂ (Ne.symm h14) (Ne.symm h34), hF]; exact nB₁
          · rw [w3bh_pow3, hf1v, hw, e1 b₂ (Ne.symm h14) (Ne.symm h34), hF, e1b, hE]; exact nA₂)
        (by rw [w3bh_pow4, hf1v, hw, e1 b₂ (Ne.symm h14) (Ne.symm h34), hF, e1b, hE,
              e1 a₂ (Ne.symm h12) h23]; exact ex),
        w3bh_fr_chain _ _ _ 2 (by norm_num) (by
          intro j hj hjk; interval_cases j
          rw [pow_one, hf2v, hw]; exact nB₂)
        (by rw [w3bh_pow2, hf2v, hw, e2b]; exact ex)]
      rw [w3bh_pow4, w3bh_pow2, hf1v, hf2v, hw, e1 b₂ (Ne.symm h14) (Ne.symm h34), hF, e1b, hE,
        e1 a₂ (Ne.symm h12) h23, e2b]
    -- pattern E2 F1 (s a₂ = a₁, s b₁ = b₂)
    · exact absurd (ρ.succ.injective (hw.trans hE.symm)) hv3
    · -- entry b₁: f₁ : v b₁ (s a₁); f₂ : v b₁ b₂ a₁ (s a₁)
      have ex : ρ.succ a₁ ≠ a₁ ∧ ρ.succ a₁ ≠ b₁ ∧ ρ.succ a₁ ≠ a₂ ∧ ρ.succ a₁ ≠ b₂ :=
        ⟨fun h => w3bh_no_fixed ρ hρ a₁ v h hv1, w3bh_succ_ne ρ hw (Ne.symm hv1),
         fun h => w3bh_no_two_cycle ρ hρ a₂ a₁ v hE h hv3 hv1, w3bh_succ_ne ρ hF h13⟩
      rw [w3bh_fr_chain _ _ _ 2 (by norm_num) (by
          intro j hj hjk; interval_cases j
          rw [pow_one, hf1v, hw]; exact nB₁)
        (by rw [w3bh_pow2, hf1v, hw, e1b]; exact ex),
        w3bh_fr_chain _ _ _ 4 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf2v, hw]; exact nB₁
          · rw [w3bh_pow2, hf2v, hw, e2 b₁ (Ne.symm h23) h34, hF]; exact nB₂
          · rw [w3bh_pow3, hf2v, hw, e2 b₁ (Ne.symm h23) h34, hF, e2b, hE]; exact nA₁)
        (by rw [w3bh_pow4, hf2v, hw, e2 b₁ (Ne.symm h23) h34, hF, e2b, hE, e2 a₁ h12 h14]; exact ex)]
      rw [w3bh_pow2, w3bh_pow4, hf1v, hf2v, hw, e1b, e2 b₁ (Ne.symm h23) h34, hF, e2b, hE, e2 a₁ h12 h14]
    · -- entry a₂: f₁ : v a₂ a₁ b₂ (s b₂); f₂ : v a₂ (s b₂)
      have ex : ρ.succ b₂ ≠ a₁ ∧ ρ.succ b₂ ≠ b₁ ∧ ρ.succ b₂ ≠ a₂ ∧ ρ.succ b₂ ≠ b₂ :=
        ⟨w3bh_succ_ne ρ hE (Ne.symm h24), fun h => w3bh_no_two_cycle ρ hρ b₁ b₂ v hF h hv2 hv4,
         w3bh_succ_ne ρ hw (Ne.symm hv4), fun h => w3bh_no_fixed ρ hρ b₂ v h hv4⟩
      rw [w3bh_fr_chain _ _ _ 4 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf1v, hw]; exact nA₂
          · rw [w3bh_pow2, hf1v, hw, e1 a₂ (Ne.symm h12) h23, hE]; exact nA₁
          · rw [w3bh_pow3, hf1v, hw, e1 a₂ (Ne.symm h12) h23, hE, e1a, hF]; exact nB₂)
        (by rw [w3bh_pow4, hf1v, hw, e1 a₂ (Ne.symm h12) h23, hE, e1a, hF,
              e1 b₂ (Ne.symm h14) (Ne.symm h34)]; exact ex),
        w3bh_fr_chain _ _ _ 2 (by norm_num) (by
          intro j hj hjk; interval_cases j
          rw [pow_one, hf2v, hw]; exact nA₂)
        (by rw [w3bh_pow2, hf2v, hw, e2a]; exact ex)]
      rw [w3bh_pow4, w3bh_pow2, hf1v, hf2v, hw, e1 a₂ (Ne.symm h12) h23, hE, e1a, hF,
        e1 b₂ (Ne.symm h14) (Ne.symm h34), e2a]
    · exact absurd (ρ.succ.injective (hw.trans hF.symm)) hv2
    -- pattern E2 F2 (s a₂ = a₁, s b₂ = b₁)
    · exact absurd (ρ.succ.injective (hw.trans hE.symm)) hv3
    · exact absurd (ρ.succ.injective (hw.trans hF.symm)) hv4
    · -- entry a₂: f₁ : v a₂ a₁ (s b₁); f₂ : v a₂ b₁ (s b₁)
      have ex : ρ.succ b₁ ≠ a₁ ∧ ρ.succ b₁ ≠ b₁ ∧ ρ.succ b₁ ≠ a₂ ∧ ρ.succ b₁ ≠ b₂ :=
        ⟨w3bh_succ_ne ρ hE (Ne.symm h23), fun h => w3bh_no_fixed ρ hρ b₁ v h hv2,
         w3bh_succ_ne ρ hw (Ne.symm hv2), fun h => w3bh_no_two_cycle ρ hρ b₂ b₁ v hF h hv4 hv2⟩
      rw [w3bh_fr_chain _ _ _ 3 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf1v, hw]; exact nA₂
          · rw [w3bh_pow2, hf1v, hw, e1 a₂ (Ne.symm h12) h23, hE]; exact nA₁)
        (by rw [w3bh_pow3, hf1v, hw, e1 a₂ (Ne.symm h12) h23, hE, e1a]; exact ex),
        w3bh_fr_chain _ _ _ 3 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf2v, hw]; exact nA₂
          · rw [w3bh_pow2, hf2v, hw, e2a, hF]; exact nB₁)
        (by rw [w3bh_pow3, hf2v, hw, e2a, hF, e2 b₁ (Ne.symm h23) h34]; exact ex)]
      rw [w3bh_pow3, w3bh_pow3, hf1v, hf2v, hw, e1 a₂ (Ne.symm h12) h23, hE, e1a, e2a, hF,
        e2 b₁ (Ne.symm h23) h34]
    · -- entry b₂: f₁ : v b₂ b₁ (s a₁); f₂ : v b₂ a₁ (s a₁)
      have ex : ρ.succ a₁ ≠ a₁ ∧ ρ.succ a₁ ≠ b₁ ∧ ρ.succ a₁ ≠ a₂ ∧ ρ.succ a₁ ≠ b₂ :=
        ⟨fun h => w3bh_no_fixed ρ hρ a₁ v h hv1, w3bh_succ_ne ρ hF h14,
         fun h => w3bh_no_two_cycle ρ hρ a₂ a₁ v hE h hv3 hv1, w3bh_succ_ne ρ hw (Ne.symm hv1)⟩
      rw [w3bh_fr_chain _ _ _ 3 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf1v, hw]; exact nB₂
          · rw [w3bh_pow2, hf1v, hw, e1 b₂ (Ne.symm h14) (Ne.symm h34), hF]; exact nB₁)
        (by rw [w3bh_pow3, hf1v, hw, e1 b₂ (Ne.symm h14) (Ne.symm h34), hF, e1b]; exact ex),
        w3bh_fr_chain _ _ _ 3 (by norm_num) (by
          intro j hj hjk; interval_cases j
          · rw [pow_one, hf2v, hw]; exact nB₂
          · rw [w3bh_pow2, hf2v, hw, e2b, hE]; exact nA₁)
        (by rw [w3bh_pow3, hf2v, hw, e2b, hE, e2 a₁ h12 h14]; exact ex)]
      rw [w3bh_pow3, w3bh_pow3, hf1v, hf2v, hw, e1 b₂ (Ne.symm h14) (Ne.symm h34), hF, e1b, e2b, hE,
        e2 a₁ h12 h14]


/-- **`w3bh_` THE pure core (Φ-free)**: on a one-circle record with the six local occurrences
`a₁,b₁` (of `x`), `a₂,c₁` (of `y`), `b₂,c₂` (of `z`), adjacent in pairs on the three strands, the first
return to the non-local occurrences of the smoothing reconnection `s ∘ (a₁ b₁)` equals that of the
reconnection `s ∘ (a₂ b₂)`.  Cyclic-word check (`(a₁ A b₁ B) ↦ (a₁ B)(b₁ A)` and `(a₂ B')(b₂ A')`): with
`s a₁ = a₂, s b₁ = b₂`: `A = a₂ A''`, `A' = A'' b₁`, `B = b₂ B''`, `B' = B'' a₁`, so the cycles are
`(a₁ b₂ B'')(b₁ a₂ A'')` versus `(a₂ B'' a₁)(b₂ A'' b₁)` — the same cyclic order on `M ∖ L`; the other
three `e/f` patterns likewise (`s a₂ = a₁, s b₁ = b₂`: `(a₁ b₂ B' a₂)(b₁ A)` vs `(a₂ B')(b₂ a₁ A b₁)`;
`s a₁ = a₂, s b₂ = b₁`: `(a₁ B)(b₁ a₂ A' b₂)` vs `(a₂ b₁ B a₁)(b₂ A')`; `s a₂ = a₁, s b₂ = b₁`:
`(a₁ B'' a₂)(b₁ A'' b₂)` vs `(a₂ b₁ B'')(b₂ a₁ A'')`).  The `g`-strand orientation and any adjacency
between the blocks are irrelevant.  OPEN (Unit H, 2026-09-15): stated, not proved; the two consumers are
`w3bh_core_firstReturn` (proved from it) and, in the same cyclic-word terms, `w3bh_core_comp`. -/
theorem w3bh_core_pure (ρ : Record) (hρ : ρ.componentCount = 1) (a₁ a₂ b₁ b₂ c₁ c₂ : ρ.M)
    (hx : ρ.pair a₁ = b₁) (hy : ρ.pair a₂ = c₁) (hz : ρ.pair b₂ = c₂)
    (hxy : ρ.crossingOf a₁ ≠ ρ.crossingOf a₂) (hxz : ρ.crossingOf a₁ ≠ ρ.crossingOf b₂)
    (hyz : ρ.crossingOf a₂ ≠ ρ.crossingOf b₂)
    (hadj_e : ρ.succ a₁ = a₂ ∨ ρ.succ a₂ = a₁) (hadj_f : ρ.succ b₁ = b₂ ∨ ρ.succ b₂ = b₁)
    (hadj_g : ρ.succ c₁ = c₂ ∨ ρ.succ c₂ = c₁)
    (v : ρ.M) (hv : v ≠ a₁ ∧ v ≠ b₁ ∧ v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂) :
    (firstReturn (ρ.succ * Equiv.swap a₁ b₁) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨v, hv⟩).1 =
      (firstReturn (ρ.succ * Equiv.swap a₂ b₂) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨v, hv⟩).1 := by
  -- the six local occurrences are distinct
  have hne : ∀ u w : ρ.M, ρ.crossingOf u ≠ ρ.crossingOf w → u ≠ w := fun u w h h' => h (h' ▸ rfl)
  have hcb₁ : ρ.crossingOf b₁ = ρ.crossingOf a₁ := by rw [← hx, ρ.crossingOf_pair]
  have h13 : a₁ ≠ b₁ := by rw [← hx]; exact ρ.ne_pair a₁
  have h12 : a₁ ≠ a₂ := hne _ _ hxy
  have h14 : a₁ ≠ b₂ := hne _ _ hxz
  have h24 : a₂ ≠ b₂ := hne _ _ hyz
  have h23 : a₂ ≠ b₁ := hne _ _ (by rw [hcb₁]; exact hxy.symm)
  have h34 : b₁ ≠ b₂ := hne _ _ (by rw [hcb₁]; exact hxz)
  -- peel off `c₁, c₂`: the first return to `N` is the first return of the first return to `P`
  have hNsplit : ∀ u : ρ.M, (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) u ↔ (fun u => (u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) ∧ (u ≠ c₁ ∧ u ≠ c₂)) u := by
    intro u; simp only; tauto
  have hv₀ : (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) v := ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.2.1⟩
  have key : firstReturn (ρ.succ * Equiv.swap a₁ b₁) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) = firstReturn (ρ.succ * Equiv.swap a₂ b₂) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) := by
    ext m
    exact w3bh_core_pure₀ ρ hρ a₁ a₂ b₁ b₂ h12 h13 h14 h23 h24 h34 hadj_e hadj_f m.1 m.2
  have step : ∀ f : Equiv.Perm ρ.M, (firstReturn f (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨v, hv⟩).1 =
      ((firstReturn (firstReturn f (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂)) (fun m => (fun u => u ≠ c₁ ∧ u ≠ c₂) m.1)) ⟨⟨v, hv₀⟩, hv.2.2.2.1, hv.2.2.2.2.2⟩).1.1 := by
    intro f
    rw [firstReturn_congr_pred f (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) (fun u => (u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) ∧ (u ≠ c₁ ∧ u ≠ c₂)) hNsplit ⟨v, hv⟩,
      firstReturn_firstReturn f (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) (fun u => u ≠ c₁ ∧ u ≠ c₂) ⟨⟨v, hv₀⟩, hv.2.2.2.1, hv.2.2.2.2.2⟩]
  rw [step, step, key]


/-- **`w3bh_` core sub-lemma (a), the twisted first return** — THE content of `w3h_record_core`: on the
retained (non-local) occurrences the first return of the reconnected successor `s ∘ (a₁ b₁)` to the
non-local set is carried by `Φ` to the first return of `s' ∘ (Φ a₁, Φ b₁)`.  Since
`s' (Φ v) = Φ (σ (s (σ v)))` this is the pure statement on `ρ`
`firstReturn (s ∘ (a₁ b₁)) N v = firstReturn (s ∘ (a₂ b₂)) N v` (conjugate by `σ`, which fixes the
non-local set pointwise): the smoothing at `x` and the "smoothing" `a₂ ↔ b₂` induce the same
first return on `M ∖ {six local occurrences}`, in each of the four `e/f` orientation patterns (cyclic-word
check: `(a₁ A b₁ B) ↦ (a₁ B)(b₁ A)` versus `(a₂ B')(b₂ A')`, where `A = a₂ A''`, `A' = A'' b₁` when `x`
precedes on both strands, etc.).  The `g`-strand orientation is irrelevant (its two occurrences are
deleted points inside `A` or `B`).  OPEN (Unit H, 2026-09-15): stated, not proved. -/
theorem w3bh_core_firstReturn (ρ ρ' : Record) (hρ : ρ.componentCount = 1) (Φ : ρ.M ≃ ρ'.M)
    (a₁ a₂ b₁ b₂ c₁ c₂ : ρ.M)
    (hx : ρ.pair a₁ = b₁) (hy : ρ.pair a₂ = c₁) (hz : ρ.pair b₂ = c₂)
    (hxy : ρ.crossingOf a₁ ≠ ρ.crossingOf a₂) (hxz : ρ.crossingOf a₁ ≠ ρ.crossingOf b₂)
    (hyz : ρ.crossingOf a₂ ≠ ρ.crossingOf b₂)
    (hadj_e : ρ.succ a₁ = a₂ ∨ ρ.succ a₂ = a₁) (hadj_f : ρ.succ b₁ = b₂ ∨ ρ.succ b₂ = b₁)
    (hadj_g : ρ.succ c₁ = c₂ ∨ ρ.succ c₂ = c₁)
    (hpair : ∀ v, Φ (ρ.pair v) = ρ'.pair (Φ v))
    (hsucc : ∀ v, Φ ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      (ρ.succ ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v))) = ρ'.succ (Φ v))
    (v : ρ.M) (hv : v ≠ a₁ ∧ v ≠ b₁ ∧ v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂)
    (hv' : Φ v ≠ Φ a₁ ∧ Φ v ≠ Φ b₁ ∧ Φ v ≠ Φ a₂ ∧ Φ v ≠ Φ c₁ ∧ Φ v ≠ Φ b₂ ∧ Φ v ≠ Φ c₂) :
    Φ (firstReturn (ρ.reconnect a₁)
        (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨v, hv⟩).1 =
      (firstReturn (ρ'.reconnect (Φ a₁))
        (fun u => u ≠ Φ a₁ ∧ u ≠ Φ b₁ ∧ u ≠ Φ a₂ ∧ u ≠ Φ c₁ ∧ u ≠ Φ b₂ ∧ u ≠ Φ c₂) ⟨Φ v, hv'⟩).1 := by
  -- the six local occurrences are distinct
  have hne : ∀ u w : ρ.M, ρ.crossingOf u ≠ ρ.crossingOf w → u ≠ w := fun u w h h' => h (h' ▸ rfl)
  have hcb₁ : ρ.crossingOf b₁ = ρ.crossingOf a₁ := by rw [← hx, ρ.crossingOf_pair]
  have hcc₁ : ρ.crossingOf c₁ = ρ.crossingOf a₂ := by rw [← hy, ρ.crossingOf_pair]
  have hcc₂ : ρ.crossingOf c₂ = ρ.crossingOf b₂ := by rw [← hz, ρ.crossingOf_pair]
  have h13 : a₁ ≠ b₁ := by rw [← hx]; exact ρ.ne_pair a₁
  have h25 : a₂ ≠ c₁ := by rw [← hy]; exact ρ.ne_pair a₂
  have h46 : b₂ ≠ c₂ := by rw [← hz]; exact ρ.ne_pair b₂
  have h14 : a₁ ≠ b₂ := hne _ _ hxz
  have h24 : a₂ ≠ b₂ := hne _ _ hyz
  have h15 : a₁ ≠ c₁ := hne _ _ (by rw [hcc₁]; exact hxy)
  have h16 : a₁ ≠ c₂ := hne _ _ (by rw [hcc₂]; exact hxz)
  have h23 : a₂ ≠ b₁ := hne _ _ (by rw [hcb₁]; exact hxy.symm)
  have h26 : a₂ ≠ c₂ := hne _ _ (by rw [hcc₂]; exact hyz)
  have h35 : b₁ ≠ c₁ := hne _ _ (by rw [hcb₁, hcc₁]; exact hxy)
  have h36 : b₁ ≠ c₂ := hne _ _ (by rw [hcb₁, hcc₂]; exact hxz)
  have h45 : b₂ ≠ c₁ := hne _ _ (by rw [hcc₁]; exact hyz.symm)
  set σ : Equiv.Perm ρ.M := Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂) with hσ
  have hσσ : ∀ u, σ (σ u) = u :=
    w3bh_swap3_apply_apply a₁ a₂ b₁ b₂ c₁ c₂ h13 h14 h23 h24 h15 h16 h25 h26 h35 h36 h45 h46
  have hσa₁ : σ a₁ = a₂ := by
    rw [hσ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h15 h16,
      Equiv.swap_apply_of_ne_of_ne h13 h14, Equiv.swap_apply_left]
  have hσb₁ : σ b₁ = b₂ := by
    rw [hσ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h35 h36,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h14.symm h24.symm]
  -- `σ` fixes the non-local occurrences, and the non-local set is `σ`-invariant
  have hσfix : ∀ u, (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) u → σ u = u := by
    intro u hu
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hu
    rw [hσ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h4 h6,
      Equiv.swap_apply_of_ne_of_ne h2 h5, Equiv.swap_apply_of_ne_of_ne h1 h3]
  have hNσ : ∀ u, (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) (σ u) ↔ (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) u := by
    intro u
    constructor
    · intro h
      have h' := hσfix _ h
      rw [hσσ] at h'
      rw [h']; exact h
    · intro h; rw [hσfix u h]; exact h
  -- the reconnections
  have hrec : ρ.reconnect a₁ = ρ.succ * Equiv.swap a₁ b₁ := by unfold Record.reconnect; rw [hx]
  have hrec' : ρ'.reconnect (Φ a₁) = ρ'.succ * Equiv.swap (Φ a₁) (Φ b₁) := by
    unfold Record.reconnect; rw [← hpair, hx]
  -- `Φ` intertwines the `σ`-conjugate `r̃ = σ (s ∘ (a₂ b₂)) σ` with `s' ∘ (Φ a₁, Φ b₁)`
  have hΦr : ∀ u, Φ ((σ * (ρ.succ * Equiv.swap a₂ b₂) * σ) u) = ρ'.reconnect (Φ a₁) (Φ u) := by
    intro u
    rw [hrec']
    show Φ (σ ((ρ.succ * Equiv.swap a₂ b₂) (σ u))) = ρ'.succ (Equiv.swap (Φ a₁) (Φ b₁) (Φ u))
    rw [← w3bh_map_swap Φ a₁ b₁ u, ← hsucc]
    show Φ (σ (ρ.succ (Equiv.swap a₂ b₂ (σ u)))) = Φ (σ (ρ.succ (σ (Equiv.swap a₁ b₁ u))))
    have h := congrArg (fun π : Equiv.Perm ρ.M => π u) (Equiv.mul_swap_eq_swap_mul σ a₁ b₁)
    simp only [Equiv.Perm.mul_apply, hσa₁, hσb₁] at h
    rw [h]
  have hp : ∀ u, (fun u => u ≠ Φ a₁ ∧ u ≠ Φ b₁ ∧ u ≠ Φ a₂ ∧ u ≠ Φ c₁ ∧ u ≠ Φ b₂ ∧ u ≠ Φ c₂) (Φ u) ↔ (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) u := by
    intro u; simp only [Ne, Φ.apply_eq_iff_eq]
  have step1 : (firstReturn (ρ'.reconnect (Φ a₁)) (fun u => u ≠ Φ a₁ ∧ u ≠ Φ b₁ ∧ u ≠ Φ a₂ ∧ u ≠ Φ c₁ ∧ u ≠ Φ b₂ ∧ u ≠ Φ c₂) ⟨Φ v, hv'⟩).1 =
      Φ (firstReturn (σ * (ρ.succ * Equiv.swap a₂ b₂) * σ) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨v, hv⟩).1 :=
    firstReturn_map_val Φ (σ * (ρ.succ * Equiv.swap a₂ b₂) * σ) (ρ'.reconnect (Φ a₁)) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) (fun u => u ≠ Φ a₁ ∧ u ≠ Φ b₁ ∧ u ≠ Φ a₂ ∧ u ≠ Φ c₁ ∧ u ≠ Φ b₂ ∧ u ≠ Φ c₂) hΦr hp ⟨v, hv⟩
  -- conjugation by `σ` does not change the first return on the (pointwise fixed) non-local set
  have step2 : (firstReturn (σ * (ρ.succ * Equiv.swap a₂ b₂) * σ) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨v, hv⟩).1 =
      (firstReturn (ρ.succ * Equiv.swap a₂ b₂) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨v, hv⟩).1 := by
    have hg : ∀ u, σ ((ρ.succ * Equiv.swap a₂ b₂) u) = (σ * (ρ.succ * Equiv.swap a₂ b₂) * σ) (σ u) := by
      intro u
      show σ ((ρ.succ * Equiv.swap a₂ b₂) u) = σ ((ρ.succ * Equiv.swap a₂ b₂) (σ (σ u)))
      rw [hσσ]
    have h := firstReturn_map_val σ (ρ.succ * Equiv.swap a₂ b₂) (σ * (ρ.succ * Equiv.swap a₂ b₂) * σ)
      (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) hg hNσ ⟨v, hv⟩
    have hσv : (⟨σ v, (hNσ v).mpr hv⟩ : {u // (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) u}) = ⟨v, hv⟩ := Subtype.ext (hσfix v hv)
    rw [hσv] at h
    rw [h]
    exact hσfix _ (firstReturn (ρ.succ * Equiv.swap a₂ b₂) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨v, hv⟩).2
  rw [step1, step2, hrec]
  exact congrArg Φ (w3bh_core_pure ρ hρ a₁ a₂ b₁ b₂ c₁ c₂ hx hy hz hxy hxz hyz hadj_e hadj_f hadj_g v hv)

/-- `w3bh_` helper: a set closed under `f` contains the whole `f`-cycle of each of its points. -/
theorem w3bh_sameCycle_closed {α : Type*} [Finite α] (f : Equiv.Perm α) (S : α → Prop)
    (hS : ∀ x, S x → S (f x)) {x v : α} (hx : S x) (h : f.SameCycle x v) : S v := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have key : ∀ n : ℕ, S ((f ^ n) x) := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hS _ ih
  rw [← hn]; exact key n

/-- **`w3bh_` the pure component core (Φ-free)**, companion of `w3bh_core_pure`: the cycles of the smoothing
reconnection `s ∘ (a₁ b₁)` and of the reconnection `s ∘ (a₂ b₂)` induce the same partition of the non-local
occurrences — a bijection of the two-element cycle sets (`mul_swap_sameCycle_or`,
`not_mul_swap_sameCycle_of_sameCycle`) fixing the class of every non-local `v`.  PROVED (Unit H, 2026-09-15):
the induced permutations on the retained set agree (`w3bh_core_pure₀`), so cycle classes of retained points
transfer (`firstReturn_sameCycle_iff`); the class of `a₁` (resp. `a₂`) is followed to its exit `s b₂` (`s b₁` when
`s b₂ = b₁`) by `sameCycle_apply_right`; a non-retained exit closes a local cycle containing no retained point
(`w3bh_sameCycle_closed`) or contradicts predecessor uniqueness / one circle.  `w3bh_core_comp` is derived from it. -/
theorem w3bh_core_comp_pure (ρ : Record) (hρ : ρ.componentCount = 1) (a₁ a₂ b₁ b₂ c₁ c₂ : ρ.M)
    (hx : ρ.pair a₁ = b₁) (hy : ρ.pair a₂ = c₁) (hz : ρ.pair b₂ = c₂)
    (hxy : ρ.crossingOf a₁ ≠ ρ.crossingOf a₂) (hxz : ρ.crossingOf a₁ ≠ ρ.crossingOf b₂)
    (hyz : ρ.crossingOf a₂ ≠ ρ.crossingOf b₂)
    (hadj_e : ρ.succ a₁ = a₂ ∨ ρ.succ a₂ = a₁) (hadj_f : ρ.succ b₁ = b₂ ∨ ρ.succ b₂ = b₁)
    (hadj_g : ρ.succ c₁ = c₂ ∨ ρ.succ c₂ = c₁) :
    ∃ e₀ : Quotient (Equiv.Perm.SameCycle.setoid (ρ.reconnect a₁)) ≃
        Quotient (Equiv.Perm.SameCycle.setoid (ρ.succ * Equiv.swap a₂ b₂)),
      ∀ v : ρ.M, (v ≠ a₁ ∧ v ≠ b₁ ∧ v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂) →
        e₀ (Quotient.mk _ v) = Quotient.mk _ v := by
  have hne : ∀ u w : ρ.M, ρ.crossingOf u ≠ ρ.crossingOf w → u ≠ w := fun u w h h' => h (h' ▸ rfl)
  have hcb₁ : ρ.crossingOf b₁ = ρ.crossingOf a₁ := by rw [← hx, ρ.crossingOf_pair]
  have h13 : a₁ ≠ b₁ := by rw [← hx]; exact ρ.ne_pair a₁
  have h12 : a₁ ≠ a₂ := hne _ _ hxy
  have h14 : a₁ ≠ b₂ := hne _ _ hxz
  have h24 : a₂ ≠ b₂ := hne _ _ hyz
  have h23 : a₂ ≠ b₁ := hne _ _ (by rw [hcb₁]; exact hxy.symm)
  have h34 : b₁ ≠ b₂ := hne _ _ (by rw [hcb₁]; exact hxz)
  have hrec : ρ.reconnect a₁ = ρ.succ * Equiv.swap a₁ b₁ := by unfold Record.reconnect; rw [hx]
  rw [hrec]
  -- evaluations of the two reconnections
  have e1 : ∀ u, u ≠ a₁ → u ≠ b₁ → (ρ.succ * Equiv.swap a₁ b₁) u = ρ.succ u := fun u h1 h2 => by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have e1a : (ρ.succ * Equiv.swap a₁ b₁) a₁ = ρ.succ b₁ := by rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have e2 : ∀ u, u ≠ a₂ → u ≠ b₂ → (ρ.succ * Equiv.swap a₂ b₂) u = ρ.succ u := fun u h1 h2 => by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have e2a : (ρ.succ * Equiv.swap a₂ b₂) a₂ = ρ.succ b₂ := by rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  -- the induced permutations on the retained set agree (`w3bh_core_pure₀`), so cycle classes transfer
  have hF : firstReturn (ρ.succ * Equiv.swap a₁ b₁) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) = firstReturn (ρ.succ * Equiv.swap a₂ b₂) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) := by
    ext m
    exact w3bh_core_pure₀ ρ hρ a₁ a₂ b₁ b₂ h12 h13 h14 h23 h24 h34 hadj_e hadj_f m.1 m.2
  have transfer : ∀ u w, (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) u → (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) w → ((ρ.succ * Equiv.swap a₁ b₁).SameCycle u w ↔ (ρ.succ * Equiv.swap a₂ b₂).SameCycle u w) := by
    intro u w hu hw
    have h1 := firstReturn_sameCycle_iff (ρ.succ * Equiv.swap a₁ b₁) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) ⟨u, hu⟩ ⟨w, hw⟩
    have h2 := firstReturn_sameCycle_iff (ρ.succ * Equiv.swap a₂ b₂) (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) ⟨u, hu⟩ ⟨w, hw⟩
    rw [hF] at h1
    exact h1.symm.trans h2
  -- the class of `a₁` under `f₁` and of `a₂` under `f₂` agree on the retained occurrences
  have key : ∀ v, (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) v → ((ρ.succ * Equiv.swap a₁ b₁).SameCycle v a₁ ↔ (ρ.succ * Equiv.swap a₂ b₂).SameCycle v a₂) := by
    intro v hv
    obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
    rcases hadj_f with hF1 | hF2
    · -- `s b₁ = b₂`: both classes continue at `s b₂`
      have t1 : (ρ.succ * Equiv.swap a₁ b₁).SameCycle v a₁ ↔ (ρ.succ * Equiv.swap a₁ b₁).SameCycle v ((ρ.succ * Equiv.swap a₁ b₁) a₁) := Equiv.Perm.sameCycle_apply_right.symm
      rw [e1a, hF1] at t1
      have t2 : (ρ.succ * Equiv.swap a₁ b₁).SameCycle v b₂ ↔ (ρ.succ * Equiv.swap a₁ b₁).SameCycle v ((ρ.succ * Equiv.swap a₁ b₁) b₂) := Equiv.Perm.sameCycle_apply_right.symm
      rw [e1 b₂ (Ne.symm h14) (Ne.symm h34)] at t2
      have u1 : (ρ.succ * Equiv.swap a₂ b₂).SameCycle v a₂ ↔ (ρ.succ * Equiv.swap a₂ b₂).SameCycle v ((ρ.succ * Equiv.swap a₂ b₂) a₂) := Equiv.Perm.sameCycle_apply_right.symm
      rw [e2a] at u1
      rw [t1, t2, u1]
      by_cases hβ : (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) (ρ.succ b₂)
      · exact transfer v _ ⟨hv1, hv2, hv3, hv4⟩ hβ
      · have hβ' : ρ.succ b₂ = a₁ ∨ ρ.succ b₂ = b₁ ∨ ρ.succ b₂ = a₂ ∨ ρ.succ b₂ = b₂ := by
          by_contra hc
          push Not at hc
          exact hβ ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
        rcases hβ' with hβ | hβ | hβ | hβ
        · rcases hadj_e with hE1 | hE2
          · rw [hβ]
            apply iff_of_false
            · intro h
              have := w3bh_sameCycle_closed (ρ.succ * Equiv.swap a₁ b₁) (fun u => u = a₁ ∨ u = b₂) (by
                  rintro u (hu | hu)
                  · rw [hu]; right; rw [e1a, hF1]
                  · rw [hu]; left; rw [e1 b₂ (Ne.symm h14) (Ne.symm h34), hβ]) (Or.inl rfl) h.symm
              rcases this with h' | h'
              · exact hv1 h'
              · exact hv4 h'
            · intro h
              have := w3bh_sameCycle_closed (ρ.succ * Equiv.swap a₂ b₂) (fun u => u = a₂ ∨ u = a₁) (by
                  rintro u (hu | hu)
                  · rw [hu]; right; rw [e2a, hβ]
                  · rw [hu]; left; rw [e2 a₁ h12 h14, hE1]) (Or.inr rfl) h.symm
              rcases this with h' | h'
              · exact hv3 h'
              · exact hv1 h'
          · exact absurd (ρ.succ.injective (hβ.trans hE2.symm)) (Ne.symm h24)
        · exact (w3bh_no_two_cycle ρ hρ b₁ b₂ v hF1 hβ hv2 hv4).elim
        · rcases hadj_e with hE1 | hE2
          · exact absurd (ρ.succ.injective (hβ.trans hE1.symm)) (Ne.symm h14)
          · rw [hβ]
            apply iff_of_false
            · intro h
              have := w3bh_sameCycle_closed (ρ.succ * Equiv.swap a₁ b₁) (fun u => u = a₁ ∨ u = b₂ ∨ u = a₂) (by
                  rintro u (hu | hu | hu)
                  · rw [hu]; right; left; rw [e1a, hF1]
                  · rw [hu]; right; right; rw [e1 b₂ (Ne.symm h14) (Ne.symm h34), hβ]
                  · rw [hu]; left; rw [e1 a₂ (Ne.symm h12) h23, hE2]) (Or.inr (Or.inr rfl)) h.symm
              rcases this with h' | h' | h'
              · exact hv1 h'
              · exact hv4 h'
              · exact hv3 h'
            · intro h
              have := w3bh_sameCycle_closed (ρ.succ * Equiv.swap a₂ b₂) (fun u => u = a₂) (by
                  rintro u hu; rw [hu, e2a, hβ]) rfl h.symm
              exact hv3 this
        · exact (w3bh_no_fixed ρ hρ b₂ v hβ hv4).elim
    · -- `s b₂ = b₁`: both classes continue at `s b₁`
      have t1 : (ρ.succ * Equiv.swap a₁ b₁).SameCycle v a₁ ↔ (ρ.succ * Equiv.swap a₁ b₁).SameCycle v ((ρ.succ * Equiv.swap a₁ b₁) a₁) := Equiv.Perm.sameCycle_apply_right.symm
      rw [e1a] at t1
      have u1 : (ρ.succ * Equiv.swap a₂ b₂).SameCycle v a₂ ↔ (ρ.succ * Equiv.swap a₂ b₂).SameCycle v ((ρ.succ * Equiv.swap a₂ b₂) a₂) := Equiv.Perm.sameCycle_apply_right.symm
      rw [e2a, hF2] at u1
      have u2 : (ρ.succ * Equiv.swap a₂ b₂).SameCycle v b₁ ↔ (ρ.succ * Equiv.swap a₂ b₂).SameCycle v ((ρ.succ * Equiv.swap a₂ b₂) b₁) := Equiv.Perm.sameCycle_apply_right.symm
      rw [e2 b₁ (Ne.symm h23) h34] at u2
      rw [t1, u1, u2]
      by_cases hγ : (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) (ρ.succ b₁)
      · exact transfer v _ ⟨hv1, hv2, hv3, hv4⟩ hγ
      · have hγ' : ρ.succ b₁ = a₁ ∨ ρ.succ b₁ = b₁ ∨ ρ.succ b₁ = a₂ ∨ ρ.succ b₁ = b₂ := by
          by_contra hc
          push Not at hc
          exact hγ ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
        rcases hγ' with hγ | hγ | hγ | hγ
        · rcases hadj_e with hE1 | hE2
          · rw [hγ]
            apply iff_of_false
            · intro h
              have := w3bh_sameCycle_closed (ρ.succ * Equiv.swap a₁ b₁) (fun u => u = a₁) (by
                  rintro u hu; rw [hu, e1a, hγ]) rfl h.symm
              exact hv1 this
            · intro h
              have := w3bh_sameCycle_closed (ρ.succ * Equiv.swap a₂ b₂) (fun u => u = a₂ ∨ u = b₁ ∨ u = a₁) (by
                  rintro u (hu | hu | hu)
                  · rw [hu]; right; left; rw [e2a, hF2]
                  · rw [hu]; right; right; rw [e2 b₁ (Ne.symm h23) h34, hγ]
                  · rw [hu]; left; rw [e2 a₁ h12 h14, hE1]) (Or.inr (Or.inr rfl)) h.symm
              rcases this with h' | h' | h'
              · exact hv3 h'
              · exact hv2 h'
              · exact hv1 h'
          · exact absurd (ρ.succ.injective (hγ.trans hE2.symm)) (Ne.symm h23)
        · exact (w3bh_no_fixed ρ hρ b₁ v hγ hv2).elim
        · rcases hadj_e with hE1 | hE2
          · exact absurd (ρ.succ.injective (hγ.trans hE1.symm)) (Ne.symm h13)
          · rw [hγ]
            apply iff_of_false
            · intro h
              have := w3bh_sameCycle_closed (ρ.succ * Equiv.swap a₁ b₁) (fun u => u = a₁ ∨ u = a₂) (by
                  rintro u (hu | hu)
                  · rw [hu]; right; rw [e1a, hγ]
                  · rw [hu]; left; rw [e1 a₂ (Ne.symm h12) h23, hE2]) (Or.inr rfl) h.symm
              rcases this with h' | h'
              · exact hv1 h'
              · exact hv3 h'
            · intro h
              have := w3bh_sameCycle_closed (ρ.succ * Equiv.swap a₂ b₂) (fun u => u = a₂ ∨ u = b₁) (by
                  rintro u (hu | hu)
                  · rw [hu]; right; rw [e2a, hF2]
                  · rw [hu]; left; rw [e2 b₁ (Ne.symm h23) h34, hγ]) (Or.inl rfl) h.symm
              rcases this with h' | h'
              · exact hv3 h'
              · exact hv2 h'
        · exact (w3bh_no_two_cycle ρ hρ b₁ b₂ v hγ hF2 hv2 hv4).elim
  -- the two-class structure of both reconnections
  have two1 : ∀ u, (ρ.succ * Equiv.swap a₁ b₁).SameCycle u a₁ ∨ (ρ.succ * Equiv.swap a₁ b₁).SameCycle u b₁ := fun u =>
    mul_swap_sameCycle_or ρ.succ a₁ b₁ (ρ.sameCycle_of_one_circle hρ u a₁)
  have two2 : ∀ u, (ρ.succ * Equiv.swap a₂ b₂).SameCycle u a₂ ∨ (ρ.succ * Equiv.swap a₂ b₂).SameCycle u b₂ := fun u =>
    mul_swap_sameCycle_or ρ.succ a₂ b₂ (ρ.sameCycle_of_one_circle hρ u a₂)
  have nab2 : ¬ (ρ.succ * Equiv.swap a₂ b₂).SameCycle a₂ b₂ :=
    not_mul_swap_sameCycle_of_sameCycle ρ.succ a₂ b₂ h24 (ρ.sameCycle_of_one_circle hρ a₂ b₂)
  have nab1 : ¬ (ρ.succ * Equiv.swap a₁ b₁).SameCycle a₁ b₁ :=
    not_mul_swap_sameCycle_of_sameCycle ρ.succ a₁ b₁ h13 (ρ.sameCycle_of_one_circle hρ a₁ b₁)
  classical
  refine ⟨{ toFun := Quotient.lift
              (fun u => if (ρ.succ * Equiv.swap a₁ b₁).SameCycle u a₁ then Quotient.mk _ a₂ else Quotient.mk _ b₂) ?_
            invFun := Quotient.lift
              (fun u => if (ρ.succ * Equiv.swap a₂ b₂).SameCycle u a₂ then Quotient.mk _ a₁ else Quotient.mk _ b₁) ?_
            left_inv := ?_
            right_inv := ?_ }, ?_⟩
  · intro u w huw
    have h : (ρ.succ * Equiv.swap a₁ b₁).SameCycle u a₁ ↔ (ρ.succ * Equiv.swap a₁ b₁).SameCycle w a₁ :=
      ⟨fun h => (huw : (ρ.succ * Equiv.swap a₁ b₁).SameCycle u w).symm.trans h, fun h => (huw : (ρ.succ * Equiv.swap a₁ b₁).SameCycle u w).trans h⟩
    simp only [h]
  · intro u w huw
    have h : (ρ.succ * Equiv.swap a₂ b₂).SameCycle u a₂ ↔ (ρ.succ * Equiv.swap a₂ b₂).SameCycle w a₂ :=
      ⟨fun h => (huw : (ρ.succ * Equiv.swap a₂ b₂).SameCycle u w).symm.trans h, fun h => (huw : (ρ.succ * Equiv.swap a₂ b₂).SameCycle u w).trans h⟩
    simp only [h]
  · intro q
    induction q using Quotient.inductionOn with
    | h u =>
      by_cases h : (ρ.succ * Equiv.swap a₁ b₁).SameCycle u a₁
      · rw [Quotient.lift_mk, if_pos h, Quotient.lift_mk, if_pos (Equiv.Perm.SameCycle.refl _ _)]
        exact Quotient.sound h.symm
      · rw [Quotient.lift_mk, if_neg h, Quotient.lift_mk, if_neg (fun h' => nab2 h'.symm)]
        exact Quotient.sound ((two1 u).resolve_left h).symm
  · intro q
    induction q using Quotient.inductionOn with
    | h u =>
      by_cases h : (ρ.succ * Equiv.swap a₂ b₂).SameCycle u a₂
      · rw [Quotient.lift_mk, if_pos h, Quotient.lift_mk, if_pos (Equiv.Perm.SameCycle.refl _ _)]
        exact Quotient.sound h.symm
      · rw [Quotient.lift_mk, if_neg h, Quotient.lift_mk, if_neg (fun h' => nab1 h'.symm)]
        exact Quotient.sound ((two2 u).resolve_left h).symm
  · intro v hv
    have hP : (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ b₂) v := ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.2.1⟩
    rw [Equiv.coe_fn_mk]
    by_cases h : (ρ.succ * Equiv.swap a₁ b₁).SameCycle v a₁
    · rw [Quotient.lift_mk, if_pos h]
      exact Quotient.sound ((key v hP).mp h).symm
    · rw [Quotient.lift_mk, if_neg h]
      have h2 : ¬ (ρ.succ * Equiv.swap a₂ b₂).SameCycle v a₂ := fun h' => h ((key v hP).mpr h')
      exact Quotient.sound ((two2 v).resolve_left h2).symm


/-- **`w3bh_` core sub-lemma (b), the component bijection**: the two cycles of `s ∘ (a₁ b₁)` (the
smoothing of a self-crossing of the single circle, `componentCount_smooth_of_self`) are the classes of
`a₁` and of `b₁` (`reconnect_sameCycle_or`, `not_reconnect_sameCycle_pair_of_self`), likewise on `ρ'`;
`e := [a₁] ↦ [Φ a₁], [b₁] ↦ [Φ b₁]` (crossing-free circles: none, one component with occurrences), and a
retained `v` lies on the cycle of `a₁` iff `Φ v` lies on the cycle of `Φ a₁` (the same cyclic-word check as
in (a): `v ∈ B''` on both sides).  OPEN (Unit H, 2026-09-15): stated, not proved. -/
theorem w3bh_core_comp (ρ ρ' : Record) (hρ : ρ.componentCount = 1) (hρ' : ρ'.componentCount = 1)
    (Φ : ρ.M ≃ ρ'.M) (a₁ a₂ b₁ b₂ c₁ c₂ : ρ.M)
    (hx : ρ.pair a₁ = b₁) (hy : ρ.pair a₂ = c₁) (hz : ρ.pair b₂ = c₂)
    (hxy : ρ.crossingOf a₁ ≠ ρ.crossingOf a₂) (hxz : ρ.crossingOf a₁ ≠ ρ.crossingOf b₂)
    (hyz : ρ.crossingOf a₂ ≠ ρ.crossingOf b₂)
    (hadj_e : ρ.succ a₁ = a₂ ∨ ρ.succ a₂ = a₁) (hadj_f : ρ.succ b₁ = b₂ ∨ ρ.succ b₂ = b₁)
    (hadj_g : ρ.succ c₁ = c₂ ∨ ρ.succ c₂ = c₁)
    (hpair : ∀ v, Φ (ρ.pair v) = ρ'.pair (Φ v))
    (hsucc : ∀ v, Φ ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      (ρ.succ ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v))) = ρ'.succ (Φ v)) :
    ∃ e : (ρ.smooth a₁).comps ≃ (ρ'.smooth (Φ a₁)).comps,
      ∀ (v : ρ.M) (hv : ρ.SmoothKeep a₁ v) (hv' : ρ'.SmoothKeep (Φ a₁) (Φ v)),
        (v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂) →
        (ρ'.smooth (Φ a₁)).comp ⟨Φ v, hv'⟩ = e ((ρ.smooth a₁).comp ⟨v, hv⟩) := by
  -- the six local occurrences are distinct (as in `w3bh_core_firstReturn`)
  have hne : ∀ u w : ρ.M, ρ.crossingOf u ≠ ρ.crossingOf w → u ≠ w := fun u w h h' => h (h' ▸ rfl)
  have hcb₁ : ρ.crossingOf b₁ = ρ.crossingOf a₁ := by rw [← hx, ρ.crossingOf_pair]
  have hcc₁ : ρ.crossingOf c₁ = ρ.crossingOf a₂ := by rw [← hy, ρ.crossingOf_pair]
  have hcc₂ : ρ.crossingOf c₂ = ρ.crossingOf b₂ := by rw [← hz, ρ.crossingOf_pair]
  have h13 : a₁ ≠ b₁ := by rw [← hx]; exact ρ.ne_pair a₁
  have h25 : a₂ ≠ c₁ := by rw [← hy]; exact ρ.ne_pair a₂
  have h46 : b₂ ≠ c₂ := by rw [← hz]; exact ρ.ne_pair b₂
  have h14 : a₁ ≠ b₂ := hne _ _ hxz
  have h24 : a₂ ≠ b₂ := hne _ _ hyz
  have h15 : a₁ ≠ c₁ := hne _ _ (by rw [hcc₁]; exact hxy)
  have h16 : a₁ ≠ c₂ := hne _ _ (by rw [hcc₂]; exact hxz)
  have h23 : a₂ ≠ b₁ := hne _ _ (by rw [hcb₁]; exact hxy.symm)
  have h26 : a₂ ≠ c₂ := hne _ _ (by rw [hcc₂]; exact hyz)
  have h35 : b₁ ≠ c₁ := hne _ _ (by rw [hcb₁, hcc₁]; exact hxy)
  have h36 : b₁ ≠ c₂ := hne _ _ (by rw [hcb₁, hcc₂]; exact hxz)
  have h45 : b₂ ≠ c₁ := hne _ _ (by rw [hcc₁]; exact hyz.symm)
  set σ : Equiv.Perm ρ.M := Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂) with hσ
  have hσsq : σ * σ = 1 :=
    w3bh_swap3_sq a₁ a₂ b₁ b₂ c₁ c₂ h13 h14 h23 h24 h15 h16 h25 h26 h35 h36 h45 h46
  have hσσ : ∀ u, σ (σ u) = u :=
    w3bh_swap3_apply_apply a₁ a₂ b₁ b₂ c₁ c₂ h13 h14 h23 h24 h15 h16 h25 h26 h35 h36 h45 h46
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσsq
  have hσa₁ : σ a₁ = a₂ := by
    rw [hσ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h15 h16,
      Equiv.swap_apply_of_ne_of_ne h13 h14, Equiv.swap_apply_left]
  have hσb₁ : σ b₁ = b₂ := by
    rw [hσ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h35 h36,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h14.symm h24.symm]
  have hσfix : ∀ u, (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) u → σ u = u := by
    intro u hu
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hu
    rw [hσ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h4 h6,
      Equiv.swap_apply_of_ne_of_ne h2 h5, Equiv.swap_apply_of_ne_of_ne h1 h3]
  have hrec' : ρ'.reconnect (Φ a₁) = ρ'.succ * Equiv.swap (Φ a₁) (Φ b₁) := by
    unfold Record.reconnect; rw [← hpair, hx]
  have hΦr : ∀ u, Φ ((σ * (ρ.succ * Equiv.swap a₂ b₂) * σ) u) = ρ'.reconnect (Φ a₁) (Φ u) := by
    intro u
    rw [hrec']
    show Φ (σ ((ρ.succ * Equiv.swap a₂ b₂) (σ u))) = ρ'.succ (Equiv.swap (Φ a₁) (Φ b₁) (Φ u))
    rw [← w3bh_map_swap Φ a₁ b₁ u, ← hsucc]
    show Φ (σ (ρ.succ (Equiv.swap a₂ b₂ (σ u)))) = Φ (σ (ρ.succ (σ (Equiv.swap a₁ b₁ u))))
    have h := congrArg (fun π : Equiv.Perm ρ.M => π u) (Equiv.mul_swap_eq_swap_mul σ a₁ b₁)
    simp only [Equiv.Perm.mul_apply, hσa₁, hσb₁] at h
    rw [h]
  -- the non-local predicate
  have hN : ∀ v : ρ.M, ρ.SmoothKeep a₁ v → (v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂) → (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) v := by
    intro v hv hQ
    rw [Record.smoothKeep_iff, hx] at hv
    exact ⟨hv.1, hv.2, hQ⟩
  -- crossing-free circles: none on a one-circle record with an occurrence
  have hfree : ∀ (τ : Record) (hτ : τ.componentCount = 1) (u : τ.M), IsEmpty τ.FreeComp := by
    intro τ hτ u
    refine ⟨fun c => c.2 u ?_⟩
    obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hτ
    rw [hx (τ.comp u), hx c.1]
  have := hfree ρ hρ a₁
  have := hfree ρ' hρ' (Φ a₁)
  -- the pure core and the two transports of the cycle quotients
  obtain ⟨e₀, he₀⟩ := w3bh_core_comp_pure ρ hρ a₁ a₂ b₁ b₂ c₁ c₂ hx hy hz hxy hxz hyz hadj_e hadj_f hadj_g
  have hconj : ∀ u w, (ρ.succ * Equiv.swap a₂ b₂).SameCycle u w ↔
      (σ * (ρ.succ * Equiv.swap a₂ b₂) * σ).SameCycle (σ u) (σ w) := by
    intro u w
    have h := Equiv.Perm.sameCycle_conj (g := σ) (f := ρ.succ * Equiv.swap a₂ b₂) (x := σ u) (y := σ w)
    rw [hσinv, hσσ, hσσ] at h
    exact h.symm
  let qσ : Quotient (Equiv.Perm.SameCycle.setoid (ρ.succ * Equiv.swap a₂ b₂)) ≃
      Quotient (Equiv.Perm.SameCycle.setoid (σ * (ρ.succ * Equiv.swap a₂ b₂) * σ)) := Quotient.congr σ hconj
  let qΦ : Quotient (Equiv.Perm.SameCycle.setoid (σ * (ρ.succ * Equiv.swap a₂ b₂) * σ)) ≃
      Quotient (Equiv.Perm.SameCycle.setoid (ρ'.reconnect (Φ a₁))) :=
    Quotient.congr Φ (fun u w => (sameCycle_map_iff Φ _ _ hΦr u w).symm)
  refine ⟨Equiv.sumCongr (e₀.trans (qσ.trans qΦ)) (Equiv.equivOfIsEmpty _ _), ?_⟩
  intro v hv hv' hQ
  have hNv := hN v hv hQ
  show Sum.inl (Quotient.mk _ (Φ v)) =
    Equiv.sumCongr (e₀.trans (qσ.trans qΦ)) (Equiv.equivOfIsEmpty _ _) (Sum.inl (Quotient.mk _ v))
  rw [Equiv.sumCongr_apply, Sum.map_inl, Equiv.trans_apply, he₀ v hNv, Equiv.trans_apply]
  show Sum.inl (Quotient.mk _ (Φ v)) = Sum.inl (Quotient.mk _ (Φ (σ v)))
  rw [hσfix v hNv]


/-- **(h) sub-leaf — the record core**: two one-circle records `ρ, ρ'` whose occurrences correspond by `Φ`
preserving pairing, bits and signs and the successor TWISTED by the three transpositions
`σ = (a₁ a₂)(b₁ b₂)(c₁ c₂)` on the six local occurrences (`Φ (σ (s (σ v))) = s' (Φ v)`, the successor form
of `G11_core_statement`'s cyclic clause) — `a₁,b₁` the occurrences of `x` on `e, f`; `a₂,c₁` of `y` on `e, g`;
`b₂,c₂` of `z` on `f, g`; on each strand the two local occurrences adjacent (R-LOC (2),
`LocalizationData.adjacent`).  After smoothing at `x` (`Record.smooth a₁`) and deleting the crossings of
`y, z` (`restrictCrossings`), the two records are isomorphic.  Sketch: the retained occurrences are the
non-local ones, on which `Φ` is a bijection; for a retained `u` the first return of the reconnected
successor `s₁ = s ∘ swap a₁ b₁` to the retained set passes through at most one local strand-pair and
reconnects `pred(a₁) ↦ succ(b₂)`, `pred(b₁) ↦ succ(a₂)` when `x` precedes on both strands, etc. — the
eight orientation patterns (`hadj_*`) each give the SAME first-return on both sides (verified case by
case in the report); components: the cycles of `s₁` correspond under `Φ` (two cycles: the smoothing of a
self-crossing of one circle, `Record.componentCount_smooth`), `RecordIso.ofOcc`-style assembly with
`firstReturn_no_between`/`cycNext_unique_on`.  ≈ 1.2k lines. -/
theorem w3h_record_core (ρ ρ' : Record) (hρ : ρ.componentCount = 1) (hρ' : ρ'.componentCount = 1)
    (Φ : ρ.M ≃ ρ'.M) (a₁ a₂ b₁ b₂ c₁ c₂ : ρ.M)
    (hx : ρ.pair a₁ = b₁) (hy : ρ.pair a₂ = c₁) (hz : ρ.pair b₂ = c₂)
    (hxy : ρ.crossingOf a₁ ≠ ρ.crossingOf a₂) (hxz : ρ.crossingOf a₁ ≠ ρ.crossingOf b₂)
    (hyz : ρ.crossingOf a₂ ≠ ρ.crossingOf b₂)
    (hadj_e : ρ.succ a₁ = a₂ ∨ ρ.succ a₂ = a₁) (hadj_f : ρ.succ b₁ = b₂ ∨ ρ.succ b₂ = b₁)
    (hadj_g : ρ.succ c₁ = c₂ ∨ ρ.succ c₂ = c₁)
    (hpair : ∀ v, Φ (ρ.pair v) = ρ'.pair (Φ v)) (hbit : ∀ v, ρ'.isOver (Φ v) = ρ.isOver v)
    (hsgn : ∀ v, ρ'.sgn (Φ v) = ρ.sgn v)
    (hsucc : ∀ v, Φ ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      (ρ.succ ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v))) = ρ'.succ (Φ v)) :
    Nonempty (RecordIso
      ((ρ.smooth a₁).restrictCrossings {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂})
      ((ρ'.smooth (Φ a₁)).restrictCrossings
        {c | ∀ v ∈ c.1, v.1 ≠ Φ a₂ ∧ v.1 ≠ Φ c₁ ∧ v.1 ≠ Φ b₂ ∧ v.1 ≠ Φ c₂})) := by
  -- the pairing on `ρ'`
  have hx' : ρ'.pair (Φ a₁) = Φ b₁ := by rw [← hpair, hx]
  have hy' : ρ'.pair (Φ a₂) = Φ c₁ := by rw [← hpair, hy]
  have hz' : ρ'.pair (Φ b₂) = Φ c₂ := by rw [← hpair, hz]
  -- the smoothing-retained occurrences correspond
  have hSK : ∀ v, ρ.SmoothKeep a₁ v ↔ ρ'.SmoothKeep (Φ a₁) (Φ v) := by
    intro v
    rw [Record.smoothKeep_iff, Record.smoothKeep_iff, ← hpair, Ne, Ne, Ne, Ne,
      Φ.apply_eq_iff_eq, Φ.apply_eq_iff_eq]
  let Φ₁ : (ρ.smooth a₁).M ≃ (ρ'.smooth (Φ a₁)).M := Equiv.subtypeEquiv Φ hSK
  -- the deletion-retained occurrences correspond
  have hQ := w3bh_crossKeep_iff ρ a₁ a₂ b₂ c₁ c₂ hy hz
  have hQ' := w3bh_crossKeep_iff ρ' (Φ a₁) (Φ a₂) (Φ b₂) (Φ c₁) (Φ c₂) hy' hz'
  have hRK : ∀ w : (ρ.smooth a₁).M,
      (ρ.smooth a₁).CrossKeep {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂} w ↔
      (ρ'.smooth (Φ a₁)).CrossKeep {c | ∀ v ∈ c.1, v.1 ≠ Φ a₂ ∧ v.1 ≠ Φ c₁ ∧ v.1 ≠ Φ b₂ ∧ v.1 ≠ Φ c₂}
        (Φ₁ w) := by
    intro w
    rw [hQ, hQ']
    show _ ↔ (Φ w.1 ≠ Φ a₂ ∧ Φ w.1 ≠ Φ c₁ ∧ Φ w.1 ≠ Φ b₂ ∧ Φ w.1 ≠ Φ c₂)
    simp only [Ne, Φ.apply_eq_iff_eq]
  let Φ₂ := Equiv.subtypeEquiv Φ₁ hRK
  -- the component bijection
  obtain ⟨e, he⟩ := w3bh_core_comp ρ ρ' hρ hρ' Φ a₁ a₂ b₁ b₂ c₁ c₂ hx hy hz hxy hxz hyz hadj_e hadj_f
    hadj_g hpair hsucc
  -- the non-local predicate
  have hN : ∀ v : ρ.M, (ρ.SmoothKeep a₁ v ∧ (v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂)) ↔
      (v ≠ a₁ ∧ v ≠ b₁ ∧ v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂) := by
    intro v; rw [Record.smoothKeep_iff, hx, and_assoc]
  have hN' : ∀ v : ρ'.M, (ρ'.SmoothKeep (Φ a₁) v ∧ (v ≠ Φ a₂ ∧ v ≠ Φ c₁ ∧ v ≠ Φ b₂ ∧ v ≠ Φ c₂)) ↔
      (v ≠ Φ a₁ ∧ v ≠ Φ b₁ ∧ v ≠ Φ a₂ ∧ v ≠ Φ c₁ ∧ v ≠ Φ b₂ ∧ v ≠ Φ c₂) := by
    intro v; rw [Record.smoothKeep_iff, hx', and_assoc]
  -- the successor of a doubly restricted record is the first return to the non-local set
  have hred : ∀ (τ : Record) (a₁ a₂ b₁ b₂ c₁ c₂ : τ.M) (hx : τ.pair a₁ = b₁) (hy : τ.pair a₂ = c₁)
      (hz : τ.pair b₂ = c₂)
      (w : ((τ.smooth a₁).restrictCrossings
        {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂}).M)
      (hw : w.1.1 ≠ a₁ ∧ w.1.1 ≠ b₁ ∧ w.1.1 ≠ a₂ ∧ w.1.1 ≠ c₁ ∧ w.1.1 ≠ b₂ ∧ w.1.1 ≠ c₂),
      (((τ.smooth a₁).restrictCrossings
        {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂}).succ w).1.1 =
      (firstReturn (τ.reconnect a₁)
        (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) ⟨w.1.1, hw⟩).1 := by
    intro τ a₁ a₂ b₁ b₂ c₁ c₂ hx hy hz w hw
    have hQτ := w3bh_crossKeep_iff τ a₁ a₂ b₂ c₁ c₂ hy hz
    have hNτ : ∀ v : τ.M, (τ.SmoothKeep a₁ v ∧ (v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂)) ↔
        (v ≠ a₁ ∧ v ≠ b₁ ∧ v ≠ a₂ ∧ v ≠ c₁ ∧ v ≠ b₂ ∧ v ≠ c₂) := by
      intro v; rw [Record.smoothKeep_iff, hx, and_assoc]
    have h1 := firstReturn_congr_pred (τ.smooth a₁).succ
      ((τ.smooth a₁).CrossKeep {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂})
      (fun m => m.1 ≠ a₂ ∧ m.1 ≠ c₁ ∧ m.1 ≠ b₂ ∧ m.1 ≠ c₂) hQτ w
    have h2 := firstReturn_firstReturn (τ.reconnect a₁) (τ.SmoothKeep a₁)
      (fun m => m ≠ a₂ ∧ m ≠ c₁ ∧ m ≠ b₂ ∧ m ≠ c₂) ⟨w.1, (hQτ w.1).mp w.2⟩
    have h3 := firstReturn_congr_pred (τ.reconnect a₁)
      (fun m => τ.SmoothKeep a₁ m ∧ (m ≠ a₂ ∧ m ≠ c₁ ∧ m ≠ b₂ ∧ m ≠ c₂))
      (fun u => u ≠ a₁ ∧ u ≠ b₁ ∧ u ≠ a₂ ∧ u ≠ c₁ ∧ u ≠ b₂ ∧ u ≠ c₂) hNτ
      ⟨w.1.1, w.1.2, (hQτ w.1).mp w.2⟩
    exact (congrArg Subtype.val h1).trans (h2.trans h3)
  refine ⟨{ e := e, Φ := Φ₂, comp_eq := ?_, succ_eq := ?_, pair_eq := ?_, bit_eq := ?_, sgn_eq := ?_ }⟩
  · intro w
    exact he w.1.1 w.1.2 ((hSK w.1.1).mp w.1.2) ((hQ w.1).mp w.2)
  · intro w
    apply Subtype.ext; apply Subtype.ext
    have hw : w.1.1 ≠ a₁ ∧ w.1.1 ≠ b₁ ∧ w.1.1 ≠ a₂ ∧ w.1.1 ≠ c₁ ∧ w.1.1 ≠ b₂ ∧ w.1.1 ≠ c₂ :=
      (hN w.1.1).mp ⟨w.1.2, (hQ w.1).mp w.2⟩
    have hw' : Φ w.1.1 ≠ Φ a₁ ∧ Φ w.1.1 ≠ Φ b₁ ∧ Φ w.1.1 ≠ Φ a₂ ∧ Φ w.1.1 ≠ Φ c₁ ∧ Φ w.1.1 ≠ Φ b₂ ∧
        Φ w.1.1 ≠ Φ c₂ := by
      simp only [Ne, Φ.apply_eq_iff_eq]; exact hw
    show Φ (((ρ.smooth a₁).restrictCrossings _).succ w).1.1 =
      (((ρ'.smooth (Φ a₁)).restrictCrossings _).succ (Φ₂ w)).1.1
    rw [hred ρ a₁ a₂ b₁ b₂ c₁ c₂ hx hy hz w hw,
      hred ρ' (Φ a₁) (Φ a₂) (Φ b₁) (Φ b₂) (Φ c₁) (Φ c₂) hx' hy' hz' (Φ₂ w) hw']
    exact w3bh_core_firstReturn ρ ρ' hρ Φ a₁ a₂ b₁ b₂ c₁ c₂ hx hy hz hxy hxz hyz hadj_e hadj_f hadj_g
      hpair hsucc w.1.1 hw hw'
  · intro w
    apply Subtype.ext; apply Subtype.ext
    exact hpair w.1.1
  · intro w; exact hbit w.1.1
  · intro w; exact hsgn w.1.1


/-- **(h) sub-leaf — the record bridge with the occurrence correspondence exposed**: the accepted
`smoothDiagram_record` gives SOME record isomorphism `(D^x).record ≅ D.record.smooth (overVisit x)`; the
consumer needs to know that it carries the crossing of `D^x` at a double point to the crossing of `D` at the
same double point (so that `y₀, z₀` go to `y, z`).  Sketch: unfold `smoothDiagram`, `split_ifs`, and read
`selfRecordIso`/`mixedRecordIso`'s `Φ` (built from `crossingEquiv`/`origCrossing`, Smoothing §8): the image
of an occurrence lies over `origCrossing` of its crossing, whose double point is the same
(`crossingPoint_origCrossing`-type lemma of §6).  ≈ 200 lines. -/
theorem w3h_smooth_record_occ (D : Diagram) (x : D.Γ.Crossing) (ε : ℝ) (hε : SmallEps D x ε) :
    ∃ ι : RecordIso (smoothDiagram D x ε hε).record (D.record.smooth (D.overVisit x)),
      ∀ v : (smoothDiagram D x ε hε).Γ.Visit,
        D.Γ.crossingPoint (ι.Φ v).1.1 = (smoothDiagram D x ε hε).Γ.crossingPoint v.1 := by
  unfold smoothDiagram
  by_cases h : (sS D x).1 = (tS D x).1
  · rw [dite_eq_left h]
    refine ⟨selfRecordIso D x hε h, fun v => ?_⟩
    exact (crossingPoint_origCrossing D x (selfModel D x ε h) hε v.1).symm
  · rw [dite_eq_right h]
    refine ⟨mixedRecordIso D x hε h, fun v => ?_⟩
    exact (crossingPoint_origCrossing D x (mixedModel D x ε h) hε v.1).symm


/-- **(h) sub-leaf — switching a DELETED crossing is invisible after the restriction** (companion of
`Record.restrictCrossings_switch`): `Record.switch v` changes only the bits and signs of the two occurrences
of `crossingOf v`, which are not retained; the identity on the retained occurrences is a `RecordIso`
(`firstReturn` of the same successor, same pairing).  ≈ 60 lines. -/
theorem w3h_restrict_switch_deleted (ρ : Record) (S : Set ρ.Crossing) (v : ρ.M)
    (hv : ρ.crossingOf v ∉ S) :
    Nonempty (RecordIso ((ρ.switch v).restrictCrossings S) (ρ.restrictCrossings S)) := by
  have hne : ∀ w : ρ.M, ρ.crossingOf w ∈ S → w ≠ v ∧ w ≠ ρ.pair v := by
    intro w hw
    constructor
    · intro h; exact hv (h ▸ hw)
    · intro h; rw [h, ρ.crossingOf_pair] at hw; exact hv hw
  exact ⟨RecordIso.mk (Equiv.refl _) (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun w => by
      show ρ.isOver w.1 = (ρ.switch v).isOver w.1
      exact (ρ.switch_isOver_of_ne v (hne w.1 w.2).1 (hne w.1 w.2).2).symm)
    (fun w => by
      show ρ.sgn w.1 = (ρ.switch v).sgn w.1
      exact (ρ.switch_sgn_of_ne v (hne w.1 w.2).1 (hne w.1 w.2).2).symm)⟩


/-- `w3bh_` bridge (one side of `w3h_hrec`, D6 glue): the reduced record of a bigon `B` on the switched
smoothing output `(D^x)^{y₀−}` with `B.y = y₀`, `B.z = z₀` at the double points of `y, z`, transported
to the occurrence-defined restriction of `D.record.smooth a₁` (`a₁` either occurrence of `x`):
`switchRecordIso` → `restrictCrossings_iso_of_recordIso` → `w3h_restrict_switch_deleted` →
`w3h_smooth_record_occ` → (`smoothPairIso`). -/
theorem w3bh_reduced_to_smooth (D : Diagram) (x y z : D.Γ.Crossing)
    (a₁ a₂ b₂ c₁ c₂ : D.Γ.Visit) (ha₁ : a₁.1 = x) (ha₂ : a₂.1 = y) (hc₁ : c₁ = D.twin a₂)
    (hb₂ : b₂.1 = z) (hc₂ : c₂ = D.twin b₂)
    {ε : ℝ} (hε : SmallEps D x ε)
    (y₀ z₀ : (smoothDiagram D x ε hε).Γ.Crossing)
    (hy₀ : (smoothDiagram D x ε hε).Γ.crossingPoint y₀ = D.Γ.crossingPoint y)
    (hz₀ : (smoothDiagram D x ε hε).Γ.crossingPoint z₀ = D.Γ.crossingPoint z)
    (B : BigonData ((smoothDiagram D x ε hε).switch y₀)) (hBy : B.y = y₀) (hBz : B.z = z₀) :
    Nonempty (RecordIso B.reducedRecord
      ((D.record.smooth a₁).restrictCrossings
        {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂})) := by
  subst hc₁ hc₂
  -- the occurrence-defined retained set on `E = smoothDiagram D x ε hε`
  let X₁ : Set (smoothDiagram D x ε hε).record.Crossing := {c | ∀ w ∈ c.1, w.1 ≠ y₀ ∧ w.1 ≠ z₀}
  have hX₁ : ∀ u : (smoothDiagram D x ε hε).Γ.Visit,
      (smoothDiagram D x ε hε).record.crossingOf u ∈ X₁ ↔ (u.1 ≠ y₀ ∧ u.1 ≠ z₀) := by
    intro u
    rw [w3bh_crossingOf_mem_setOf]
    show (u.1 ≠ y₀ ∧ u.1 ≠ z₀) ∧
      (((smoothDiagram D x ε hε).twin u).1 ≠ y₀ ∧ ((smoothDiagram D x ε hε).twin u).1 ≠ z₀) ↔ _
    rw [Diagram.twin_fst, and_self]
  -- Step A/B: `B.reducedRecord ≅ (E.record.switch v₀).restrictCrossings X₁`
  obtain ⟨ι₂⟩ := w3bh_restrictCrossings_iso_of_recordIso
    ((smoothDiagram D x ε hε).switchRecordIso y₀ ((smoothDiagram D x ε hε).overVisit y₀) rfl) B.keep X₁ (by
    intro u
    show (((smoothDiagram D x ε hε).switch y₀).record.crossingOf u ≠
        ((smoothDiagram D x ε hε).switch y₀).record.crossingOf
          (((smoothDiagram D x ε hε).switch y₀).overVisit B.y) ∧
      ((smoothDiagram D x ε hε).switch y₀).record.crossingOf u ≠
        ((smoothDiagram D x ε hε).switch y₀).record.crossingOf
          (((smoothDiagram D x ε hε).switch y₀).overVisit B.z)) ↔
      (smoothDiagram D x ε hε).record.crossingOf u ∈ X₁
    rw [Ne, Ne, w3bh_record_crossingOf_eq_iff, w3bh_record_crossingOf_eq_iff, Diagram.overVisit_fst,
      Diagram.overVisit_fst, hBy, hBz]
    exact (hX₁ u).symm)
  -- Step C: the switch at the deleted `y₀` is invisible
  obtain ⟨ι₃⟩ := w3h_restrict_switch_deleted (smoothDiagram D x ε hε).record X₁
    ((smoothDiagram D x ε hε).overVisit y₀) (fun h => ((hX₁ _).mp h).1 rfl)
  -- Step D: the smoothing bridge
  obtain ⟨ι₄, hι₄⟩ := w3h_smooth_record_occ D x ε hε
  have hpt : ∀ (u : (smoothDiagram D x ε hε).Γ.Visit) (w : D.Γ.Crossing)
      (w₀ : (smoothDiagram D x ε hε).Γ.Crossing)
      (hw₀ : (smoothDiagram D x ε hε).Γ.crossingPoint w₀ = D.Γ.crossingPoint w),
      (ι₄.Φ u).1.1 = w ↔ u.1 = w₀ := by
    intro u w w₀ hw₀
    constructor
    · intro h
      apply (smoothDiagram D x ε hε).generic.crossingPoint_injective
      rw [← hι₄ u, h, hw₀]
    · intro h
      apply D.generic.crossingPoint_injective
      rw [hι₄ u, h, hw₀]
  let X₂ : Set (D.record.smooth (D.overVisit x)).Crossing :=
    {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ D.twin a₂ ∧ v.1 ≠ b₂ ∧ v.1 ≠ D.twin b₂}
  have hP : ∀ w : D.Γ.Visit, (w ≠ a₂ ∧ w ≠ D.twin a₂ ∧ w ≠ b₂ ∧ w ≠ D.twin b₂) ↔
      (w.1 ≠ y ∧ w.1 ≠ z) := by
    intro w
    rw [← and_assoc, w3bh_ne_ne_twin_iff, w3bh_ne_ne_twin_iff, ha₂, hb₂]
  have hX₂ : ∀ u : (smoothDiagram D x ε hε).Γ.Visit, (smoothDiagram D x ε hε).record.crossingOf u ∈ X₁ ↔
      (D.record.smooth (D.overVisit x)).crossingOf (ι₄.Φ u) ∈ X₂ := by
    intro u
    rw [hX₁, w3bh_crossingOf_mem_setOf]
    show (u.1 ≠ y₀ ∧ u.1 ≠ z₀) ↔
      ((ι₄.Φ u).1 ≠ a₂ ∧ (ι₄.Φ u).1 ≠ D.twin a₂ ∧ (ι₄.Φ u).1 ≠ b₂ ∧ (ι₄.Φ u).1 ≠ D.twin b₂) ∧
      (D.twin (ι₄.Φ u).1 ≠ a₂ ∧ D.twin (ι₄.Φ u).1 ≠ D.twin a₂ ∧ D.twin (ι₄.Φ u).1 ≠ b₂ ∧
        D.twin (ι₄.Φ u).1 ≠ D.twin b₂)
    rw [hP, hP, Diagram.twin_fst, and_self]
    exact Iff.and (not_congr (hpt u y y₀ hy₀).symm) (not_congr (hpt u z z₀ hz₀).symm)
  obtain ⟨ι₅⟩ := w3bh_restrictCrossings_iso_of_recordIso ι₄ X₁ X₂ hX₂
  -- Step E: land on `a₁`
  rcases D.eq_or_eq_twin (D.overVisit x) a₁ ha₁ with h | h
  · subst h
    exact ⟨ι₂.trans (ι₃.trans ι₅)⟩
  · subst h
    obtain ⟨ι₆⟩ := w3bh_restrictCrossings_iso_of_recordIso (D.record.smoothPairIso (D.overVisit x)).symm X₂
      {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ D.twin a₂ ∧ v.1 ≠ b₂ ∧ v.1 ≠ D.twin b₂} (by
        intro u
        rw [w3bh_crossingOf_mem_setOf, w3bh_crossingOf_mem_setOf]
        exact Iff.rfl)
    exact ⟨ι₂.trans (ι₃.trans (ι₅.trans ι₆))⟩

/-- **(h) THE reduced-smoothed-record lemma, in the consumer's terms** (`esc_rii_after_smoothing_of_bigons`'s
`hrec`): two one-component diagrams `D_H, D_L` with a wall bijection `Ψ` (twins, bits, signs, the cyclic
order twisted by the three transpositions on the six local occurrences — the shape of
`G11_core_statement`, produced by G11 Unit F's `G11_twisted_key_lt` machinery on the two lifts), the
triangle `x, y, z` with adjacent local occurrences on each strand, the two `smoothDiagram` outputs at `x`,
the crossings `y₀, z₀` at the double points of `y, z`, and two `BigonData` on the switched outputs with
`B.y = y₀`, `B.z = z₀`: the two reduced records are isomorphic.  Sketch: `B.reducedRecord =
((D^x).switch y₀).record.restrictCrossings keep` `≅ ((D^x).record.switch _).restrictCrossings keep`
(`switchRecordIso`, `restrictCrossings_iso_of_recordIso` CBProducts:1358) `≅ (D^x).record.restrictCrossings
keep` (`w3h_restrict_switch_deleted`: `y₀` is deleted) `≅ (D.record.smooth (overVisit x)).restrictCrossings
{y,z}ᶜ` (`w3h_smooth_record_occ` + `restrictCrossings_iso_of_recordIso`; `smoothPairIso` to land on `a₁`), on
both sides; then `w3h_record_core` with `Φ := Ψ` (`hsucc` from `hcyc` by `nextVisit_comm_of_visitBetween_iff`
on the one-component `D_H`, `record_succ_apply`).  ≈ 400 lines of glue. -/
theorem w3h_hrec (D_H D_L : Diagram) (hH : D_H.componentCount = 1) (hL : D_L.componentCount = 1)
    (x_H y_H z_H : D_H.Γ.Crossing) (x_L y_L z_L : D_L.Γ.Crossing)
    (Ψ : D_H.Γ.Visit ≃ D_L.Γ.Visit) (a₁ a₂ b₁ b₂ c₁ c₂ : D_H.Γ.Visit)
    (ha₁ : a₁.1 = x_H) (hb₁ : b₁ = D_H.twin a₁) (ha₂ : a₂.1 = y_H) (hc₁ : c₁ = D_H.twin a₂)
    (hb₂ : b₂.1 = z_H) (hc₂ : c₂ = D_H.twin b₂)
    (hxy : x_H ≠ y_H) (hxz : x_H ≠ z_H) (hyz : y_H ≠ z_H)
    (hadj_e : D_H.nextVisit a₁ = a₂ ∨ D_H.nextVisit a₂ = a₁)
    (hadj_f : D_H.nextVisit b₁ = b₂ ∨ D_H.nextVisit b₂ = b₁)
    (hadj_g : D_H.nextVisit c₁ = c₂ ∨ D_H.nextVisit c₂ = c₁)
    (htw : ∀ v, Ψ (D_H.twin v) = D_L.twin (Ψ v)) (hbit : ∀ v, D_L.overBit (Ψ v) = D_H.overBit v)
    (hsgn : ∀ v, D_L.sign (Ψ v).1 = D_H.sign v.1)
    (hcyc : ∀ u v w, D_L.VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔
      D_H.VisitBetween ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) u)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) w))
    (hxL : (Ψ a₁).1 = x_L) (hyL : (Ψ a₂).1 = y_L) (hzL : (Ψ b₂).1 = z_L)
    {εH εL : ℝ} (hεH : SmallEps D_H x_H εH) (hεL : SmallEps D_L x_L εL)
    (yH0 zH0 : (smoothDiagram D_H x_H εH hεH).Γ.Crossing)
    (hyH0 : (smoothDiagram D_H x_H εH hεH).Γ.crossingPoint yH0 = D_H.Γ.crossingPoint y_H)
    (hzH0 : (smoothDiagram D_H x_H εH hεH).Γ.crossingPoint zH0 = D_H.Γ.crossingPoint z_H)
    (yL0 zL0 : (smoothDiagram D_L x_L εL hεL).Γ.Crossing)
    (hyL0 : (smoothDiagram D_L x_L εL hεL).Γ.crossingPoint yL0 = D_L.Γ.crossingPoint y_L)
    (hzL0 : (smoothDiagram D_L x_L εL hεL).Γ.crossingPoint zL0 = D_L.Γ.crossingPoint z_L)
    (B_H : BigonData ((smoothDiagram D_H x_H εH hεH).switch yH0)) (hBHy : B_H.y = yH0) (hBHz : B_H.z = zH0)
    (B_L : BigonData ((smoothDiagram D_L x_L εL hεL).switch yL0)) (hBLy : B_L.y = yL0) (hBLz : B_L.z = zL0) :
    Nonempty (RecordIso B_H.reducedRecord B_L.reducedRecord) := by
  -- the six local occurrences and their crossings
  have hb₁x : b₁.1 = x_H := by rw [hb₁]; exact ha₁
  have hc₁y : c₁.1 = y_H := by rw [hc₁]; exact ha₂
  have hc₂z : c₂.1 = z_H := by rw [hc₂]; exact hb₂
  have hne : ∀ (u v : D_H.Γ.Visit), u.1 ≠ v.1 → u ≠ v :=
    fun u v h h' => h (congrArg (fun w : D_H.Γ.Visit => w.1) h')
  have h13 : a₁ ≠ b₁ := by rw [hb₁]; exact (D_H.twin_ne a₁).symm
  have h25 : a₂ ≠ c₁ := by rw [hc₁]; exact (D_H.twin_ne a₂).symm
  have h46 : b₂ ≠ c₂ := by rw [hc₂]; exact (D_H.twin_ne b₂).symm
  have h14 : a₁ ≠ b₂ := hne _ _ (by rw [ha₁, hb₂]; exact hxz)
  have h23 : a₂ ≠ b₁ := hne _ _ (by rw [ha₂, hb₁x]; exact hxy.symm)
  have h24 : a₂ ≠ b₂ := hne _ _ (by rw [ha₂, hb₂]; exact hyz)
  have h15 : a₁ ≠ c₁ := hne _ _ (by rw [ha₁, hc₁y]; exact hxy)
  have h16 : a₁ ≠ c₂ := hne _ _ (by rw [ha₁, hc₂z]; exact hxz)
  have h26 : a₂ ≠ c₂ := hne _ _ (by rw [ha₂, hc₂z]; exact hyz)
  have h35 : b₁ ≠ c₁ := hne _ _ (by rw [hb₁x, hc₁y]; exact hxy)
  have h36 : b₁ ≠ c₂ := hne _ _ (by rw [hb₁x, hc₂z]; exact hxz)
  have h45 : b₂ ≠ c₁ := hne _ _ (by rw [hb₂, hc₁y]; exact hyz.symm)
  have hσσ : ∀ v, (Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v) = v :=
    w3bh_swap3_apply_apply a₁ a₂ b₁ b₂ c₁ c₂ h13 h14 h23 h24 h15 h16 h25 h26 h35 h36 h45 h46
  -- the twisted successor clause from the twisted cyclic order (one component on both sides)
  have hsucc : ∀ v, Ψ ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      (D_H.nextVisit ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v))) =
      D_L.nextVisit (Ψ v) := by
    let Φ' : D_H.Γ.Visit ≃ D_L.Γ.Visit :=
      (Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)).trans Ψ
    have hcomp : ∀ v w, D_L.compOf (Φ' v) = D_L.compOf (Φ' w) ↔ D_H.compOf v = D_H.compOf w :=
      fun v w => ⟨fun _ => w3bh_compOf_eq_of_one D_H hH v w, fun _ => w3bh_compOf_eq_of_one D_L hL _ _⟩
    have hbetw : ∀ v w u, D_H.compOf w = D_H.compOf v → D_H.compOf u = D_H.compOf v →
        (D_L.VisitBetween (Φ' v) (Φ' w) (Φ' u) ↔ D_H.VisitBetween v w u) := by
      intro v w u _ _
      have := hcyc ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) w)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) u)
      rw [hσσ, hσσ, hσσ] at this
      exact this
    intro v
    have key := D_H.nextVisit_comm_of_visitBetween_iff Φ' hcomp hbetw
      ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v)
    simp only [Φ', Equiv.trans_apply, hσσ] at key
    exact key
  -- the crossings of `D_L`
  have hΨfst := w3bh_fst_eq_iff_of_twin Ψ htw
  have hxyL : x_L ≠ y_L := by
    rw [← hxL, ← hyL, Ne, hΨfst, ha₁, ha₂]; exact hxy
  have hxzL : x_L ≠ z_L := by
    rw [← hxL, ← hzL, Ne, hΨfst, ha₁, hb₂]; exact hxz
  have hyzL : y_L ≠ z_L := by
    rw [← hyL, ← hzL, Ne, hΨfst, ha₂, hb₂]; exact hyz
  -- the two bridges
  obtain ⟨ιH⟩ := w3bh_reduced_to_smooth D_H x_H y_H z_H a₁ a₂ b₂ c₁ c₂ ha₁ ha₂ hc₁ hb₂ hc₂ hεH
    yH0 zH0 hyH0 hzH0 B_H hBHy hBHz
  obtain ⟨ιL⟩ := w3bh_reduced_to_smooth D_L x_L y_L z_L (Ψ a₁) (Ψ a₂) (Ψ b₂) (Ψ c₁) (Ψ c₂) hxL hyL
    (by rw [hc₁, htw]) hzL (by rw [hc₂, htw]) hεL yL0 zL0 hyL0 hzL0 B_L hBLy hBLz
  -- the core
  have hcr : ∀ u v : D_H.Γ.Visit, u.1 ≠ v.1 → D_H.record.crossingOf u ≠ D_H.record.crossingOf v :=
    fun u v h h' => h ((w3bh_record_crossingOf_eq_iff D_H u v).mp h')
  obtain ⟨κ⟩ := w3h_record_core D_H.record D_L.record (D_H.record_componentCount.trans hH)
    (D_L.record_componentCount.trans hL) Ψ a₁ a₂ b₁ b₂ c₁ c₂ hb₁.symm hc₁.symm hc₂.symm
    (hcr _ _ (by rw [ha₁, ha₂]; exact hxy)) (hcr _ _ (by rw [ha₁, hb₂]; exact hxz))
    (hcr _ _ (by rw [ha₂, hb₂]; exact hyz)) hadj_e hadj_f hadj_g htw hbit hsgn hsucc
  exact ⟨ιH.trans (κ.trans ιL.symm)⟩


end Row177_6

/-! ## 6. UNIT REAL (Wave 3b): the two realisers and the F-177-2 interface replay (prefix `w3bi_`)

(a) `w3bi_switch_riii` realises `esc_MoveData.switch_riii` from `w3e_strong_case_sw` (PROVED modulo unit E);
(b) `w3bi_rii_after_smoothing_weak` realises (6) in the weak form `esc_rii_after_smoothing_weak` from the library
smoothings and the site box `w3bi_rii_sites`, itself reduced to the site data `w3bi_site_data` (β1′, OPEN: units G +
D4/D5, consuming `w3g_*` and the corrected `w3bi_*_switch_z` forms by name) and the wall data `w3bi_wall_data` (β2,
PROVED: `w3bi_wallEquiv`, `w3bi_wall_data_lift`, `w3bi_adjacent_lift_proof`), glued by `w3bi_hrec_general` (the
`ST/ST` case is `w3h_hrec`); (c) `w3bi_esc_interface_ext` (the interface with `GenericTableData`, `AV_EventRadius`
and the weak move data `w3bi_esc_MoveDataWeak`), the replayed `w3bi_esc_contact_identity` / `w3bi_esc_couple` /
`w3bi_esc_ledger`, and `w3bi_extreme_selected : RowShape @ExtremeSelectedData`.  Black boxes: `w3bi_esc_outer_data`
(the outer interface data, not 177-(4)/(6)), `w3bi_site_data_data`, the three non-`ST/ST` cases of `w3bi_hrec_general`,
the two `switch_z` statements.  Report: `W3B_REAL_REPORT.md`. -/
section W3BI_REAL
open RProof SM.GeoCarrier SM.Carrier Smoothing
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- an alternating triple stays alternating under the relabelling `f ↔ g` (`strandSign P g f = -strandSign P f g`) -/
theorem w3bi_alt_swap {P : LabelledTuple n} {e f g : ZMod n}
    (h : IsAlternating (strandSign P e f) (strandSign P e g) (strandSign P f g)) :
    IsAlternating (strandSign P e g) (strandSign P e f) (strandSign P g f) := by
  rw [show strandSign P g f = -strandSign P f g from crossingSign_swap P f g]
  unfold IsAlternating at h ⊢
  generalize strandSign P e f = sa at *
  generalize strandSign P e g = sb at *
  generalize strandSign P f g = sc at *
  revert h sa sb sc
  decide

/-- **(a) the realiser of `esc_MoveData.switch_riii`** at a configuration of the (extended) interface:
`D_H = carrierDiagram (K3 side) = geoPositiveLift`, `D_L` likewise on the empty side; the contact carrier
`q₀'` is the wall image of `q₀` (`esc_contact_unique`), `hcarr` from `GT_empty_wall`, `htri` from
`esc_contact_owns`, `hX` from `hL.gauss_words`, `hdet` from `hR.sign_eq`, the flipped strand-sign triple
non-alternating from `w3e_alt_of_completeLocal` and the nonzero signs `SEL_strandSigns_ne_zero hGT` (D3);
`sw := 0` in the main case, `sw := 1` after the relabelling `f ↔ g` (as `GT_G11_strong_proof`). -/
theorem w3bi_switch_riii (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    (hK : CompleteLocal (geomAt E t ht.1) hef heg hfg)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
    (q₀ : GeoComponent (geomAt E t ht.1) Q)
    (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q))
    (hq₀ : ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀)
    (hq₀' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀')
    (x_H : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Crossing)
    (x_L : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.Crossing)
    (hxH : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.crossingPoint x_H =
      crossingPoint (xPair hef))
    (hxL : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.crossingPoint x_L =
      crossingPoint (xPair ((hs _).mp hef))) :
    esc_switch_riii (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀)
      (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_H x_L := by
  have hef₀ : e ≠ f := P1.ne_of_isCrossing_pair hef
  have heg₀ : e ≠ g := P1.ne_of_isCrossing_pair heg
  have hfg₀ : f ≠ g := P1.ne_of_isCrossing_pair hfg
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  have hTq₀ := esc_contact_owns hL hef₀ heg₀ hfg₀ ht hQ hfull hq₀
  -- the wall and the transported contact carrier
  have W := GT_empty_wall hL hR hef₀ heg₀ hfg₀ ht ht' hop hs hQ
  have hcarr := GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q₀
  have hq₀'' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g
      (GT_carrierEquiv W q₀) := by
    rw [esc_not_triangleDisjoint_iff]
    have hmem : crossingTransport hs (xPair hef) ∈
        geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs Q) (GT_carrierEquiv W q₀) := by
      rw [hcarr, Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact hTq₀ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl))
    obtain ⟨i, -, -⟩ := crossing_visits_exist (crossingTransport hs (xPair hef))
    exact ⟨⟨_, i⟩, (P1.mem_triangleSupports _).mpr (Or.inl rfl),
      ((mem_geoCarrierCrossings _ _ _ _).mp hmem).2 _ rfl⟩
  have hq₀eq : q₀' = GT_carrierEquiv W q₀ :=
    esc_contact_unique hL hef₀ heg₀ hfg₀ ht' hQ' hfull' hq₀' hq₀''
  subst hq₀eq
  -- the wall data
  have hX := hL.gauss_words t t' ht ht' hop hs
  have hdet : ∀ i j : ZMod n, IsCrossing (E.curve t) {i, j} →
      (0 < det (edge (E.curve t) i) (edge (E.curve t) j) ↔
        0 < det (edge (E.curve t') i) (edge (E.curve t') j)) :=
    fun i j hij => GT_det_pos_iff_of_sign (hR.sign_eq t t' ht ht' i j hij)
  have halt := w3e_alt_of_completeLocal hGT t ht hef heg hfg hK
  obtain ⟨ha, hb, -⟩ := SEL_strandSigns_ne_zero hGT t ht
  unfold esc_switch_riii
  unfold CV.carrierDiagram at x_H x_L hxH hxL ⊢
  rcases lt_or_gt_of_ne (G11_param_ne (CarrierGeometry.ofDiagrammatic ((genericAt E t ht.1).diagrammatic hn))
      hfg₀ hef heg) with hord | hord
  · -- main case: `x = x_ef`, `sw = 0`
    exact (w3e_strong_case_sw hn _ _ hs _ _ q₀ _ hef₀ heg₀ hfg₀ hef heg hfg hX hdet hcarr hTq₀ hord 0
      (w3e_trans_sw_of_alt _ _ _ ha halt 0) x_H x_L hxH hxL).symm
  · -- relabelled case `f ↔ g`: `x = x_ef` is the SECOND crossing along `e`, `sw = 1`
    exact (w3e_strong_case_sw hn _ _ hs _ _ q₀ _ heg₀ hef₀ (Ne.symm hfg₀) heg hef (G11_isCrossing_comm hfg)
      (G11_exact_swap hs hX) hdet hcarr (by rw [G11_triangleCrossings_swap]; exact hTq₀) hord 1
      (w3e_trans_sw_of_alt _ _ _ hb (w3bi_alt_swap halt) 1) x_H x_L hxH hxL).symm


/-! ### The weak move data, the extended interface (F-177-2 as a replay, decision D2 / D-RM-5) and the two
black boxes of this unit -/

/-- the `knot_after_two` clause of `esc_MoveData` as a Prop (byte-identical field statement) -/
def w3bi_knot_after_two (D_H : Diagram) (pxH pyH : Plane) : Prop :=
  ∀ (x_H : D_H.Γ.Crossing), D_H.Γ.crossingPoint x_H = pxH →
    ∀ D_H0 : Diagram, IsOrientedSmoothing D_H x_H D_H0 →
    ∀ (y_H : D_H0.Γ.Crossing), D_H0.Γ.crossingPoint y_H = pyH →
    ∀ J_H : Diagram, IsOrientedSmoothing D_H0 y_H J_H → J_H.componentCount = 1

/-- the `three_components` clause of `esc_MoveData` as a Prop (byte-identical field statement) -/
def w3bi_three_components (D_L : Diagram) (pxL pyL : Plane) (Λ : ℕ) (fA fB fC : R) : Prop :=
  ∀ (x_L : D_L.Γ.Crossing), D_L.Γ.crossingPoint x_L = pxL →
    ∀ D_L0 : Diagram, IsOrientedSmoothing D_L x_L D_L0 →
    ∀ (y_L : D_L0.Γ.Crossing), D_L0.Γ.crossingPoint y_L = pyL →
    ∀ J_L : Diagram, IsOrientedSmoothing D_L0 y_L J_L → esc_three_components J_L Λ fA fB fC

/-- **`esc_MoveData` with (6) in its WEAK form** (`esc_rii_after_smoothing_weak`, SM/BigonDeletion.lean:
ONE pair of smoothings with their record clauses, the form the toolkit realises — the literal field
quantifies over every oriented smoothing, F-177-1).  Fields (4), the two outer clauses byte-identical. -/
structure w3bi_esc_MoveDataWeak (D_H D_L : Diagram) (pxH pyH pxL pyL : Plane) (Λ : ℕ)
    (fA fB fC : R) : Prop where
  /-- (4), for the crossings at the double points of `x`. -/
  switch_riii : ∀ (x_H : D_H.Γ.Crossing) (x_L : D_L.Γ.Crossing),
    D_H.Γ.crossingPoint x_H = pxH → D_L.Γ.crossingPoint x_L = pxL → esc_switch_riii D_H D_L x_H x_L
  /-- (6) in the weak form, for the crossings at the double points of `x`. -/
  rii_after_smoothing_weak : ∀ (x_H : D_H.Γ.Crossing) (x_L : D_L.Γ.Crossing),
    D_H.Γ.crossingPoint x_H = pxH → D_L.Γ.crossingPoint x_L = pxL →
    esc_rii_after_smoothing_weak D_H D_L x_H x_L pyH pyL
  knot_after_two : w3bi_knot_after_two D_H pxH pyH
  three_components : w3bi_three_components D_L pxL pyL Λ fA fB fC

/-- **The interface of row 177, EXTENDED (F-177-2)**: `esc_interface`'s statement with the two extra
hypotheses `GenericTableData` and `AV_EventRadius` (needed for `trans_sw` and `hdet`, skeleton report
§1.4) and the move data in the weak form `w3bi_esc_MoveDataWeak`.  `RProof/RALedgers.lean` is untouched;
the ledger is replayed below (`w3bi_esc_couple`, `w3bi_esc_ledger`). -/
def w3bi_esc_interface_ext : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ (A B C Z : GeoComponent (geomAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)) (Λ : ℕ),
        esc_FullSplitData hn (genericAt E t' ht'.1) e f g hQi' hS' q₀' A B C Z Λ ∧
        w3bi_esc_MoveDataWeak (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀)
          (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')
          (crossingPoint (xPair hef)) (crossingPoint (xPair heg))
          (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg))) Λ
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' A) (CV.groupedPoly hn (genericAt E t' ht'.1) hS' B)
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' C)

/-- **BLACK BOX (not this unit's): the OUTER data of the interface** — the carrier split of `Q ∪ T` on
the empty side (`esc_FullSplitData`, ESC §1, §4–§5) and the two outer clauses of the move data
(`knot_after_two`, `three_components`, ESC §2–§3) at a common `Λ`, at every configuration of the
extended interface.  Same binders as `w3bi_esc_interface_ext`. -/
def w3bi_esc_outer : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ (A B C Z : GeoComponent (geomAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)) (Λ : ℕ),
        esc_FullSplitData hn (genericAt E t' ht'.1) e f g hQi' hS' q₀' A B C Z Λ ∧
        w3bi_knot_after_two (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀)
          (crossingPoint (xPair hef)) (crossingPoint (xPair heg)) ∧
        w3bi_three_components (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')
          (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg))) Λ
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' A) (CV.groupedPoly hn (genericAt E t' ht'.1) hS' B)
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' C)

/-- the black box asserted (open body): NOT this unit's content (units E/G/H realise (4) and (6) only). -/
theorem w3bi_esc_outer_data : w3bi_esc_outer := by
  sorry

/-- **BLACK BOX (units G + H at the 177 site, D4–D6): the two `j = 2` bigon sites on the switched
`smoothDiagram` outputs and the identification of their reduced records.**  At a configuration of the
extended interface, for the crossings `x_H, x_L` at the double points of `x_ef` and `y_H, y_L` of the two
library smoothings `smoothDiagram … (eps …) (eps_small …)` at the double points of `x_eg`: `BigonData` on
`(D_H^x).switch y_H` and `(D_L^x).switch y_L` with isomorphic reduced records.  Decomposes into
`w3g_bigonData_smooth_arcST`/`_arcTS` (with the coherent orientation D4 and `hover` D5 derived from the
177 sign table), `w3h_hrec` (with the wall bijection D6 of G11 Unit F) — the site hypotheses (`hy hz hsy
htz hys hzt clear clear_vertex hover`) are the open realiser obligations. -/
def w3bi_rii_sites : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∀ (x_H : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Crossing)
        (x_L : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.Crossing),
        (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.crossingPoint x_H = crossingPoint (xPair hef) →
        (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.crossingPoint x_L =
          crossingPoint (xPair ((hs _).mp hef)) →
        ∀ (y_H : (smoothDiagram (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H
              (eps (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H)
              (eps_small (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H)).Γ.Crossing)
          (y_L : (smoothDiagram (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L
              (eps (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L)
              (eps_small (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L)).Γ.Crossing),
          (smoothDiagram (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H
              (eps (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H)
              (eps_small (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H)).Γ.crossingPoint y_H =
            crossingPoint (xPair heg) →
          (smoothDiagram (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L
              (eps (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L)
              (eps_small (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L)).Γ.crossingPoint y_L =
            crossingPoint (xPair ((hs _).mp heg)) →
          ∃ (B_H : BigonData ((smoothDiagram (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H
                (eps (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H)
                (eps_small (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H)).switch y_H))
            (B_L : BigonData ((smoothDiagram (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L
                (eps (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L)
                (eps_small (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L)).switch y_L)),
            Nonempty (RecordIso B_H.reducedRecord B_L.reducedRecord)

/-- **β1 (unit G at the 177 site, D4 + D5; reduced below to the site data β1′ `w3bi_site_data`)**: the two bigons.  For the crossings `y_H, y_L` of the
two library smoothings at the double points of `x_eg`: crossings `z_H, z_L` at the double points of `x_fg` and
`BigonData` on the outputs SWITCHED AT `y` whose pair `{B.y, B.z}` is `{y, z}` — in EITHER order: `B.y = y` is
the `arcST` orientation of `w3g_bigonData_smooth_arcST` (`y` precedes `x` on the over strand), `B.y = z`
the `arcTS` one; the two sides of the wall may have different orientations (the same-edge visit orders are
reversed across the wall, `ExactTriangleVisitOrders`).  Contents: `w3g_*` applied at the lift with `g` the
third lift strand, `y, z` the lift crossings at the double points of `x_eg, x_fg` (`esc_lift_crossing`),
`hy/hz` from the over data at `x` (`e` over `f` at `x_ef` gives `sS = e`, `y = x_eg`: `w3g_*`; `f` over `e` gives
`z = x_eg`: the corrected `w3bi_bigonData_smooth_*_switch_z` below), `clear`/`clear_vertex`
from `G11_cfg_clear_frontier/vertex`, `hover` from the sign table, the orientation from the strand orders. -/
def w3bi_bigon_pair : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∀ (x_H : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Crossing)
        (x_L : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.Crossing),
        (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.crossingPoint x_H = crossingPoint (xPair hef) →
        (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.crossingPoint x_L =
          crossingPoint (xPair ((hs _).mp hef)) →
        ∀ (y_H : (smoothDiagram (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H (eps (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H) (eps_small (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H)).Γ.Crossing)
          (y_L : (smoothDiagram (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L (eps (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L) (eps_small (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L)).Γ.Crossing),
          (smoothDiagram (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H (eps (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H) (eps_small (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H)).Γ.crossingPoint y_H = crossingPoint (xPair heg) →
          (smoothDiagram (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L (eps (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L) (eps_small (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L)).Γ.crossingPoint y_L = crossingPoint (xPair ((hs _).mp heg)) →
          ∃ (z_H : (smoothDiagram (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H (eps (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H) (eps_small (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H)).Γ.Crossing)
            (z_L : (smoothDiagram (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L (eps (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L) (eps_small (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L)).Γ.Crossing),
            (smoothDiagram (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H (eps (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H) (eps_small (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H)).Γ.crossingPoint z_H = crossingPoint (xPair hfg) ∧
            (smoothDiagram (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L (eps (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L) (eps_small (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L)).Γ.crossingPoint z_L = crossingPoint (xPair ((hs _).mp hfg)) ∧
            ∃ (B_H : BigonData ((smoothDiagram (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H (eps (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H) (eps_small (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H)).switch y_H))
              (B_L : BigonData ((smoothDiagram (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L (eps (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L) (eps_small (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L)).switch y_L)),
              ((B_H.y = y_H ∧ B_H.z = z_H) ∨ (B_H.y = z_H ∧ B_H.z = y_H)) ∧
              ((B_L.y = y_L ∧ B_L.z = z_L) ∨ (B_L.y = z_L ∧ B_L.z = y_L))

/-- **Rule (3) — the corrected forms of `w3g_bigonData_smooth_arcST/TS` needed by the (6) realiser when the
SWITCHED crossing is `z`.**  The frozen `w3g_*` put the bigon on `(D^x).switch y₀` with `y = {sS D x, g}` on
the OVER strand at `x`; the consumer (`esc_MoveData.rii_after_smoothing`, `esc_rii_after_smoothing_weak`) switches
the crossing at the double point of `x_eg`.  On the K3 side both alternating orientations occur
(`ExtremeLocal` is symmetric): if `e` is over `f` at `x_ef` then `sS = e`, `y = x_eg` and `w3g_*` apply; if `f`
is over `e` then `y = x_fg`, `z = x_eg` and the bigon must be read on `(D^x).switch z₀` — the same statement
with the switch moved (`same_over` holds after switching EITHER of `y, z`, by `hover`; no other field sees the
over data).  Stated here (open), consumed by the realisation of `w3bi_bigon_pair`. -/
theorem w3bi_bigonData_smooth_arcST_switch_z (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : D.crossingParam y hsy < τs D x) (hzt : τt D x < D.crossingParam z htz)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (clear_vertex : ∀ (i : Fin D.Γ.c) (a : ZMod (D.Γ.comp i).k),
      (D.Γ.comp i).P a ∉ convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z})
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z) :
    ∃ B : BigonData ((toDiagram D x M hε).switch z₀),
      B.j = 2 ∧ B.y = y₀ ∧ B.z = z₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint y, sMinus D x ε, tPlus D x ε, D.Γ.crossingPoint z} := by
  sorry

/-- the `arcTS` companion with the switch at `z₀` (see `w3bi_bigonData_smooth_arcST_switch_z`). -/
theorem w3bi_bigonData_smooth_arcTS_switch_z (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
    (g : D.Γ.Strand) (hgs : g ≠ sS D x) (hgt : g ≠ tS D x)
    (y z : D.Γ.Crossing) (hy : y.val = {sS D x, g}) (hz : z.val = {tS D x, g})
    (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val)
    (hys : τs D x < D.crossingParam y hsy) (hzt : D.crossingParam z htz < τt D x)
    (clear : ∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}))
    (clear_vertex : ∀ (i : Fin D.Γ.c) (a : ZMod (D.Γ.comp i).k),
      (D.Γ.comp i).P a ∉ convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z})
    (hover : D.overStrand y = g ↔ D.overStrand z ≠ g)
    (y₀ z₀ : Γ₀.Crossing) (hy₀ : origCrossing D x M hε y₀ = y) (hz₀ : origCrossing D x M hε z₀ = z) :
    ∃ B : BigonData ((toDiagram D x M hε).switch z₀),
      B.j = 2 ∧ B.y = z₀ ∧ B.z = y₀ ∧
      B.s = M.strandOf (StrandKind.old g) (StrandKind.occurs_old hgs hgt) ∧
      (⟨B.i, B.a⟩ : Γ₀.Strand) = M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT ∧
      B.K = convexHull ℝ {D.Γ.crossingPoint z, tMinus D x ε, sPlus D x ε, D.Γ.crossingPoint y} := by
  sorry


/-- **The site data of one `j = 2` bigon site (the inputs of `w3g_bigonData_smooth_arcST/TS`, D4 + D5)** at a
crossing `x` of `D` with the two other triangle crossings at the double points `py, pz`: the remote strand `g`,
the crossings `y = {sS, g}` (on the over strand at `x`) and `z = {tS, g}`, their parameters relative to `x`
in one of the two coherent orientations (D4: `arcST` or `arcTS`), the clearance of the triangle disc, the
over data `hover` (D5), and which of `y, z` sits at `py` (the switched crossing of the consumer). -/
def w3bi_SiteData (D : Diagram) (x : D.Γ.Crossing) (py pz : Plane) : Prop :=
  ∃ (g : D.Γ.Strand) (_hgs : g ≠ sS D x) (_hgt : g ≠ tS D x) (y z : D.Γ.Crossing) (_hyx : y ≠ x) (_hzx : z ≠ x)
    (_hy : y.val = {sS D x, g}) (_hz : z.val = {tS D x, g}) (hsy : sS D x ∈ y.val) (htz : tS D x ∈ z.val),
    ((D.crossingParam y hsy < τs D x ∧ τt D x < D.crossingParam z htz) ∨
      (τs D x < D.crossingParam y hsy ∧ D.crossingParam z htz < τt D x)) ∧
    (∀ u : D.Γ.Strand, u ≠ sS D x → u ≠ tS D x → u ≠ g →
      Disjoint (D.Γ.seg u) (convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z})) ∧
    (∀ (i : Fin D.Γ.c) (a : ZMod (D.Γ.comp i).k),
      (D.Γ.comp i).P a ∉ convexHull ℝ {D.Γ.crossingPoint x, D.Γ.crossingPoint y, D.Γ.crossingPoint z}) ∧
    (D.overStrand y = g ↔ D.overStrand z ≠ g) ∧
    ((D.Γ.crossingPoint y = py ∧ D.Γ.crossingPoint z = pz) ∨ (D.Γ.crossingPoint y = pz ∧ D.Γ.crossingPoint z = py))

/-- **One bigon from the site data, any `SpliceModel` (PROVED from `w3g_*` and the `switch_z` forms by name)**:
the smoothing crossings `y₀, z₀` over `y, z` (`liftCrossing`, `origCrossing_liftCrossing`), the consumer's `y_H`
at `py` is `y₀` or `z₀` (`crossingPoint_origCrossing` + generic injectivity), then the four cases
(orientation × switched crossing). -/
theorem w3bi_bigon_of_site_model (D : Diagram) (x : D.Γ.Crossing) {ε : ℝ} {Γ₀ : Shadow}
    (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε) (py pz : Plane) (hsite : w3bi_SiteData D x py pz)
    (y_H : (toDiagram D x M hε).Γ.Crossing) (hyH : (toDiagram D x M hε).Γ.crossingPoint y_H = py) :
    ∃ z_H : (toDiagram D x M hε).Γ.Crossing, (toDiagram D x M hε).Γ.crossingPoint z_H = pz ∧
      ∃ B : BigonData ((toDiagram D x M hε).switch y_H), (B.y = y_H ∧ B.z = z_H) ∨ (B.y = z_H ∧ B.z = y_H) := by
  obtain ⟨g, hgs, hgt, y, z, hyx, hzx, hy, hz, hsy, htz, hor, clear, clear_vertex, hover, hpts⟩ := hsite
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, origCrossing D x M hε y₀ = y := ⟨_, origCrossing_liftCrossing D x M hε y hyx⟩
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, origCrossing D x M hε z₀ = z := ⟨_, origCrossing_liftCrossing D x M hε z hzx⟩
  have hpy₀ : (toDiagram D x M hε).Γ.crossingPoint y₀ = D.Γ.crossingPoint y :=
    (crossingPoint_origCrossing D x M hε y₀).trans (by rw [hy₀])
  have hpz₀ : (toDiagram D x M hε).Γ.crossingPoint z₀ = D.Γ.crossingPoint z :=
    (crossingPoint_origCrossing D x M hε z₀).trans (by rw [hz₀])
  rcases hpts with ⟨hpy, hpz⟩ | ⟨hpy, hpz⟩
  · -- `y` at `py`: the switched crossing is `y₀`
    have hyH₀ : y₀ = y_H :=
      (toDiagram D x M hε).generic.crossingPoint_injective (hpy₀.trans (hpy.trans hyH.symm))
    subst hyH₀
    refine ⟨z₀, hpz₀.trans hpz, ?_⟩
    rcases hor with ⟨hys, hzt⟩ | ⟨hys, hzt⟩
    · obtain ⟨B, -, hBy, hBz, -, -, -⟩ := w3g_bigonData_smooth_arcST D x M hε g hgs hgt y z hy hz hsy htz hys hzt
        clear clear_vertex hover y₀ z₀ hy₀ hz₀
      exact ⟨B, Or.inl ⟨hBy, hBz⟩⟩
    · obtain ⟨B, -, hBy, hBz, -, -, -⟩ := w3g_bigonData_smooth_arcTS D x M hε g hgs hgt y z hy hz hsy htz hys hzt
        clear clear_vertex hover y₀ z₀ hy₀ hz₀
      exact ⟨B, Or.inr ⟨hBy, hBz⟩⟩
  · -- `z` at `py`: the switched crossing is `z₀` (the corrected `switch_z` forms)
    have hyH₀ : z₀ = y_H :=
      (toDiagram D x M hε).generic.crossingPoint_injective (hpz₀.trans (hpz.trans hyH.symm))
    subst hyH₀
    refine ⟨y₀, hpy₀.trans hpy, ?_⟩
    rcases hor with ⟨hys, hzt⟩ | ⟨hys, hzt⟩
    · obtain ⟨B, -, hBy, hBz, -, -, -⟩ := w3bi_bigonData_smooth_arcST_switch_z D x M hε g hgs hgt y z hy hz hsy htz
        hys hzt clear clear_vertex hover y₀ z₀ hy₀ hz₀
      exact ⟨B, Or.inr ⟨hBy, hBz⟩⟩
    · obtain ⟨B, -, hBy, hBz, -, -, -⟩ := w3bi_bigonData_smooth_arcTS_switch_z D x M hε g hgs hgt y z hy hz hsy htz
        hys hzt clear clear_vertex hover y₀ z₀ hy₀ hz₀
      exact ⟨B, Or.inl ⟨hBy, hBz⟩⟩

/-- the same on the library smoothing `smoothDiagram D x (eps D x) (eps_small D x)` (`unfold; split_ifs`) -/
theorem w3bi_bigon_of_site (D : Diagram) (x : D.Γ.Crossing) (py pz : Plane) (hsite : w3bi_SiteData D x py pz)
    (y_H : (smoothDiagram D x (eps D x) (eps_small D x)).Γ.Crossing)
    (hyH : (smoothDiagram D x (eps D x) (eps_small D x)).Γ.crossingPoint y_H = py) :
    ∃ z_H : (smoothDiagram D x (eps D x) (eps_small D x)).Γ.Crossing,
      (smoothDiagram D x (eps D x) (eps_small D x)).Γ.crossingPoint z_H = pz ∧
      ∃ B : BigonData ((smoothDiagram D x (eps D x) (eps_small D x)).switch y_H),
        (B.y = y_H ∧ B.z = z_H) ∨ (B.y = z_H ∧ B.z = y_H) := by
  revert y_H hyH
  unfold smoothDiagram
  by_cases h : (sS D x).1 = (tS D x).1
  · rw [dif_pos h]
    exact w3bi_bigon_of_site_model D x (selfModel D x (eps D x) h) (eps_small D x) py pz hsite
  · rw [dif_neg h]
    exact w3bi_bigon_of_site_model D x (mixedModel D x (eps D x) h) (eps_small D x) py pz hsite

/-- **BLACK BOX β1′ (the site data at the 177 configuration, both sides)** — what remains of β1 after the
reduction: at every configuration, `w3bi_SiteData` for the two lifts at `x_H, x_L` with `py, pz` the double points
of `x_eg, x_fg` (and their transports).  Contents: `g` the third lift strand, `y, z` the lift crossings at the double
points (`esc_lift_crossing`), `hy/hz` from the over data at `x`, `clear`/`clear_vertex` from
`G11_cfg_clear_frontier/vertex`, `hover` from the sign table (D5), the orientation from the strand orders (D4). -/
def w3bi_site_data : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∀ (x_H : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Crossing)
        (x_L : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.Crossing),
        (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.crossingPoint x_H = crossingPoint (xPair hef) →
        (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.crossingPoint x_L =
          crossingPoint (xPair ((hs _).mp hef)) →
        w3bi_SiteData (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H (crossingPoint (xPair heg)) (crossingPoint (xPair hfg)) ∧
        w3bi_SiteData (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L
          (crossingPoint (xPair ((hs _).mp heg))) (crossingPoint (xPair ((hs _).mp hfg)))

/-! ### Unit SITE (`w3cs_`, W3C): β1′ `w3bi_site_data` PROVED — D4 as a determinant identity, D5 from the
positive over-strand convention, the lift wiring through `G11_cfg_*` / `gu2_x*_eq` / `G11_carrierSign`.
Report: `W3C_SITE_REPORT.md`. -/

/-! ### SITE (unit `w3cs_`): the site data from an alternating triangle on a positive diagram -/

theorem w3cs_det_lin (α β : ℝ) (u v w : Plane) : det (α • u - β • v) w = α * det u w - β * det v w := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  ring

theorem w3cs_det_self (u : Plane) : det u u = 0 := by simp only [det]; ring

/-- the crossing parameter depends only on the strand -/
theorem w3cs_crossingParam_congr (D : Diagram) (x : D.Γ.Crossing) {s s' : D.Γ.Strand} (h : s = s')
    (hs : s ∈ x.val) (hs' : s' ∈ x.val) : D.crossingParam x hs = D.crossingParam x hs' := by
  subst h; rfl

/-- two crossings on one strand differ by a multiple of the strand direction -/
theorem w3cs_sub_eq (D : Diagram) (x y : D.Γ.Crossing) {s : D.Γ.Strand} (hsx : s ∈ x.val) (hsy : s ∈ y.val) :
    D.Γ.crossingPoint y - D.Γ.crossingPoint x = (D.crossingParam y hsy - D.crossingParam x hsx) • D.Γ.dir s := by
  rw [(D.crossingParam_spec y hsy).2.2, (D.crossingParam_spec x hsx).2.2]
  unfold edgePoint
  show _ = (D.crossingParam y hsy - D.crossingParam x hsx) • edge (D.Γ.comp s.1).P s.2
  rw [sub_smul]
  abel

/-- the over strand of the positive diagram at a crossing `{s, t}` is `s` iff `det (dir s) (dir t) > 0` -/
theorem w3cs_pos_overStrand_eq_iff (Γ : Shadow) (hΓ : Γ.Generic) (y : Γ.Crossing) (s t : Γ.Strand)
    (hs : s ∈ y.val) (ht : t ∈ y.val) (hst : s ≠ t) :
    (Γ.positiveDiagram hΓ).overStrand y = s ↔ 0 < det (Γ.dir s) (Γ.dir t) := by
  have key : ∀ (o : Γ.Strand) (ho : o ∈ y.val), 0 < det (Γ.dir o) (Γ.dir (Γ.other y ho)) →
      (o = s ↔ 0 < det (Γ.dir s) (Γ.dir t)) := by
    intro o ho hpos
    rcases (Γ.mem_iff_eq_or_other y hs o).mp ho with rfl | h
    · have ht' : Γ.other y ho = t := (Γ.eq_other_of_mem_of_ne y ho ht hst.symm).symm
      rw [ht'] at hpos
      exact iff_of_true rfl hpos
    · have hot : o = t := by
        rw [h]; exact (Γ.eq_other_of_mem_of_ne y hs ht hst.symm).symm
      subst hot
      have hs' : Γ.other y ho = s := (Γ.eq_other_of_mem_of_ne y ho hs hst).symm
      rw [hs', det_swap] at hpos
      exact iff_of_false hst.symm (by linarith)
  exact key _ ((Γ.positiveDiagram hΓ).over_mem y) (Γ.positiveDiagram_det_pos hΓ y)

/-- **D4 core**: `α·det(a,c) = β·det(b,c)` with `det(a,c)`, `det(b,c)` of opposite signs and `α ≠ 0` forces
`α, β` to have opposite signs. -/
theorem w3cs_opposite_signs {α β dac dbc : ℝ} (h : α * dac = β * dbc) (hα : α ≠ 0)
    (hac : dac ≠ 0) (hbc : dbc ≠ 0) (hsign : SignType.sign dac = -SignType.sign dbc) :
    (α < 0 ∧ 0 < β) ∨ (0 < α ∧ β < 0) := by
  rcases lt_or_gt_of_ne hac with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
    simp only [sign_pos, sign_neg, h1, h2] at hsign
  · exact absurd hsign (by decide)
  · rcases lt_or_gt_of_ne hα with h3 | h3
    · exact Or.inl ⟨h3, by nlinarith⟩
    · exact Or.inr ⟨h3, by nlinarith⟩
  · rcases lt_or_gt_of_ne hα with h3 | h3
    · exact Or.inl ⟨h3, by nlinarith⟩
    · exact Or.inr ⟨h3, by nlinarith⟩
  · exact absurd hsign (by decide)

theorem w3cs_det_smul_self (γ : ℝ) (u : Plane) : det (γ • u) u = 0 := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- **The site data from an alternating triangle on the positive diagram of a generic shadow** (D4 + D5):
`x = {a, b}`, `y = {a, c}`, `z = {b, c}` with `sign det(a,b), det(a,c), det(b,c)` alternating, the closed
triangle clear of the other strands and of all vertices.  D4 is the identity
`(τ_y^a − τ_x^a)·det(a,c) = (τ_z^b − τ_x^b)·det(b,c)` (`y − x ∥ a`, `z − x ∥ b`, `y − z ∥ c`), D5 the
positive over-strand convention read on the two determinants. -/
theorem w3cs_siteData_of_triangle (Γ : Shadow) (hΓ : Γ.Generic) (x y z : Γ.Crossing) (a b c : Γ.Strand)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hx : x.val = {a, b}) (hy : y.val = {a, c}) (hz : z.val = {b, c})
    (halt : IsAlternating (SignType.sign (det (Γ.dir a) (Γ.dir b))) (SignType.sign (det (Γ.dir a) (Γ.dir c)))
      (SignType.sign (det (Γ.dir b) (Γ.dir c))))
    (hclear : ∀ u : Γ.Strand, u ≠ a → u ≠ b → u ≠ c →
      Disjoint (Γ.seg u) (convexHull ℝ {Γ.crossingPoint x, Γ.crossingPoint y, Γ.crossingPoint z}))
    (hvert : ∀ (i : Fin Γ.c) (l : ZMod (Γ.comp i).k),
      (Γ.comp i).P l ∉ convexHull ℝ {Γ.crossingPoint x, Γ.crossingPoint y, Γ.crossingPoint z}) :
    w3bi_SiteData (Γ.positiveDiagram hΓ) x (Γ.crossingPoint y) (Γ.crossingPoint z) := by
  have hxa : a ∈ x.val := by rw [hx]; exact Finset.mem_insert_self _ _
  have hxb : b ∈ x.val := by rw [hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hya : a ∈ y.val := by rw [hy]; exact Finset.mem_insert_self _ _
  have hyc : c ∈ y.val := by rw [hy]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hzb : b ∈ z.val := by rw [hz]; exact Finset.mem_insert_self _ _
  have hzc : c ∈ z.val := by rw [hz]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hdac : det (Γ.dir a) (Γ.dir c) ≠ 0 := by
    obtain ⟨hna, hmeet⟩ := Γ.crossing_pair_spec y hya hyc hac
    exact hΓ.transverse a c hna hmeet
  have hdbc : det (Γ.dir b) (Γ.dir c) ≠ 0 := by
    obtain ⟨hna, hmeet⟩ := Γ.crossing_pair_spec z hzb hzc hbc
    exact hΓ.transverse b c hna hmeet
  have hsign : SignType.sign (det (Γ.dir a) (Γ.dir c)) = -SignType.sign (det (Γ.dir b) (Γ.dir c)) := by
    rw [halt.2, halt.1]
  have hyx : y ≠ x := by
    intro h
    have hb' : b ∈ ({a, c} : Finset Γ.Strand) := by rw [← hy, h]; exact hxb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
    rcases hb' with h' | h'
    · exact hab h'.symm
    · exact hbc h'
  have hzx : z ≠ x := by
    intro h
    have ha' : a ∈ ({b, c} : Finset Γ.Strand) := by rw [← hz, h]; exact hxa
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha'
    rcases ha' with h' | h'
    · exact hab h'
    · exact hac h'
  -- D4
  have hyx_eq : Γ.crossingPoint y - Γ.crossingPoint x =
      ((Γ.positiveDiagram hΓ).crossingParam y hya - (Γ.positiveDiagram hΓ).crossingParam x hxa) • Γ.dir a := w3cs_sub_eq (Γ.positiveDiagram hΓ) x y hxa hya
  have hzx_eq : Γ.crossingPoint z - Γ.crossingPoint x =
      ((Γ.positiveDiagram hΓ).crossingParam z hzb - (Γ.positiveDiagram hΓ).crossingParam x hxb) • Γ.dir b := w3cs_sub_eq (Γ.positiveDiagram hΓ) x z hxb hzb
  have hyz_eq : Γ.crossingPoint y - Γ.crossingPoint z =
      ((Γ.positiveDiagram hΓ).crossingParam y hyc - (Γ.positiveDiagram hΓ).crossingParam z hzc) • Γ.dir c := w3cs_sub_eq (Γ.positiveDiagram hΓ) z y hzc hyc
  have hkey : ((Γ.positiveDiagram hΓ).crossingParam y hya - (Γ.positiveDiagram hΓ).crossingParam x hxa) * det (Γ.dir a) (Γ.dir c) =
      ((Γ.positiveDiagram hΓ).crossingParam z hzb - (Γ.positiveDiagram hΓ).crossingParam x hxb) * det (Γ.dir b) (Γ.dir c) := by
    have h1 : ((Γ.positiveDiagram hΓ).crossingParam y hya - (Γ.positiveDiagram hΓ).crossingParam x hxa) • Γ.dir a -
        ((Γ.positiveDiagram hΓ).crossingParam z hzb - (Γ.positiveDiagram hΓ).crossingParam x hxb) • Γ.dir b =
        ((Γ.positiveDiagram hΓ).crossingParam y hyc - (Γ.positiveDiagram hΓ).crossingParam z hzc) • Γ.dir c := by
      rw [← hyx_eq, ← hzx_eq, ← hyz_eq]; abel
    have h2 : det (((Γ.positiveDiagram hΓ).crossingParam y hya - (Γ.positiveDiagram hΓ).crossingParam x hxa) • Γ.dir a -
        ((Γ.positiveDiagram hΓ).crossingParam z hzb - (Γ.positiveDiagram hΓ).crossingParam x hxb) • Γ.dir b) (Γ.dir c) =
        det (((Γ.positiveDiagram hΓ).crossingParam y hyc - (Γ.positiveDiagram hΓ).crossingParam z hzc) • Γ.dir c) (Γ.dir c) := by
      rw [h1]
    rw [w3cs_det_lin, w3cs_det_smul_self] at h2
    linarith
  have hα0 : (Γ.positiveDiagram hΓ).crossingParam y hya - (Γ.positiveDiagram hΓ).crossingParam x hxa ≠ 0 := by
    intro h0
    apply hyx
    apply hΓ.crossingPoint_injective
    have : Γ.crossingPoint y - Γ.crossingPoint x = 0 := by rw [hyx_eq, h0, zero_smul]
    exact sub_eq_zero.mp this
  have hD4 := w3cs_opposite_signs hkey hα0 hdac hdbc hsign
  -- D5
  have hoy : (Γ.positiveDiagram hΓ).overStrand y = c ↔ 0 < det (Γ.dir c) (Γ.dir a) :=
    w3cs_pos_overStrand_eq_iff Γ hΓ y c a hyc hya hac.symm
  have hoz : (Γ.positiveDiagram hΓ).overStrand z = c ↔ 0 < det (Γ.dir c) (Γ.dir b) :=
    w3cs_pos_overStrand_eq_iff Γ hΓ z c b hzc hzb hbc.symm
  have hover : (Γ.positiveDiagram hΓ).overStrand y = c ↔ (Γ.positiveDiagram hΓ).overStrand z ≠ c := by
    rcases lt_or_gt_of_ne hdac with h1 | h1 <;> rcases lt_or_gt_of_ne hdbc with h2 | h2 <;>
      simp only [sign_pos, sign_neg, h1, h2] at hsign
    · exact absurd hsign (by decide)
    · refine iff_of_true (hoy.mpr (by rw [det_swap]; linarith)) (fun h => ?_)
      have := hoz.mp h
      rw [det_swap] at this
      linarith
    · refine iff_of_false (fun h => ?_) (fun h => h (hoz.mpr (by rw [det_swap]; linarith)))
      have := hoy.mp h
      rw [det_swap] at this
      linarith
    · exact absurd hsign (by decide)
  have hset : ({Γ.crossingPoint x, Γ.crossingPoint z, Γ.crossingPoint y} : Set Plane) =
      {Γ.crossingPoint x, Γ.crossingPoint y, Γ.crossingPoint z} := by
    rw [Set.pair_comm]
  have hover' : (Γ.positiveDiagram hΓ).overStrand z = c ↔ (Γ.positiveDiagram hΓ).overStrand y ≠ c := by
    constructor
    · intro hq hp; exact hover.mp hp hq
    · intro hnp; by_contra hnq; exact hnp (hover.mpr hnq)
  -- the case split on the over strand at `x`
  have hsx : (Γ.positiveDiagram hΓ).overStrand x ∈ ({a, b} : Finset Γ.Strand) := by
    rw [← hx]; exact (Γ.positiveDiagram hΓ).over_mem x
  unfold w3bi_SiteData
  rcases Finset.mem_insert.mp hsx with hsa | hsb'
  · -- `sS = a`, `tS = b`: `y` at `py`
    have htb : (Γ.positiveDiagram hΓ).underStrand x = b :=
      ((Γ.positiveDiagram hΓ).eq_under_of_mem_of_ne x hxb (by rw [hsa]; exact hab.symm)).symm
    have hsy' : sS (Γ.positiveDiagram hΓ) x ∈ y.val := by show (Γ.positiveDiagram hΓ).overStrand x ∈ y.val; rw [hsa]; exact hya
    have htz' : tS (Γ.positiveDiagram hΓ) x ∈ z.val := by show (Γ.positiveDiagram hΓ).underStrand x ∈ z.val; rw [htb]; exact hzb
    refine ⟨c, ?_, ?_, y, z, hyx, hzx, ?_, ?_, hsy', htz', ?_, ?_, hvert, hover, Or.inl ⟨rfl, rfl⟩⟩
    · show c ≠ (Γ.positiveDiagram hΓ).overStrand x; rw [hsa]; exact hac.symm
    · show c ≠ (Γ.positiveDiagram hΓ).underStrand x; rw [htb]; exact hbc.symm
    · show y.val = {(Γ.positiveDiagram hΓ).overStrand x, c}; rw [hsa]; exact hy
    · show z.val = {(Γ.positiveDiagram hΓ).underStrand x, c}; rw [htb]; exact hz
    · have e1 : (Γ.positiveDiagram hΓ).crossingParam y hsy' = (Γ.positiveDiagram hΓ).crossingParam y hya := w3cs_crossingParam_congr (Γ.positiveDiagram hΓ) y hsa _ _
      have e2 : τs (Γ.positiveDiagram hΓ) x = (Γ.positiveDiagram hΓ).crossingParam x hxa := w3cs_crossingParam_congr (Γ.positiveDiagram hΓ) x hsa _ _
      have e3 : (Γ.positiveDiagram hΓ).crossingParam z htz' = (Γ.positiveDiagram hΓ).crossingParam z hzb := w3cs_crossingParam_congr (Γ.positiveDiagram hΓ) z htb _ _
      have e4 : τt (Γ.positiveDiagram hΓ) x = (Γ.positiveDiagram hΓ).crossingParam x hxb := w3cs_crossingParam_congr (Γ.positiveDiagram hΓ) x htb _ _
      rw [e1, e2, e3, e4]
      rcases hD4 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; constructor <;> linarith
      · right; constructor <;> linarith
    · intro u hu1 hu2 hu3
      apply hclear u _ _ hu3
      · intro h; apply hu1; rw [h]; exact hsa.symm
      · intro h; apply hu2; rw [h]; exact htb.symm
  · -- `sS = b`, `tS = a`: the roles of `y, z` swap, `y` at `pz`
    have hsb : (Γ.positiveDiagram hΓ).overStrand x = b := Finset.mem_singleton.mp hsb'
    have hta : (Γ.positiveDiagram hΓ).underStrand x = a :=
      ((Γ.positiveDiagram hΓ).eq_under_of_mem_of_ne x hxa (by rw [hsb]; exact hab)).symm
    have hsz' : sS (Γ.positiveDiagram hΓ) x ∈ z.val := by show (Γ.positiveDiagram hΓ).overStrand x ∈ z.val; rw [hsb]; exact hzb
    have hty' : tS (Γ.positiveDiagram hΓ) x ∈ y.val := by show (Γ.positiveDiagram hΓ).underStrand x ∈ y.val; rw [hta]; exact hya
    refine ⟨c, ?_, ?_, z, y, hzx, hyx, ?_, ?_, hsz', hty', ?_, ?_, ?_, hover', Or.inr ⟨rfl, rfl⟩⟩
    · show c ≠ (Γ.positiveDiagram hΓ).overStrand x; rw [hsb]; exact hbc.symm
    · show c ≠ (Γ.positiveDiagram hΓ).underStrand x; rw [hta]; exact hac.symm
    · show z.val = {(Γ.positiveDiagram hΓ).overStrand x, c}; rw [hsb]; exact hz
    · show y.val = {(Γ.positiveDiagram hΓ).underStrand x, c}; rw [hta]; exact hy
    · have e1 : (Γ.positiveDiagram hΓ).crossingParam z hsz' = (Γ.positiveDiagram hΓ).crossingParam z hzb := w3cs_crossingParam_congr (Γ.positiveDiagram hΓ) z hsb _ _
      have e2 : τs (Γ.positiveDiagram hΓ) x = (Γ.positiveDiagram hΓ).crossingParam x hxb := w3cs_crossingParam_congr (Γ.positiveDiagram hΓ) x hsb _ _
      have e3 : (Γ.positiveDiagram hΓ).crossingParam y hty' = (Γ.positiveDiagram hΓ).crossingParam y hya := w3cs_crossingParam_congr (Γ.positiveDiagram hΓ) y hta _ _
      have e4 : τt (Γ.positiveDiagram hΓ) x = (Γ.positiveDiagram hΓ).crossingParam x hxa := w3cs_crossingParam_congr (Γ.positiveDiagram hΓ) x hta _ _
      rw [e1, e2, e3, e4]
      rcases hD4 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; constructor <;> linarith
      · left; constructor <;> linarith
    · intro u hu1 hu2 hu3
      show Disjoint (Γ.seg u) (convexHull ℝ {Γ.crossingPoint x, Γ.crossingPoint z, Γ.crossingPoint y})
      rw [hset]
      apply hclear u _ _ hu3
      · intro h; apply hu2; rw [h]; exact hta.symm
      · intro h; apply hu1; rw [h]; exact hsb.symm
    · show ∀ (i : Fin Γ.c) (l : ZMod (Γ.comp i).k),
        (Γ.comp i).P l ∉ convexHull ℝ {Γ.crossingPoint x, Γ.crossingPoint z, Γ.crossingPoint y}
      rw [hset]
      exact hvert


/-! ### SITE (unit `w3cs_`): the site data at the lift of the distinguished carrier -/

section W3CS_Lift

open SM.GeoCarrier SM.Carrier

/-- `ExactTriangleVisitOrders` is symmetric in the two polygons (copy of `s174_exact_symm`, not imported here). -/
theorem w3cs_exact_symm {P P' : LabelledTuple n} {e f g : ZMod n}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
    (hX : ExactTriangleVisitOrders P P' e f g hs) :
    ExactTriangleVisitOrders P' P e f g (fun s => (hs s).symm) := by
  intro v w he
  have h1 := hX ((visitTransport hs).symm w) ((visitTransport hs).symm v) he.symm
  have h2 := hX ((visitTransport hs).symm v) ((visitTransport hs).symm w) he
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1 h2
  refine ⟨fun hu => ?_, fun hu => ?_⟩
  · have hu' : ((visitTransport hs).symm w).1.val ∪ ((visitTransport hs).symm v).1.val =
        {e, f, g} := by
      rw [Finset.union_comm]; exact hu
    exact (h1.1 hu').symm
  · exact (h2.2 hu).symm

/-- **β1′ at the lift level (PROVED)**: the site data of the positive lift of the distinguished carrier at the
lift crossing over `x_ef`, with `py, pz` the double points of `x_eg, x_fg`.  The three lift crossings are
`(singleCrossingEquiv).symm (xPair hmp / hmq / hpq)` of the configuration crossings `G11_cfg_hmp/hmq/hpq`
(double points `gu2_x*_eq`), the strands `⟨0, m⟩ ⟨0, p⟩ ⟨0, q⟩`, the alternating triple through
`G11_carrierSign`, the closed triangle through `G11_cfg_clear_frontier/vertex`; then
`w3cs_siteData_of_triangle`. -/
theorem w3cs_site_data_lift (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {e f g : ZMod n}
    {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q)
    (halt : IsAlternating (crossingSign P e f) (crossingSign P e g) (crossingSign P f g))
    (x_H : (geoPositiveLift hn hG hT q).Γ.Crossing)
    (hxH : (geoPositiveLift hn hG hT q).Γ.crossingPoint x_H = crossingPoint (xPair hcef)) :
    w3bi_SiteData (geoPositiveLift hn hG hT q) x_H (crossingPoint (xPair hceg)) (crossingPoint (xPair hcfg)) := by
  have hmp := G11_cfg_hmp hn hG hT q hcef htri
  have hmq := G11_cfg_hmq hn hG hs hT q hcef hceg htri hX
  have hpq := G11_cfg_hpq hn hG hs hT q hfg hcef hceg hcfg htri hX
  have hgen : (Shadow.single (geoCarrierPolyComp hn hG hT q)).Generic := geoCarrierShadow_generic hn hG hT q
  have cp : ∀ c : Crossing (geoCornerPolygon hG.cg T q),
      (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
        ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm c) = crossingPoint c := by
    intro c
    rw [Shadow.single_crossingPoint _ hgen, Equiv.apply_symm_apply]
  have hxm : (Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmp) = x_H := by
    apply hgen.crossingPoint_injective
    rw [cp, gu2_xmp_eq hn hG hT q hcef htri hmp]
    exact hxH.symm
  have hym : (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
      ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmq)) =
      crossingPoint (xPair hceg) := by
    rw [cp, gu2_xmq_eq hn hG hT q hcef hceg htri hmq]
  have hzm : (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
      ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hpq)) =
      crossingPoint (xPair hcfg) := by
    rw [cp, gu2_xpq_eq hn hG hT q hcef hceg hcfg htri hpq]
  have hval : ∀ (i j : ZMod (geoCornerCount hG.cg T q)) (h : IsCrossing (geoCornerPolygon hG.cg T q) {i, j}),
      ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair h)).val =
        {(⟨0, i⟩ : (Shadow.single (geoCarrierPolyComp hn hG hT q)).Strand), ⟨0, j⟩} := by
    intro i j h
    show ({i, j} : Finset (ZMod (geoCornerCount hG.cg T q))).map _ = _
    rw [Finset.map_insert, Finset.map_singleton]
    rfl
  have hne : ∀ (i j : ZMod (geoCornerCount hG.cg T q)), i ≠ j →
      (⟨0, i⟩ : (Shadow.single (geoCarrierPolyComp hn hG hT q)).Strand) ≠ ⟨0, j⟩ := by
    intro i j hij h
    exact hij (congrArg (Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q)) h)
  have hsgn : IsAlternating
      (crossingSign (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) (G11_pE hn hG hT q hcef htri))
      (crossingSign (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) (G11_qE hn hG hT q hceg htri))
      (crossingSign (geoCornerPolygon hG.cg T q) (G11_pE hn hG hT q hcef htri) (G11_qE hn hG hT q hceg htri)) := by
    have h1 : crossingSign (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) (G11_pE hn hG hT q hcef htri) =
        crossingSign P e f :=
      G11_carrierSign hn hG hT q (G11_vef hcef) (G11_vfe hcef) _ _
    have h2 : crossingSign (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) (G11_qE hn hG hT q hceg htri) =
        crossingSign P e g :=
      G11_carrierSign hn hG hT q (G11_vef hcef) (G11_vge hceg) _ _
    have h3 : crossingSign (geoCornerPolygon hG.cg T q) (G11_pE hn hG hT q hcef htri) (G11_qE hn hG hT q hceg htri) =
        crossingSign P f g :=
      G11_carrierSign hn hG hT q (G11_vfe hcef) (G11_vge hceg) _ _
    rw [h1, h2, h3]
    exact halt
  have hclear_closed : ∀ h : ZMod (geoCornerCount hG.cg T q), h ≠ G11_mE hn hG hT q hcef htri →
      h ≠ G11_pE hn hG hT q hcef htri → h ≠ G11_qE hn hG hT q hceg htri →
      ∀ y ∈ edgeSegment (geoCornerPolygon hG.cg T q) h, y ∉ G11_triangle (geoCornerPolygon hG.cg T q) hmp hmq hpq := by
    intro h hm hp hq y hy hyΔ
    obtain ⟨w, hw, hwF⟩ := G11_preconnected_meets_frontier
      (G11_edgeSegment_isPreconnected (geoCornerPolygon hG.cg T q) h) ⟨y, hy, hyΔ⟩
      ⟨geoCornerPolygon hG.cg T q h, ⟨0, le_rfl, zero_le_one, (edgePoint_zero _ h).symm⟩,
        G11_cfg_clear_vertex hn hG hs hT q hcef hceg hcfg htri hef heg hfg hX h⟩
    exact G11_cfg_clear_frontier hn hG hs hT q hcef hceg hcfg htri hef heg hfg hX h hm hp hq w hw hwF
  have htri_eq : convexHull ℝ
      {(Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
          ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmp)),
        (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
          ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmq)),
        (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
          ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hpq))} =
      G11_triangle (geoCornerPolygon hG.cg T q) hmp hmq hpq := by
    unfold G11_triangle
    rw [cp, cp, cp]
  have hclear : ∀ u : (Shadow.single (geoCarrierPolyComp hn hG hT q)).Strand,
      u ≠ ⟨0, G11_mE hn hG hT q hcef htri⟩ → u ≠ ⟨0, G11_pE hn hG hT q hcef htri⟩ →
      u ≠ ⟨0, G11_qE hn hG hT q hceg htri⟩ →
      Disjoint ((Shadow.single (geoCarrierPolyComp hn hG hT q)).seg u) (convexHull ℝ
        {(Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
            ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmp)),
          (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
            ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmq)),
          (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
            ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hpq))}) := by
    intro u hu1 hu2 hu3
    rw [htri_eq, Set.disjoint_left]
    intro y hy hyΔ
    refine hclear_closed u.2 ?_ ?_ ?_ y hy hyΔ
    · intro h
      exact hu1 ((Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q)).injective
        (show Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q) u =
          Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q) ⟨0, _⟩ from h))
    · intro h
      exact hu2 ((Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q)).injective
        (show Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q) u =
          Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q) ⟨0, _⟩ from h))
    · intro h
      exact hu3 ((Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q)).injective
        (show Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q) u =
          Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q) ⟨0, _⟩ from h))
  have hvert : ∀ (i : Fin (Shadow.single (geoCarrierPolyComp hn hG hT q)).c)
      (l : ZMod ((Shadow.single (geoCarrierPolyComp hn hG hT q)).comp i).k),
      ((Shadow.single (geoCarrierPolyComp hn hG hT q)).comp i).P l ∉ convexHull ℝ
        {(Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
            ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmp)),
          (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
            ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmq)),
          (Shadow.single (geoCarrierPolyComp hn hG hT q)).crossingPoint
            ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hpq))} := by
    intro i l
    rw [htri_eq]
    exact G11_cfg_clear_vertex hn hG hs hT q hcef hceg hcfg htri hef heg hfg hX l
  have main := w3cs_siteData_of_triangle (Shadow.single (geoCarrierPolyComp hn hG hT q)) hgen
    ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmp))
    ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hmq))
    ((Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hpq))
    ⟨0, G11_mE hn hG hT q hcef htri⟩ ⟨0, G11_pE hn hG hT q hcef htri⟩ ⟨0, G11_qE hn hG hT q hceg htri⟩
    (hne _ _ (P1.ne_of_isCrossing_pair hmp)) (hne _ _ (P1.ne_of_isCrossing_pair hmq))
    (hne _ _ (P1.ne_of_isCrossing_pair hpq))
    (hval _ _ hmp) (hval _ _ hmq) (hval _ _ hpq) hsgn hclear hvert
  rw [hym, hzm] at main
  subst hxm
  exact main

/-- the transported triangle crossings are carried by the transported carrier (`hcarr`) -/
theorem w3cs_triangle_transport {P P' : LabelledTuple n} (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {e f g : ZMod n}
    {T : Finset (Crossing P)} {T' : Finset (Crossing P')} (q : GeoComponent hP T) (q' : GeoComponent hP' T')
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    (hcarr : geoCarrierCrossings hP' T' q' =
      (geoCarrierCrossings hP T q).map (crossingTransport hs).toEmbedding)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hP T q) :
    triangleCrossings P' e f g ⊆ geoCarrierCrossings hP' T' q' := by
  intro c hc
  rw [hcarr, Finset.mem_map_equiv]
  apply htri
  rw [P1.mem_triangleCrossings_iff hef heg hfg]
  rw [P1.mem_triangleCrossings_iff ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg)] at hc
  rcases hc with rfl | rfl | rfl
  · left; rfl
  · right; left; rfl
  · right; right; rfl

end W3CS_Lift

/-- **β1′ PROVED**: the site glue of `w3bi_wall_data_of` (the contact carrier owns the triangle, the transported
carrier is the contact carrier of the other side, `hcarr`), the alternating triple from `CompleteLocal`
(`w3e_alt_of_completeLocal`) transported by `AV_EventRadius.sign_eq`, then `w3cs_site_data_lift` on each side. -/
theorem w3cs__w3bi_site_data_data_proof : w3bi_site_data := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' q₀ q₀' hq₀ hq₀' x_H x_L
    hxH hxL
  have hef₀ : e ≠ f := P1.ne_of_isCrossing_pair hef
  have heg₀ : e ≠ g := P1.ne_of_isCrossing_pair heg
  have hfg₀ : f ≠ g := P1.ne_of_isCrossing_pair hfg
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  have hTq₀ := esc_contact_owns hL hef₀ heg₀ hfg₀ ht hQ hfull hq₀
  have W := GT_empty_wall hL hR hef₀ heg₀ hfg₀ ht ht' hop hs hQ
  have hcarr := GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q₀
  have hq₀'' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g
      (GT_carrierEquiv W q₀) := by
    rw [esc_not_triangleDisjoint_iff]
    have hmem : crossingTransport hs (xPair hef) ∈
        geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs Q) (GT_carrierEquiv W q₀) := by
      rw [hcarr, Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact hTq₀ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl))
    obtain ⟨i, -, -⟩ := crossing_visits_exist (crossingTransport hs (xPair hef))
    exact ⟨⟨_, i⟩, (P1.mem_triangleSupports _).mpr (Or.inl rfl),
      ((mem_geoCarrierCrossings _ _ _ _).mp hmem).2 _ rfl⟩
  have hq₀eq : q₀' = GT_carrierEquiv W q₀ :=
    esc_contact_unique hL hef₀ heg₀ hfg₀ ht' hQ' hfull' hq₀' hq₀''
  subst hq₀eq
  have hX := hL.gauss_words t t' ht ht' hop hs
  have halt : IsAlternating (crossingSign (E.curve t) e f) (crossingSign (E.curve t) e g)
      (crossingSign (E.curve t) f g) :=
    w3e_alt_of_completeLocal hGT t ht hef heg hfg hK
  have halt' : IsAlternating (crossingSign (E.curve t') e f) (crossingSign (E.curve t') e g)
      (crossingSign (E.curve t') f g) := by
    rw [hR.sign_eq t t' ht ht' e f hef, hR.sign_eq t t' ht ht' e g heg, hR.sign_eq t t' ht ht' f g hfg]
    exact halt
  have htri' := w3cs_triangle_transport _ _ hs q₀ (GT_carrierEquiv W q₀) hef heg hfg hcarr hTq₀
  unfold CV.carrierDiagram at x_H x_L hxH hxL ⊢
  exact ⟨w3cs_site_data_lift hn _ hs _ q₀ hef₀ heg₀ hfg₀ hef heg hfg hX hTq₀ halt x_H hxH,
    w3cs_site_data_lift hn _ (fun s => (hs s).symm) _ (GT_carrierEquiv W q₀) hef₀ heg₀ hfg₀
      ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) (w3cs_exact_symm hs hX) htri' halt' x_L hxL⟩


/-- the black box asserted (open body) -/
theorem w3bi_site_data_data : w3bi_site_data := by
  exact w3cs__w3bi_site_data_data_proof

/-! ### Unit SITE — the NON-KINK condition of unit G at the 177 site (stated; the site-level black box is OPEN,
W3C_SITE_REPORT.md §4) -/

/-- the two non-kink conditions of `w3bg_bigonData_smooth_arcST_of_not_kink` / `_arcTS_of_not_kink` at `x`: the
strand before `s` is not the strand after `t`, and the strand before `t` is not the strand after `s` (on the
one-component lift: the two strands of `x` are not at cyclic distance `2`, so the oriented smoothing of `x` does not
split off a `4`-gon). -/
def w3cs_NotKink (D : Diagram) (x : D.Γ.Crossing) : Prop :=
  (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩ ∧
  (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩

/-- the `hkink` of `w3bg_bigonData_smooth_arcST_of_not_kink` / `w3bg_hk5_arcST_of_not_kink` -/
theorem w3cs_not_kink_arcST (D : Diagram) (x : D.Γ.Crossing) (h : w3cs_NotKink D x) :
    (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩ := h.1

/-- the `hkink` of `w3bg_bigonData_smooth_arcTS_of_not_kink` / `w3bg_hk5_arcTS_of_not_kink` -/
theorem w3cs_not_kink_arcTS (D : Diagram) (x : D.Γ.Crossing) (h : w3cs_NotKink D x) :
    (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩ := h.2

/-- **BLACK BOX (SITE, OPEN — rule (4), reported)**: at every 177 configuration the lift crossing over `x_ef` is
not a kink of the one-component lift, on both sides.  This is NOT a consequence of `w3bi_SiteData` (the report
gives a numerical kink loop `p = m − 2` cut by `q` that satisfies D4, D5, `clear` and `clear_vertex`); at the lift
level it says that the carrier edges `m = G11_mE`, `p = G11_pE` of `x_ef` are not at cyclic distance `2` in
`geoCornerPolygon` (equivalently the oriented smoothing of `x_H` does not split off a `4`-gon component), a
combinatorial fact about the corner polygon of the contact carrier that the present hypotheses do not obviously
imply (`outsideSupports` excludes only the three triangle crossings from `Q`). -/
def w3cs_not_kink_site : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∀ (x_H : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Crossing)
        (x_L : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.Crossing),
        (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.crossingPoint x_H = crossingPoint (xPair hef) →
        (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.crossingPoint x_L =
          crossingPoint (xPair ((hs _).mp hef)) →
        w3cs_NotKink (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) x_H ∧
        w3cs_NotKink (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_L

/-- the black box asserted (OPEN body; W3C_SITE_REPORT.md §4) -/
theorem w3cs_not_kink_site_data : w3cs_not_kink_site := by
  sorry


/-- **β1 from β1′ (PROVED)**: one bigon per side by `w3bi_bigon_of_site`. -/
theorem w3bi_bigon_pair_of (hsite : w3bi_site_data) : w3bi_bigon_pair := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' q₀ q₀' hq₀ hq₀' x_H x_L
    hxH hxL y_H y_L hyH hyL
  obtain ⟨sH, sL⟩ := hsite hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' q₀ q₀'
    hq₀ hq₀' x_H x_L hxH hxL
  obtain ⟨z_H, hzH, B_H, hBH⟩ := w3bi_bigon_of_site _ x_H _ _ sH y_H hyH
  obtain ⟨z_L, hzL, B_L, hBL⟩ := w3bi_bigon_of_site _ x_L _ _ sL y_L hyL
  exact ⟨z_H, z_L, hzH, hzL, B_H, B_L, hBH, hBL⟩

/-- β1 with β1′ asserted -/
theorem w3bi_bigon_pair_data : w3bi_bigon_pair := w3bi_bigon_pair_of w3bi_site_data_data

section W3BI_Lift
variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {e f g : ZMod n}
  {T : Finset (Crossing P)} {T' : Finset (Crossing P')}
  (hT : GeoIndependent hG.cg T) (hT' : GeoIndependent hG'.cg T')
  (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T')

/-- **The wall bijection of the two UNSWITCHED lifts (D6, the reusable core of β2)** — the `Λ` of the
accepted `G11_recordIsoData` (:10852–10920) on its own, `halt`-free: `Λ` lifts `visitTransport` through
`CV.liftVisitEquiv` (`hcarr`), carries twins (`liftVisit_twin`, `visitTransport_visitTwin`), the over
bits (a positive lift's bit is the divide sign, carried by `hdet`), the signs (all `+1`,
`geoPositiveLift_sign`), and the cyclic order TWISTED by any `σ` lifting `G11_σP` (`visitBetween_iff_key`,
`G11_twisted_key_lt`, `GT_cyc_congr_of_lt`).  What β2 (`w3bi_wall_data`) still needs on top: the six local
lift visits `a₁ b₁ | a₂ c₁ | b₂ c₂` over `G11_vef, vfe | veg, vge | vfg, vgf` (`G11_mem_tri_*` + `htri`),
`σ := swap a₁ a₂ * (swap b₁ b₂ * swap c₁ c₂)` lifting `G11_σP` (`Function.Injective.swap_apply` with
`liftVisit_injective`), and the adjacency of the local pairs on each strand (`LocalizationData.adjacent`
lifted to `nextVisit`). -/
theorem w3bi_wallEquiv (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (hdet : ∀ i j : ZMod n, IsCrossing P {i, j} →
      (0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i) (edge P' j)))
    (hcarr : geoCarrierCrossings hG'.cg T' q' =
      (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding) :
    ∃ Λ : (geoPositiveLift hn hG hT q).Γ.Visit ≃ (geoPositiveLift hn hG' hT' q').Γ.Visit,
      (∀ v, CV.liftVisit hn hG' hT' q' (Λ v) = visitTransport hs (CV.liftVisit hn hG hT q v)) ∧
      (∀ v, Λ ((geoPositiveLift hn hG hT q).twin v) = (geoPositiveLift hn hG' hT' q').twin (Λ v)) ∧
      (∀ v, (geoPositiveLift hn hG' hT' q').overBit (Λ v) = (geoPositiveLift hn hG hT q).overBit v) ∧
      (∀ v, (geoPositiveLift hn hG' hT' q').sign (Λ v).1 = (geoPositiveLift hn hG hT q).sign v.1) ∧
      (∀ σ : Equiv.Perm (geoPositiveLift hn hG hT q).Γ.Visit,
        (∀ v, CV.liftVisit hn hG hT q (σ v) = G11_σP hcef hceg hcfg (CV.liftVisit hn hG hT q v)) →
        ∀ u v w, (geoPositiveLift hn hG' hT' q').VisitBetween (Λ u) (Λ v) (Λ w) ↔
          (geoPositiveLift hn hG hT q).VisitBetween (σ u) (σ v) (σ w)) := by
  let ψ : {w : Visit P // w.1 ∈ geoCarrierCrossings hG.cg T q} ≃
      {w : Visit P' // w.1 ∈ geoCarrierCrossings hG'.cg T' q'} :=
    (visitTransport hs).subtypeEquiv fun w => by
      rw [hcarr, visitTransport_crossing, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  let Λ : (geoPositiveLift hn hG hT q).Γ.Visit ≃ (geoPositiveLift hn hG' hT' q').Γ.Visit :=
    (CV.liftVisitEquiv hn hG hT q).trans (ψ.trans (CV.liftVisitEquiv hn hG' hT' q').symm)
  have hΛ : ∀ v, CV.liftVisit hn hG' hT' q' (Λ v) = visitTransport hs (CV.liftVisit hn hG hT q v) := by
    intro v
    show CV.liftVisit hn hG' hT' q'
      ((CV.liftVisitEquiv hn hG' hT' q').symm (ψ (CV.liftVisitEquiv hn hG hT q v))) = _
    rw [CV.liftVisit_symm]
    rfl
  have hΛtw : ∀ v, Λ ((geoPositiveLift hn hG hT q).twin v) = (geoPositiveLift hn hG' hT' q').twin (Λ v) := by
    intro v
    apply CV.liftVisit_injective hn hG' hT' q'
    rw [hΛ, CV.liftVisit_twin, CV.liftVisit_twin, hΛ, visitTransport_visitTwin]
  refine ⟨Λ, hΛ, hΛtw, ?_, ?_, ?_⟩
  · intro v
    rw [Bool.eq_iff_iff, CV.overBit_eq_true_iff_parent, CV.overBit_eq_true_iff_parent, hΛ,
      visitTransport_edge, ← visitTransport_visitTwin, visitTransport_edge]
    exact (hdet _ _ (by rw [← visit_crossing_val_eq_pair]; exact (CV.liftVisit hn hG hT q _).1.property)).symm
  · intro v
    rw [geoPositiveLift_sign, geoPositiveLift_sign]
  · intro σ hσ u v w
    rw [CV.visitBetween_iff_key, hΛ, hΛ, hΛ, CV.visitBetween_iff_key, hσ, hσ, hσ]
    exact (GT_cyc_congr_of_lt
      (G11_twisted_key_lt hG hG' hs hef heg hfg hcef hceg hcfg hX _ _)
      (G11_twisted_key_lt hG hG' hs hef heg hfg hcef hceg hcfg hX _ _)
      (G11_twisted_key_lt hG hG' hs hef heg hfg hcef hceg hcfg hX _ _)).symm


/-- **β2a (adjacency lifted to the carrier lift; PROVED below, `w3bi_adjacent_lift_proof`)**: two visits of the lift whose parents are
adjacent on the traversal circle of `P` (`AdjacentVisits`, R-LOC (2): no visit of `P` strictly between, in
one of the two directions) are consecutive on the one-component lift (`nextVisit`; the lift's visits are a
subset of `P`'s, ordered by the same key: `visitBetween_iff_key`, `traversalBetween_iff_cycBetween`,
`nextVisit_no_between` + the uniqueness of the cyclic successor). -/
def w3bi_adjacent_lift : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)
    (v w : (geoPositiveLift hn hG hT q).Γ.Visit),
    AdjacentVisits hG.cg (CV.liftVisit hn hG hT q v) (CV.liftVisit hn hG hT q w) →
    (geoPositiveLift hn hG hT q).nextVisit v = w ∨ (geoPositiveLift hn hG hT q).nextVisit w = v

/-- three distinct reals are cyclically ordered one way or the other -/
theorem w3bi_cycBetween_or {a b c : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cycBetween a b c ∨ cycBetween a c b := by
  unfold cycBetween
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
    rcases lt_or_gt_of_ne hac with h3 | h3
  all_goals first
    | (left; first | exact Or.inl ⟨h1, h2⟩ | exact Or.inr (Or.inl ⟨h2, h3⟩) | exact Or.inr (Or.inr ⟨h3, h1⟩))
    | (right; first | exact Or.inl ⟨h3, h2⟩ | exact Or.inr (Or.inl ⟨h2, h1⟩) | exact Or.inr (Or.inr ⟨h1, h3⟩))

/-- **β2a PROVED**: on the one-component lift every two visits share the component
(`compOf_eq_of_single`), `VisitBetween` is the cyclic order of the parents' traversal keys
(`visitBetween_iff_key`), and the cyclic successor is the unique visit with nothing strictly between
(`not_visitBetween_nextVisit`, `nextVisit_ne_self`, `visitCoord_injOn`, the trichotomy above). -/
theorem w3bi_adjacent_lift_proof : w3bi_adjacent_lift := by
  intro n _ hn P hG T hT q v w hadj
  obtain ⟨hne, hcase⟩ := hadj
  have hvw : v ≠ w := fun h => hne (by rw [h])
  have hc1 : ∀ a b : (geoPositiveLift hn hG hT q).Γ.Visit,
      (geoPositiveLift hn hG hT q).compOf a = (geoPositiveLift hn hG hT q).compOf b :=
    CV.compOf_eq_of_single rfl
  have hkey : ∀ a b c : (geoPositiveLift hn hG hT q).Γ.Visit,
      (geoPositiveLift hn hG hT q).VisitBetween a b c ↔
        traversalBetween (geometricVisitPosition hG.cg (CV.liftVisit hn hG hT q a))
          (geometricVisitPosition hG.cg (CV.liftVisit hn hG hT q b))
          (geometricVisitPosition hG.cg (CV.liftVisit hn hG hT q c)) := fun a b c => by
    rw [CV.visitBetween_iff_key]
    exact Iff.rfl
  have tri : ∀ a b c : (geoPositiveLift hn hG hT q).Γ.Visit, a ≠ b → b ≠ c → a ≠ c →
      (geoPositiveLift hn hG hT q).VisitBetween a b c ∨ (geoPositiveLift hn hG hT q).VisitBetween a c b := by
    intro a b c hab hbc hac
    exact w3bi_cycBetween_or (fun h => hab ((geoPositiveLift hn hG hT q).visitCoord_injOn (hc1 a b) h))
      (fun h => hbc ((geoPositiveLift hn hG hT q).visitCoord_injOn (hc1 b c) h))
      (fun h => hac ((geoPositiveLift hn hG hT q).visitCoord_injOn (hc1 a c) h))
  rcases hcase with h | h
  · left
    by_contra hne'
    have hn1 : (geoPositiveLift hn hG hT q).nextVisit v ≠ v :=
      (geoPositiveLift hn hG hT q).nextVisit_ne_self v w (hc1 w v) hvw.symm
    rcases tri v w _ hvw (Ne.symm hne') hn1.symm with hb | hb
    · exact (geoPositiveLift hn hG hT q).not_visitBetween_nextVisit v w (hc1 w v) hb
    · exact h _ ((hkey _ _ _).mp hb)
  · right
    by_contra hne'
    have hn1 : (geoPositiveLift hn hG hT q).nextVisit w ≠ w :=
      (geoPositiveLift hn hG hT q).nextVisit_ne_self w v (hc1 v w) hvw
    rcases tri w v _ hvw.symm (Ne.symm hne') hn1.symm with hb | hb
    · exact (geoPositiveLift hn hG hT q).not_visitBetween_nextVisit w v (hc1 v w) hb
    · exact h _ ((hkey _ _ _).mp hb)

/-- β2a, PROVED (kept under its black-box name for the consumers below) -/
theorem w3bi_adjacent_lift_data : w3bi_adjacent_lift := w3bi_adjacent_lift_proof

/-- **β2 at the lift level (PROVED from `w3bi_wallEquiv` and β2a)**: the six local lift visits
`a₁ b₁ | a₂ c₁ | b₂ c₂` over `G11_vef, vfe | veg, vge | vfg, vgf`, `σ = swap a₁ a₂ * (swap b₁ b₂ * swap c₁ c₂)`
lifting `G11_σP` (`Function.Injective.swap_apply`), twins (`liftVisit_twin`, `gu2_visitTwin_*`), the double
points (`liftVisit_fst`, `crossingPoint_liftCrossing`), the transported crossings (generic injectivity on
the empty-side lift), adjacency through β2a. -/
theorem w3bi_wall_data_lift (hadjl : w3bi_adjacent_lift) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (hdet : ∀ i j : ZMod n, IsCrossing P {i, j} →
      (0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i) (edge P' j)))
    (hcarr : geoCarrierCrossings hG'.cg T' q' =
      (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q)
    (hadjE : AdjacentVisits hG.cg (G11_vef hcef) (G11_veg hceg))
    (hadjF : AdjacentVisits hG.cg (G11_vfe hcef) (G11_vfg hcfg))
    (hadjG : AdjacentVisits hG.cg (G11_vge hceg) (G11_vgf hcfg))
    (x_H : (geoPositiveLift hn hG hT q).Γ.Crossing) (x_L : (geoPositiveLift hn hG' hT' q').Γ.Crossing)
    (hxH : (geoPositiveLift hn hG hT q).Γ.crossingPoint x_H = crossingPoint (xPair hcef))
    (hxL : (geoPositiveLift hn hG' hT' q').Γ.crossingPoint x_L = crossingPoint (crossingTransport hs (xPair hcef))) :
    ∃ (y_H z_H : (geoPositiveLift hn hG hT q).Γ.Crossing) (y_L z_L : (geoPositiveLift hn hG' hT' q').Γ.Crossing)
      (Ψ : (geoPositiveLift hn hG hT q).Γ.Visit ≃ (geoPositiveLift hn hG' hT' q').Γ.Visit) (a₁ a₂ b₁ b₂ c₁ c₂ : (geoPositiveLift hn hG hT q).Γ.Visit),
      (geoPositiveLift hn hG hT q).Γ.crossingPoint y_H = crossingPoint (xPair hceg) ∧
      (geoPositiveLift hn hG hT q).Γ.crossingPoint z_H = crossingPoint (xPair hcfg) ∧
      (geoPositiveLift hn hG' hT' q').Γ.crossingPoint y_L = crossingPoint (crossingTransport hs (xPair hceg)) ∧
      (geoPositiveLift hn hG' hT' q').Γ.crossingPoint z_L = crossingPoint (crossingTransport hs (xPair hcfg)) ∧
      a₁.1 = x_H ∧ b₁ = (geoPositiveLift hn hG hT q).twin a₁ ∧ a₂.1 = y_H ∧ c₁ = (geoPositiveLift hn hG hT q).twin a₂ ∧ b₂.1 = z_H ∧ c₂ = (geoPositiveLift hn hG hT q).twin b₂ ∧
      ((geoPositiveLift hn hG hT q).nextVisit a₁ = a₂ ∨ (geoPositiveLift hn hG hT q).nextVisit a₂ = a₁) ∧
      ((geoPositiveLift hn hG hT q).nextVisit b₁ = b₂ ∨ (geoPositiveLift hn hG hT q).nextVisit b₂ = b₁) ∧
      ((geoPositiveLift hn hG hT q).nextVisit c₁ = c₂ ∨ (geoPositiveLift hn hG hT q).nextVisit c₂ = c₁) ∧
      (∀ v, Ψ ((geoPositiveLift hn hG hT q).twin v) = (geoPositiveLift hn hG' hT' q').twin (Ψ v)) ∧
      (∀ v, (geoPositiveLift hn hG' hT' q').overBit (Ψ v) = (geoPositiveLift hn hG hT q).overBit v) ∧
      (∀ v, (geoPositiveLift hn hG' hT' q').sign (Ψ v).1 = (geoPositiveLift hn hG hT q).sign v.1) ∧
      (∀ u v w, (geoPositiveLift hn hG' hT' q').VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔
        (geoPositiveLift hn hG hT q).VisitBetween ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) u) ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v) ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) w)) ∧
      (Ψ a₁).1 = x_L ∧ (Ψ a₂).1 = y_L ∧ (Ψ b₂).1 = z_L := by
  obtain ⟨Λ, hΛ, hΛtw, hΛbit, hΛsgn, hΛcyc⟩ :=
    w3bi_wallEquiv hn hG hG' hs hT hT' q q' hef heg hfg hcef hceg hcfg hX hdet hcarr
  -- the six local lift visits
  let a₁ : (geoPositiveLift hn hG hT q).Γ.Visit := (CV.liftVisitEquiv hn hG hT q).symm ⟨G11_vef hcef, G11_mem_tri_ef hG q hcef htri⟩
  let b₁ : (geoPositiveLift hn hG hT q).Γ.Visit := (CV.liftVisitEquiv hn hG hT q).symm ⟨G11_vfe hcef, G11_mem_tri_ef hG q hcef htri⟩
  let a₂ : (geoPositiveLift hn hG hT q).Γ.Visit := (CV.liftVisitEquiv hn hG hT q).symm ⟨G11_veg hceg, G11_mem_tri_eg hG q hceg htri⟩
  let c₁ : (geoPositiveLift hn hG hT q).Γ.Visit := (CV.liftVisitEquiv hn hG hT q).symm ⟨G11_vge hceg, G11_mem_tri_eg hG q hceg htri⟩
  let b₂ : (geoPositiveLift hn hG hT q).Γ.Visit := (CV.liftVisitEquiv hn hG hT q).symm ⟨G11_vfg hcfg, G11_mem_tri_fg hG q hcfg htri⟩
  let c₂ : (geoPositiveLift hn hG hT q).Γ.Visit := (CV.liftVisitEquiv hn hG hT q).symm ⟨G11_vgf hcfg, G11_mem_tri_fg hG q hcfg htri⟩
  have la₁ : CV.liftVisit hn hG hT q a₁ = G11_vef hcef := CV.liftVisit_symm hn hG hT q _
  have lb₁ : CV.liftVisit hn hG hT q b₁ = G11_vfe hcef := CV.liftVisit_symm hn hG hT q _
  have la₂ : CV.liftVisit hn hG hT q a₂ = G11_veg hceg := CV.liftVisit_symm hn hG hT q _
  have lc₁ : CV.liftVisit hn hG hT q c₁ = G11_vge hceg := CV.liftVisit_symm hn hG hT q _
  have lb₂ : CV.liftVisit hn hG hT q b₂ = G11_vfg hcfg := CV.liftVisit_symm hn hG hT q _
  have lc₂ : CV.liftVisit hn hG hT q c₂ = G11_vgf hcfg := CV.liftVisit_symm hn hG hT q _
  have hinj := CV.liftVisit_injective hn hG hT q
  -- double points of the lift crossings through the parents
  have hpt : ∀ v : (geoPositiveLift hn hG hT q).Γ.Visit,
      (geoPositiveLift hn hG hT q).Γ.crossingPoint v.1 = crossingPoint (CV.liftVisit hn hG hT q v).1 := fun v => by
    rw [CV.liftVisit_fst, CV.crossingPoint_liftCrossing]
  have hpt' : ∀ v : (geoPositiveLift hn hG' hT' q').Γ.Visit,
      (geoPositiveLift hn hG' hT' q').Γ.crossingPoint v.1 = crossingPoint (CV.liftVisit hn hG' hT' q' v).1 := fun v => by
    rw [CV.liftVisit_fst, CV.crossingPoint_liftCrossing]
  -- the twisting permutation lifts `σ_P`
  have hσ : ∀ v, CV.liftVisit hn hG hT q ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v) =
      G11_σP hcef hceg hcfg (CV.liftVisit hn hG hT q v) := by
    intro v
    simp only [G11_σP, Equiv.Perm.mul_apply]
    rw [← la₁, ← la₂, ← lb₁, ← lb₂, ← lc₁, ← lc₂, hinj.swap_apply, hinj.swap_apply, hinj.swap_apply]
  refine ⟨a₂.1, b₂.1, (Λ a₂).1, (Λ b₂).1, Λ, a₁, a₂, b₁, b₂, c₁, c₂, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, rfl, ?_,
    ?_, ?_, ?_, hΛtw, hΛbit, hΛsgn, hΛcyc _ hσ, ?_, rfl, rfl⟩
  · rw [hpt, la₂]; rfl
  · rw [hpt, lb₂]; rfl
  · rw [hpt', hΛ, la₂]; rfl
  · rw [hpt', hΛ, lb₂]; rfl
  · exact (geoPositiveLift hn hG hT q).generic.crossingPoint_injective (by rw [hpt, la₁, hxH]; rfl)
  · exact hinj (by rw [CV.liftVisit_twin, la₁, lb₁, gu2_visitTwin_vef])
  · exact hinj (by rw [CV.liftVisit_twin, la₂, lc₁, gu2_visitTwin_veg])
  · exact hinj (by rw [CV.liftVisit_twin, lb₂, lc₂, gu2_visitTwin_vfg])
  · exact hadjl hn hG hT q a₁ a₂ (by rw [la₁, la₂]; exact hadjE)
  · exact hadjl hn hG hT q b₁ b₂ (by rw [lb₁, lb₂]; exact hadjF)
  · exact hadjl hn hG hT q c₁ c₂ (by rw [lc₁, lc₂]; exact hadjG)
  · exact (geoPositiveLift hn hG' hT' q').generic.crossingPoint_injective (by rw [hpt', hΛ, la₁, hxL]; rfl)

end W3BI_Lift

/-- **BLACK BOX β2 (G11 Unit F at the 177 site, D6)**: the wall bijection `Ψ` between the two UNSWITCHED
lifts with twins, bits, signs and the cyclic order twisted by the three transpositions on the six local
visits (the `G11_core_statement` shape, `G11_twisted_key_lt` + `visitTransport`), the local visits
`a₁ b₁ | a₂ c₁ | b₂ c₂` of `x, y, z` (`x = x_ef`, `y = x_eg`, `z = x_fg`) with adjacency on each strand
(R-LOC (2), `LocalizationData.adjacent`), the transported crossings — exactly the inputs of `w3h_hrec`. -/
def w3bi_wall_data : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ) (_hGT : GenericTableData E e f g δ) (_hR : AV_EventRadius E δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∀ (x_H : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Crossing)
        (x_L : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.Crossing),
        (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.crossingPoint x_H = crossingPoint (xPair hef) →
        (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.crossingPoint x_L =
          crossingPoint (xPair ((hs _).mp hef)) →
        ∃ (y_H z_H : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Crossing)
          (y_L z_L : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.Crossing)
          (Ψ : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Visit ≃ (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.Visit)
          (a₁ a₂ b₁ b₂ c₁ c₂ : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Visit),
          (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.crossingPoint y_H = crossingPoint (xPair heg) ∧
          (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.crossingPoint z_H = crossingPoint (xPair hfg) ∧
          (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.crossingPoint y_L = crossingPoint (xPair ((hs _).mp heg)) ∧
          (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.crossingPoint z_L = crossingPoint (xPair ((hs _).mp hfg)) ∧
          a₁.1 = x_H ∧ b₁ = (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).twin a₁ ∧
          a₂.1 = y_H ∧ c₁ = (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).twin a₂ ∧
          b₂.1 = z_H ∧ c₂ = (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).twin b₂ ∧
          ((CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).nextVisit a₁ = a₂ ∨
            (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).nextVisit a₂ = a₁) ∧
          ((CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).nextVisit b₁ = b₂ ∨
            (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).nextVisit b₂ = b₁) ∧
          ((CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).nextVisit c₁ = c₂ ∨
            (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).nextVisit c₂ = c₁) ∧
          (∀ v, Ψ ((CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).twin v) = (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').twin (Ψ v)) ∧
          (∀ v, (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').overBit (Ψ v) = (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).overBit v) ∧
          (∀ v, (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').sign (Ψ v).1 = (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).sign v.1) ∧
          (∀ u v w, (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔
            (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).VisitBetween ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) u) ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v) ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) w)) ∧
          (Ψ a₁).1 = x_L ∧ (Ψ a₂).1 = y_L ∧ (Ψ b₂).1 = z_L

/-- **β2 at the site (PROVED from β2a)**: `q₀'` is the wall image of `q₀` (`esc_contact_unique`), `hcarr`
from `GT_empty_wall`, `htri` from `esc_contact_owns`, `hX` from `hL.gauss_words`, `hdet` from `hR.sign_eq`,
the three adjacencies from `hL.adjacent` (R-LOC (2)); then `w3bi_wall_data_lift` after
`unfold CV.carrierDiagram`. -/
theorem w3bi_wall_data_of (hadjl : w3bi_adjacent_lift) : w3bi_wall_data := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' q₀ q₀' hq₀ hq₀' x_H x_L
    hxH hxL
  have hef₀ : e ≠ f := P1.ne_of_isCrossing_pair hef
  have heg₀ : e ≠ g := P1.ne_of_isCrossing_pair heg
  have hfg₀ : f ≠ g := P1.ne_of_isCrossing_pair hfg
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  have hTq₀ := esc_contact_owns hL hef₀ heg₀ hfg₀ ht hQ hfull hq₀
  have W := GT_empty_wall hL hR hef₀ heg₀ hfg₀ ht ht' hop hs hQ
  have hcarr := GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q₀
  have hq₀'' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g
      (GT_carrierEquiv W q₀) := by
    rw [esc_not_triangleDisjoint_iff]
    have hmem : crossingTransport hs (xPair hef) ∈
        geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs Q) (GT_carrierEquiv W q₀) := by
      rw [hcarr, Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact hTq₀ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl))
    obtain ⟨i, -, -⟩ := crossing_visits_exist (crossingTransport hs (xPair hef))
    exact ⟨⟨_, i⟩, (P1.mem_triangleSupports _).mpr (Or.inl rfl),
      ((mem_geoCarrierCrossings _ _ _ _).mp hmem).2 _ rfl⟩
  have hq₀eq : q₀' = GT_carrierEquiv W q₀ :=
    esc_contact_unique hL hef₀ heg₀ hfg₀ ht' hQ' hfull' hq₀' hq₀''
  subst hq₀eq
  have hX := hL.gauss_words t t' ht ht' hop hs
  have hdet : ∀ i j : ZMod n, IsCrossing (E.curve t) {i, j} →
      (0 < det (edge (E.curve t) i) (edge (E.curve t) j) ↔
        0 < det (edge (E.curve t') i) (edge (E.curve t') j)) :=
    fun i j hij => GT_det_pos_iff_of_sign (hR.sign_eq t t' ht ht' i j hij)
  obtain ⟨hadjE, hadjF, hadjG⟩ := hL.adjacent t ht hef heg hfg
  unfold CV.carrierDiagram at x_H x_L hxH hxL ⊢
  exact w3bi_wall_data_lift hn _ _ hs _ _ q₀ _ hadjl hef₀ heg₀ hfg₀ hef heg hfg hX hdet hcarr hTq₀ hadjE hadjF
    hadjG x_H x_L hxH hxL

/-- β2 with β2a asserted -/
theorem w3bi_wall_data_data : w3bi_wall_data :=
  w3bi_wall_data_of w3bi_adjacent_lift_data

/-! ### Assembler connections (prefix `w3ba_`, W3B_ASSEMBLY_REPORT.md): unit H's bridge and `w3h_hrec` in the
orientation-general form REAL's `w3bi_hrec_general` needs.  `BigonData.keep` is symmetric in `B.y, B.z`, so the
text of `w3bh_reduced_to_smooth` proves the disjunctive form with one `and_comm`; `w3ba_hrec_gen` is the text of
`w3h_hrec` calling it (derived from W3B_H.lean by `assemble_W3B_connect.py`). -/

/-- `w3bh_reduced_to_smooth` with `{B.y, B.z} = {y₀, z₀}` in either order (assembler copy). -/
theorem w3ba_reduced_to_smooth_gen (D : Diagram) (x y z : D.Γ.Crossing)
    (a₁ a₂ b₂ c₁ c₂ : D.Γ.Visit) (ha₁ : a₁.1 = x) (ha₂ : a₂.1 = y) (hc₁ : c₁ = D.twin a₂)
    (hb₂ : b₂.1 = z) (hc₂ : c₂ = D.twin b₂)
    {ε : ℝ} (hε : SmallEps D x ε)
    (y₀ z₀ : (smoothDiagram D x ε hε).Γ.Crossing)
    (hy₀ : (smoothDiagram D x ε hε).Γ.crossingPoint y₀ = D.Γ.crossingPoint y)
    (hz₀ : (smoothDiagram D x ε hε).Γ.crossingPoint z₀ = D.Γ.crossingPoint z)
    (B : BigonData ((smoothDiagram D x ε hε).switch y₀))
    (hB : (B.y = y₀ ∧ B.z = z₀) ∨ (B.y = z₀ ∧ B.z = y₀)) :
    Nonempty (RecordIso B.reducedRecord
      ((D.record.smooth a₁).restrictCrossings
        {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ c₁ ∧ v.1 ≠ b₂ ∧ v.1 ≠ c₂})) := by
  subst hc₁ hc₂
  -- the occurrence-defined retained set on `E = smoothDiagram D x ε hε`
  let X₁ : Set (smoothDiagram D x ε hε).record.Crossing := {c | ∀ w ∈ c.1, w.1 ≠ y₀ ∧ w.1 ≠ z₀}
  have hX₁ : ∀ u : (smoothDiagram D x ε hε).Γ.Visit,
      (smoothDiagram D x ε hε).record.crossingOf u ∈ X₁ ↔ (u.1 ≠ y₀ ∧ u.1 ≠ z₀) := by
    intro u
    rw [w3bh_crossingOf_mem_setOf]
    show (u.1 ≠ y₀ ∧ u.1 ≠ z₀) ∧
      (((smoothDiagram D x ε hε).twin u).1 ≠ y₀ ∧ ((smoothDiagram D x ε hε).twin u).1 ≠ z₀) ↔ _
    rw [Diagram.twin_fst, and_self]
  -- Step A/B: `B.reducedRecord ≅ (E.record.switch v₀).restrictCrossings X₁`
  obtain ⟨ι₂⟩ := w3bh_restrictCrossings_iso_of_recordIso
    ((smoothDiagram D x ε hε).switchRecordIso y₀ ((smoothDiagram D x ε hε).overVisit y₀) rfl) B.keep X₁ (by
    intro u
    show (((smoothDiagram D x ε hε).switch y₀).record.crossingOf u ≠
        ((smoothDiagram D x ε hε).switch y₀).record.crossingOf
          (((smoothDiagram D x ε hε).switch y₀).overVisit B.y) ∧
      ((smoothDiagram D x ε hε).switch y₀).record.crossingOf u ≠
        ((smoothDiagram D x ε hε).switch y₀).record.crossingOf
          (((smoothDiagram D x ε hε).switch y₀).overVisit B.z)) ↔
      (smoothDiagram D x ε hε).record.crossingOf u ∈ X₁
    rw [Ne, Ne, w3bh_record_crossingOf_eq_iff, w3bh_record_crossingOf_eq_iff, Diagram.overVisit_fst,
      Diagram.overVisit_fst]
    rcases hB with ⟨hBy, hBz⟩ | ⟨hBy, hBz⟩
    · rw [hBy, hBz]; exact (hX₁ u).symm
    · rw [hBy, hBz]; exact and_comm.trans (hX₁ u).symm)
  -- Step C: the switch at the deleted `y₀` is invisible
  obtain ⟨ι₃⟩ := w3h_restrict_switch_deleted (smoothDiagram D x ε hε).record X₁
    ((smoothDiagram D x ε hε).overVisit y₀) (fun h => ((hX₁ _).mp h).1 rfl)
  -- Step D: the smoothing bridge
  obtain ⟨ι₄, hι₄⟩ := w3h_smooth_record_occ D x ε hε
  have hpt : ∀ (u : (smoothDiagram D x ε hε).Γ.Visit) (w : D.Γ.Crossing)
      (w₀ : (smoothDiagram D x ε hε).Γ.Crossing)
      (hw₀ : (smoothDiagram D x ε hε).Γ.crossingPoint w₀ = D.Γ.crossingPoint w),
      (ι₄.Φ u).1.1 = w ↔ u.1 = w₀ := by
    intro u w w₀ hw₀
    constructor
    · intro h
      apply (smoothDiagram D x ε hε).generic.crossingPoint_injective
      rw [← hι₄ u, h, hw₀]
    · intro h
      apply D.generic.crossingPoint_injective
      rw [hι₄ u, h, hw₀]
  let X₂ : Set (D.record.smooth (D.overVisit x)).Crossing :=
    {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ D.twin a₂ ∧ v.1 ≠ b₂ ∧ v.1 ≠ D.twin b₂}
  have hP : ∀ w : D.Γ.Visit, (w ≠ a₂ ∧ w ≠ D.twin a₂ ∧ w ≠ b₂ ∧ w ≠ D.twin b₂) ↔
      (w.1 ≠ y ∧ w.1 ≠ z) := by
    intro w
    rw [← and_assoc, w3bh_ne_ne_twin_iff, w3bh_ne_ne_twin_iff, ha₂, hb₂]
  have hX₂ : ∀ u : (smoothDiagram D x ε hε).Γ.Visit, (smoothDiagram D x ε hε).record.crossingOf u ∈ X₁ ↔
      (D.record.smooth (D.overVisit x)).crossingOf (ι₄.Φ u) ∈ X₂ := by
    intro u
    rw [hX₁, w3bh_crossingOf_mem_setOf]
    show (u.1 ≠ y₀ ∧ u.1 ≠ z₀) ↔
      ((ι₄.Φ u).1 ≠ a₂ ∧ (ι₄.Φ u).1 ≠ D.twin a₂ ∧ (ι₄.Φ u).1 ≠ b₂ ∧ (ι₄.Φ u).1 ≠ D.twin b₂) ∧
      (D.twin (ι₄.Φ u).1 ≠ a₂ ∧ D.twin (ι₄.Φ u).1 ≠ D.twin a₂ ∧ D.twin (ι₄.Φ u).1 ≠ b₂ ∧
        D.twin (ι₄.Φ u).1 ≠ D.twin b₂)
    rw [hP, hP, Diagram.twin_fst, and_self]
    exact Iff.and (not_congr (hpt u y y₀ hy₀).symm) (not_congr (hpt u z z₀ hz₀).symm)
  obtain ⟨ι₅⟩ := w3bh_restrictCrossings_iso_of_recordIso ι₄ X₁ X₂ hX₂
  -- Step E: land on `a₁`
  rcases D.eq_or_eq_twin (D.overVisit x) a₁ ha₁ with h | h
  · subst h
    exact ⟨ι₂.trans (ι₃.trans ι₅)⟩
  · subst h
    obtain ⟨ι₆⟩ := w3bh_restrictCrossings_iso_of_recordIso (D.record.smoothPairIso (D.overVisit x)).symm X₂
      {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ D.twin a₂ ∧ v.1 ≠ b₂ ∧ v.1 ≠ D.twin b₂} (by
        intro u
        rw [w3bh_crossingOf_mem_setOf, w3bh_crossingOf_mem_setOf]
        exact Iff.rfl)
    exact ⟨ι₂.trans (ι₃.trans (ι₅.trans ι₆))⟩

/-- `w3h_hrec` with either orientation on either side (assembler copy of unit H's proof). -/
theorem w3ba_hrec_gen (D_H D_L : Diagram) (hH : D_H.componentCount = 1) (hL : D_L.componentCount = 1)
    (x_H y_H z_H : D_H.Γ.Crossing) (x_L y_L z_L : D_L.Γ.Crossing)
    (Ψ : D_H.Γ.Visit ≃ D_L.Γ.Visit) (a₁ a₂ b₁ b₂ c₁ c₂ : D_H.Γ.Visit)
    (ha₁ : a₁.1 = x_H) (hb₁ : b₁ = D_H.twin a₁) (ha₂ : a₂.1 = y_H) (hc₁ : c₁ = D_H.twin a₂)
    (hb₂ : b₂.1 = z_H) (hc₂ : c₂ = D_H.twin b₂)
    (hxy : x_H ≠ y_H) (hxz : x_H ≠ z_H) (hyz : y_H ≠ z_H)
    (hadj_e : D_H.nextVisit a₁ = a₂ ∨ D_H.nextVisit a₂ = a₁)
    (hadj_f : D_H.nextVisit b₁ = b₂ ∨ D_H.nextVisit b₂ = b₁)
    (hadj_g : D_H.nextVisit c₁ = c₂ ∨ D_H.nextVisit c₂ = c₁)
    (htw : ∀ v, Ψ (D_H.twin v) = D_L.twin (Ψ v)) (hbit : ∀ v, D_L.overBit (Ψ v) = D_H.overBit v)
    (hsgn : ∀ v, D_L.sign (Ψ v).1 = D_H.sign v.1)
    (hcyc : ∀ u v w, D_L.VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔
      D_H.VisitBetween ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) u)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) w))
    (hxL : (Ψ a₁).1 = x_L) (hyL : (Ψ a₂).1 = y_L) (hzL : (Ψ b₂).1 = z_L)
    {εH εL : ℝ} (hεH : SmallEps D_H x_H εH) (hεL : SmallEps D_L x_L εL)
    (yH0 zH0 : (smoothDiagram D_H x_H εH hεH).Γ.Crossing)
    (hyH0 : (smoothDiagram D_H x_H εH hεH).Γ.crossingPoint yH0 = D_H.Γ.crossingPoint y_H)
    (hzH0 : (smoothDiagram D_H x_H εH hεH).Γ.crossingPoint zH0 = D_H.Γ.crossingPoint z_H)
    (yL0 zL0 : (smoothDiagram D_L x_L εL hεL).Γ.Crossing)
    (hyL0 : (smoothDiagram D_L x_L εL hεL).Γ.crossingPoint yL0 = D_L.Γ.crossingPoint y_L)
    (hzL0 : (smoothDiagram D_L x_L εL hεL).Γ.crossingPoint zL0 = D_L.Γ.crossingPoint z_L)
    (B_H : BigonData ((smoothDiagram D_H x_H εH hεH).switch yH0))
    (hBH : (B_H.y = yH0 ∧ B_H.z = zH0) ∨ (B_H.y = zH0 ∧ B_H.z = yH0))
    (B_L : BigonData ((smoothDiagram D_L x_L εL hεL).switch yL0))
    (hBL : (B_L.y = yL0 ∧ B_L.z = zL0) ∨ (B_L.y = zL0 ∧ B_L.z = yL0)) :
    Nonempty (RecordIso B_H.reducedRecord B_L.reducedRecord) := by
  -- the six local occurrences and their crossings
  have hb₁x : b₁.1 = x_H := by rw [hb₁]; exact ha₁
  have hc₁y : c₁.1 = y_H := by rw [hc₁]; exact ha₂
  have hc₂z : c₂.1 = z_H := by rw [hc₂]; exact hb₂
  have hne : ∀ (u v : D_H.Γ.Visit), u.1 ≠ v.1 → u ≠ v :=
    fun u v h h' => h (congrArg (fun w : D_H.Γ.Visit => w.1) h')
  have h13 : a₁ ≠ b₁ := by rw [hb₁]; exact (D_H.twin_ne a₁).symm
  have h25 : a₂ ≠ c₁ := by rw [hc₁]; exact (D_H.twin_ne a₂).symm
  have h46 : b₂ ≠ c₂ := by rw [hc₂]; exact (D_H.twin_ne b₂).symm
  have h14 : a₁ ≠ b₂ := hne _ _ (by rw [ha₁, hb₂]; exact hxz)
  have h23 : a₂ ≠ b₁ := hne _ _ (by rw [ha₂, hb₁x]; exact hxy.symm)
  have h24 : a₂ ≠ b₂ := hne _ _ (by rw [ha₂, hb₂]; exact hyz)
  have h15 : a₁ ≠ c₁ := hne _ _ (by rw [ha₁, hc₁y]; exact hxy)
  have h16 : a₁ ≠ c₂ := hne _ _ (by rw [ha₁, hc₂z]; exact hxz)
  have h26 : a₂ ≠ c₂ := hne _ _ (by rw [ha₂, hc₂z]; exact hyz)
  have h35 : b₁ ≠ c₁ := hne _ _ (by rw [hb₁x, hc₁y]; exact hxy)
  have h36 : b₁ ≠ c₂ := hne _ _ (by rw [hb₁x, hc₂z]; exact hxz)
  have h45 : b₂ ≠ c₁ := hne _ _ (by rw [hb₂, hc₁y]; exact hyz.symm)
  have hσσ : ∀ v, (Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v) = v :=
    w3bh_swap3_apply_apply a₁ a₂ b₁ b₂ c₁ c₂ h13 h14 h23 h24 h15 h16 h25 h26 h35 h36 h45 h46
  -- the twisted successor clause from the twisted cyclic order (one component on both sides)
  have hsucc : ∀ v, Ψ ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂))
      (D_H.nextVisit ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v))) =
      D_L.nextVisit (Ψ v) := by
    let Φ' : D_H.Γ.Visit ≃ D_L.Γ.Visit :=
      (Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)).trans Ψ
    have hcomp : ∀ v w, D_L.compOf (Φ' v) = D_L.compOf (Φ' w) ↔ D_H.compOf v = D_H.compOf w :=
      fun v w => ⟨fun _ => w3bh_compOf_eq_of_one D_H hH v w, fun _ => w3bh_compOf_eq_of_one D_L hL _ _⟩
    have hbetw : ∀ v w u, D_H.compOf w = D_H.compOf v → D_H.compOf u = D_H.compOf v →
        (D_L.VisitBetween (Φ' v) (Φ' w) (Φ' u) ↔ D_H.VisitBetween v w u) := by
      intro v w u _ _
      have := hcyc ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) w)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) u)
      rw [hσσ, hσσ, hσσ] at this
      exact this
    intro v
    have key := D_H.nextVisit_comm_of_visitBetween_iff Φ' hcomp hbetw
      ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v)
    simp only [Φ', Equiv.trans_apply, hσσ] at key
    exact key
  -- the crossings of `D_L`
  have hΨfst := w3bh_fst_eq_iff_of_twin Ψ htw
  have hxyL : x_L ≠ y_L := by
    rw [← hxL, ← hyL, Ne, hΨfst, ha₁, ha₂]; exact hxy
  have hxzL : x_L ≠ z_L := by
    rw [← hxL, ← hzL, Ne, hΨfst, ha₁, hb₂]; exact hxz
  have hyzL : y_L ≠ z_L := by
    rw [← hyL, ← hzL, Ne, hΨfst, ha₂, hb₂]; exact hyz
  -- the two bridges
  obtain ⟨ιH⟩ := w3ba_reduced_to_smooth_gen D_H x_H y_H z_H a₁ a₂ b₂ c₁ c₂ ha₁ ha₂ hc₁ hb₂ hc₂ hεH
    yH0 zH0 hyH0 hzH0 B_H hBH
  obtain ⟨ιL⟩ := w3ba_reduced_to_smooth_gen D_L x_L y_L z_L (Ψ a₁) (Ψ a₂) (Ψ b₂) (Ψ c₁) (Ψ c₂) hxL hyL
    (by rw [hc₁, htw]) hzL (by rw [hc₂, htw]) hεL yL0 zL0 hyL0 hzL0 B_L hBL
  -- the core
  have hcr : ∀ u v : D_H.Γ.Visit, u.1 ≠ v.1 → D_H.record.crossingOf u ≠ D_H.record.crossingOf v :=
    fun u v h h' => h ((w3bh_record_crossingOf_eq_iff D_H u v).mp h')
  obtain ⟨κ⟩ := w3h_record_core D_H.record D_L.record (D_H.record_componentCount.trans hH)
    (D_L.record_componentCount.trans hL) Ψ a₁ a₂ b₁ b₂ c₁ c₂ hb₁.symm hc₁.symm hc₂.symm
    (hcr _ _ (by rw [ha₁, ha₂]; exact hxy)) (hcr _ _ (by rw [ha₁, hb₂]; exact hxz))
    (hcr _ _ (by rw [ha₂, hb₂]; exact hyz)) hadj_e hadj_f hadj_g htw hbit hsgn hsucc
  exact ⟨ιH.trans (κ.trans ιL.symm)⟩

/-- **`w3h_hrec` in the form the (6) realiser needs (rule (3), corrected form)**: the frozen `w3h_hrec` fixes
`B.y = y₀` (the switched crossing) and `B.z = z₀` on BOTH sides, i.e. the `arcST` orientation on both sides
of the wall; the reduced record `B.reducedRecord = restrictCrossings keep` is symmetric in `B.y, B.z`, so the
same statement holds for either assignment on either side.  PROVED from `w3h_hrec` in the `ST/ST` case; the
three other orientation pairs are closed by the assembler's `w3ba_hrec_gen` (unit H's proof, `and_comm`). -/
theorem w3bi_hrec_general (D_H D_L : Diagram) (hH : D_H.componentCount = 1) (hL : D_L.componentCount = 1)
    (x_H y_H z_H : D_H.Γ.Crossing) (x_L y_L z_L : D_L.Γ.Crossing)
    (Ψ : D_H.Γ.Visit ≃ D_L.Γ.Visit) (a₁ a₂ b₁ b₂ c₁ c₂ : D_H.Γ.Visit)
    (ha₁ : a₁.1 = x_H) (hb₁ : b₁ = D_H.twin a₁) (ha₂ : a₂.1 = y_H) (hc₁ : c₁ = D_H.twin a₂)
    (hb₂ : b₂.1 = z_H) (hc₂ : c₂ = D_H.twin b₂)
    (hxy : x_H ≠ y_H) (hxz : x_H ≠ z_H) (hyz : y_H ≠ z_H)
    (hadj_e : D_H.nextVisit a₁ = a₂ ∨ D_H.nextVisit a₂ = a₁)
    (hadj_f : D_H.nextVisit b₁ = b₂ ∨ D_H.nextVisit b₂ = b₁)
    (hadj_g : D_H.nextVisit c₁ = c₂ ∨ D_H.nextVisit c₂ = c₁)
    (htw : ∀ v, Ψ (D_H.twin v) = D_L.twin (Ψ v)) (hbit : ∀ v, D_L.overBit (Ψ v) = D_H.overBit v)
    (hsgn : ∀ v, D_L.sign (Ψ v).1 = D_H.sign v.1)
    (hcyc : ∀ u v w, D_L.VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔
      D_H.VisitBetween ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) u)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) v)
        ((Equiv.swap a₁ a₂ * (Equiv.swap b₁ b₂ * Equiv.swap c₁ c₂)) w))
    (hxL : (Ψ a₁).1 = x_L) (hyL : (Ψ a₂).1 = y_L) (hzL : (Ψ b₂).1 = z_L)
    {εH εL : ℝ} (hεH : SmallEps D_H x_H εH) (hεL : SmallEps D_L x_L εL)
    (yH0 zH0 : (smoothDiagram D_H x_H εH hεH).Γ.Crossing)
    (hyH0 : (smoothDiagram D_H x_H εH hεH).Γ.crossingPoint yH0 = D_H.Γ.crossingPoint y_H)
    (hzH0 : (smoothDiagram D_H x_H εH hεH).Γ.crossingPoint zH0 = D_H.Γ.crossingPoint z_H)
    (yL0 zL0 : (smoothDiagram D_L x_L εL hεL).Γ.Crossing)
    (hyL0 : (smoothDiagram D_L x_L εL hεL).Γ.crossingPoint yL0 = D_L.Γ.crossingPoint y_L)
    (hzL0 : (smoothDiagram D_L x_L εL hεL).Γ.crossingPoint zL0 = D_L.Γ.crossingPoint z_L)
    (B_H : BigonData ((smoothDiagram D_H x_H εH hεH).switch yH0))
    (hBH : (B_H.y = yH0 ∧ B_H.z = zH0) ∨ (B_H.y = zH0 ∧ B_H.z = yH0))
    (B_L : BigonData ((smoothDiagram D_L x_L εL hεL).switch yL0))
    (hBL : (B_L.y = yL0 ∧ B_L.z = zL0) ∨ (B_L.y = zL0 ∧ B_L.z = yL0)) :
    Nonempty (RecordIso B_H.reducedRecord B_L.reducedRecord) := by
  rcases hBH with ⟨hBHy, hBHz⟩ | ⟨hBHy, hBHz⟩ <;> rcases hBL with ⟨hBLy, hBLz⟩ | ⟨hBLy, hBLz⟩
  · exact w3h_hrec D_H D_L hH hL x_H y_H z_H x_L y_L z_L Ψ a₁ a₂ b₁ b₂ c₁ c₂ ha₁ hb₁ ha₂ hc₁ hb₂ hc₂ hxy hxz hyz
      hadj_e hadj_f hadj_g htw hbit hsgn hcyc hxL hyL hzL hεH hεL yH0 zH0 hyH0 hzH0 yL0 zL0 hyL0 hzL0 B_H hBHy hBHz
      B_L hBLy hBLz
  · exact w3ba_hrec_gen D_H D_L hH hL x_H y_H z_H x_L y_L z_L Ψ a₁ a₂ b₁ b₂ c₁ c₂ ha₁ hb₁ ha₂ hc₁ hb₂ hc₂ hxy hxz hyz
      hadj_e hadj_f hadj_g htw hbit hsgn hcyc hxL hyL hzL hεH hεL yH0 zH0 hyH0 hzH0 yL0 zL0 hyL0 hzL0
      B_H (Or.inl ⟨hBHy, hBHz⟩) B_L (Or.inr ⟨hBLy, hBLz⟩)
  · exact w3ba_hrec_gen D_H D_L hH hL x_H y_H z_H x_L y_L z_L Ψ a₁ a₂ b₁ b₂ c₁ c₂ ha₁ hb₁ ha₂ hc₁ hb₂ hc₂ hxy hxz hyz
      hadj_e hadj_f hadj_g htw hbit hsgn hcyc hxL hyL hzL hεH hεL yH0 zH0 hyH0 hzH0 yL0 zL0 hyL0 hzL0
      B_H (Or.inr ⟨hBHy, hBHz⟩) B_L (Or.inl ⟨hBLy, hBLz⟩)
  · exact w3ba_hrec_gen D_H D_L hH hL x_H y_H z_H x_L y_L z_L Ψ a₁ a₂ b₁ b₂ c₁ c₂ ha₁ hb₁ ha₂ hc₁ hb₂ hc₂ hxy hxz hyz
      hadj_e hadj_f hadj_g htw hbit hsgn hcyc hxL hyL hzL hεH hεL yH0 zH0 hyH0 hzH0 yL0 zL0 hyL0 hzL0
      B_H (Or.inr ⟨hBHy, hBHz⟩) B_L (Or.inr ⟨hBLy, hBLz⟩)

/-- **The (6) site black box from β1 + β2 + the generalised record lemma** (PROVED glue): distinctness of
`x, y, z` from their double points (`crossingPoint_injective_of_geometry`, `P1.xPair_*_ne_*`), the smoothing
crossings at the double points of `y, z`, then `w3bi_hrec_general`. -/
theorem w3bi_rii_sites_of (hbig : w3bi_bigon_pair) (hwall : w3bi_wall_data) : w3bi_rii_sites := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' q₀ q₀' hq₀ hq₀' x_H x_L
    hxH hxL y_H y_L hyH hyL
  obtain ⟨zH0, zL0, hzH0, hzL0, B_H, B_L, hBH, hBL⟩ := hbig hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg
    hK Q hQ hfull hQi hQi' q₀ q₀' hq₀ hq₀' x_H x_L hxH hxL y_H y_L hyH hyL
  obtain ⟨y_H', z_H', y_L', z_L', Ψ, a₁, a₂, b₁, b₂, c₁, c₂, hyH', hzH', hyL', hzL', ha₁, hb₁, ha₂, hc₁, hb₂, hc₂,
    hadj_e, hadj_f, hadj_g, htw, hbit, hsgn, hcyc, hxL', hyL'', hzL''⟩ := hwall hn E e f g δ hL hGT hR t t' ht ht'
    hop hs hef heg hfg hK Q hQ hfull hQi hQi' q₀ q₀' hq₀ hq₀' x_H x_L hxH hxL
  have hxy : x_H ≠ y_H' := by
    intro h
    apply P1.xPair_ef_ne_eg hef heg hfg
    apply crossingPoint_injective_of_geometry (geomAt E t ht.1)
    rw [← hxH, ← hyH', h]
  have hxz : x_H ≠ z_H' := by
    intro h
    apply P1.xPair_ef_ne_fg hef heg hfg
    apply crossingPoint_injective_of_geometry (geomAt E t ht.1)
    rw [← hxH, ← hzH', h]
  have hyz : y_H' ≠ z_H' := by
    intro h
    apply P1.xPair_eg_ne_fg hef heg hfg
    apply crossingPoint_injective_of_geometry (geomAt E t ht.1)
    rw [← hyH', ← hzH', h]
  exact ⟨B_H, B_L, w3bi_hrec_general _ _ rfl rfl x_H y_H' z_H' x_L y_L' z_L' Ψ a₁ a₂ b₁ b₂ c₁ c₂ ha₁ hb₁ ha₂ hc₁
    hb₂ hc₂ hxy hxz hyz hadj_e hadj_f hadj_g htw hbit hsgn hcyc hxL' hyL'' hzL'' (eps_small _ x_H) (eps_small _ x_L)
    y_H zH0 (hyH.trans hyH'.symm) (hzH0.trans hzH'.symm) y_L zL0 (hyL.trans hyL'.symm) (hzL0.trans hzL'.symm)
    B_H hBH B_L hBL⟩

/-- the (6) site black box reduced to β1 + β2 (+ the three open orientation cases of `w3bi_hrec_general`) -/
theorem w3bi_rii_sites_data : w3bi_rii_sites :=
  w3bi_rii_sites_of w3bi_bigon_pair_data w3bi_wall_data_data

/-- **(b) the realiser of (6) in the weak form** from the two library smoothings (`smoothDiagram` at
`eps`: `isOrientedSmoothing_smoothDiagram`, `smoothDiagram_record`) and the bigon sites
(`w3bi_rii_sites` → `esc_rii_after_smoothing_of_bigons`). -/
theorem w3bi_rii_after_smoothing_weak (hsites : w3bi_rii_sites) (hn : 3 ≤ n) {E : CV.Event n}
    {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    (hK : CompleteLocal (geomAt E t ht.1) hef heg hfg)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
    (q₀ : GeoComponent (geomAt E t ht.1) Q)
    (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q))
    (hq₀ : ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀)
    (hq₀' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀')
    (x_H : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.Crossing)
    (x_L : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.Crossing)
    (hxH : (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀).Γ.crossingPoint x_H =
      crossingPoint (xPair hef))
    (hxL : (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀').Γ.crossingPoint x_L =
      crossingPoint (xPair ((hs _).mp hef))) :
    esc_rii_after_smoothing_weak (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀)
      (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_H x_L
      (crossingPoint (xPair heg)) (crossingPoint (xPair ((hs _).mp heg))) :=
  ⟨_, _, isOrientedSmoothing_smoothDiagram _ _ _ (eps_small _ x_H),
    isOrientedSmoothing_smoothDiagram _ _ _ (eps_small _ x_L),
    smoothDiagram_record _ _ _ (eps_small _ x_H), smoothDiagram_record _ _ _ (eps_small _ x_L),
    fun y_H y_L hyH hyL => by
      obtain ⟨B_H, B_L, hrec⟩ := hsites hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull
        hQi hQi' q₀ q₀' hq₀ hq₀' x_H x_L hxH hxL y_H y_L hyH hyL
      exact esc_rii_after_smoothing_of_bigons _ _ y_H y_L B_H B_L hrec⟩

/-- **The extended interface from (a), (b) and the outer black box.** -/
theorem w3bi_esc_interface_ext_of (houter : w3bi_esc_outer) (hsites : w3bi_rii_sites) :
    w3bi_esc_interface_ext := by
  intro n _ hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  obtain ⟨A, B, C, Z, Λ, hsplit, hk2, h3c⟩ := houter hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg
    hK Q hQ hfull hQi hQi' hS' q₀ q₀' hq₀ hq₀'
  exact ⟨A, B, C, Z, Λ, hsplit,
    { switch_riii := fun x_H x_L hxH hxL =>
        w3bi_switch_riii hn hL hGT hR ht ht' hop hs hef heg hfg hK hQ hfull hQi hQi' q₀ q₀' hq₀ hq₀'
          x_H x_L hxH hxL
      rii_after_smoothing_weak := fun x_H x_L hxH hxL =>
        w3bi_rii_after_smoothing_weak hsites hn hL hGT hR ht ht' hop hs hef heg hfg hK hQ hfull hQi hQi'
          q₀ q₀' hq₀ hq₀' x_H x_L hxH hxL
      knot_after_two := hk2
      three_components := h3c }⟩

/-- the extended interface, with the two black boxes asserted -/
theorem w3bi_esc_interface_ext_holds : w3bi_esc_interface_ext :=
  w3bi_esc_interface_ext_of w3bi_esc_outer_data w3bi_rii_sites_data

/-! ### The ledger replayed (byte-faithful copies of `esc_contact_identity`, `esc_couple`, `esc_ledger`) -/

/-- **The contact identity, replayed (D-RM-5) on the WEAK move data** (`w3bi_esc_MoveDataWeak`: the two
smoothings at `x` are the ones the weak clause provides instead of `exists_smoothing_record_visit`; body
otherwise the accepted `esc_contact_identity`).  **The contact identity**: the difference of the two touching factors of the empty row is the
touching factor of the full row on the empty side (ESC §1–§5 at one configuration), from the interface
data and `CarrierSlotFloor`. -/
theorem w3bi_esc_contact_identity (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n}
    {δ : ℝ} (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef₀ : e ≠ f) (heg₀ : e ≠ g) (hfg₀ : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) (_hK : CompleteLocal (geomAt E t ht.1) hef heg hfg)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
    (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
    (hI : ∀ (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ (A B C Z : GeoComponent (geomAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)) (Λ : ℕ),
        esc_FullSplitData hn (genericAt E t' ht'.1) e f g hQi' hS' q₀' A B C Z Λ ∧
        w3bi_esc_MoveDataWeak (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀)
          (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')
          (crossingPoint (xPair hef)) (crossingPoint (xPair heg))
          (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg))) Λ
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' A) (CV.groupedPoly hn (genericAt E t' ht'.1) hS' B)
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' C)) :
    touchingFactor hn (genericAt E t ht.1) hQi e f g -
        touchingFactor hn (genericAt E t' ht'.1) hQi' e f g =
      touchingFactor hn (genericAt E t' ht'.1) hS' e f g := by
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  -- the contact carrier on the `K3` side
  obtain ⟨q₀, hq₀⟩ := esc_contact_exists ht hef Q
  have huniq : ∀ q, ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q ↔ q = q₀ :=
    fun q => ⟨fun hq => esc_contact_unique hL hef₀ heg₀ hfg₀ ht hQ hfull hq hq₀, fun h => h ▸ hq₀⟩
  have hTq₀ := esc_contact_owns hL hef₀ heg₀ hfg₀ ht hQ hfull hq₀
  -- the wall and the transported contact carrier on the empty side
  have W := GT_empty_wall hL hR hef₀ heg₀ hfg₀ ht ht' hop hs hQ
  have hX := GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q₀
  have hq₀' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g
      (GT_carrierEquiv W q₀) := by
    rw [esc_not_triangleDisjoint_iff]
    have hmem : crossingTransport hs (xPair hef) ∈
        geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs Q) (GT_carrierEquiv W q₀) := by
      rw [hX, Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact hTq₀ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl))
    obtain ⟨i, -, -⟩ := crossing_visits_exist (crossingTransport hs (xPair hef))
    exact ⟨⟨_, i⟩, (P1.mem_triangleSupports _).mpr (Or.inl rfl),
      ((mem_geoCarrierCrossings _ _ _ _).mp hmem).2 _ rfl⟩
  have huniq' : ∀ q, ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q ↔
      q = GT_carrierEquiv W q₀ :=
    fun q => ⟨fun hq => esc_contact_unique hL hef₀ heg₀ hfg₀ ht' hQ' hfull' hq hq₀', fun h => h ▸ hq₀'⟩
  have hT'q₀' := esc_contact_owns hL hef₀ heg₀ hfg₀ ht' hQ' hfull' hq₀'
  -- the interface data
  obtain ⟨A, B, C, Z, Λ, hsplit, hmove⟩ := hI q₀ (GT_carrierEquiv W q₀) hq₀ hq₀'
  -- notation
  set hG := genericAt E t ht.1
  set hG' := genericAt E t' ht'.1
  set q₀' := GT_carrierEquiv W q₀
  set D_H := CV.carrierDiagram hn hG hQi q₀
  set D_L := CV.carrierDiagram hn hG' hQi' q₀'
  set fA := CV.groupedPoly hn hG' hS' A
  set fB := CV.groupedPoly hn hG' hS' B
  set fC := CV.groupedPoly hn hG' hS' C
  -- the transported data of the contact carrier
  have hw : CV.weight hG'.crossingGeometry (transportSupport hs Q) q₀' = CV.weight hG.crossingGeometry Q q₀ :=
    GT_weight_eq hn hG hG' W q₀
  have hRq : CV.carrierR hn hG' hQi' q₀' = CV.carrierR hn hG hQi q₀ := GT_carrierR_eq hn hG hG' W hQi hQi' q₀
  have hwr : CV.groupedWrithe hG' q₀' = CV.groupedWrithe hG q₀ := by
    rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi,
      hX, Finset.card_map]
  have hslot : CV.slot hn hG' hQi' q₀' = CV.slot hn hG hQi q₀ := by
    unfold CV.slot; rw [hRq, hwr]
  -- the two touching factors of the empty row and the one of the full row
  rw [esc_touchingFactor_eq_of_unique hn hG hQi e f g q₀ huniq,
    esc_touchingFactor_eq_of_unique hn hG' hQi' e f g q₀' huniq',
    esc_touchingFactor_eq_of_four hn hG' hS' e f g A B C Z hsplit.distinct hsplit.touching_iff, ← hw,
    ← mul_sub]
  -- the central carrier: `Ω₁ = 1`
  have hΩZ : CV.Omega1 hn hG' hS' Z = 1 := by
    unfold CV.Omega1 CV.slot
    rw [CV.groupedPoly_of_piecesOn_eq_empty hn hG' hS' Z hsplit.central_no_piece,
      CV.groupedWrithe_of_piecesOn_eq_empty hG' Z hsplit.central_no_piece, hsplit.central_rot]
    simp [coeffAt_one]
  rw [hΩZ]
  -- `Ω_H − Ω_L = [a^d z^0](F_H − F_L)`, `d` the common slot
  have hΩ : CV.Omega1 hn hG hQi q₀ - CV.Omega1 hn hG' hQi' q₀' =
      coeffAt (CV.slot hn hG' hQi' q₀') 0 (homfly D_H - homfly D_L) := by
    unfold CV.Omega1
    rw [hslot, GT_groupedPoly_eq_homfly, GT_groupedPoly_eq_homfly, coeffAt_sub]
  -- the crossings `x`, `y` on the grouped contact diagrams, the smoothings, the moves
  have hxT : xPair hef ∈ triangleCrossings (E.curve t) e f g :=
    (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl)
  have hyT : xPair heg ∈ triangleCrossings (E.curve t) e f g :=
    (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inl rfl))
  have hef' : IsCrossing (E.curve t') {e, f} := (hs _).mp hef
  have heg' : IsCrossing (E.curve t') {e, g} := (hs _).mp heg
  have hfg' : IsCrossing (E.curve t') {f, g} := (hs _).mp hfg
  have hxT' : xPair hef' ∈ triangleCrossings (E.curve t') e f g :=
    (P1.mem_triangleCrossings_iff hef' heg' hfg' _).mpr (Or.inl rfl)
  have hyT' : xPair heg' ∈ triangleCrossings (E.curve t') e f g :=
    (P1.mem_triangleCrossings_iff hef' heg' hfg' _).mpr (Or.inr (Or.inl rfl))
  obtain ⟨x_H, hxH_pt, hxH_pos⟩ := esc_lift_crossing hn hG hQi q₀ (xPair hef) (hTq₀ hxT)
  obtain ⟨y_H, hyH_pt, hyH_pos⟩ := esc_lift_crossing hn hG hQi q₀ (xPair heg) (hTq₀ hyT)
  obtain ⟨x_L, hxL_pt, hxL_pos⟩ := esc_lift_crossing hn hG' hQi' q₀' (xPair hef') (hT'q₀' hxT')
  obtain ⟨y_L, hyL_pt, hyL_pos⟩ := esc_lift_crossing hn hG' hQi' q₀' (xPair heg') (hT'q₀' hyT')
  have hyxH : y_H ≠ x_H := by
    intro h
    apply P1.xPair_ef_ne_eg hef heg hfg
    apply crossingPoint_injective_of_geometry (geomAt E t ht.1)
    rw [← hxH_pt, ← hyH_pt, h]
  have hyxL : y_L ≠ x_L := by
    intro h
    apply P1.xPair_ef_ne_eg hef' heg' hfg'
    apply crossingPoint_injective_of_geometry (geomAt E t' ht'.1)
    rw [← hxL_pt, ← hyL_pt, h]
  have m6w := hmove.rii_after_smoothing_weak x_H x_L hxH_pt hxL_pt
  unfold esc_rii_after_smoothing_weak at m6w
  obtain ⟨D_H0, D_L0, hsmH, hsmL, -, -, m6f⟩ := m6w
  obtain ⟨y_H0, hyH0_pt, hyH0_pos⟩ := esc_smoothing_outer hsmH y_H hyxH
  obtain ⟨y_L0, hyL0_pt, hyL0_pos⟩ := esc_smoothing_outer hsmL y_L hyxL
  rw [hyH_pt] at hyH0_pt
  rw [hyL_pt] at hyL0_pt
  obtain ⟨J_H, hsmJH, -⟩ := exists_smoothing_record_visit D_H0 y_H0 (D_H0.overVisit y_H0) rfl
  obtain ⟨J_L, hsmJL, -⟩ := exists_smoothing_record_visit D_L0 y_L0 (D_L0.overVisit y_L0) rfl
  have m4 := hmove.switch_riii x_H x_L hxH_pt hxL_pt
  have m6 : esc_rii_after_smoothing D_H0 D_L0 y_H0 y_L0 := m6f y_H0 y_L0 hyH0_pt hyL0_pt
  have hJH := hmove.knot_after_two x_H hxH_pt D_H0 hsmH y_H0 hyH0_pt J_H hsmJH
  have h12 := esc_three_component_row (hmove.three_components x_L hxL_pt D_L0 hsmL y_L0 hyL0_pt J_L hsmJL)
  -- (13)
  have h13 := esc_coefficient_identity hxH_pos hxL_pos hsmH hsmL (hyH0_pos.mpr hyH_pos)
    (hyL0_pos.mpr hyL_pos) hsmJH hsmJL m4 m6 hJH h12 (CV.slot hn hG' hQi' q₀')
  rw [hΩ, h13, esc_coeffAt_sq_mul]
  -- the three selector branches on the empty contact carrier
  set d := CV.slot hn hG' hQi' q₀' with hd
  set K := fA * fB * fC with hK
  have hprod : (CV.weight hG'.crossingGeometry _ A * CV.Omega1 hn hG' hS' A) *
      (CV.weight hG'.crossingGeometry _ B * CV.Omega1 hn hG' hS' B) *
      (CV.weight hG'.crossingGeometry _ C * CV.Omega1 hn hG' hS' C) *
      (CV.weight hG'.crossingGeometry _ Z * 1) =
      (CV.weight hG'.crossingGeometry _ A * CV.weight hG'.crossingGeometry _ B *
        CV.weight hG'.crossingGeometry _ C * CV.weight hG'.crossingGeometry _ Z) *
      (CV.Omega1 hn hG' hS' A * CV.Omega1 hn hG' hS' B * CV.Omega1 hn hG' hS' C) := by ring
  rw [hprod]
  by_cases huni : CV.CarrierUniform hG'.crossingGeometry (transportSupport hs Q) q₀'
  · -- the uniform contact carrier: the outer floors
    obtain ⟨haltA, haltB, haltC⟩ := hsplit.outer_alternative huni
    have hqA := esc_quadrant_groupedPoly hF hn hG' hS' A haltA
    have hqB := esc_quadrant_groupedPoly hF hn hG' hS' B haltB
    have hqC := esc_quadrant_groupedPoly hF hn hG' hS' C haltC
    have hqK := esc_quadrant_mul (esc_quadrant_mul hqA hqB) hqC
    -- (19)
    have h19 : coeffAt (CV.slot hn hG' hS' A + CV.slot hn hG' hS' B + CV.slot hn hG' hS' C) 0 K =
        CV.Omega1 hn hG' hS' A * CV.Omega1 hn hG' hS' B * CV.Omega1 hn hG' hS' C := by
      rw [hK, esc_coeffAt_corner (esc_quadrant_mul hqA hqB) hqC, esc_coeffAt_corner hqA hqB]
      rfl
    have hwrq := hsplit.writhe
    have hdq : d = 1 - CV.groupedWrithe hG' q₀' - (CV.carrierR hn hG' hQi' q₀' : ℤ) := rfl
    rcases hsplit.uniform huni with ⟨hrot, hwf⟩ | ⟨hrot, hwf⟩
    · -- live branch `χ = 1`: (18) `D = d + 4 + 2Λ`; (20) `Ω_H − Ω_L = −ω_A ω_B ω_C`
      have hrot' : (CV.carrierR hn hG' hS' A : ℤ) + CV.carrierR hn hG' hS' B + CV.carrierR hn hG' hS' C =
          CV.carrierR hn hG' hQi' q₀' + 1 := by exact_mod_cast hrot
      have hD : CV.slot hn hG' hS' A + CV.slot hn hG' hS' B + CV.slot hn hG' hS' C = d + 4 + 2 * (Λ : ℤ) := by
        simp only [CV.slot] at hdq ⊢
        omega
      rw [hD] at h19 hqK
      rw [show d + 2 + 2 * (Λ : ℤ) - 2 = d + 2 * Λ by ring,
        show d + 2 + 2 * (Λ : ℤ) + 2 = d + 4 + 2 * Λ by ring, h19,
        hqK.coeffAt_eq_zero (by omega), hqK.coeffAt_eq_zero (by omega), hwf]
      ring
    · -- dead branch `χ = 0`: (18) `D = d + 6 + 2Λ`; every sample is below the floor
      have hrot' : (CV.carrierR hn hG' hS' A : ℤ) + CV.carrierR hn hG' hS' B + CV.carrierR hn hG' hS' C + 1 =
          CV.carrierR hn hG' hQi' q₀' := by exact_mod_cast hrot
      have hD : CV.slot hn hG' hS' A + CV.slot hn hG' hS' B + CV.slot hn hG' hS' C = d + 6 + 2 * (Λ : ℤ) := by
        simp only [CV.slot] at hdq ⊢
        omega
      rw [hD] at hqK
      rw [hqK.coeffAt_eq_zero (by omega), hqK.coeffAt_eq_zero (by omega),
        hqK.coeffAt_eq_zero (by omega), hwf]
      ring
  · -- the mixed contact carrier: `W = 0` and `W_full = 0`
    have hW0 : CV.weight hG'.crossingGeometry (transportSupport hs Q) q₀' = 0 :=
      CV.weight_of_mixed _ _ q₀' huni
    rw [hsplit.mixed huni, hW0]
    ring

/-- **The `couple` field of row 177, replayed on the extended interface** (F-177-2 / D-RM-5: `hGT` is an
extra hypothesis, discharged in `w3bi_esc_ledger` by `generic_table`; body otherwise the accepted `esc_couple`). from the interface, `CarrierSlotFloor`, and the accepted data at a
common radius: (2) "`T_H(empty) - T_L(empty) = T_L(xyz)`" — the exterior factor `C_Q` is common to the
three rows (row 168: `EXT_exteriorFactor_wall`, `EXT_exteriorFactor_eq_base`), the rest is the contact
identity.  "No exterior scalar, selector, or coefficient was divided out." -/
theorem w3bi_esc_couple (hI : w3bi_esc_interface_ext) (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n) {E : CV.Event n}
    {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (hguard : ∀ u : E.Parameter, |u.val| < δ → EXT_GuardAt E u) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t ht.1) Q - rowTerm hn (genericAt E t' ht'.1) (transportSupport hs Q) =
        rowTerm hn (genericAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) := by
  intro t t' ht ht' hop hs hef heg hfg hK Q hQ hfull
  have hef₀ : e ≠ f := AV_ne_of_remote h3.1
  have hfg₀ : f ≠ g := AV_ne_of_remote h3.2.1
  have heg₀ : e ≠ g := AV_ne_of_remote h3.2.2.1
  have hef' : IsCrossing (E.curve t') {e, f} := (hs _).mp hef
  have heg' : IsCrossing (E.curve t') {e, g} := (hs _).mp heg
  have hfg' : IsCrossing (E.curve t') {f, g} := (hs _).mp hfg
  have hQi : Q ∈ CV.Ind (geomAt E t ht.1) := mem_Ind_of_mem_outsideSupports hQ
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1) := mem_Ind_of_mem_outsideSupports hQ'
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  have hEmpty : EmptyLocal (geomAt E t' ht'.1) hef' heg' hfg' :=
    (PRE_176_graphs_complementary hL t t' ht ht' hop hef heg hfg hef' heg' hfg').mp hK
  have hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1) :=
    PRE_177_full_present_on_empty E e f g δ t' ht' hef' heg' hfg' hEmpty _ hQ' hfull'
  -- the exterior factor `C_Q` of the three rows (row 168)
  have hQT : ∀ x ∈ Q, x.val ∉ triangleSupports e f g := fun x hx hxT =>
    Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hx
      ((P1.mem_triangleCrossings x).mpr hxT)
  have hQ'T : ∀ x ∈ transportSupport hs Q, x.val ∉ triangleSupports e f g := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact hQT y hy
  rw [rowTerm_eq_exterior_mul_touching hn (genericAt E t ht.1) hQi e f g,
    rowTerm_eq_exterior_mul_touching hn (genericAt E t' ht'.1) hQi' e f g,
    rowTerm_eq_exterior_mul_touching hn (genericAt E t' ht'.1) hS' e f g,
    EXT_exteriorFactor_wall hE hn hL hguard ht ht' hop hs hQi hQT hQi',
    ← EXT_exteriorFactor_eq_base hn (genericAt E t' ht'.1) hQ'T
      (fun x hx => (P1.mem_triangleCrossings x).mp hx) hS' hQi',
    EXT_exteriorFactor_wall hE hn hL hguard ht ht' hop hs hQi hQT hQi', ← mul_sub]
  congr 1
  exact w3bi_esc_contact_identity hF hn hL hR hef₀ heg₀ hfg₀ ht ht' hop hs hef heg hfg hK hQ hfull hQi hQi' hS'
    (fun q₀ q₀' hq₀ hq₀' => hI hn E e f g δ hL hGT hR t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi'
      hS' q₀ q₀' hq₀ hq₀')

/-- **The RA ledger of row 177, replayed on the extended interface** (body the accepted `esc_ledger` with the
fourth radius of `generic_table` and `SEL_genericTableData_mono`, as `generic_transport` does). -/
theorem w3bi_esc_ledger (hI : w3bi_esc_interface_ext) (hF : CV.CarrierSlotFloor) :
    RowShape @ExtremeSelectedData := by
  intro n _ hn E e f g h3 h4e h4f h4g hE
  obtain ⟨δL, hδL, hδLr, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  obtain ⟨δR, hδR, -, hR⟩ := AV_exists_eventRadius hE
  obtain ⟨δG, hδG, -, hguard⟩ := EXT_exists_guardRadius hE
  obtain ⟨δT, hδT, -, hGT⟩ := generic_table E e f g h3 h4e h4f h4g hE
  refine ⟨min δL (min δR (min δG δT)), lt_min hδL (lt_min hδR (lt_min hδG hδT)),
    (min_le_left _ _).trans hδLr, ?_⟩
  have h1 : min δL (min δR (min δG δT)) ≤ δL := min_le_left _ _
  have h2 : min δL (min δR (min δG δT)) ≤ δR := (min_le_right _ _).trans (min_le_left _ _)
  have h3' : min δL (min δR (min δG δT)) ≤ δG :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : min δL (min δR (min δG δT)) ≤ δT :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hL' := F1.localizationData_mono h1 hL
  have hR' := AV_eventRadius_mono h2 hR
  have hGT' := SEL_genericTableData_mono h4 hGT
  have hguard' : ∀ u : E.Parameter, |u.val| < min δL (min δR (min δG δT)) → EXT_GuardAt E u :=
    fun u hu => hguard u (lt_of_lt_of_le hu h3')
  exact { full_present_on_empty := PRE_177_full_present_on_empty E e f g _
          full_absent_on_complete := PRE_177_full_absent_on_complete E e f g _
          couple := w3bi_esc_couple hI hF hn hE hL' hGT' hR' hguard' }

/-- **Row 177 (R:extreme_selected) in the fixed row shape**, the replayed composition: the extended
interface from (a) + (b) + the two black boxes, the replayed ledger, `CV.carrierSlotFloor` (row 155). -/
theorem w3bi_extreme_selected : RowShape @ExtremeSelectedData :=
  w3bi_esc_ledger w3bi_esc_interface_ext_holds CV.carrierSlotFloor

/-- the fixed leaf statement of `RProof.extreme_selected` (Statements_FINAL.lean:803, byte-for-byte after
the name), from the row shape -/
theorem w3bi_extreme_selected_leaf (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeSelectedData hn E e f g δ :=
  w3bi_extreme_selected n hn E e f g h3 h4e h4f h4g hE

end W3BI_REAL


end

end SM.Link
