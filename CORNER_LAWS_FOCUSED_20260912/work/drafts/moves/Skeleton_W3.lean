import SM.Smoothing
import SM.MarkedProducts
import SM.SingleCrossing
import CV.FullTwist
import RProof.GenericTransport
import SM.BigonDeletion

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

namespace G11_ParamsSw

variable {k : ℕ} [NeZero k] {C : G11_ConfigSw k} (π : G11_ParamsSw C)

theorem hk₃ (_π : G11_ParamsSw C) : 3 ≤ k + 3 := by omega

/-- the subdivided polygon `X₀` (three flat vertices on `m`) -/
def X₀ : LabelledTuple (k + 3) := G11_subdiv C.X C.m π.t₁ π.t₂ π.t₃

def mid (_π : G11_ParamsSw C) : ZMod (k + 3) := ((C.m.val + 2 : ℕ) : ZMod (k + 3))
def mA (_π : G11_ParamsSw C) : ZMod (k + 3) := (C.m.val : ZMod (k + 3))
def mB (_π : G11_ParamsSw C) : ZMod (k + 3) := ((C.m.val + 1 : ℕ) : ZMod (k + 3))
def mC (_π : G11_ParamsSw C) : ZMod (k + 3) := ((C.m.val + 2 : ℕ) : ZMod (k + 3))
def mD (_π : G11_ParamsSw C) : ZMod (k + 3) := ((C.m.val + 3 : ℕ) : ZMod (k + 3))
def p' (_π : G11_ParamsSw C) : ZMod (k + 3) := G11_lab C.m C.p
def q' (_π : G11_ParamsSw C) : ZMod (k + 3) := G11_lab C.m C.q

/-- the apex `w = m₀ + λ (x_pq − m₀)` -/
def apex : Plane :=
  edgePoint C.X C.m π.t₂ + π.lam • (crossingPoint (xPair C.hpq) - edgePoint C.X C.m π.t₂)

/-- the moved polygon `X₁` -/
def X₁ : LabelledTuple (k + 3) := Function.update π.X₀ π.mid π.apex

/-- the disc -/
def U : Set Plane := G11_discOfSw C π.r

def comp₀ : PolyComp := ⟨k + 3, π.hk₃, π.X₀⟩
def comp₁ : PolyComp := ⟨k + 3, π.hk₃, π.X₁⟩

/-- **(a) sub-leaf B1′** (copy of `G11_Params.X₀_generic`, GenericTransport 857): the subdivided polygon
is generic — the `appendVertex` chain `X ≅ shift (m+1) X → +p_in → +m₀ → +p_out ≅ X₀` (U3 Block A). -/
theorem w3a_X₀_generic : (Shadow.single π.comp₀).Generic := by
  sorry

/-- **(a) sub-leaf C1′** (copy of `G11_Params.X₁_generic`, GenericTransport 2858): the moved polygon is
generic — the four genericity clauses at the apex (U4 helpers 2708–2850). -/
theorem w3a_X₁_generic : (Shadow.single π.comp₁).Generic := by
  sorry

/-- `M₀`, `M₁`: the positive diagrams of `X₀`, `X₁` -/
def M₀ : Diagram := (Shadow.single π.comp₀).positiveDiagram π.w3a_X₀_generic
def M₁ : Diagram := (Shadow.single π.comp₁).positiveDiagram π.w3a_X₁_generic

theorem M₀_componentCount : π.M₀.componentCount = 1 := rfl
theorem M₁_componentCount : π.M₁.componentCount = 1 := rfl

/-- the strand of label `i` of the one-component shadows of `X₀`, `X₁` -/
def st₀ (i : ZMod (k + 3)) : π.M₀.Γ.Strand := (⟨0, i⟩ : (Shadow.single π.comp₀).Strand)
def st₁ (i : ZMod (k + 3)) : π.M₁.Γ.Strand := (⟨0, i⟩ : (Shadow.single π.comp₁).Strand)

/-- **(a) sub-leaves** (copies of `X₀_cross_mp/mq/pq` :949–969 and `X₁_cross_pC/qB/pq` :2869–3380): the
three local pairs are crossings of `X₀` (`{mB, p'}`, `{mC, q'}`, `{p', q'}`) and of `X₁`
(`{p', mC}`, `{q', mB}`, `{p', q'}`). -/
theorem w3a_X₀_cross_mp : IsCrossing π.X₀ {π.mB, π.p'} := by
  sorry
theorem w3a_X₀_cross_mq : IsCrossing π.X₀ {π.mC, π.q'} := by
  sorry
theorem w3a_X₀_cross_pq : IsCrossing π.X₀ {π.p', π.q'} := by
  sorry
theorem w3a_X₁_cross_pC : IsCrossing π.X₁ {π.p', π.mC} := by
  sorry
theorem w3a_X₁_cross_qB : IsCrossing π.X₁ {π.q', π.mB} := by
  sorry
theorem w3a_X₁_cross_pq : IsCrossing π.X₁ {π.p', π.q'} := by
  sorry

/-- the three local crossings of `M₀` and of `M₁` (`gu6_y_mp` … for the switched configuration) -/
def y_mp : π.M₀.Γ.Crossing := (Shadow.singleCrossingEquiv π.comp₀).symm (xPair π.w3a_X₀_cross_mp)
def y_mq : π.M₀.Γ.Crossing := (Shadow.singleCrossingEquiv π.comp₀).symm (xPair π.w3a_X₀_cross_mq)
def y_pq : π.M₀.Γ.Crossing := (Shadow.singleCrossingEquiv π.comp₀).symm (xPair π.w3a_X₀_cross_pq)
def y'_pC : π.M₁.Γ.Crossing := (Shadow.singleCrossingEquiv π.comp₁).symm (xPair π.w3a_X₁_cross_pC)
def y'_qB : π.M₁.Γ.Crossing := (Shadow.singleCrossingEquiv π.comp₁).symm (xPair π.w3a_X₁_cross_qB)
def y'_pq : π.M₁.Γ.Crossing := (Shadow.singleCrossingEquiv π.comp₁).symm (xPair π.w3a_X₁_cross_pq)

/-- the six local occurrences of `M₀` (`w_mp` …) and of `M₁` (`w'_Cp` …; `w'_Cp` is the occurrence on the
moved piece `mC` at the crossing with `p'`, the image of `w_mp` under `Ψ₁`) -/
def w_mp : π.M₀.Γ.Visit :=
  (Shadow.singleVisitEquiv π.comp₀).symm ⟨xPair π.w3a_X₀_cross_mp, ⟨π.mB, mem_pair_left _ _⟩⟩
def w_pm : π.M₀.Γ.Visit :=
  (Shadow.singleVisitEquiv π.comp₀).symm ⟨xPair π.w3a_X₀_cross_mp, ⟨π.p', mem_pair_right _ _⟩⟩
def w_mq : π.M₀.Γ.Visit :=
  (Shadow.singleVisitEquiv π.comp₀).symm ⟨xPair π.w3a_X₀_cross_mq, ⟨π.mC, mem_pair_left _ _⟩⟩
def w_qm : π.M₀.Γ.Visit :=
  (Shadow.singleVisitEquiv π.comp₀).symm ⟨xPair π.w3a_X₀_cross_mq, ⟨π.q', mem_pair_right _ _⟩⟩
def w_pq : π.M₀.Γ.Visit :=
  (Shadow.singleVisitEquiv π.comp₀).symm ⟨xPair π.w3a_X₀_cross_pq, ⟨π.p', mem_pair_left _ _⟩⟩
def w_qp : π.M₀.Γ.Visit :=
  (Shadow.singleVisitEquiv π.comp₀).symm ⟨xPair π.w3a_X₀_cross_pq, ⟨π.q', mem_pair_right _ _⟩⟩
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

/-- **(a) sub-leaves** (copies of `gu6_y_mp_ne_mq` … :7016–7044 via `gu6_xPair_ne_of_not_mem` and the
label facts `gu3_remote_*`): the three local crossings are distinct on each side. -/
theorem w3a_y_ne : π.y_mp ≠ π.y_mq ∧ π.y_mp ≠ π.y_pq ∧ π.y_mq ≠ π.y_pq := by
  sorry
theorem w3a_y'_ne : π.y'_pC ≠ π.y'_qB ∧ π.y'_pC ≠ π.y'_pq ∧ π.y'_qB ≠ π.y'_pq := by
  sorry

/-- **(a) sub-leaves — the over data of the POSITIVE `M₀`, `M₁` at the six local crossings**, by the
determinant sign of the ORIGINAL configuration (copies of `gu6_ov_mp_pos/neg` … :7115–7162 through
`gu6_Rmp_iff`/`gu6_R_pC_iff` :7069–7087 and `gu6_over_under_of_pos/neg` :5879–5926, read on strands).
These are the "six local over bits" of PLAN §5 (a): the positive instance of the parametrised D8. -/
theorem w3a_over_mp₀ :
    (0 < det (edge C.X C.m) (edge C.X C.p) →
      π.M₀.overStrand π.y_mp = π.st₀ π.mB ∧ π.M₀.underStrand π.y_mp = π.st₀ π.p') ∧
    (¬ 0 < det (edge C.X C.m) (edge C.X C.p) →
      π.M₀.overStrand π.y_mp = π.st₀ π.p' ∧ π.M₀.underStrand π.y_mp = π.st₀ π.mB) := by
  sorry
theorem w3a_over_mq₀ :
    (0 < det (edge C.X C.m) (edge C.X C.q) →
      π.M₀.overStrand π.y_mq = π.st₀ π.mC ∧ π.M₀.underStrand π.y_mq = π.st₀ π.q') ∧
    (¬ 0 < det (edge C.X C.m) (edge C.X C.q) →
      π.M₀.overStrand π.y_mq = π.st₀ π.q' ∧ π.M₀.underStrand π.y_mq = π.st₀ π.mC) := by
  sorry
theorem w3a_over_pq₀ :
    (0 < det (edge C.X C.p) (edge C.X C.q) →
      π.M₀.overStrand π.y_pq = π.st₀ π.p' ∧ π.M₀.underStrand π.y_pq = π.st₀ π.q') ∧
    (¬ 0 < det (edge C.X C.p) (edge C.X C.q) →
      π.M₀.overStrand π.y_pq = π.st₀ π.q' ∧ π.M₀.underStrand π.y_pq = π.st₀ π.p') := by
  sorry
theorem w3a_over_mp₁ :
    (0 < det (edge C.X C.m) (edge C.X C.p) →
      π.M₁.overStrand π.y'_pC = π.st₁ π.mC ∧ π.M₁.underStrand π.y'_pC = π.st₁ π.p') ∧
    (¬ 0 < det (edge C.X C.m) (edge C.X C.p) →
      π.M₁.overStrand π.y'_pC = π.st₁ π.p' ∧ π.M₁.underStrand π.y'_pC = π.st₁ π.mC) := by
  sorry
theorem w3a_over_mq₁ :
    (0 < det (edge C.X C.m) (edge C.X C.q) →
      π.M₁.overStrand π.y'_qB = π.st₁ π.mB ∧ π.M₁.underStrand π.y'_qB = π.st₁ π.q') ∧
    (¬ 0 < det (edge C.X C.m) (edge C.X C.q) →
      π.M₁.overStrand π.y'_qB = π.st₁ π.q' ∧ π.M₁.underStrand π.y'_qB = π.st₁ π.mB) := by
  sorry
theorem w3a_over_pq₁ :
    (0 < det (edge C.X C.p) (edge C.X C.q) →
      π.M₁.overStrand π.y'_pq = π.st₁ π.p' ∧ π.M₁.underStrand π.y'_pq = π.st₁ π.q') ∧
    (¬ 0 < det (edge C.X C.p) (edge C.X C.q) →
      π.M₁.overStrand π.y'_pq = π.st₁ π.q' ∧ π.M₁.underStrand π.y'_pq = π.st₁ π.p') := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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

/-- **(a) sub-leaf (Units B–D, the choice of parameters)** — copy of `G11_exists_params` :8705 over
`G11_ConfigSw` (`G11_ConfigSw.clear_edge` in place of `G11_Config.clear_edge`; `gu3_triangle_compact`,
`gu3_disc_convex`, `gu3_triangle_sub_interior_disc`, `gu3_exists_small` re-stated for `G11_discOfSw`). -/
theorem w3a_exists_params {k : ℕ} [NeZero k] (C : G11_ConfigSw k) : Nonempty (G11_ParamsSw C) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- **(h) sub-leaf — switching a DELETED crossing is invisible after the restriction** (companion of
`Record.restrictCrossings_switch`): `Record.switch v` changes only the bits and signs of the two occurrences
of `crossingOf v`, which are not retained; the identity on the retained occurrences is a `RecordIso`
(`firstReturn` of the same successor, same pairing).  ≈ 60 lines. -/
theorem w3h_restrict_switch_deleted (ρ : Record) (S : Set ρ.Crossing) (v : ρ.M)
    (hv : ρ.crossingOf v ∉ S) :
    Nonempty (RecordIso ((ρ.switch v).restrictCrossings S) (ρ.restrictCrossings S)) := by
  sorry

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
  sorry

end Row177_6


end

end SM.Link
