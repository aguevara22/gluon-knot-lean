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


/-! ### W3-A1-DE — the trans-free copy of GenericTransport.lean 4918–8630 (Units D, D8, E) over
`G11_ParamsSw` (unit W3-A1, second prover, file `W3_A1_DE.lean`).  Mechanical: `G11_Config → G11_ConfigSw`,
`G11_Params → G11_ParamsSw`, `X₀_generic/X₁_generic/X*_cross_* → w3a_*` (the skeleton's sub-leaves); the
`C`-free helpers of the accepted namespace are reused by a selective `open RProof.G11_Params (…)`, not
copied; `gu6_htrans` is dropped (replaced by the `htrans` hypothesis of `w3a_riii_param`), `riii` is re-typed
as `w3a_riii_param`, `exists_Ψ₁` as `w3a_exists_Ψ₁`, `homfly_M₁`/`core_of_params` are the skeleton's
`w3c_homfly_M₁sw`/`G11_core_sw`.  The Unit B–C facts the copy consumes are the BC prover's; here they are
unproved black boxes (accepted names, statements verbatim; the assembler de-duplicates). -/

section W3DECopy

open SM.GeoCarrier SM.Carrier
open RProof.G11_Params (gu6_D9_core_p gu6_D9_core_q gu6_arc_inner_of_path_bwd gu6_arc_inner_of_path_fwd gu6_arc_inner_of_path_start gu6_arc_start_between gu6_arc_two_paths gu6_before_iff gu6_common_eq_single gu6_cp_injective_single gu6_decode_start_same gu6_det_ne_zero_single gu6_edgePoint_comb gu6_edge_interior_of_convex gu6_edge_interior_of_convex' gu6_exists_arc_of_interior gu6_lab_val gu6_neg_iff_of_pos_iff gu6_outside_cmp gu6_overBit_iff_det gu6_over_under_of_neg gu6_over_under_of_pos gu6_riii_of_strands gu6_single_pt_eta gu6_strand_eq_iff gu6_subdiv_lab gu6_subdiv_lab_succ gu6_subdiv_mA gu6_subdiv_mB gu6_subdiv_mC gu6_subdiv_mD gu6_subdiv_mD_succ gu6_sv_fst' gu6_sv_fst_eq gu6_sv_ne gu6_sv_param_spec gu6_sv_strand' gu6_sv_visitPt_snd gu6_swap_edge gu6_tb_edge_start gu6_tb_same_edge gu6_tb_same_edge_of_start gu6_tb_span_one gu6_tb_span_two gu6_tb_vertex_between gu6_triple_eq gu6_visit_ext gu6_visit_ne_of_edge gu6_xPair_ne_of_not_mem gu6_svisit_ext gu6_sv_strand gu6_strand_ne)

variable {n : ℕ} [NeZero n]

/-! #### Aliases: the accepted names of the eight Unit B–C sub-leaves the skeleton states as `w3a_*`
(statements verbatim from the accepted file, so the copy elaborates exactly as the accepted one). -/

theorem X₀_generic : (Shadow.single ⟨k + 3, π.hk₃, π.X₀⟩).Generic := π.w3a_X₀_generic
theorem X₁_generic : (Shadow.single ⟨k + 3, π.hk₃, π.X₁⟩).Generic := π.w3a_X₁_generic
theorem X₀_cross_mp : IsCrossing π.X₀ {π.mB, π.p'} := π.w3a_X₀_cross_mp
theorem X₀_cross_mq : IsCrossing π.X₀ {π.mC, π.q'} := π.w3a_X₀_cross_mq
theorem X₀_cross_pq : IsCrossing π.X₀ {π.p', π.q'} := π.w3a_X₀_cross_pq
theorem X₁_cross_pC : IsCrossing π.X₁ {π.p', π.mC} := π.w3a_X₁_cross_pC
theorem X₁_cross_qB : IsCrossing π.X₁ {π.q', π.mB} := π.w3a_X₁_cross_qB
theorem X₁_cross_pq : IsCrossing π.X₁ {π.p', π.q'} := π.w3a_X₁_cross_pq

/-! #### Unit B–C black boxes (the BC prover's copies; statements verbatim from the accepted file) -/

/-- **BLACK BOX (Unit B–C, copy of `G11_Params.X₁_cross_iff` :2887)** — proved by the BC prover. -/
theorem X₁_cross_iff (s : Finset (ZMod (k + 3))) (hs : π.mB ∉ s) (hs' : π.mC ∉ s) :
    IsCrossing π.X₁ s ↔ IsCrossing π.X₀ s := by
  sorry

/-- **BLACK BOX (Unit B–C, copy of `G11_Params.X₁_sign_pC` :2901)** — proved by the BC prover. -/
theorem X₁_sign_pC : crossingSign π.X₁ π.p' π.mC = crossingSign C.X C.p C.m := by
  sorry

/-- **BLACK BOX (Unit B–C, copy of `G11_Params.X₁_sign_qB` :2911)** — proved by the BC prover. -/
theorem X₁_sign_qB : crossingSign π.X₁ π.q' π.mB = crossingSign C.X C.q C.m := by
  sorry

/-- **BLACK BOX (Unit B–C, copy of `G11_Params.disc_isDisc` :3130)** — proved by the BC prover. -/
theorem disc_isDisc : IsDisc π.U := by
  sorry

/-- **BLACK BOX (Unit B–C, copy of `G11_Params.triangle_sub_interior` :3136)** — proved by the BC prover. -/
theorem triangle_sub_interior : G11_triangle C.X C.hmp C.hmq C.hpq ⊆ interior π.U := by
  sorry

/-- **BLACK BOX (Unit B–C, copy of `G11_Params.inner_M₀` :3346)** — proved by the BC prover. -/
theorem inner_M₀ (y : π.M₀.Γ.Crossing) :
    π.M₀.Γ.crossingPoint y ∈ interior π.U ↔
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ y = xPair π.X₀_cross_mp ∨
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ y = xPair π.X₀_cross_mq ∨
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ y = xPair π.X₀_cross_pq := by
  sorry

/-- **BLACK BOX (Unit B–C, copy of `G11_Params.inner_M₁` :3559)** — proved by the BC prover. -/
theorem inner_M₁ (y : π.M₁.Γ.Crossing) :
    π.M₁.Γ.crossingPoint y ∈ interior π.U ↔
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩ y = xPair π.X₁_cross_pC ∨
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩ y = xPair π.X₁_cross_qB ∨
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩ y = xPair π.X₁_cross_pq := by
  sorry

/-- **BLACK BOX (Unit B–C, copy of `G11_Params.clean_M₀` :4875)** — proved by the BC prover. -/
theorem clean_M₀ : Clean π.U π.M₀ := by
  sorry

/-- **BLACK BOX (Unit B–C, copy of `G11_Params.clean_M₁` :4880)** — proved by the BC prover. -/
theorem clean_M₁ : Clean π.U π.M₁ := by
  sorry

/-- **BLACK BOX (Unit B–C, copy of `G11_Params.exists_moveMatch` :4883)** — proved by the BC prover. -/
theorem exists_moveMatch : Nonempty (MoveMatch π.U π.M₀ π.M₁) := by
  sorry

/-- **BLACK BOX (Unit B–C, copy of `G11_Params.exists_arcCovers` :4890)** — proved by the BC prover. -/
theorem exists_arcCovers : ∃ (a b c : π.M₀.Γ.Arc) (a' b' c' : π.M₁.Γ.Arc),
    a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a' ≠ b' ∧ b' ≠ c' ∧ a' ≠ c' ∧
    π.M₀.Γ.ArcCover π.U {a, b, c} ∧ π.M₁.Γ.ArcCover π.U {a', b', c'} ∧
    π.M₁.Γ.eval a'.startPt = π.M₀.Γ.eval a.startPt ∧ π.M₁.Γ.eval a'.stopPt = π.M₀.Γ.eval a.stopPt ∧
    π.M₁.Γ.eval b'.startPt = π.M₀.Γ.eval b.startPt ∧ π.M₁.Γ.eval b'.stopPt = π.M₀.Γ.eval b.stopPt ∧
    π.M₁.Γ.eval c'.startPt = π.M₀.Γ.eval c.startPt ∧ π.M₁.Γ.eval c'.stopPt = π.M₀.Γ.eval c.stopPt := by
  sorry

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
