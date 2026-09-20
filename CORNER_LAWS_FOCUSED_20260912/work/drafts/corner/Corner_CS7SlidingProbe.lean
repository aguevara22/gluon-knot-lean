-- Corner_CS7SlidingProbe.lean — the merge assembler's PORT-READINESS PROBE (2026-09-15, scratch, not a product): the wave-2b helper blocks s7a2_ (Corner_Assembled.lean 5721-6432) and s7e_ (6434-8653) verbatim, as their own module on top of the ported SM.CornerChainUnits (work/lean/SM, 20:00Z).  Compiled with `lake env lean`: 0 errors, 0 warnings.
import SM.CornerChainUnits

/-! # Row 110 thm:C-S7, sliding companion: units W2-S7A2 (prefix `s7a2_`) and S7E (prefix `s7e_`) -/

namespace SM

open Link Carrier

attribute [local instance] Classical.propDecidable

noncomputable section

section VertexEdge

variable {n : ℕ} [NeZero n]

/-! ### Unit W2-S7A2 helpers (prefix `s7a2_`): the ROTATION EQUALITY `hr` of the persistent
transport (sm-4:483-503, eq. s7c:full-rotation; PLAN_FINAL §3.3 sliding step (1), bigon ineligible /
eligible `T`), the geometric input U110-A left open (U_S7A_REPORT §2) and U110-D's
`s7d_cornerCoefficient_eq_of_strictMono` / `_cut` and U110-I's `s7i_full_rotation_germ` consume.

Route.  For a persistent support `S` of the side `b` polygon `P = g.curve (g.sideTime b t)` and a
carrier `q`, the family `u ↦ s7a2_cornerFamily … q u` reads the corner marks of `q` on `g.curve u`
(vertex `i ↦ g.curve u i`; selected visit on edge `e` with twin edge `f` ↦ `edgePoint (g.curve u) e
(edgeParameter (g.curve u) e f)`, CSilent's `silentMarkPoint` template).  Its `j`-th edge is
`ψ_j(u) • edge (g.curve u) ε_j` (`s7a2_point_sub`), where `ε_j` is the outgoing edge of `c_j` = the
incoming edge of `c_{j+1}` (lem:carriers (ii), `ccpCornerPolygon_outEdge_eq_inEdge`) and `ψ_j(u)` is the
difference of the two Cramer parameters on `ε_j`.  `ψ_j` is positive at `u = sideTime b t`
(`ccpCornerPolygon_edge`), continuous on `|u| < δ` (`continuousAt_contact_edgeParameter` at the centre,
`continuousAt_edgeParameter` off it) and NEVER ZERO there — at the centre by `contact_pair_data`
(interior parameters) and `contact_unaffected_parameters_ne` (distinct parameters of two persistent
crossings on one edge) — so it is positive on `|u| ≤ t` by sign constancy (`s7a2_pos_of_ne_zero`):
"positive edge pieces".  The corner determinants are `ψ_{j-1} ψ_j det(edge ε_{j-1}, edge ε_j)` with the
last factor nonzero at every `|u| < δ` (vertex turns: `ChirotopesOutsideZerosAgree`; selected
crossings: `contact_pair_data.det_ne_zero`): "nonzero contact determinants".  Hence the family is
regular on `|u| ≤ t` INCLUDING the wall, and lem:rot (ii) (`rotationNumber_family_constant`) gives one
rotation number; the two side values are the corner polygon of `q` and (up to `recastTuple`) that of
`s7a_sideComponentEquiv … q` (`s7a_ccpCornerMark_map`), whence `hr` (`s7a2_carrierRotation_eq`).
The family with `s7a2_cornerFamily_continuousOn` / `s7a2_cornerFamily_regular` is exactly the object
`s7i_full_rotation_germ` / `s7i_carrierRotation_sides_of_family` expect. -/

section S7A2Marks

variable {R : LabelledTuple n}

omit [NeZero n] in
/-- The original edge along which the carrier LEAVES a true corner: the vertex's own edge, the
twin's edge for a selected visit (the smoothing continues along the twin's edge). -/
def s7a2_outEdge : Mark R → ZMod n
  | Sum.inl i => i
  | Sum.inr v => (visitTwin v).2.val

omit [NeZero n] in
/-- The original edge along which the carrier ARRIVES at a true corner: the previous edge at a
vertex, the visit's own edge at a visit. -/
def s7a2_inEdge : Mark R → ZMod n
  | Sum.inl i => i - 1
  | Sum.inr v => v.2.val

omit [NeZero n] in
/-- The parameter on `s7a2_outEdge m` at which the mark `m`, read on the polygon `Q`, leaves. -/
def s7a2_outParam (Q : LabelledTuple n) : Mark R → ℝ
  | Sum.inl _ => 0
  | Sum.inr v => edgeParameter Q (visitTwin v).2.val v.2.val

omit [NeZero n] in
/-- The parameter on `s7a2_inEdge m` at which the mark `m`, read on the polygon `Q`, is reached. -/
def s7a2_inParam (Q : LabelledTuple n) : Mark R → ℝ
  | Sum.inl _ => 1
  | Sum.inr v => edgeParameter Q v.2.val (visitTwin v).2.val

omit [NeZero n] in
/-- The plane point of a mark of `R` READ ON the polygon `Q`: a vertex by its label, a visit as the
Cramer point of its edge and its twin's edge (CSilent's `silentMarkPoint`, for any pair `R`, `Q`). -/
def s7a2_point (Q : LabelledTuple n) : Mark R → Plane
  | Sum.inl i => Q i
  | Sum.inr v => edgePoint Q v.2.val (edgeParameter Q v.2.val (visitTwin v).2.val)

omit [NeZero n] in
@[simp] theorem s7a2_outEdge_inl (i : ZMod n) : s7a2_outEdge (Sum.inl i : Mark R) = i := rfl
omit [NeZero n] in
@[simp] theorem s7a2_outEdge_inr (v : Visit R) : s7a2_outEdge (Sum.inr v) = (visitTwin v).2.val := rfl
omit [NeZero n] in
@[simp] theorem s7a2_inEdge_inl (i : ZMod n) : s7a2_inEdge (Sum.inl i : Mark R) = i - 1 := rfl
omit [NeZero n] in
@[simp] theorem s7a2_inEdge_inr (v : Visit R) : s7a2_inEdge (Sum.inr v) = v.2.val := rfl
omit [NeZero n] in
@[simp] theorem s7a2_outParam_inl (Q : LabelledTuple n) (i : ZMod n) :
    s7a2_outParam Q (Sum.inl i : Mark R) = 0 := rfl
omit [NeZero n] in
@[simp] theorem s7a2_outParam_inr (Q : LabelledTuple n) (v : Visit R) :
    s7a2_outParam Q (Sum.inr v) = edgeParameter Q (visitTwin v).2.val v.2.val := rfl
omit [NeZero n] in
@[simp] theorem s7a2_inParam_inl (Q : LabelledTuple n) (i : ZMod n) :
    s7a2_inParam Q (Sum.inl i : Mark R) = 1 := rfl
omit [NeZero n] in
@[simp] theorem s7a2_inParam_inr (Q : LabelledTuple n) (v : Visit R) :
    s7a2_inParam Q (Sum.inr v) = edgeParameter Q v.2.val (visitTwin v).2.val := rfl
omit [NeZero n] in
@[simp] theorem s7a2_point_inl (Q : LabelledTuple n) (i : ZMod n) :
    s7a2_point Q (Sum.inl i : Mark R) = Q i := rfl
omit [NeZero n] in
@[simp] theorem s7a2_point_inr (Q : LabelledTuple n) (v : Visit R) :
    s7a2_point Q (Sum.inr v) = edgePoint Q v.2.val (edgeParameter Q v.2.val (visitTwin v).2.val) := rfl

omit [NeZero n] in
/-- Cramer's rule on abstract vectors: the two parametrisations of the intersection point of the
lines `a + ℝ u` and `b + ℝ v` agree when `det u v ≠ 0`. -/
theorem s7a2_cramer_vec (a b u v : Plane) (hd : det u v ≠ 0) :
    a + cramerFirst a b u v • u = b + cramerFirst b a v u • v := by
  unfold cramerFirst
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  simp only [det] at hd ⊢
  have hneg : v1 * u2 - v2 * u1 = -(u1 * v2 - u2 * v1) := by ring
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
    rw [hneg, div_neg, div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (b1 - a1) * (mul_inv_cancel₀ hd)
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
    rw [hneg, div_neg, div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (b2 - a2) * (mul_inv_cancel₀ hd)

omit [NeZero n] in
/-- **Cramer symmetry**: the crossing point of two transverse edge lines is the same whichever
edge it is read on. -/
theorem s7a2_cramer_symm (Q : LabelledTuple n) (e f : ZMod n)
    (hd : det (edge Q e) (edge Q f) ≠ 0) :
    edgePoint Q e (edgeParameter Q e f) = edgePoint Q f (edgeParameter Q f e) :=
  s7a2_cramer_vec (Q e) (Q f) (edge Q e) (edge Q f) hd

omit [NeZero n] in
/-- The point of a mark is reached on its incoming edge at its incoming parameter. -/
theorem s7a2_point_eq_in (Q : LabelledTuple n) (m : Mark R) :
    s7a2_point Q m = edgePoint Q (s7a2_inEdge m) (s7a2_inParam Q m) := by
  cases m with
  | inl i => rw [s7a2_point_inl, s7a2_inEdge_inl, s7a2_inParam_inl, edgePoint_one, sub_add_cancel]
  | inr v => rfl

omit [NeZero n] in
/-- The point of a mark is left on its outgoing edge at its outgoing parameter (for a visit this is
Cramer symmetry, so it needs the transversality of the visit's two edges on `Q`). -/
theorem s7a2_point_eq_out (Q : LabelledTuple n) (m : Mark R)
    (hd : ∀ v : Visit R, m = Sum.inr v → det (edge Q v.2.val) (edge Q (visitTwin v).2.val) ≠ 0) :
    s7a2_point Q m = edgePoint Q (s7a2_outEdge m) (s7a2_outParam Q m) := by
  cases m with
  | inl i => rw [s7a2_point_inl, s7a2_outEdge_inl, s7a2_outParam_inl, edgePoint_zero]
  | inr v =>
    rw [s7a2_point_inr, s7a2_outEdge_inr, s7a2_outParam_inr]
    exact s7a2_cramer_symm Q _ _ (hd v rfl)

/-- **The edge formula.** When the outgoing edge of `m` is the incoming edge of `m'`, the vector from
the point of `m` to the point of `m'` (both read on `Q`) is the parameter difference times that
original edge direction. -/
theorem s7a2_point_sub (Q : LabelledTuple n) (m m' : Mark R)
    (hε : s7a2_outEdge m = s7a2_inEdge m')
    (hd : ∀ v : Visit R, m = Sum.inr v → det (edge Q v.2.val) (edge Q (visitTwin v).2.val) ≠ 0) :
    s7a2_point Q m' - s7a2_point Q m =
      (s7a2_inParam Q m' - s7a2_outParam Q m) • edge Q (s7a2_outEdge m) := by
  rw [s7a2_point_eq_in Q m', s7a2_point_eq_out Q m hd, ← hε, edgePoint_sub_edgePoint]

/-! #### On a generic polygon: the mark points are the corner-polygon points, and consecutive
corners of a carrier are joined along one original edge with increasing parameters (lem:carriers
(ii), `ccpCornerPolygon_edge`). -/

/-- The point of a mark read on its own generic polygon is its traversal point. -/
theorem s7a2_point_eq_evaluation (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (m : Mark P) :
    traversalEvaluation P (markPosition hn hP.1 m) = s7a2_point P m := by
  cases m with
  | inl i => rw [markPosition_evaluation_vertex]; rfl
  | inr v =>
    rw [markPosition_evaluation_visit, s7a2_point_inr,
      (crossingParameter_spec v.1 v.2.val v.2.property).2.2]
    have h := visitParameter_eq_of_support_pair hn hP.1 v (visitTwin v).2.val
      (visit_crossing_val_eq_pair v)
    unfold visitParameter at h
    rw [h]

omit [NeZero n] in
/-- The crossing of a visit, as the pair of its edge and its twin's edge. -/
theorem s7a2_visit_isCrossing {P : LabelledTuple n} (v : Visit P) :
    IsCrossing P {v.2.val, (visitTwin v).2.val} := by
  rw [← visit_crossing_val_eq_pair v]
  exact v.1.property

/-- The outgoing slot of a true corner lies on `s7a2_outEdge`. -/
theorem s7a2_outSlot_fst (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (m : Mark P) (hm : IsTrueCorner S m) :
    (ccpOutSlot hn hP S m).1 = s7a2_outEdge m := by
  cases m with
  | inl i => rfl
  | inr v => exact ccpOutSlot_selected hn hP S v hm

/-- The incoming edge of a mark is `s7a2_inEdge`. -/
theorem s7a2_inEdge_eq (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (m : Mark P) :
    ccpInEdge hn hP m = s7a2_inEdge m := by
  cases m with
  | inl i => exact ccpInEdge_vertex hn hP i
  | inr v => exact ccpInEdge_visit hn hP v

/-- Consecutive corners of a carrier: the outgoing edge of `c_j` is the incoming edge of `c_{j+1}`. -/
theorem s7a2_corner_edges (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (j : ZMod (ccpCornerCount hn hP S q)) :
    s7a2_outEdge (ccpCornerMark hn hP S q j) = s7a2_inEdge (ccpCornerMark hn hP S q (j + 1)) := by
  rw [← s7a2_outSlot_fst hn hP S _ (ccpCornerMark_isTrueCorner hn hP S q j), ← s7a2_inEdge_eq hn hP]
  exact ccpCornerPolygon_outEdge_eq_inEdge hn hP hS q j

omit [NeZero n] in
/-- The transversality needed by `s7a2_point_eq_out` on a generic polygon. -/
theorem s7a2_det_ne_zero_generic (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (m : Mark P) :
    ∀ v : Visit P, m = Sum.inr v → det (edge P v.2.val) (edge P (visitTwin v).2.val) ≠ 0 :=
  fun v _ => crossing_edgeParameter_det_ne_zero hn hP.1 (s7a2_visit_isCrossing v)

/-- Consecutive corners of a carrier: the parameter increases along the common edge
(the positive coefficient of `ccpCornerPolygon_edge`). -/
theorem s7a2_corner_params_lt (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (j : ZMod (ccpCornerCount hn hP S q)) :
    s7a2_outParam P (ccpCornerMark hn hP S q j) <
      s7a2_inParam P (ccpCornerMark hn hP S q (j + 1)) := by
  obtain ⟨c, hc, he⟩ := ccpCornerPolygon_edge hn hP hS q j
  rw [s7a2_outSlot_fst hn hP S _ (ccpCornerMark_isTrueCorner hn hP S q j)] at he
  have hpt : edge (ccpCornerPolygon hn hP S q) j =
      s7a2_point P (ccpCornerMark hn hP S q (j + 1)) - s7a2_point P (ccpCornerMark hn hP S q j) := by
    show ccpCornerPolygon hn hP S q (j + 1) - ccpCornerPolygon hn hP S q j = _
    rw [ccpCornerPolygon_apply, ccpCornerPolygon_apply, s7a2_point_eq_evaluation hn hP,
      s7a2_point_eq_evaluation hn hP]
  rw [hpt, s7a2_point_sub P _ _ (s7a2_corner_edges hn hP hS q j) (s7a2_det_ne_zero_generic hn hP _)]
    at he
  have hne : edge P (s7a2_outEdge (ccpCornerMark hn hP S q j)) ≠ 0 := (g1 hn P hP.1).2.1 _
  have hzero : (s7a2_inParam P (ccpCornerMark hn hP S q (j + 1)) -
      s7a2_outParam P (ccpCornerMark hn hP S q j) - c) • edge P (s7a2_outEdge (ccpCornerMark hn hP S q j)) = 0 := by
    rw [sub_smul, he, sub_self]
  rcases smul_eq_zero.mp hzero with h0 | h0
  · linarith [sub_eq_zero.mp h0]
  · exact absurd h0 hne

omit [NeZero n] in
theorem s7a2_det_smul_smul (c d : ℝ) (u w : Plane) : det (c • u) (d • w) = (c * d) * det u w := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

end S7A2Marks

section S7A2Germ

variable (hn : 3 ≤ n) (g : WallGerm n)

/-- lem:wall-sides (V) (`VertexLocalData`) at EVERY parameter `|u| < δ` of the germ, relative to the
centre — the interval form of `s7a_SideLocal` (which reads it at the two side times of one `t`). -/
def s7a2_IntervalLocal (M a : ZMod n) (r η δ : ℝ) : Prop :=
  ∀ u : g.Parameter, |u.val| < δ → VertexLocalData hn g.center (g.curve u) M a r η

/-- `vertex_sides` supplies the interval-local data below a radius `δ`. -/
theorem s7a2_exists_intervalLocal (M a : ZMod n) (h : g.VertexEdgeAt M a) :
    ∃ r η : ℝ, 0 < r ∧ r < 1 ∧ g.center M = edgePoint g.center a r ∧
      0 < η ∧ 4 * η < r ∧ 4 * η < 1 - r ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ s7a2_IntervalLocal hn g M a r η δ := by
  obtain ⟨-, -, -, -, r, η, hr0, hr1, hr, hη, hηr, hηr1, δ, hδ, hδr, hloc⟩ := vertex_sides hn g h
  exact ⟨r, η, hr0, hr1, hr, hη, hηr, hηr1, δ, hδ, hδr, hloc⟩

variable {M a : ZMod n} {r η δ : ℝ}

/-- The interval-local data restricts to the side-local data of any `t < δ`. -/
theorem s7a2_sideLocal (hloc : s7a2_IntervalLocal hn g M a r η δ) {t : g.SideParameter}
    (ht : t.val < δ) : s7a_SideLocal hn g M a r η t :=
  fun b => hloc (g.sideTime b t) (by rw [g.sideTime_val_abs]; exact ht)

variable (h : g.VertexEdgeAt M a) (hloc : s7a2_IntervalLocal hn g M a r η δ)
  {u : g.Parameter} (hu : |u.val| < δ)

include hloc hu in
/-- Persistent crossings agree with the centre's at every `|u| < δ`. -/
theorem s7a2_crossing_iff (s : Finset (ZMod n)) (hs : ¬ ContactAffected M a s) :
    IsCrossing (g.curve u) s ↔ IsCrossing g.center s :=
  (hloc u hu).windows.1 s hs

include hloc hu in
/-- Chirotopes outside the centre's zero triple are nonzero at every `|u| < δ`. -/
theorem s7a2_chi_ne_zero (i j k : ZMod n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hnot : ({i, j, k} : Finset (ZMod n)) ∉ pointZeroTriples g.center) :
    chi (g.curve u) i j k ≠ 0 :=
  ((hloc u hu).chirotopes i j k hij hjk hik hnot).2

include h hloc hu in
/-- Every vertex turn is nonzero at every `|u| < δ` (the turn triple is never the contact support,
`contactSupport_ne_turnSupport`) — including the centre. -/
theorem s7a2_turn_ne_zero (i : ZMod n) : turn (g.curve u) i ≠ 0 := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  have h1 : i - 1 ≠ i := prev_ne_self i
  have h2 : i ≠ i + 1 := (next_ne_self i).symm
  have h3 : i - 1 ≠ i + 1 := prev_ne_next hn i
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.2.1
  have hnot : ({i - 1, i, i + 1} : Finset (ZMod n)) ∉ pointZeroTriples g.center := by
    rw [hz, Finset.mem_singleton]
    exact fun he => contactSupport_ne_turnSupport hn h.1 i he.symm
  exact s7a2_chi_ne_zero hn g hloc hu (i - 1) i (i + 1) h1 h2 h3 hnot

include h hloc hu in
theorem s7a2_turn_det_ne_zero (i : ZMod n) :
    det (edge (g.curve u) (i - 1)) (edge (g.curve u) i) ≠ 0 := by
  have := s7a2_turn_ne_zero hn g h hloc hu i
  rw [turn_det] at this
  exact sign_ne_zero.mp this

include h hloc hu in
/-- Every edge is nonzero at every `|u| < δ` — including the centre. -/
theorem s7a2_edge_ne_zero (i : ZMod n) : edge (g.curve u) i ≠ 0 := by
  intro h0
  apply s7a2_turn_det_ne_zero hn g h hloc hu i
  rw [h0]
  simp [det]

include h hloc hu in
/-- The two edges of a persistent crossing are transverse at every `|u| < δ`: off the centre by
genericity, at the centre by `contact_pair_data` (sm-4:495-500, "nonzero contact determinants"). -/
theorem s7a2_det_ne_zero {i j : ZMod n} (hc : IsCrossing g.center {i, j})
    (hnot : ¬ ContactAffected M a {i, j}) :
    det (edge (g.curve u) i) (edge (g.curve u) j) ≠ 0 := by
  rcases eq_or_ne u.val 0 with hu0 | hu0
  · have hu' : u = g.zeroParameter := Subtype.ext hu0
    subst hu'
    exact (contact_pair_data hn h.1 h.2.1 hc hnot).det_ne_zero
  · exact crossing_edgeParameter_det_ne_zero hn (g.generic_punctured u hu0).1
      ((s7a2_crossing_iff hn g hloc hu _ hnot).mpr hc)

include h hloc hu in
/-- The Cramer parameter of a persistent crossing is interior at every `|u| < δ` — including the
centre ("positive edge pieces"). -/
theorem s7a2_edgeParameter_interior {i j : ZMod n} (hc : IsCrossing g.center {i, j})
    (hnot : ¬ ContactAffected M a {i, j}) :
    0 < edgeParameter (g.curve u) i j ∧ edgeParameter (g.curve u) i j < 1 := by
  rcases eq_or_ne u.val 0 with hu0 | hu0
  · have hu' : u = g.zeroParameter := Subtype.ext hu0
    subst hu'
    exact (contact_pair_data hn h.1 h.2.1 hc hnot).parameter_interior
  · have hc' := (s7a2_crossing_iff hn g hloc hu _ hnot).mpr hc
    have hG := (g.generic_punctured u hu0).1
    rw [← crossingParameter_eq_edgeParameter hn hG hc']
    exact crossingParameter_interior hn hG _ i _

include h hloc hu in
/-- Two persistent crossings on one edge have distinct Cramer parameters at every `|u| < δ`:
off the centre `generic_edgeParameters_ne`, at the centre `contact_unaffected_parameters_ne`. -/
theorem s7a2_edgeParameters_ne {i j k : ZMod n} (hjk : j ≠ k)
    (hij : IsCrossing g.center {i, j}) (hnij : ¬ ContactAffected M a {i, j})
    (hik : IsCrossing g.center {i, k}) (hnik : ¬ ContactAffected M a {i, k}) :
    edgeParameter (g.curve u) i j ≠ edgeParameter (g.curve u) i k := by
  rcases eq_or_ne u.val 0 with hu0 | hu0
  · have hu' : u = g.zeroParameter := Subtype.ext hu0
    subst hu'
    exact contact_unaffected_parameters_ne hn h.1 h.2.1 h.2.2.1 hjk hij hnij hik hnik
  · exact generic_edgeParameters_ne hn (g.generic_punctured u hu0) hjk
      ((s7a2_crossing_iff hn g hloc hu _ hnij).mpr hij)
      ((s7a2_crossing_iff hn g hloc hu _ hnik).mpr hik)

include h hloc hu in
/-- The Cramer parameter of a persistent crossing is continuous in the germ parameter at every
`|u| < δ`: at the centre `continuousAt_contact_edgeParameter`, off it `continuousAt_edgeParameter`. -/
theorem s7a2_continuousAt_edgeParameter {i j : ZMod n} (hc : IsCrossing g.center {i, j})
    (hnot : ¬ ContactAffected M a {i, j}) :
    ContinuousAt (fun w : g.Parameter => edgeParameter (g.curve w) i j) u := by
  have hF : ContinuousAt (fun Q : LabelledTuple n => edgeParameter Q i j) (g.curve u) := by
    rcases eq_or_ne u.val 0 with hu0 | hu0
    · have hu' : u = g.zeroParameter := Subtype.ext hu0
      subst hu'
      exact continuousAt_contact_edgeParameter hn h.1 h.2.1 hc hnot
    · exact continuousAt_edgeParameter hn (g.generic_punctured u hu0).1
        ((s7a2_crossing_iff hn g hloc hu _ hnot).mpr hc)
  exact ContinuousAt.comp (f := g.curve) (x := u) hF g.continuous_curve.continuousAt

omit [NeZero n] in
/-- **Sign constancy on `|u| ≤ t`.** A real function of the germ parameter, continuous and nonzero
on `|u| < δ` and positive at one side time of `t < δ`, is positive on all of `|u| ≤ t`. -/
theorem s7a2_pos_of_ne_zero {ψ : g.Parameter → ℝ} {δ : ℝ} {t : g.SideParameter} (ht : t.val < δ)
    (hcont : ∀ u : g.Parameter, |u.val| < δ → ContinuousAt ψ u)
    (hne : ∀ u : g.Parameter, |u.val| < δ → ψ u ≠ 0) (b : Bool) (hpos : 0 < ψ (g.sideTime b t)) :
    ∀ u : g.Parameter, |u.val| ≤ t.val → 0 < ψ u := by
  intro u hu
  have hpre : PreconnectedSpace (Set.Icc (-t.val) t.val) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let ι : Set.Icc (-t.val) t.val → g.Parameter := fun w =>
    ⟨w.1, by obtain ⟨h1, h2⟩ := w.2; have := t.property.2; constructor <;> linarith⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have hιδ : ∀ w, |(ι w).val| < δ := fun w => lt_of_le_of_lt (abs_le.mpr w.2) ht
  have hsign : Continuous fun w => SignType.sign (ψ (ι w)) := by
    rw [continuous_iff_continuousAt]
    intro w
    have hψι : ContinuousAt (fun w => ψ (ι w)) w :=
      ContinuousAt.comp (f := ι) (x := w) (hcont _ (hιδ w)) hι.continuousAt
    exact ContinuousAt.comp (g := SignType.sign) (f := fun w => ψ (ι w)) (x := w)
      (continuousAt_sign_of_ne_zero (hne _ (hιδ w))) hψι
  have hconst := PreconnectedSpace.constant hpre hsign (x := ⟨u.val, abs_le.mp hu⟩)
    (y := ⟨(g.sideTime b t).val, abs_le.mp (le_of_eq (g.sideTime_val_abs b t))⟩)
  change SignType.sign (ψ u) = SignType.sign (ψ (g.sideTime b t)) at hconst
  exact sign_eq_one_iff.mp (hconst.trans (sign_eq_one_iff.mpr hpos))

end S7A2Germ

/-! #### The corner-polygon family of a persistent carrier through the wall -/

section S7A2Family

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} {r η δ : ℝ}
  (h : g.VertexEdgeAt M a) (hloc : s7a2_IntervalLocal hn g M a r η δ)
  {t : g.SideParameter} (ht : t.val < δ) (b : Bool)
  (S : Finset (Crossing (g.curve (g.sideTime b t))))
  (hS : IsDecomposition hn (s7a_sideGeneric g b) S)
  (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val)
  (q : Component hn (s7a_sideGeneric g b) S)

/-- **The corner-polygon family** of the carrier `q` of side `b` through the wall: at the parameter
`u` the `j`-th vertex is the `j`-th corner mark of `q` READ ON `g.curve u` (vertex `i ↦ g.curve u i`,
selected visit `↦ edgePoint (g.curve u) e (edgeParameter (g.curve u) e f)`); CSilent's
`silentCornerFamily` for the persistent transport. -/
def s7a2_cornerFamily (u : g.Parameter) : LabelledTuple (ccpCornerCount hn (s7a_sideGeneric g b) S q) :=
  fun j => s7a2_point (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) S q j)

/-- At the side time of its own side the family IS the corner polygon of `q`. -/
theorem s7a2_cornerFamily_side_self :
    s7a2_cornerFamily hn g b S q (g.sideTime b t) = ccpCornerPolygon hn (s7a_sideGeneric g b) S q := by
  funext j
  exact (s7a2_point_eq_evaluation hn (s7a_sideGeneric g b) _).symm

include hloc ht hSp in
/-- The crossing of a selected visit of a persistent support is a persistent crossing of the centre. -/
theorem s7a2_corner_crossing (v : Visit (g.curve (g.sideTime b t))) (hv : v.1 ∈ S) :
    IsCrossing g.center {v.2.val, (visitTwin v).2.val} ∧
      ¬ ContactAffected M a {v.2.val, (visitTwin v).2.val} := by
  have hnot : ¬ ContactAffected M a {v.2.val, (visitTwin v).2.val} := by
    rw [← visit_crossing_val_eq_pair v]
    exact hSp v.1 hv
  refine ⟨?_, hnot⟩
  exact (s7a2_crossing_iff hn g hloc (u := g.sideTime b t)
    (by rw [g.sideTime_val_abs]; exact ht) _ hnot).mp (s7a2_visit_isCrossing v)

include hloc ht hSp in
theorem s7a2_corner_crossing' (v : Visit (g.curve (g.sideTime b t))) (hv : v.1 ∈ S) :
    IsCrossing g.center {(visitTwin v).2.val, v.2.val} ∧
      ¬ ContactAffected M a {(visitTwin v).2.val, v.2.val} := by
  rw [Finset.pair_comm]
  exact s7a2_corner_crossing hn g hloc ht b S hSp v hv

include h hloc ht hSp in
/-- Transversality at a true corner, at every `|u| < δ` (the `hd` of `s7a2_point_sub`). -/
theorem s7a2_corner_hd (u : g.Parameter) (hu : |u.val| < δ) (m : Mark (g.curve (g.sideTime b t)))
    (hm : IsTrueCorner S m) :
    ∀ v, m = Sum.inr v → det (edge (g.curve u) v.2.val) (edge (g.curve u) (visitTwin v).2.val) ≠ 0 := by
  rintro v rfl
  obtain ⟨hc, hnot⟩ := s7a2_corner_crossing hn g hloc ht b S hSp v hm
  exact s7a2_det_ne_zero hn g h hloc hu hc hnot

include h hloc ht hS hSp in
/-- **The edges of the family** are the parameter differences times the original edge directions
read on `g.curve u`, at every `|u| < δ`. -/
theorem s7a2_cornerFamily_edge (u : g.Parameter) (hu : |u.val| < δ)
    (j : ZMod (ccpCornerCount hn (s7a_sideGeneric g b) S q)) :
    edge (s7a2_cornerFamily hn g b S q u) j =
      (s7a2_inParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) S q (j + 1)) -
        s7a2_outParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) S q j)) •
        edge (g.curve u) (s7a2_outEdge (ccpCornerMark hn (s7a_sideGeneric g b) S q j)) := by
  show s7a2_point (g.curve u) _ - s7a2_point (g.curve u) _ = _
  exact s7a2_point_sub (g.curve u) _ _ (s7a2_corner_edges hn _ hS q j)
    (s7a2_corner_hd hn g h hloc ht b S hSp u hu _ (ccpCornerMark_isTrueCorner hn _ S q j))

include h hloc ht hS hSp in
/-- **The parameter difference of consecutive corners never vanishes** on `|u| < δ` — including the
centre: vertex–vertex `1`, vertex–visit and visit–vertex by interiority of the Cramer parameter,
visit–visit by distinctness of the Cramer parameters of two persistent crossings on one edge (their
twin edges differ because the parameters are ordered on side `b`). -/
theorem s7a2_psi_ne_zero (u : g.Parameter) (hu : |u.val| < δ)
    (j : ZMod (ccpCornerCount hn (s7a_sideGeneric g b) S q)) :
    s7a2_inParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) S q (j + 1)) -
      s7a2_outParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) S q j) ≠ 0 := by
  have hε := s7a2_corner_edges hn (s7a_sideGeneric g b) hS q j
  have hlt := s7a2_corner_params_lt hn (s7a_sideGeneric g b) hS q j
  have hm := ccpCornerMark_isTrueCorner hn (s7a_sideGeneric g b) S q j
  have hm' := ccpCornerMark_isTrueCorner hn (s7a_sideGeneric g b) S q (j + 1)
  rcases hmj : ccpCornerMark hn (s7a_sideGeneric g b) S q j with i | v <;>
    rcases hmj' : ccpCornerMark hn (s7a_sideGeneric g b) S q (j + 1) with i' | v' <;>
    rw [hmj, hmj'] at hε hlt <;> rw [hmj] at hm <;> rw [hmj'] at hm'
  · simp
  · simp only [s7a2_inParam_inr, s7a2_outParam_inl, sub_zero]
    obtain ⟨hc, hnot⟩ := s7a2_corner_crossing hn g hloc ht b S hSp v' hm'
    exact (s7a2_edgeParameter_interior hn g h hloc hu hc hnot).1.ne'
  · simp only [s7a2_inParam_inl, s7a2_outParam_inr]
    obtain ⟨hc, hnot⟩ := s7a2_corner_crossing' hn g hloc ht b S hSp v hm
    exact (sub_pos.mpr (s7a2_edgeParameter_interior hn g h hloc hu hc hnot).2).ne'
  · simp only [s7a2_inParam_inr, s7a2_outParam_inr, s7a2_outEdge_inr, s7a2_inEdge_inr] at hε hlt ⊢
    obtain ⟨hc, hnot⟩ := s7a2_corner_crossing' hn g hloc ht b S hSp v hm
    obtain ⟨hc', hnot'⟩ := s7a2_corner_crossing hn g hloc ht b S hSp v' hm'
    rw [← hε] at hc' hnot' hlt ⊢
    have hne : (visitTwin v').2.val ≠ v.2.val := by
      intro heq
      rw [heq] at hlt
      exact lt_irrefl _ hlt
    exact sub_ne_zero.mpr (s7a2_edgeParameters_ne hn g h hloc hu hne hc' hnot' hc hnot)

include h hloc ht hSp in
/-- The parameter difference of consecutive corners is continuous in the germ parameter on `|u| < δ`. -/
theorem s7a2_psi_continuousAt (u : g.Parameter) (hu : |u.val| < δ)
    (j : ZMod (ccpCornerCount hn (s7a_sideGeneric g b) S q)) :
    ContinuousAt (fun w : g.Parameter =>
      s7a2_inParam (g.curve w) (ccpCornerMark hn (s7a_sideGeneric g b) S q (j + 1)) -
        s7a2_outParam (g.curve w) (ccpCornerMark hn (s7a_sideGeneric g b) S q j)) u := by
  have hm := ccpCornerMark_isTrueCorner hn (s7a_sideGeneric g b) S q j
  have hm' := ccpCornerMark_isTrueCorner hn (s7a_sideGeneric g b) S q (j + 1)
  apply ContinuousAt.sub
  · rcases hmj' : ccpCornerMark hn (s7a_sideGeneric g b) S q (j + 1) with i' | v'
    · simp only [s7a2_inParam_inl]
      exact continuousAt_const
    · simp only [s7a2_inParam_inr]
      rw [hmj'] at hm'
      obtain ⟨hc, hnot⟩ := s7a2_corner_crossing hn g hloc ht b S hSp v' hm'
      exact s7a2_continuousAt_edgeParameter hn g h hloc hu hc hnot
  · rcases hmj : ccpCornerMark hn (s7a_sideGeneric g b) S q j with i | v
    · simp only [s7a2_outParam_inl]
      exact continuousAt_const
    · simp only [s7a2_outParam_inr]
      rw [hmj] at hm
      obtain ⟨hc, hnot⟩ := s7a2_corner_crossing' hn g hloc ht b S hSp v hm
      exact s7a2_continuousAt_edgeParameter hn g h hloc hu hc hnot

include h hloc ht hS hSp in
/-- **Positive edge pieces on `|u| ≤ t`** (sm-4:495-500): the parameter difference of consecutive
corners is positive on side `b` (`ccpCornerPolygon_edge`), continuous and nonzero on `|u| < δ`, hence
positive on all of `|u| ≤ t` — including the centre. -/
theorem s7a2_psi_pos (u : g.Parameter) (hu : |u.val| ≤ t.val)
    (j : ZMod (ccpCornerCount hn (s7a_sideGeneric g b) S q)) :
    0 < s7a2_inParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) S q (j + 1)) -
      s7a2_outParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) S q j) :=
  s7a2_pos_of_ne_zero g ht (fun w hw => s7a2_psi_continuousAt hn g h hloc ht b S hSp q w hw j)
    (fun w hw => s7a2_psi_ne_zero hn g h hloc ht b S hS hSp q w hw j) b
    (sub_pos.mpr (s7a2_corner_params_lt hn (s7a_sideGeneric g b) hS q j)) u hu

include h hloc ht hSp in
/-- The incoming and outgoing original directions at a true corner are transverse at every `|u| < δ`
(vertex: the turn; selected visit: the crossing determinant). -/
theorem s7a2_corner_det_ne_zero (u : g.Parameter) (hu : |u.val| < δ)
    (m : Mark (g.curve (g.sideTime b t))) (hm : IsTrueCorner S m) :
    det (edge (g.curve u) (s7a2_inEdge m)) (edge (g.curve u) (s7a2_outEdge m)) ≠ 0 := by
  cases m with
  | inl i => exact s7a2_turn_det_ne_zero hn g h hloc hu i
  | inr v =>
    obtain ⟨hc, hnot⟩ := s7a2_corner_crossing hn g hloc ht b S hSp v hm
    exact s7a2_det_ne_zero hn g h hloc hu hc hnot

include h hloc ht hS hSp in
/-- **The family is regular on `|u| ≤ t`, including at the wall**: nonzero edges (positive pieces of
nonzero original edges) and nonzero corner determinants (positive multiples of the transverse
original directions at each true corner). -/
theorem s7a2_cornerFamily_regular (u : g.Parameter) (hu : |u.val| ≤ t.val) :
    Regular (s7a2_cornerFamily hn g b S q u) := by
  have hu' : |u.val| < δ := lt_of_le_of_lt hu ht
  rw [regular_iff_edges]
  intro j
  have hψ := s7a2_psi_pos hn g h hloc ht b S hS hSp q u hu j
  have hψ' := s7a2_psi_pos hn g h hloc ht b S hS hSp q u hu (j - 1)
  rw [sub_add_cancel] at hψ'
  have he := s7a2_cornerFamily_edge hn g h hloc ht b S hS hSp q u hu' j
  have he' := s7a2_cornerFamily_edge hn g h hloc ht b S hS hSp q u hu' (j - 1)
  rw [sub_add_cancel] at he'
  have hε' := s7a2_corner_edges hn (s7a_sideGeneric g b) hS q (j - 1)
  rw [sub_add_cancel] at hε'
  have hdet : det (edge (s7a2_cornerFamily hn g b S q u) (j - 1))
      (edge (s7a2_cornerFamily hn g b S q u) j) ≠ 0 := by
    rw [he, he', s7a2_det_smul_smul, hε']
    exact mul_ne_zero (mul_ne_zero hψ'.ne' hψ.ne')
      (s7a2_corner_det_ne_zero hn g h hloc ht b S hSp u hu' _
        (ccpCornerMark_isTrueCorner hn (s7a_sideGeneric g b) S q j))
  refine ⟨?_, ?_⟩
  · rw [he]
    exact smul_ne_zero hψ.ne' (s7a2_edge_ne_zero hn g h hloc hu' _)
  · rintro ⟨r, _, hr⟩
    apply hdet
    rw [hr]
    exact det_smul_self _ r

include h hloc ht hSp in
/-- **The family is continuous on `|u| ≤ t`**: vertices by `g.continuous_curve`, selected visits by
the continuity of the Cramer parameter of a persistent crossing (`continuousAt_contact_edgeParameter`
at the centre, `continuousAt_edgeParameter` off it). -/
theorem s7a2_cornerFamily_continuousOn :
    ContinuousOn (s7a2_cornerFamily hn g b S q) {u : g.Parameter | |u.val| ≤ t.val} := by
  intro u hu
  apply ContinuousAt.continuousWithinAt
  have hu' : |u.val| < δ := lt_of_le_of_lt hu ht
  apply continuousAt_pi.mpr
  intro j
  show ContinuousAt (fun w : g.Parameter =>
    s7a2_point (g.curve w) (ccpCornerMark hn (s7a_sideGeneric g b) S q j)) u
  have hm := ccpCornerMark_isTrueCorner hn (s7a_sideGeneric g b) S q j
  rcases hmj : ccpCornerMark hn (s7a_sideGeneric g b) S q j with i | v
  · simp only [s7a2_point_inl]
    exact ((continuous_apply i).comp g.continuous_curve).continuousAt
  · simp only [s7a2_point_inr]
    rw [hmj] at hm
    obtain ⟨hc, hnot⟩ := s7a2_corner_crossing hn g hloc ht b S hSp v hm
    show ContinuousAt (fun w : g.Parameter => (g.curve w) v.2.val +
      edgeParameter (g.curve w) v.2.val (visitTwin v).2.val • edge (g.curve w) v.2.val) u
    exact (((continuous_apply _).comp g.continuous_curve).continuousAt).add
      ((s7a2_continuousAt_edgeParameter hn g h hloc hu' hc hnot).smul
        ((continuous_edge _).comp g.continuous_curve).continuousAt)

include h hloc ht hS hSp in
/-- **eq. s7c:full-rotation for the persistent carrier** (lem:rot (ii), `rotationNumber_family_constant`
on `[−t, t]`): the rotation number of the family is constant on `|u| ≤ t`. -/
theorem s7a2_cornerFamily_rotation (u : g.Parameter) (hu : |u.val| ≤ t.val) :
    rotationNumber (s7a2_cornerFamily hn g b S q u) =
      rotationNumber (s7a2_cornerFamily hn g b S q (g.sideTime b t)) := by
  have hpre : PreconnectedSpace (Set.Icc (-t.val) t.val) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let ι : Set.Icc (-t.val) t.val → g.Parameter := fun w =>
    ⟨w.1, by obtain ⟨h1, h2⟩ := w.2; have := t.property.2; constructor <;> linarith⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have hmem : ∀ w, |(ι w).val| ≤ t.val := fun w => abs_le.mpr w.2
  have hF : Continuous (fun w => s7a2_cornerFamily hn g b S q (ι w)) :=
    (s7a2_cornerFamily_continuousOn hn g h hloc ht b S hSp q).comp_continuous hι hmem
  exact rotationNumber_family_constant hF
    (fun w => s7a2_cornerFamily_regular hn g h hloc ht b S hS hSp q (ι w) (hmem w))
    ⟨u.val, abs_le.mp hu⟩ ⟨(g.sideTime b t).val, abs_le.mp (le_of_eq (g.sideTime_val_abs b t))⟩

end S7A2Family

/-! #### The rotation equality `hr` -/

section S7A2Assembly

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} {r η δ : ℝ}

omit [NeZero n] in
/-- The point of a persistent mark read on `Q'` is unchanged by the mark map `s7a_markMap`: the
vertex is fixed, a transported visit keeps its edge and its twin's edge (`s7a_visit_twin`). -/
theorem s7a2_point_markMap {P Q : LabelledTuple n}
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (Q' : LabelledTuple n) (m : Mark P) (hm : s7a_Persistent M a m) :
    s7a2_point Q' (s7a_markMap hs m) = s7a2_point Q' m := by
  cases m with
  | inl i => rfl
  | inr v =>
    rw [s7a_markMap_inr hs v hm, s7a2_point_inr, s7a2_point_inr, ← s7a_visit_twin hs v hm]
    rfl

variable (h : g.VertexEdgeAt M a) (hloc : s7a2_IntervalLocal hn g M a r η δ)
  {t : g.SideParameter} (ht : t.val < δ) (hL : s7a_SideLocal hn g M a r η t) (b b' : Bool)
  (S : Finset (Crossing (g.curve (g.sideTime b t))))
  (S' : Finset (Crossing (g.curve (g.sideTime b' t))))
  (hSS' : ∀ (v : Visit (g.curve (g.sideTime b t))) (hv : ¬ ContactAffected M a v.1.val),
    (s7a_visit (s7a_side_hs hn g hL b b') v hv).1 ∈ S' ↔ v.1 ∈ S)
  (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val) (hSp' : ∀ x ∈ S', ¬ ContactAffected M a x.val)
  (hS : IsDecomposition hn (s7a_sideGeneric g b) S) (q : Component hn (s7a_sideGeneric g b) S)

include hL hSS' hSp hSp' in
/-- The equal corner counts of corresponding carriers, stated on `s7a_sideComponentEquiv`
(`s7a_ccpCornerCount_eq`). -/
theorem s7a2_sideCornerCount_eq :
    ccpCornerCount hn (s7a_sideGeneric g b) S q =
      ccpCornerCount hn (s7a_sideGeneric g b') S'
        (s7a_sideComponentEquiv hn g hL b b' S S' hSS' hSp hSp' q) :=
  (s7a_ccpCornerCount_eq hn (s7a_sideGeneric g b) (s7a_sideGeneric g b') (s7a_side_hs hn g hL b b')
    (s7a_side_hpar hn g hL b b') S S' hSS' hSp hSp' q).symm

include hL hSS' hSp hSp' in
/-- At the side time of the OTHER side `b'` the family is the corner polygon of the corresponding
carrier `s7a_sideComponentEquiv … q` of `S'`, recast along the equal corner counts
(`s7a_ccpCornerMark_map`: the corner marks correspond index by index). -/
theorem s7a2_cornerFamily_side_other :
    s7a2_cornerFamily hn g b S q (g.sideTime b' t) =
      recastTuple (s7a2_sideCornerCount_eq hn g hL b b' S S' hSS' hSp hSp' q)
        (ccpCornerPolygon hn (s7a_sideGeneric g b') S'
          (s7a_sideComponentEquiv hn g hL b b' S S' hSS' hSp hSp' q)) := by
  funext j
  have key := s7a_ccpCornerMark_map hn (s7a_sideGeneric g b) (s7a_sideGeneric g b')
    (s7a_side_hs hn g hL b b') (s7a_side_hpar hn g hL b b') S S' hSS' hSp hSp' q j
  show s7a2_point (g.curve (g.sideTime b' t)) (ccpCornerMark hn (s7a_sideGeneric g b) S q j) =
    traversalEvaluation (g.curve (g.sideTime b' t)) (markPosition hn (s7a_sideGeneric g b').1
      (ccpCornerMark hn (s7a_sideGeneric g b') S'
        (s7a_componentEquiv hn (s7a_sideGeneric g b) (s7a_sideGeneric g b') (s7a_side_hs hn g hL b b')
          (s7a_side_hpar hn g hL b b') S S' hSS' hSp hSp' q)
        (Equiv.cast (congrArg ZMod (s7a_ccpCornerCount_eq hn (s7a_sideGeneric g b) (s7a_sideGeneric g b')
          (s7a_side_hs hn g hL b b') (s7a_side_hpar hn g hL b b') S S' hSS' hSp hSp' q).symm) j)))
  rw [key, s7a2_point_eq_evaluation hn (s7a_sideGeneric g b')]
  exact (s7a2_point_markMap (s7a_side_hs hn g hL b b') _ _
    (s7a_isTrueCorner_persistent S hSp _
      (ccpCornerMark_isTrueCorner hn (s7a_sideGeneric g b) S q j))).symm

include h hloc ht hL hSS' hSp hSp' hS in
/-- **The rotation equality `hr`** (sm-4:493-503, eq. s7c:full-rotation for the persistent carriers):
lem:rot (ii) along `s7a2_cornerFamily`, continuous and regular on `|u| ≤ t` INCLUDING the wall —
corresponding carriers on the two sides of a simple vertex–edge wall have equal `carrierRotation`.
This is the hypothesis `hr` of `s7d_cornerCoefficient_eq_of_strictMono` / `_cut` for the spectator
carriers, with `hP := s7a_sideGeneric g b`, `hQ := s7a_sideGeneric g b'` (definitionally
`(g.sideTuple b t).property`), `q' := s7a_sideComponentEquiv hn g hL b b' S S' hSS' hSp hSp' q`.
Inputs: `hloc`/`ht` from `s7a2_exists_intervalLocal` (or `vertex_sides`), `hL` any proof of the
side-local data (e.g. `s7a2_sideLocal hn g hloc ht`; proof-irrelevant). -/
theorem s7a2_carrierRotation_eq :
    carrierRotation hn (s7a_sideGeneric g b) S q =
      carrierRotation hn (s7a_sideGeneric g b') S'
        (s7a_sideComponentEquiv hn g hL b b' S S' hSS' hSp hSp' q) := by
  have h1 := s7a2_cornerFamily_side_self hn g b S q
  have h2 := s7a2_cornerFamily_side_other hn g hL b b' S S' hSS' hSp hSp' q
  have h3 := s7a2_cornerFamily_rotation hn g h hloc ht b S hS hSp q (g.sideTime b' t)
    (le_of_eq (g.sideTime_val_abs b' t))
  rw [h1, h2, rotationNumber_recastTuple] at h3
  exact h3.symm

include h hloc ht hS hSp in
/-- The family is regular at the centre `u = 0` (the value `rot(L*)` of U110-I is defined). -/
theorem s7a2_cornerFamily_regular_centre :
    Regular (s7a2_cornerFamily hn g b S q g.zeroParameter) :=
  s7a2_cornerFamily_regular hn g h hloc ht b S hS hSp q g.zeroParameter
    (by show |(0 : ℝ)| ≤ t.val; rw [abs_zero]; exact t.property.1.le)

include h hloc ht hS hSp in
/-- The rotation number of the centre polygon `L*` of the family is the carrier rotation of `q`
(`rot(L*) = rot(L_L) = rot(L_H)`, sm-4:501-503). -/
theorem s7a2_rotation_centre :
    rotationNumber (s7a2_cornerFamily hn g b S q g.zeroParameter) =
      carrierRotation hn (s7a_sideGeneric g b) S q := by
  rw [carrierRotation, ← s7a2_cornerFamily_side_self hn g b S q]
  exact s7a2_cornerFamily_rotation hn g h hloc ht b S hS hSp q g.zeroParameter
    (by show |(0 : ℝ)| ≤ t.val; rw [abs_zero]; exact t.property.1.le)

end S7A2Assembly

/-! ### Unit S7E (leaf unit U110-E `s7_sliding_law_at`, prefix `s7e_`; PLAN_FINAL §3.3 sliding
(1)-(4), §4 row U110-E).  Probe section. -/

section S7EAlgebra

/-- The summand of lem:C-X1 as a total function of the support (`0` off `Ind(G_P)`): CS3's
`stateTerm`, re-declared here because `SM.CS3` is not among the frozen imports. -/
def s7e_term (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (S : Finset (Crossing P)) : ℤ :=
  if h : IsDecomposition hn hP S then wind hn hP S * cornerProduct hn hP S h else 0

theorem s7e_term_of_not (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (h : ¬ IsDecomposition hn hP S) : s7e_term hn hP S = 0 :=
  dite_eq_right h

theorem s7e_term_of_decomposition (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (h : IsDecomposition hn hP S) :
    s7e_term hn hP S = wind hn hP S * cornerProduct hn hP S h :=
  dite_eq_left h

/-- lem:C-X1 as a sum over ALL supports (`C_X1.selector_form`, completion by zeros). -/
theorem s7e_cornerStateSum_eq_sum_term (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    cornerStateSum hn hP = ∑ S : Finset (Crossing P), s7e_term hn hP S := by
  rw [C_X1.selector_form]
  have h1 : (∑ S ∈ (independentSupports hn hP).attach,
      wind hn hP S.1 * cornerProduct hn hP S.1 S.2) =
      ∑ S ∈ (independentSupports hn hP).attach, s7e_term hn hP S.1 :=
    Finset.sum_congr rfl fun S _ => (s7e_term_of_decomposition hn hP S.2).symm
  rw [h1, Finset.sum_attach]
  exact Finset.sum_subset (Finset.subset_univ _) fun S _ hS => s7e_term_of_not hn hP hS

omit [NeZero n] in
/-- A finite sum split by a predicate into the two subtype sums (`¬P` first). -/
theorem s7e_sum_split {ι : Type*} [Fintype ι] (F : ι → ℤ) (P : ι → Prop) :
    ∑ S, F S = ∑ S : {S // ¬ P S}, F S.1 + ∑ S : {S // P S}, F S.1 := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype P F, add_comm]

omit [NeZero n] in
/-- Terms vanishing off `D` may be restricted to `D`. -/
theorem s7e_sum_full_eq_of_zero {ι : Type*} [Fintype ι] (F : ι → ℤ) (D : ι → Prop)
    (hz : ∀ S, ¬ D S → F S = 0) : ∑ S : {S // D S}, F S.1 = ∑ S, F S := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype D F]
  have h0 : ∑ S : {S // ¬ D S}, F S.1 = 0 := Finset.sum_eq_zero fun S _ => hz S.1 S.2
  rw [h0, add_zero]

omit [NeZero n] in
/-- Inside the sector `P`, terms vanishing off `D` may be restricted to `D ∧ P`. -/
theorem s7e_sum_subtype_eq_of_zero {ι : Type*} [Fintype ι] (F : ι → ℤ) (P D : ι → Prop)
    (hz : ∀ S, ¬ D S → F S = 0) :
    ∑ S : {S // P S}, F S.1 = ∑ S : {S // D S ∧ P S}, F S.1 := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun S : {S // P S} => D S.1) (fun S => F S.1)]
  have h0 : ∑ S : {S : {S // P S} // ¬ D S.1}, F S.1.1 = 0 :=
    Finset.sum_eq_zero fun S _ => hz _ S.2
  rw [h0, add_zero]
  exact Fintype.sum_equiv ((Equiv.subtypeSubtypeEquivSubtypeInter P D).trans
    (Equiv.subtypeEquivRight fun S => and_comm)) _ _ (fun S => rfl)

omit [NeZero n] in
/-- **The algebra of the sliding law** (PLAN §3.3 sliding (4): `Finset.sum_bij` + distributivity).
Two state sums `Σ f`, `Σ f'` (indexed by the supports of `P₋`, `P₊`) are compared through two sectors:
the SPECTATOR sector (`¬p`: supports avoiding the contact crossing) is matched term by term by `e₀`;
the CONTACT sector (`p`) is matched, on the decompositions `D`, `D'`, with the product `Ind(λ₁) × Ind(λ₂)`
by `e`, `e'`, where the termwise difference is `s · g₁ · g₂` (eq. s7c:sliding-selector-difference times
the equal coefficient products).  Terms vanish off the decompositions (`hz`, `hz'`, `hz₁`, `hz₂`).  Then
`Σ f' − Σ f = s (Σ g₁)(Σ g₂)`. -/
theorem s7e_law_of_sectors {α β γ₁ γ₂ : Type*} [Fintype α] [Fintype β] [Fintype γ₁] [Fintype γ₂]
    (f : α → ℤ) (f' : β → ℤ) (g₁ : γ₁ → ℤ) (g₂ : γ₂ → ℤ)
    (p : α → Prop) (p' : β → Prop) (D : α → Prop) (D' : β → Prop) (D₁ : γ₁ → Prop) (D₂ : γ₂ → Prop)
    (e₀ : {S : α // ¬ p S} ≃ {S : β // ¬ p' S}) (he₀ : ∀ S, f' (e₀ S).1 = f S.1)
    (hz : ∀ S, ¬ D S → f S = 0) (hz' : ∀ S, ¬ D' S → f' S = 0)
    (hz₁ : ∀ S, ¬ D₁ S → g₁ S = 0) (hz₂ : ∀ S, ¬ D₂ S → g₂ S = 0)
    (e : {S : α // D S ∧ p S} ≃ {S₁ : γ₁ // D₁ S₁} × {S₂ : γ₂ // D₂ S₂})
    (e' : {S : β // D' S ∧ p' S} ≃ {S₁ : γ₁ // D₁ S₁} × {S₂ : γ₂ // D₂ S₂}) (s : ℤ)
    (hc : ∀ q, f' (e'.symm q).1 - f (e.symm q).1 = s * (g₁ q.1.1 * g₂ q.2.1)) :
    ∑ S, f' S - ∑ S, f S = s * ((∑ S₁, g₁ S₁) * (∑ S₂, g₂ S₂)) := by
  classical
  rw [s7e_sum_split f' p', s7e_sum_split f p]
  have hpers : ∑ S : {S // ¬ p' S}, f' S.1 = ∑ S : {S // ¬ p S}, f S.1 :=
    (Fintype.sum_equiv e₀ _ _ (fun S => (he₀ S).symm)).symm
  rw [hpers, s7e_sum_subtype_eq_of_zero f' p' D' hz', s7e_sum_subtype_eq_of_zero f p D hz]
  have h' : ∑ S : {S // D' S ∧ p' S}, f' S.1 =
      ∑ q : {S₁ // D₁ S₁} × {S₂ // D₂ S₂}, f' (e'.symm q).1 :=
    Fintype.sum_equiv e' _ _ (fun S => by rw [Equiv.symm_apply_apply])
  have h : ∑ S : {S // D S ∧ p S}, f S.1 =
      ∑ q : {S₁ // D₁ S₁} × {S₂ // D₂ S₂}, f (e.symm q).1 :=
    Fintype.sum_equiv e _ _ (fun S => by rw [Equiv.symm_apply_apply])
  rw [h', h]
  have hdiff : (∑ S : {S // ¬ p S}, f S.1 + ∑ q, f' (e'.symm q).1) -
      (∑ S : {S // ¬ p S}, f S.1 + ∑ q, f (e.symm q).1) =
      ∑ q : {S₁ // D₁ S₁} × {S₂ // D₂ S₂}, (f' (e'.symm q).1 - f (e.symm q).1) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hdiff]
  simp_rw [hc]
  rw [← Finset.mul_sum, Fintype.sum_prod_type, ← s7e_sum_full_eq_of_zero g₁ D₁ hz₁,
    ← s7e_sum_full_eq_of_zero g₂ D₂ hz₂, Finset.sum_mul_sum]

end S7EAlgebra

section S7ESliding

variable {g : WallGerm n} {M a : ZMod n}

/-- The leg of the contact crossing on the NEGATIVE side (`P₋ = g.curve (g.sideTime false t)`):
`true` if `P₋` carries the crossing `{a, M}`, `false` if it carries `{a, M − 1}` (constant along the
side, `s7e_pattern`).  The positive side carries the other one (`SlidingCrossingPattern`). -/
noncomputable def s7e_leg (g : WallGerm n) (M a : ZMod n) : Bool :=
  decide (IsCrossing (g.sideTuple false g.sideBase).val {a, M})

/-- The sliding crossing pattern (lem:wall-sides (V), `vertex_sides`, `SlidingCrossingPattern`) read
with the leg `s7e_leg`: `P₋(t)` has exactly the contact crossing `{a, contactLeg (s7e_leg) M}` and
`P₊(t)` exactly `{a, contactLeg (!s7e_leg) M}`, at EVERY side parameter `t`. -/
theorem s7e_pattern (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter) :
    IsCrossing (g.curve (g.sideTime false t)) {a, contactLeg (s7e_leg g M a) M} ∧
    ¬ IsCrossing (g.curve (g.sideTime false t)) {a, contactLeg (!s7e_leg g M a) M} ∧
    IsCrossing (g.curve (g.sideTime true t)) {a, contactLeg (!s7e_leg g M a) M} ∧
    ¬ IsCrossing (g.curve (g.sideTime true t)) {a, contactLeg (s7e_leg g M a) M} := by
  have hpat : SlidingCrossingPattern (g.curve (g.sideTime true t)) (g.curve (g.sideTime false t)) M a :=
    ((vertex_sides hn g h.1).2.2.2.1 t t).2.2.1 h.2
  have hbase : SlidingCrossingPattern (g.curve (g.sideTime true t))
      (g.curve (g.sideTime false g.sideBase)) M a :=
    ((vertex_sides hn g h.1).2.2.2.1 t g.sideBase).2.2.1 h.2
  unfold s7e_leg
  by_cases hM : IsCrossing (g.sideTuple false g.sideBase).val {a, M}
  · rw [decide_eq_true hM]
    simp only [Bool.not_true, contactLeg, ↓reduceIte, Bool.false_eq_true]
    rcases hpat with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact ⟨h4, h3, h1, h2⟩
    · exfalso
      rcases hbase with ⟨b1, _, _, _⟩ | ⟨_, _, _, b4⟩
      · exact h1 b1
      · exact b4 hM
  · rw [decide_eq_false hM]
    simp only [Bool.not_false, contactLeg, ↓reduceIte, Bool.false_eq_true]
    rcases hpat with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exfalso
      rcases hbase with ⟨_, _, _, b4⟩ | ⟨b1, _, _, _⟩
      · exact hM b4
      · exact b1 h1
    · exact ⟨h3, h4, h2, h1⟩


/-- The contact crossing `x₋` of `P₋(t)`. -/
noncomputable def s7e_xm (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter) :
    Crossing (g.curve (g.sideTime false t)) :=
  ⟨{a, contactLeg (s7e_leg g M a) M}, (s7e_pattern hn h t).1⟩

/-- The contact crossing `x₊` of `P₊(t)`. -/
noncomputable def s7e_xp (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter) :
    Crossing (g.curve (g.sideTime true t)) :=
  ⟨{a, contactLeg (!s7e_leg g M a) M}, (s7e_pattern hn h t).2.2.1⟩

theorem s7e_xm_val (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter) :
    (s7e_xm hn h t).val = {a, contactLeg (s7e_leg g M a) M} := rfl

theorem s7e_xp_val (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter) :
    (s7e_xp hn h t).val = {a, contactLeg (!s7e_leg g M a) M} := rfl

theorem s7e_xm_affected (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter) :
    ContactAffected M a (s7e_xm hn h t).val :=
  (contactAffected_iff_leg _).mpr ⟨_, rfl⟩

theorem s7e_xp_affected (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter) :
    ContactAffected M a (s7e_xp hn h t).val :=
  (contactAffected_iff_leg _).mpr ⟨_, rfl⟩

/-- `x₋` is the ONLY contact-affected crossing of `P₋(t)`. -/
theorem s7e_eq_xm_of_affected (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter)
    (y : Crossing (g.curve (g.sideTime false t))) (hy : ContactAffected M a y.val) :
    y = s7e_xm hn h t := by
  obtain ⟨f, hf⟩ := (contactAffected_iff_leg _).mp hy
  apply Subtype.ext
  rw [hf, s7e_xm_val]
  by_cases hfl : f = s7e_leg g M a
  · rw [hfl]
  · exfalso
    have hf' : f = !s7e_leg g M a := by
      cases f <;> cases hl : s7e_leg g M a <;> simp_all
    rw [hf'] at hf
    exact (s7e_pattern hn h t).2.1 (hf ▸ y.property)

/-- `x₊` is the ONLY contact-affected crossing of `P₊(t)`. -/
theorem s7e_eq_xp_of_affected (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter)
    (y : Crossing (g.curve (g.sideTime true t))) (hy : ContactAffected M a y.val) :
    y = s7e_xp hn h t := by
  obtain ⟨f, hf⟩ := (contactAffected_iff_leg _).mp hy
  apply Subtype.ext
  rw [hf, s7e_xp_val]
  by_cases hfl : f = !s7e_leg g M a
  · rw [hfl]
  · exfalso
    have hf' : f = s7e_leg g M a := by
      cases f <;> cases hl : s7e_leg g M a <;> simp_all
    rw [hf'] at hf
    exact (s7e_pattern hn h t).2.2.2 (hf ▸ y.property)

/-- The CONTACT sector at the side parameter `t` (PLAN §3.3 sliding (2)-(3)), as the algebra
`s7e_law_of_sectors` consumes it: the decompositions of `P₋(t)` through `x₋` and those of `P₊(t)`
through `x₊` are both in bijection with `Ind(λ₁) × Ind(λ₂)` (eq. s7c:sliding-bijection,
`s7b_slidingDecompositionEquiv` on each side), and along the two bijections the difference of the
selector-form terms is `s · term(S₁) · term(S₂)` (eq. s7c:sliding-selector-difference with equal
coefficient products eq. s7c:sliding-coefficients). -/
def s7e_ContactSector (hn : 3 ≤ n) (h : g.SlidingAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (t : g.SideParameter) : Prop :=
  ∃ (e : {S : Finset (Crossing (g.curve (g.sideTime false t))) //
        IsDecomposition hn (s7a_sideGeneric g false) S ∧ s7e_xm hn h t ∈ S} ≃
      {S₁ : Finset (Crossing (firstHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂})
    (e' : {S : Finset (Crossing (g.curve (g.sideTime true t))) //
        IsDecomposition hn (s7a_sideGeneric g true) S ∧ s7e_xp hn h t ∈ S} ≃
      {S₁ : Finset (Crossing (firstHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}),
    ∀ q, s7e_term hn (s7a_sideGeneric g true) (e'.symm q).1 -
        s7e_term hn (s7a_sideGeneric g false) (e.symm q).1 =
      (g.contactSign M a : ℤ) *
        (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ q.1.1 *
          s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ q.2.1)

/-- The SPECTATOR sector at `t` (PLAN §3.3 sliding (1)): a bijection between the supports of `P₋(t)`
avoiding `x₋` and the supports of `P₊(t)` avoiding `x₊` preserving the selector-form term. -/
def s7e_SpectatorSector (hn : 3 ≤ n) (h : g.SlidingAt M a) (t : g.SideParameter) : Prop :=
  ∃ e₀ : {S : Finset (Crossing (g.curve (g.sideTime false t))) // s7e_xm hn h t ∉ S} ≃
      {S : Finset (Crossing (g.curve (g.sideTime true t))) // s7e_xp hn h t ∉ S},
    ∀ S, s7e_term hn (s7a_sideGeneric g true) (e₀ S).1 = s7e_term hn (s7a_sideGeneric g false) S.1

/-- The sliding law at one side parameter from its two sectors. -/
theorem s7e_law_at_of_sectors (hn : 3 ≤ n) (h : g.SlidingAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (t : g.SideParameter)
    (hsp : s7e_SpectatorSector hn h t) (hct : s7e_ContactSector hn h h₁ h₂ t) :
    cornerStateSum hn (g.sideTuple true t).property -
        cornerStateSum hn (g.sideTuple false t).property =
      (g.contactSign M a : ℤ) *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  obtain ⟨e₀, he₀⟩ := hsp
  obtain ⟨e, e', hc⟩ := hct
  rw [s7e_cornerStateSum_eq_sum_term, s7e_cornerStateSum_eq_sum_term,
    s7e_cornerStateSum_eq_sum_term, s7e_cornerStateSum_eq_sum_term]
  exact s7e_law_of_sectors (s7e_term hn (s7a_sideGeneric g false)) (s7e_term hn (s7a_sideGeneric g true))
    (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
    (s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
    (fun S => s7e_xm hn h t ∈ S) (fun S => s7e_xp hn h t ∈ S)
    (IsDecomposition hn (s7a_sideGeneric g false)) (IsDecomposition hn (s7a_sideGeneric g true))
    (IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
    (IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
    e₀ he₀ (fun S hS => s7e_term_of_not _ _ hS) (fun S hS => s7e_term_of_not _ _ hS)
    (fun S hS => s7e_term_of_not _ _ hS) (fun S hS => s7e_term_of_not _ _ hS) e e' _ hc

/-- The leaf from the two sectors, each available below a radius. -/
theorem s7e_sliding_law_at_of_sectors (hn : 3 ≤ n) (h : g.SlidingAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a))
    (hsp : ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → s7e_SpectatorSector hn h t)
    (hct : ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → s7e_ContactSector hn h h₁ h₂ t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  obtain ⟨δ₁, hδ₁, hsp⟩ := hsp
  obtain ⟨δ₂, hδ₂, hct⟩ := hct
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht => ?_⟩
  exact s7e_law_at_of_sectors hn h h₁ h₂ t (hsp t (lt_of_lt_of_le ht (min_le_left _ _)))
    (hct t (lt_of_lt_of_le ht (min_le_right _ _)))

end S7ESliding

section S7EMarks

/-! #### Generic mark-successor lemmas (any generic polygon): the key decomposition
`markKey m = edge.val + param`, and the shape of `nextMark` at a visit and at a vertex. -/

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)

omit [NeZero n] in
/-- The edge of a mark: the vertex's own label, the visit's edge. -/
def s7e_mEdge : Mark P → ZMod n
  | Sum.inl i => i
  | Sum.inr v => v.2.val

omit [NeZero n] in
/-- The parameter of a mark on its edge: `0` for a vertex, the visit parameter for a visit. -/
def s7e_mParam : Mark P → ℝ
  | Sum.inl _ => 0
  | Sum.inr v => visitParameter v

omit [NeZero n] in
@[simp] theorem s7e_mEdge_inl (i : ZMod n) : s7e_mEdge (Sum.inl i : Mark P) = i := rfl
omit [NeZero n] in
@[simp] theorem s7e_mEdge_inr (v : Visit P) : s7e_mEdge (Sum.inr v) = v.2.val := rfl
omit [NeZero n] in
@[simp] theorem s7e_mParam_inl (i : ZMod n) : s7e_mParam (Sum.inl i : Mark P) = 0 := rfl
omit [NeZero n] in
@[simp] theorem s7e_mParam_inr (v : Visit P) : s7e_mParam (Sum.inr v) = visitParameter v := rfl

omit [NeZero n] in
include hn hP in
theorem s7e_visitParameter_pos (v : Visit P) : 0 < visitParameter v :=
  (crossingParameter_interior hn hP.1 v.1 v.2.val v.2.property).1

omit [NeZero n] in
include hn hP in
theorem s7e_visitParameter_lt_one (v : Visit P) : visitParameter v < 1 :=
  (crossingParameter_interior hn hP.1 v.1 v.2.val v.2.property).2

omit [NeZero n] in
include hn hP in
theorem s7e_mParam_nonneg (m : Mark P) : 0 ≤ s7e_mParam m := by
  cases m with
  | inl i => exact le_refl 0
  | inr v => exact (s7e_visitParameter_pos hn hP v).le

omit [NeZero n] in
include hn hP in
theorem s7e_mParam_lt_one (m : Mark P) : s7e_mParam m < 1 := by
  cases m with
  | inl i => exact zero_lt_one
  | inr v => exact s7e_visitParameter_lt_one hn hP v

/-- `markKey m = (edge m).val + param m`. -/
theorem s7e_markKey_eq (m : Mark P) :
    markKey hn hP.1 m = ((s7e_mEdge m).val : ℝ) + s7e_mParam m := by
  cases m with
  | inl i => rw [markKey_vertex]; simp
  | inr v => rfl

/-- The key order decoded (edge label first, then parameter). -/
theorem s7e_markKey_lt_iff (m m' : Mark P) :
    markKey hn hP.1 m < markKey hn hP.1 m' ↔
      (s7e_mEdge m).val < (s7e_mEdge m').val ∨
        (s7e_mEdge m = s7e_mEdge m' ∧ s7e_mParam m < s7e_mParam m') := by
  have h := traversalKey_lt_iff (markPosition hn hP.1 m) (markPosition hn hP.1 m')
  cases m <;> cases m' <;> exact h

omit [NeZero n] in
/-- `traversalBetween` on mark positions, read on keys. -/
theorem s7e_between_iff (p q r : Mark P) :
    traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 q) (markPosition hn hP.1 r) ↔
      (markKey hn hP.1 p < markKey hn hP.1 q ∧ markKey hn hP.1 q < markKey hn hP.1 r) ∨
      (markKey hn hP.1 q < markKey hn hP.1 r ∧ markKey hn hP.1 r < markKey hn hP.1 p) ∨
      (markKey hn hP.1 r < markKey hn hP.1 p ∧ markKey hn hP.1 p < markKey hn hP.1 q) := Iff.rfl

/-- A key strictly between two integers-plus-parameters pins the edge: if
`e.val + p < e'.val + p' < e.val + 1` with `0 ≤ p'` then `e' = e`. -/
theorem s7e_edge_eq_of_key_sandwich {e e' : ZMod n} {p p' : ℝ} (hp0 : 0 ≤ p) (hp0' : 0 ≤ p')
    (hp1 : p' < 1) (h1 : (e.val : ℝ) + p < e'.val + p') (h2 : (e'.val : ℝ) + p' < e.val + 1) :
    e' = e := by
  apply ZMod.val_injective
  have h3 : (e.val : ℝ) < e'.val + 1 := by linarith
  have h4 : (e'.val : ℝ) < e.val + 1 := by linarith
  have h3' : e.val < e'.val + 1 := by exact_mod_cast h3
  have h4' : e'.val < e.val + 1 := by exact_mod_cast h4
  omega

/-- The key of a mark lies in `[edge.val, edge.val + 1)`. -/
theorem s7e_markKey_bounds (m : Mark P) :
    ((s7e_mEdge m).val : ℝ) ≤ markKey hn hP.1 m ∧ markKey hn hP.1 m < (s7e_mEdge m).val + 1 := by
  rw [s7e_markKey_eq hn hP]
  exact ⟨by linarith [s7e_mParam_nonneg hn hP m], by linarith [s7e_mParam_lt_one hn hP m]⟩

theorem s7e_markKey_nonneg (m : Mark P) : 0 ≤ markKey hn hP.1 m := by
  have := (s7e_markKey_bounds hn hP m).1
  have h0 : (0 : ℝ) ≤ (s7e_mEdge m).val := Nat.cast_nonneg _
  linarith

theorem s7e_markKey_lt_n (m : Mark P) : markKey hn hP.1 m < n := by
  have := (s7e_markKey_bounds hn hP m).2
  have h0 : ((s7e_mEdge m).val : ℝ) + 1 ≤ n := by exact_mod_cast (ZMod.val_lt (s7e_mEdge m))
  linarith

omit [NeZero n] in
/-- A mark with positive parameter is a visit. -/
theorem s7e_mark_visit_of_param_pos (m : Mark P) (h : 0 < s7e_mParam m) :
    ∃ w : Visit P, m = Sum.inr w := by
  cases m with
  | inl i => exact absurd h (lt_irrefl 0)
  | inr w => exact ⟨w, rfl⟩

/-- `(i + 1).val` in the two cases. -/
theorem s7e_val_succ (i : ZMod n) :
    (i ≠ -1 ∧ ((i + 1).val : ℝ) = i.val + 1) ∨ (i = -1 ∧ (i + 1 : ZMod n) = 0 ∧ (i.val : ℝ) = n - 1) := by
  by_cases hi : i = -1
  · right
    refine ⟨hi, by rw [hi]; ring, ?_⟩
    rw [hi]
    have h := last_index_val_succ (n := n)
    have h' : (((-1 : ZMod n).val : ℕ) : ℝ) + 1 = n := by exact_mod_cast h
    linarith
  · left
    refine ⟨hi, ?_⟩
    rw [zmod_val_next_of_ne_last hi]
    push_cast; ring

/-- **The next mark after a visit** is either the next vertex or a later visit on the same edge. -/
theorem s7e_nextMark_inr (v : Visit P) :
    nextMark hn hP (Sum.inr v) = Sum.inl (v.2.val + 1) ∨
      ∃ w : Visit P, nextMark hn hP (Sum.inr v) = Sum.inr w ∧ w.2.val = v.2.val ∧
        visitParameter v < visitParameter w := by
  by_cases hm : nextMark hn hP (Sum.inr v) = Sum.inl (v.2.val + 1)
  · exact Or.inl hm
  right
  have hne2 : Sum.inr v ≠ nextMark hn hP (Sum.inr v) := (markSuccessor_ne_self hn hP (Sum.inr v)).symm
  have hne1 : (Sum.inr v : Mark P) ≠ Sum.inl (v.2.val + 1) := Sum.inr_ne_inl
  have hb := (s7a_between_or hn hP (Sum.inr v) (nextMark hn hP (Sum.inr v)) (Sum.inl (v.2.val + 1))
    hne2 hm hne1).resolve_right (nextMark_no_mark_between hn hP rfl _)
  rw [s7e_between_iff hn hP] at hb
  have hkv : markKey hn hP.1 (Sum.inr v) = (v.2.val.val : ℝ) + visitParameter v :=
    s7e_markKey_eq hn hP _
  have hkm : markKey hn hP.1 (nextMark hn hP (Sum.inr v)) =
      ((s7e_mEdge (nextMark hn hP (Sum.inr v))).val : ℝ) + s7e_mParam (nextMark hn hP (Sum.inr v)) :=
    s7e_markKey_eq hn hP _
  have hkl : markKey hn hP.1 (Sum.inl (v.2.val + 1) : Mark P) = ((v.2.val + 1).val : ℝ) :=
    markKey_vertex hn hP.1 _
  have hc0 := s7e_visitParameter_pos hn hP v
  have hc1 := s7e_visitParameter_lt_one hn hP v
  have hp0 := s7e_mParam_nonneg hn hP (nextMark hn hP (Sum.inr v))
  have hp1 := s7e_mParam_lt_one hn hP (nextMark hn hP (Sum.inr v))
  have hk0 := s7e_markKey_nonneg hn hP (nextMark hn hP (Sum.inr v))
  have hev : ((s7e_mEdge (nextMark hn hP (Sum.inr v))).val : ℝ) + 1 ≤ n := by
    exact_mod_cast ZMod.val_lt (s7e_mEdge (nextMark hn hP (Sum.inr v)))
  have key : s7e_mEdge (nextMark hn hP (Sum.inr v)) = v.2.val ∧
      visitParameter v < s7e_mParam (nextMark hn hP (Sum.inr v)) := by
    rcases s7e_val_succ (v.2.val) with ⟨_, hval⟩ | ⟨_, hzero, hval⟩
    · rcases hb with ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨h2, _⟩
      · have h1' : (v.2.val.val : ℝ) + visitParameter v <
            ((s7e_mEdge (nextMark hn hP (Sum.inr v))).val : ℝ) +
              s7e_mParam (nextMark hn hP (Sum.inr v)) := by linarith
        have h2' : ((s7e_mEdge (nextMark hn hP (Sum.inr v))).val : ℝ) +
            s7e_mParam (nextMark hn hP (Sum.inr v)) < (v.2.val.val : ℝ) + 1 := by linarith
        have he := s7e_edge_eq_of_key_sandwich hc0.le hp0 hp1 h1' h2'
        refine ⟨he, ?_⟩
        have : ((s7e_mEdge (nextMark hn hP (Sum.inr v))).val : ℝ) = v.2.val.val := by rw [he]
        linarith
      · exfalso; linarith
      · exfalso; linarith
    · have hz : markKey hn hP.1 (Sum.inl (v.2.val + 1) : Mark P) = 0 := by
        rw [hkl, hzero, ZMod.val_zero, Nat.cast_zero]
      rcases hb with ⟨_, h2⟩ | ⟨h2, _⟩ | ⟨_, h2⟩
      · exfalso; linarith
      · exfalso; linarith
      · have h3 : ((n - 1 : ℕ) : ℝ) < (((s7e_mEdge (nextMark hn hP (Sum.inr v))).val + 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (NeZero.one_le : 1 ≤ n)]; push_cast; linarith
        have h3' : n - 1 < (s7e_mEdge (nextMark hn hP (Sum.inr v))).val + 1 := by exact_mod_cast h3
        have h4 : n - 1 ≤ (s7e_mEdge (nextMark hn hP (Sum.inr v))).val := by omega
        have h5 : ((n - 1 : ℕ) : ℝ) ≤ (s7e_mEdge (nextMark hn hP (Sum.inr v))).val := by
          exact_mod_cast h4
        rw [Nat.cast_sub (NeZero.one_le : 1 ≤ n)] at h5
        push_cast at h5
        have h10 : ((s7e_mEdge (nextMark hn hP (Sum.inr v))).val : ℝ) = v.2.val.val := by linarith
        have he : s7e_mEdge (nextMark hn hP (Sum.inr v)) = v.2.val :=
          ZMod.val_injective n (by exact_mod_cast h10)
        exact ⟨he, by linarith⟩
  obtain ⟨w, hw⟩ := s7e_mark_visit_of_param_pos (nextMark hn hP (Sum.inr v))
    (lt_of_le_of_lt hc0.le key.2)
  refine ⟨w, hw, ?_, ?_⟩
  · have := key.1; rw [hw] at this; exact this
  · have := key.2; rw [hw] at this; exact this

/-- **The next mark after a vertex** is either the next vertex or a visit on the vertex's edge. -/
theorem s7e_nextMark_inl (i : ZMod n) :
    nextMark hn hP (Sum.inl i) = Sum.inl (i + 1) ∨
      ∃ w : Visit P, nextMark hn hP (Sum.inl i) = Sum.inr w ∧ w.2.val = i := by
  by_cases hm : nextMark hn hP (Sum.inl i) = Sum.inl (i + 1)
  · exact Or.inl hm
  right
  have hne2 : (Sum.inl i : Mark P) ≠ nextMark hn hP (Sum.inl i) :=
    (markSuccessor_ne_self hn hP (Sum.inl i)).symm
  have hne1 : (Sum.inl i : Mark P) ≠ Sum.inl (i + 1) := by
    intro h
    have h' : i = i + 1 := Sum.inl_injective h
    have : (1 : ZMod n) = 0 := by linear_combination -h'
    have _inst : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
    exact one_ne_zero this
  have hb := (s7a_between_or hn hP (Sum.inl i) (nextMark hn hP (Sum.inl i)) (Sum.inl (i + 1))
    hne2 hm hne1).resolve_right (nextMark_no_mark_between hn hP rfl _)
  rw [s7e_between_iff hn hP] at hb
  have hki : markKey hn hP.1 (Sum.inl i : Mark P) = (i.val : ℝ) := markKey_vertex hn hP.1 _
  have hkm : markKey hn hP.1 (nextMark hn hP (Sum.inl i)) =
      ((s7e_mEdge (nextMark hn hP (Sum.inl i))).val : ℝ) + s7e_mParam (nextMark hn hP (Sum.inl i)) :=
    s7e_markKey_eq hn hP _
  have hkl : markKey hn hP.1 (Sum.inl (i + 1) : Mark P) = ((i + 1).val : ℝ) := markKey_vertex hn hP.1 _
  have hp0 := s7e_mParam_nonneg hn hP (nextMark hn hP (Sum.inl i))
  have hp1 := s7e_mParam_lt_one hn hP (nextMark hn hP (Sum.inl i))
  have hk0 := s7e_markKey_nonneg hn hP (nextMark hn hP (Sum.inl i))
  have hev : ((s7e_mEdge (nextMark hn hP (Sum.inl i))).val : ℝ) + 1 ≤ n := by
    exact_mod_cast ZMod.val_lt (s7e_mEdge (nextMark hn hP (Sum.inl i)))
  have key : s7e_mEdge (nextMark hn hP (Sum.inl i)) = i ∧ 0 < s7e_mParam (nextMark hn hP (Sum.inl i)) := by
    rcases s7e_val_succ i with ⟨_, hval⟩ | ⟨_, hzero, hval⟩
    · rcases hb with ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨h2, _⟩
      · have h1' : (i.val : ℝ) + 0 < ((s7e_mEdge (nextMark hn hP (Sum.inl i))).val : ℝ) +
            s7e_mParam (nextMark hn hP (Sum.inl i)) := by linarith
        have h2' : ((s7e_mEdge (nextMark hn hP (Sum.inl i))).val : ℝ) +
            s7e_mParam (nextMark hn hP (Sum.inl i)) < (i.val : ℝ) + 1 := by linarith
        have he := s7e_edge_eq_of_key_sandwich (le_refl (0 : ℝ)) hp0 hp1 h1' h2'
        refine ⟨he, ?_⟩
        have : ((s7e_mEdge (nextMark hn hP (Sum.inl i))).val : ℝ) = i.val := by rw [he]
        linarith
      · exfalso; linarith
      · exfalso; linarith
    · have hz : markKey hn hP.1 (Sum.inl (i + 1) : Mark P) = 0 := by
        rw [hkl, hzero, ZMod.val_zero, Nat.cast_zero]
      rcases hb with ⟨_, h2⟩ | ⟨h2, _⟩ | ⟨_, h2⟩
      · exfalso; linarith
      · exfalso; linarith
      · have h3 : ((n - 1 : ℕ) : ℝ) < (((s7e_mEdge (nextMark hn hP (Sum.inl i))).val + 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (NeZero.one_le : 1 ≤ n)]; push_cast; linarith
        have h3' : n - 1 < (s7e_mEdge (nextMark hn hP (Sum.inl i))).val + 1 := by exact_mod_cast h3
        have h4 : n - 1 ≤ (s7e_mEdge (nextMark hn hP (Sum.inl i))).val := by omega
        have h5 : ((n - 1 : ℕ) : ℝ) ≤ (s7e_mEdge (nextMark hn hP (Sum.inl i))).val := by
          exact_mod_cast h4
        rw [Nat.cast_sub (NeZero.one_le : 1 ≤ n)] at h5
        push_cast at h5
        have h10 : ((s7e_mEdge (nextMark hn hP (Sum.inl i))).val : ℝ) = i.val := by linarith
        have he : s7e_mEdge (nextMark hn hP (Sum.inl i)) = i :=
          ZMod.val_injective n (by exact_mod_cast h10)
        exact ⟨he, by linarith⟩
  obtain ⟨w, hw⟩ := s7e_mark_visit_of_param_pos (nextMark hn hP (Sum.inl i)) key.2
  refine ⟨w, hw, ?_⟩
  have := key.1; rw [hw] at this; exact this

/-- Uniqueness of the successor: a mark `m' ≠ m` with no mark strictly between `m` and `m'` is
`nextMark m`. -/
theorem s7e_nextMark_eq_of_no_between (m m' : Mark P) (hne : m ≠ m')
    (hno : ∀ u : Mark P, ¬ traversalBetween (markPosition hn hP.1 m) (markPosition hn hP.1 u)
      (markPosition hn hP.1 m')) : nextMark hn hP m = m' := by
  by_contra hne'
  have hne2 : m ≠ nextMark hn hP m := (markSuccessor_ne_self hn hP m).symm
  rcases s7a_between_or hn hP m (nextMark hn hP m) m' hne2 hne' hne with hb | hb
  · exact hno _ hb
  · exact nextMark_no_mark_between hn hP rfl m' hb

include hn hP in
/-- Two visits on one edge with equal parameters coincide. -/
theorem s7e_visit_eq_of_param (u w : Visit P) (he : u.2.val = w.2.val)
    (hp : visitParameter u = visitParameter w) : u = w := by
  have hk : markKey hn hP.1 (Sum.inr u) = markKey hn hP.1 (Sum.inr w) := by
    rw [s7e_markKey_eq hn hP, s7e_markKey_eq hn hP]
    simp only [s7e_mEdge_inr, s7e_mParam_inr, he, hp]
  exact Sum.inr_injective (markKey_injective hn hP hk)

/-- Betweenness of three marks on one edge in parameter order. -/
theorem s7e_between_same_edge (p q r : Mark P) (hpq : s7e_mEdge p = s7e_mEdge q)
    (hqr : s7e_mEdge q = s7e_mEdge r) (h1 : s7e_mParam p < s7e_mParam q)
    (h2 : s7e_mParam q < s7e_mParam r) :
    traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 q) (markPosition hn hP.1 r) := by
  rw [s7e_between_iff hn hP]
  left
  rw [s7e_markKey_eq hn hP, s7e_markKey_eq hn hP, s7e_markKey_eq hn hP, hpq, hqr]
  constructor <;> linarith

/-- A mark on edge `i` with positive parameter lies between the vertex `i` and the vertex `i + 1`. -/
theorem s7e_between_inl_mark_inl (i : ZMod n) (q : Mark P) (hq : s7e_mEdge q = i)
    (hp : 0 < s7e_mParam q) :
    traversalBetween (markPosition hn hP.1 (Sum.inl i)) (markPosition hn hP.1 q)
      (markPosition hn hP.1 (Sum.inl (i + 1))) := by
  rw [s7e_between_iff hn hP, markKey_vertex, markKey_vertex, s7e_markKey_eq hn hP, hq]
  have hp1 := s7e_mParam_lt_one hn hP q
  rcases s7e_val_succ i with ⟨_, hval⟩ | ⟨_, hzero, hval⟩
  · left; rw [hval]; constructor <;> linarith
  · right; right
    rw [hzero, ZMod.val_zero, Nat.cast_zero, hval]
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    constructor <;> linarith

/-- A visit on edge `i` with parameter above `p`'s (on the same edge) lies between `p` and the vertex
`i + 1`. -/
theorem s7e_between_mark_mark_inl (p q : Mark P) (hpq : s7e_mEdge p = s7e_mEdge q)
    (h1 : s7e_mParam p < s7e_mParam q) :
    traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 q)
      (markPosition hn hP.1 (Sum.inl (s7e_mEdge p + 1))) := by
  rw [s7e_between_iff hn hP, markKey_vertex, s7e_markKey_eq hn hP, s7e_markKey_eq hn hP, ← hpq]
  have hp1 := s7e_mParam_lt_one hn hP q
  have hp0 := s7e_mParam_nonneg hn hP p
  rcases s7e_val_succ (s7e_mEdge p) with ⟨_, hval⟩ | ⟨_, hzero, hval⟩
  · left; rw [hval]; constructor <;> linarith
  · right; right
    rw [hzero, ZMod.val_zero, Nat.cast_zero, hval]
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    constructor <;> linarith

/-- `nextMark (inr v) = inl (v.edge + 1)` when no visit on the edge comes later. -/
theorem s7e_nextMark_inr_eq_inl (v : Visit P)
    (hlast : ∀ u : Visit P, u.2.val = v.2.val → visitParameter u ≤ visitParameter v) :
    nextMark hn hP (Sum.inr v) = Sum.inl (v.2.val + 1) := by
  rcases s7e_nextMark_inr hn hP v with h | ⟨w, _, hwe, hwp⟩
  · exact h
  · exact absurd (hlast w hwe) (not_le.mpr hwp)

/-- `nextMark (inl i) = inr w` when `w` is the first visit on edge `i`. -/
theorem s7e_nextMark_inl_eq_inr (i : ZMod n) (w : Visit P) (hw : w.2.val = i)
    (hmin : ∀ u : Visit P, u.2.val = i → visitParameter w ≤ visitParameter u) :
    nextMark hn hP (Sum.inl i) = Sum.inr w := by
  rcases s7e_nextMark_inl hn hP i with h | ⟨w', h', hw'⟩
  · exfalso
    have hb := s7e_between_inl_mark_inl hn hP i (Sum.inr w) hw (s7e_visitParameter_pos hn hP w)
    exact nextMark_no_mark_between hn hP h (Sum.inr w) hb
  · by_cases hww : w' = w
    · rw [h', hww]
    · exfalso
      have hle := hmin w' hw'
      have hlt : visitParameter w < visitParameter w' := by
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact hlt
        · exact absurd (s7e_visit_eq_of_param hn hP w' w (hw'.trans hw.symm) heq.symm) hww
      have hb := s7e_between_same_edge hn hP (Sum.inl i) (Sum.inr w) (Sum.inr w') hw.symm
        (hw.trans hw'.symm) (s7e_visitParameter_pos hn hP w) hlt
      exact nextMark_no_mark_between hn hP h' (Sum.inr w) hb

/-- `nextMark (inr v) = inr w` when `w` is the first later visit on the same edge. -/
theorem s7e_nextMark_inr_eq_inr (v w : Visit P) (he : w.2.val = v.2.val)
    (hp : visitParameter v < visitParameter w)
    (hmin : ∀ u : Visit P, u.2.val = v.2.val → visitParameter v < visitParameter u →
      visitParameter w ≤ visitParameter u) :
    nextMark hn hP (Sum.inr v) = Sum.inr w := by
  rcases s7e_nextMark_inr hn hP v with h | ⟨w', h', hw'e, hw'p⟩
  · exfalso
    have hb := s7e_between_mark_mark_inl hn hP (Sum.inr v) (Sum.inr w) he.symm hp
    exact nextMark_no_mark_between hn hP h (Sum.inr w) hb
  · by_cases hww : w' = w
    · rw [h', hww]
    · exfalso
      have hle := hmin w' hw'e hw'p
      have hlt : visitParameter w < visitParameter w' := by
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact hlt
        · exact absurd (s7e_visit_eq_of_param hn hP w' w (hw'e.trans he.symm) heq.symm) hww
      have hb := s7e_between_same_edge hn hP (Sum.inr v) (Sum.inr w) (Sum.inr w') he.symm
        (he.trans hw'e.symm) hp hlt
      exact nextMark_no_mark_between hn hP h' (Sum.inr w) hb

/-- The owner of an UNSELECTED visit is the owner of the next mark. -/
theorem s7e_owner_inr_eq_next (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    owner hn hP S (Sum.inr v) = owner hn hP S (nextMark hn hP (Sum.inr v)) := by
  rw [owner_eq_iff]
  have h := (Equiv.Perm.SameCycle.refl (smoothingSuccessor hn hP S) (Sum.inr v)).apply_right
  rwa [smoothingSuccessor_visit_of_not_mem hn hP S v hv] at h

/-- The owner of a vertex is the owner of the next mark. -/
theorem s7e_owner_inl_eq_next (S : Finset (Crossing P)) (i : ZMod n) :
    owner hn hP S (Sum.inl i) = owner hn hP S (nextMark hn hP (Sum.inl i)) := by
  rw [owner_eq_iff]
  have h := (Equiv.Perm.SameCycle.refl (smoothingSuccessor hn hP S) (Sum.inl i)).apply_right
  rwa [smoothingSuccessor_vertex hn hP S i] at h

end S7EMarks

section S7ERotated

/-! #### Rotated Gauss lists from a relocation (U110-D's cut form, specialised): the visit map is
key-monotone except at ONE visit `z`, which moves from the top of the key order to the bottom
(`s7e_isRotated_of_top_to_bottom`) or from the bottom to the top (`s7e_isRotated_of_bottom_to_top`);
or is key-monotone throughout (`s7e_isRotated_of_strictMono`). -/

variable {m : ℕ} [NeZero m] {P : LabelledTuple n} {Q : LabelledTuple m}

theorem s7e_isRotated_of_strictMono (hcP : CrossingGeometry P) (hcQ : CrossingGeometry Q)
    (X : Finset (Crossing P)) (Y : Finset (Crossing Q)) (φ : Visit P → Visit Q)
    (hmem : ∀ w : Visit Q, w.1 ∈ Y ↔ ∃ v : Visit P, v.1 ∈ X ∧ φ v = w)
    (hmono : ∀ v w : Visit P, v.1 ∈ X → w.1 ∈ X →
      geometricVisitKey hcP v < geometricVisitKey hcP w →
        geometricVisitKey hcQ (φ v) < geometricVisitKey hcQ (φ w)) :
    (CB.gaussList hcQ Y).IsRotated ((CB.gaussList hcP X).map φ) := by
  rw [s7d_gaussList_eq_of_strictMono hcP hcQ X Y φ hmem hmono]

/-- The relocated visit `z` is the LAST visit of `X` in the key order of `P` and its image the FIRST
in the key order of `Q`; everything else is key-monotone. -/
theorem s7e_isRotated_of_top_to_bottom (hcP : CrossingGeometry P) (hcQ : CrossingGeometry Q)
    (X : Finset (Crossing P)) (Y : Finset (Crossing Q)) (φ : Visit P → Visit Q) (z : Visit P)
    (hmem : ∀ w : Visit Q, w.1 ∈ Y ↔ ∃ v : Visit P, v.1 ∈ X ∧ φ v = w)
    (hmono : ∀ v w : Visit P, v.1 ∈ X → w.1 ∈ X → v ≠ z → w ≠ z →
      geometricVisitKey hcP v < geometricVisitKey hcP w →
        geometricVisitKey hcQ (φ v) < geometricVisitKey hcQ (φ w))
    (htop : ∀ v : Visit P, v.1 ∈ X → v ≠ z → geometricVisitKey hcP v < geometricVisitKey hcP z)
    (hbot : ∀ v : Visit P, v.1 ∈ X → v ≠ z →
      geometricVisitKey hcQ (φ z) < geometricVisitKey hcQ (φ v)) :
    (CB.gaussList hcQ Y).IsRotated ((CB.gaussList hcP X).map φ) := by
  apply s7d_gaussList_isRotated_of_cut hcP hcQ X Y φ (geometricVisitKey hcP z) hmem
  · intro v w hv hw hvw hblk
    have hwz : w ≠ z := by
      rintro rfl
      rcases hblk with h | h
      · exact lt_irrefl _ h
      · exact lt_irrefl _ (lt_of_le_of_lt h hvw)
    have hvz : v ≠ z := by
      rintro rfl
      exact lt_irrefl _ (hvw.trans (htop w hw hwz))
    exact hmono v w hv hw hvz hwz hvw
  · intro v w hv hw hvc hcw
    have hwz : w = z := by
      by_contra hne
      exact absurd (htop w hw hne) (not_lt.mpr hcw)
    have hvz : v ≠ z := by
      rintro rfl
      exact lt_irrefl _ hvc
    subst hwz
    exact hbot v hv hvz

/-- The relocated visit `z` is the FIRST visit of `X` in the key order of `P` (below the cut `c`, all
others at or above it) and its image the LAST in the key order of `Q`; everything else is
key-monotone. -/
theorem s7e_isRotated_of_bottom_to_top (hcP : CrossingGeometry P) (hcQ : CrossingGeometry Q)
    (X : Finset (Crossing P)) (Y : Finset (Crossing Q)) (φ : Visit P → Visit Q) (z : Visit P) (c : ℝ)
    (hzc : geometricVisitKey hcP z < c)
    (hc : ∀ v : Visit P, v.1 ∈ X → v ≠ z → c ≤ geometricVisitKey hcP v)
    (hmem : ∀ w : Visit Q, w.1 ∈ Y ↔ ∃ v : Visit P, v.1 ∈ X ∧ φ v = w)
    (hmono : ∀ v w : Visit P, v.1 ∈ X → w.1 ∈ X → v ≠ z → w ≠ z →
      geometricVisitKey hcP v < geometricVisitKey hcP w →
        geometricVisitKey hcQ (φ v) < geometricVisitKey hcQ (φ w))
    (htop : ∀ v : Visit P, v.1 ∈ X → v ≠ z →
      geometricVisitKey hcQ (φ v) < geometricVisitKey hcQ (φ z)) :
    (CB.gaussList hcQ Y).IsRotated ((CB.gaussList hcP X).map φ) := by
  apply s7d_gaussList_isRotated_of_cut hcP hcQ X Y φ c hmem
  · intro v w hv hw hvw hblk
    have hwz : w ≠ z := by
      intro hwz
      have hvz : v ≠ z := by
        intro hvz
        rw [hvz, hwz] at hvw
        exact lt_irrefl _ hvw
      rw [hwz] at hvw
      exact lt_irrefl _ (lt_trans (lt_of_le_of_lt (hc v hv hvz) hvw) hzc)
    have hvz : v ≠ z := by
      intro hvz
      rw [hvz] at hblk
      rcases hblk with h | h
      · exact absurd (hc w hw hwz) (not_le.mpr h)
      · exact lt_irrefl _ (lt_of_lt_of_le hzc h)
    exact hmono v w hv hw hvz hwz hvw
  · intro v w hv hw hvc hcw
    have hvz : v = z := by
      by_contra hne
      exact absurd (hc v hv hne) (not_le.mpr hvc)
    have hwz : w ≠ z := by
      rintro rfl
      exact lt_irrefl _ (lt_of_lt_of_le hzc hcw)
    subst hvz
    exact htop w hw hwz

end S7ERotated

section S7EContactVisits

/-! #### The two visits of a crossing `{a, ℓ}` (generic `Q`): `s7e_va` on edge `a`, `s7e_vl` on edge `ℓ`
(twins of each other), their parameters (Cramer's `edgeParameter`), and exhaustion. -/

variable (hn : 3 ≤ n) {Q : LabelledTuple n} (hQ : Generic Q) {a ℓ : ZMod n}

omit [NeZero n] in
/-- The visit of the crossing `{a, ℓ}` on edge `a`. -/
def s7e_va (hc : IsCrossing Q {a, ℓ}) : Visit Q := pairVisit hc

omit [NeZero n] in
/-- The visit of the crossing `{a, ℓ}` on edge `ℓ`. -/
def s7e_vl (hc : IsCrossing Q {a, ℓ}) : Visit Q :=
  pairVisit (by rw [Finset.pair_comm]; exact hc : IsCrossing Q {ℓ, a})

omit [NeZero n] in
theorem s7e_va_fst_val (hc : IsCrossing Q {a, ℓ}) : (s7e_va hc).1.val = {a, ℓ} := rfl
omit [NeZero n] in
theorem s7e_va_edge (hc : IsCrossing Q {a, ℓ}) : (s7e_va hc).2.val = a := rfl
omit [NeZero n] in
theorem s7e_vl_fst_val (hc : IsCrossing Q {a, ℓ}) : (s7e_vl hc).1.val = {ℓ, a} := rfl
omit [NeZero n] in
theorem s7e_vl_edge (hc : IsCrossing Q {a, ℓ}) : (s7e_vl hc).2.val = ℓ := rfl

omit [NeZero n] in
theorem s7e_vl_fst (hc : IsCrossing Q {a, ℓ}) : (s7e_vl hc).1 = (s7e_va hc).1 :=
  Subtype.ext (Finset.pair_comm ℓ a)

omit [NeZero n] in
theorem s7e_va_fst_eq (hc : IsCrossing Q {a, ℓ}) : (s7e_va hc).1 = ⟨{a, ℓ}, hc⟩ := rfl

omit [NeZero n] in
include hn hQ in
theorem s7e_va_param (hc : IsCrossing Q {a, ℓ}) :
    visitParameter (s7e_va hc) = edgeParameter Q a ℓ :=
  pairVisit_parameter hn hQ.1 hc

omit [NeZero n] in
include hn hQ in
theorem s7e_vl_param (hc : IsCrossing Q {a, ℓ}) :
    visitParameter (s7e_vl hc) = edgeParameter Q ℓ a :=
  pairVisit_parameter hn hQ.1 _

omit [NeZero n] in
theorem s7e_vl_ne_va (hc : IsCrossing Q {a, ℓ}) (ha : a ≠ ℓ) : s7e_vl hc ≠ s7e_va hc := by
  intro h
  exact ha (congrArg (fun v : Visit Q => v.2.val) h).symm

omit [NeZero n] in
theorem s7e_twin_va (hc : IsCrossing Q {a, ℓ}) (ha : a ≠ ℓ) : visitTwin (s7e_va hc) = s7e_vl hc :=
  (visitTwin_unique (s7e_va hc) (s7e_vl hc) (s7e_vl_fst hc) (s7e_vl_ne_va hc ha)).symm

omit [NeZero n] in
theorem s7e_twin_vl (hc : IsCrossing Q {a, ℓ}) (ha : a ≠ ℓ) : visitTwin (s7e_vl hc) = s7e_va hc := by
  rw [← s7e_twin_va hc ha, visitTwin_involutive]

omit [NeZero n] in
/-- Every visit of the crossing `{a, ℓ}` is one of the two. -/
theorem s7e_visit_of_fst (hc : IsCrossing Q {a, ℓ}) (v : Visit Q) (hv : v.1.val = {a, ℓ}) (ha : a ≠ ℓ) :
    v = s7e_va hc ∨ v = s7e_vl hc := by
  have h1 : v.1 = (s7e_va hc).1 := Subtype.ext hv
  rcases visit_eq_or_twin (s7e_va hc) v h1 with h | h
  · exact Or.inl h
  · right; rw [h, s7e_twin_va hc ha]

omit [NeZero n] in
theorem s7e_visit_eq_va (hc : IsCrossing Q {a, ℓ}) (v : Visit Q) (hv : v.1.val = {a, ℓ})
    (he : v.2.val = a) (ha : a ≠ ℓ) : v = s7e_va hc := by
  rcases s7e_visit_of_fst hc v hv ha with h | h
  · exact h
  · exfalso; rw [h, s7e_vl_edge] at he; exact ha he.symm

omit [NeZero n] in
theorem s7e_visit_eq_vl (hc : IsCrossing Q {a, ℓ}) (v : Visit Q) (hv : v.1.val = {a, ℓ})
    (he : v.2.val = ℓ) (ha : a ≠ ℓ) : v = s7e_vl hc := by
  rcases s7e_visit_of_fst hc v hv ha with h | h
  · exfalso; rw [h, s7e_va_edge] at he; exact ha he
  · exact h

omit [NeZero n] in
/-- A visit of the crossing `{a, ℓ}` is on edge `a` or on edge `ℓ`. -/
theorem s7e_edge_of_fst (v : Visit Q) (hv : v.1.val = {a, ℓ}) : v.2.val = a ∨ v.2.val = ℓ := by
  have hm : v.2.val ∈ ({a, ℓ} : Finset (ZMod n)) := hv ▸ v.2.property
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hm

end S7EContactVisits

section S7ECrossEquiv

/-! #### The crossing bijection `Crossing P ≃ Crossing Q` of a sliding wall: `xm ↦ xp`, persistent
crossings by their supports (`s7a_cross`); its `Finset.map` on supports. -/

variable {P Q : LabelledTuple n} {M a : ZMod n}
  (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
  (xm : Crossing P) (xp : Crossing Q)

omit [NeZero n] in
/-- The crossing map: the contact crossing to the contact crossing, persistent crossings by support. -/
def s7e_crossMap (x : Crossing P) : Crossing Q :=
  if hx : ContactAffected M a x.val then xp else s7a_cross hs x hx

omit [NeZero n] in
theorem s7e_crossMap_of_not (x : Crossing P) (hx : ¬ ContactAffected M a x.val) :
    s7e_crossMap hs xp x = s7a_cross hs x hx := dite_eq_right hx

omit [NeZero n] in
theorem s7e_crossMap_of_affected (x : Crossing P) (hx : ContactAffected M a x.val) :
    s7e_crossMap hs xp x = xp := dite_eq_left hx

variable (hm : ∀ y : Crossing P, ContactAffected M a y.val → y = xm)
  (hp : ∀ y : Crossing Q, ContactAffected M a y.val → y = xp)
  (hxm : ContactAffected M a xm.val) (hxp : ContactAffected M a xp.val)

include hm hxp in
omit [NeZero n] in
theorem s7e_crossMap_injective : Function.Injective (s7e_crossMap hs xp) := by
  intro x y hxy
  by_cases hx : ContactAffected M a x.val <;> by_cases hy : ContactAffected M a y.val
  · rw [hm x hx, hm y hy]
  · exfalso
    rw [s7e_crossMap_of_affected hs xp x hx, s7e_crossMap_of_not hs xp y hy] at hxy
    have hv := congrArg Subtype.val hxy
    rw [s7a_cross_val] at hv
    exact hy (hv ▸ hxp)
  · exfalso
    rw [s7e_crossMap_of_affected hs xp y hy, s7e_crossMap_of_not hs xp x hx] at hxy
    have hv := congrArg Subtype.val hxy
    rw [s7a_cross_val] at hv
    exact hx (hv.symm ▸ hxp)
  · rw [s7e_crossMap_of_not hs xp x hx, s7e_crossMap_of_not hs xp y hy] at hxy
    have hv := congrArg Subtype.val hxy
    exact Subtype.ext hv

include hp hxm in
omit [NeZero n] in
theorem s7e_crossMap_surjective : Function.Surjective (s7e_crossMap hs xp) := by
  intro y
  by_cases hy : ContactAffected M a y.val
  · refine ⟨xm, ?_⟩
    rw [s7e_crossMap_of_affected hs xp xm hxm, hp y hy]
  · obtain ⟨x, hx, hxy⟩ := s7a_cross_surj hs y hy
    refine ⟨x, ?_⟩
    rw [s7e_crossMap_of_not hs xp x hx]
    exact hxy

omit [NeZero n] in
/-- The crossing bijection of the sliding wall. -/
def s7e_crossEquiv : Crossing P ≃ Crossing Q :=
  Equiv.ofBijective (s7e_crossMap hs xp)
    ⟨s7e_crossMap_injective hs xm xp hm hxp, s7e_crossMap_surjective hs xm xp hp hxm⟩

omit [NeZero n] in
theorem s7e_crossEquiv_apply (x : Crossing P) :
    s7e_crossEquiv hs xm xp hm hp hxm hxp x = s7e_crossMap hs xp x := rfl

omit [NeZero n] in
theorem s7e_crossEquiv_xm : s7e_crossEquiv hs xm xp hm hp hxm hxp xm = xp :=
  s7e_crossMap_of_affected hs xp xm hxm

omit [NeZero n] in
theorem s7e_crossEquiv_symm_xp : (s7e_crossEquiv hs xm xp hm hp hxm hxp).symm xp = xm :=
  (Equiv.symm_apply_eq _).mpr (s7e_crossEquiv_xm hs xm xp hm hp hxm hxp).symm

omit [NeZero n] in
theorem s7e_crossEquiv_of_not (x : Crossing P) (hx : ¬ ContactAffected M a x.val) :
    s7e_crossEquiv hs xm xp hm hp hxm hxp x = s7a_cross hs x hx :=
  s7e_crossMap_of_not hs xp x hx

omit [NeZero n] in
/-- The induced bijection of supports (`Finset.map` along the crossing bijection). -/
def s7e_supportEquiv : Finset (Crossing P) ≃ Finset (Crossing Q) where
  toFun S := S.map (s7e_crossEquiv hs xm xp hm hp hxm hxp).toEmbedding
  invFun S := S.map (s7e_crossEquiv hs xm xp hm hp hxm hxp).symm.toEmbedding
  left_inv S := by simp [Finset.map_map]
  right_inv S := by simp [Finset.map_map]

omit [NeZero n] in
theorem s7e_supportEquiv_apply (S : Finset (Crossing P)) :
    s7e_supportEquiv hs xm xp hm hp hxm hxp S =
      S.map (s7e_crossEquiv hs xm xp hm hp hxm hxp).toEmbedding := rfl

omit [NeZero n] in
theorem s7e_mem_supportEquiv (S : Finset (Crossing P)) (x : Crossing P) :
    s7e_crossEquiv hs xm xp hm hp hxm hxp x ∈ s7e_supportEquiv hs xm xp hm hp hxm hxp S ↔ x ∈ S :=
  Finset.mem_map' _

omit [NeZero n] in
theorem s7e_xp_mem_supportEquiv (S : Finset (Crossing P)) :
    xp ∈ s7e_supportEquiv hs xm xp hm hp hxm hxp S ↔ xm ∈ S := by
  rw [s7e_supportEquiv_apply, Finset.mem_map_equiv, s7e_crossEquiv_symm_xp]

include hm in
omit [NeZero n] in
/-- The supports avoiding `xm` are persistent. -/
theorem s7e_persistent_of_not_mem (S : Finset (Crossing P)) (hS : xm ∉ S) :
    ∀ x ∈ S, ¬ ContactAffected M a x.val :=
  fun x hx hxa => hS (hm x hxa ▸ hx)

omit [NeZero n] in
/-- The image of a support avoiding `xm` is persistent. -/
theorem s7e_supportEquiv_persistent (S : Finset (Crossing P)) (hS : xm ∉ S) :
    ∀ y ∈ s7e_supportEquiv hs xm xp hm hp hxm hxp S, ¬ ContactAffected M a y.val := by
  intro y hy hya
  rw [hp y hya, s7e_xp_mem_supportEquiv] at hy
  exact hS hy

omit [NeZero n] in
/-- U110-A's `hSS'` for the image support. -/
theorem s7e_supportEquiv_hSS' (S : Finset (Crossing P)) :
    ∀ (v : Visit P) (hv : ¬ ContactAffected M a v.1.val),
      (s7a_visit hs v hv).1 ∈ s7e_supportEquiv hs xm xp hm hp hxm hxp S ↔ v.1 ∈ S := by
  intro v hv
  rw [s7a_visit_fst, ← s7e_crossEquiv_of_not hs xm xp hm hp hxm hxp v.1 hv, s7e_mem_supportEquiv]

omit [NeZero n] in
/-- The spectator bijection `{S // xm ∉ S} ≃ {S // xp ∉ S}`. -/
def s7e_spectatorEquiv : {S : Finset (Crossing P) // xm ∉ S} ≃ {S : Finset (Crossing Q) // xp ∉ S} :=
  Equiv.subtypeEquiv (s7e_supportEquiv hs xm xp hm hp hxm hxp)
    (fun S => not_congr (s7e_xp_mem_supportEquiv hs xm xp hm hp hxm hxp S).symm)

omit [NeZero n] in
theorem s7e_spectatorEquiv_val (S : {S : Finset (Crossing P) // xm ∉ S}) :
    (s7e_spectatorEquiv hs xm xp hm hp hxm hxp S).1 = s7e_supportEquiv hs xm xp hm hp hxm hxp S.1 := rfl

end S7ECrossEquiv

section S7ESidePolygon

/-! #### A side polygon `Q` of a sliding wall with its contact crossing `{a, contactLeg f M}` and the
parameter windows (lem:wall-sides (V), `ContactParameterWindows`): the leg visit is adjacent to the
vertex `μ_M` (so they share their owner for every support avoiding the contact crossing), and the
successor of the `a`-visit is persistent. -/

variable (hn : 3 ≤ n) {C Q : LabelledTuple n} (hQ : Generic Q) {M a : ZMod n} {r η : ℝ} (f : Bool)
  (hsep : ContactSeparated M a) (hη : 0 < η) (hηr : 4 * η < r) (hηr1 : 4 * η < 1 - r)
  (hw : ContactParameterWindows C Q M a r η)
  (hc : IsCrossing Q {a, contactLeg f M})
  (huniq : ∀ y : Crossing Q, ContactAffected M a y.val → y.val = {a, contactLeg f M})

include hsep in
omit [NeZero n] in
theorem s7e_a_ne_leg : a ≠ contactLeg f M := by
  intro h
  cases f
  · exact hsep.2.2.1 (by simp only [contactLeg, Bool.false_eq_true, ↓reduceIte] at h; rw [h]; ring)
  · exact hsep.2.1 (by simp only [contactLeg, ↓reduceIte] at h; exact h.symm)

include hsep in
omit [NeZero n] in
theorem s7e_a_ne_M : a ≠ M := fun h => hsep.2.1 h.symm

include hsep in
omit [NeZero n] in
theorem s7e_a_ne_M_sub_one : a ≠ M - 1 := fun h => hsep.2.2.1 (by rw [h]; ring)

include hsep in
omit [NeZero n] in
theorem s7e_a_add_one_ne_M : a + 1 ≠ M := fun h => hsep.2.2.1 h.symm

include hsep in
omit [NeZero n] in
theorem s7e_M_ne_a_add_one : M ≠ a + 1 := hsep.2.2.1

include hn hQ hw in
/-- A persistent visit on edge `a` has its parameter more than `3η` away from `r`. -/
theorem s7e_persist_a (u : Visit Q) (hu : ¬ ContactAffected M a u.1.val) (he : u.2.val = a) :
    3 * η < |visitParameter u - r| :=
  unaffected_visit_outside_window hn hQ.1 hw u hu none he

include hn hQ hw in
/-- A persistent visit on the leg edge `contactLeg f' M` has its parameter more than `3η` away from
the contact endpoint. -/
theorem s7e_persist_leg (f' : Bool) (u : Visit Q) (hu : ¬ ContactAffected M a u.1.val)
    (he : u.2.val = contactLeg f' M) : 3 * η < |visitParameter u - contactEndpoint f'| :=
  unaffected_visit_outside_window hn hQ.1 hw u hu (some f') he

include hn hQ hw in
theorem s7e_persist_M_sub_one (u : Visit Q) (hu : ¬ ContactAffected M a u.1.val)
    (he : u.2.val = M - 1) : visitParameter u < 1 - 3 * η := by
  have h1 := s7e_persist_leg hn hQ hw false u hu he
  have h2 := s7e_visitParameter_lt_one hn hQ u
  simp only [contactEndpoint, Bool.false_eq_true, ↓reduceIte] at h1
  rw [abs_of_neg (by linarith)] at h1
  linarith

include hn hQ hw in
theorem s7e_persist_M (u : Visit Q) (hu : ¬ ContactAffected M a u.1.val) (he : u.2.val = M) :
    3 * η < visitParameter u := by
  have h1 := s7e_persist_leg hn hQ hw true u hu he
  have h2 := s7e_visitParameter_pos hn hQ u
  simp only [contactEndpoint, ↓reduceIte] at h1
  rw [abs_of_pos (by linarith)] at h1
  linarith

omit [NeZero n] in
include hn hQ hw in
/-- The contact visit on edge `a` has its parameter within `η` of `r`. -/
theorem s7e_va_param_near (hc : IsCrossing Q {a, contactLeg f M}) :
    |visitParameter (s7e_va hc) - r| < η := by
  rw [s7e_va_param hn hQ]
  exact (hw.2.2 f).1

omit [NeZero n] in
include hn hQ hw in
/-- The contact visit on the leg has its parameter within `η` of the contact endpoint. -/
theorem s7e_vl_param_near (hc : IsCrossing Q {a, contactLeg f M}) :
    |visitParameter (s7e_vl hc) - contactEndpoint f| < η := by
  rw [s7e_vl_param hn hQ]
  exact (hw.2.2 f).2

omit [NeZero n] in
include hn hQ hw in
theorem s7e_vl_param_false (hc : IsCrossing Q {a, contactLeg false M}) :
    1 - η < visitParameter (s7e_vl hc) := by
  have h1 := s7e_vl_param_near hn hQ false hw hc
  simp only [contactEndpoint, Bool.false_eq_true, ↓reduceIte] at h1
  have := (abs_lt.mp h1).1
  linarith

omit [NeZero n] in
include hn hQ hw in
theorem s7e_vl_param_true (hc : IsCrossing Q {a, contactLeg true M}) :
    visitParameter (s7e_vl hc) < η := by
  have h1 := s7e_vl_param_near hn hQ true hw hc
  simp only [contactEndpoint, ↓reduceIte] at h1
  have := (abs_lt.mp h1).2
  linarith

include huniq hsep in
omit [NeZero n] in
/-- Every visit of `Q` is the contact `a`-visit, the contact leg visit, or persistent. -/
theorem s7e_visit_cases (v : Visit Q) :
    v = s7e_va hc ∨ v = s7e_vl hc ∨ ¬ ContactAffected M a v.1.val := by
  by_cases hv : ContactAffected M a v.1.val
  · rcases s7e_visit_of_fst hc v (huniq v.1 hv) (s7e_a_ne_leg f hsep) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr hv)

include huniq hsep in
omit [NeZero n] in
/-- A visit on edge `a` that is not the contact `a`-visit is persistent. -/
theorem s7e_persistent_of_edge_a (v : Visit Q) (he : v.2.val = a) (hv : v ≠ s7e_va hc) :
    ¬ ContactAffected M a v.1.val := by
  intro hva
  exact hv (s7e_visit_eq_va hc v (huniq v.1 hva) he (s7e_a_ne_leg f hsep))

include huniq hsep in
omit [NeZero n] in
/-- A visit on the leg edge that is not the contact leg visit is persistent. -/
theorem s7e_persistent_of_edge_leg (v : Visit Q) (he : v.2.val = contactLeg f M)
    (hv : v ≠ s7e_vl hc) : ¬ ContactAffected M a v.1.val := by
  intro hva
  exact hv (s7e_visit_eq_vl hc v (huniq v.1 hva) he (s7e_a_ne_leg f hsep))

include huniq in
omit [NeZero n] in
/-- A visit on an edge other than `a` and the leg is persistent. -/
theorem s7e_persistent_of_edge_ne (v : Visit Q) (ha : v.2.val ≠ a) (hl : v.2.val ≠ contactLeg f M) :
    ¬ ContactAffected M a v.1.val := by
  intro hva
  rcases s7e_edge_of_fst v (huniq v.1 hva) with h | h
  · exact ha h
  · exact hl h

include hn hQ hsep hη hw huniq in
/-- **The leg visit and the vertex `μ_M` share their owner** for every support avoiding the contact
crossing (`f = false`: `nextMark v_ℓ = μ_M`; `f = true`: `nextMark μ_M = v_ℓ`). -/
theorem s7e_owner_vl_eq_vertex (S : Finset (Crossing Q)) (hS : (s7e_va hc).1 ∉ S) :
    owner hn hQ S (Sum.inr (s7e_vl hc)) = owner hn hQ S (Sum.inl M) := by
  cases f
  · -- the leg is `M - 1`: the leg visit is the last mark on edge `M - 1`
    have hnext : nextMark hn hQ (Sum.inr (s7e_vl hc)) = Sum.inl ((s7e_vl hc).2.val + 1) := by
      apply s7e_nextMark_inr_eq_inl hn hQ
      intro u hu
      by_cases hul : u = s7e_vl hc
      · rw [hul]
      · have hup := s7e_persistent_of_edge_leg false hsep hc huniq u (hu.trans (s7e_vl_edge hc)) hul
        have h1 := s7e_persist_M_sub_one hn hQ hw u hup
          (by rw [hu, s7e_vl_edge]; simp [contactLeg])
        have h2 := s7e_vl_param_false hn hQ hw hc
        linarith
    have hM : (s7e_vl hc).2.val + 1 = M := by
      rw [s7e_vl_edge]; simp only [contactLeg, Bool.false_eq_true, ↓reduceIte]; ring
    rw [s7e_owner_inr_eq_next hn hQ S _ (by rw [s7e_vl_fst]; exact hS), hnext, hM]
  · -- the leg is `M`: the leg visit is the first mark on edge `M`
    have hnext : nextMark hn hQ (Sum.inl M) = Sum.inr (s7e_vl hc) := by
      apply s7e_nextMark_inl_eq_inr hn hQ M (s7e_vl hc)
        (by rw [s7e_vl_edge]; simp [contactLeg])
      intro u hu
      by_cases hul : u = s7e_vl hc
      · rw [hul]
      · have hup := s7e_persistent_of_edge_leg true hsep hc huniq u
          (by rw [hu]; simp [contactLeg]) hul
        have h1 := s7e_persist_M hn hQ hw u hup hu
        have h2 := s7e_vl_param_true hn hQ hw hc
        linarith
    rw [s7e_owner_inl_eq_next hn hQ S M, hnext]

include hsep huniq in
/-- The successor of the contact `a`-visit is persistent. -/
theorem s7e_nextMark_va_persistent : s7a_Persistent M a (nextMark hn hQ (Sum.inr (s7e_va hc))) := by
  rcases s7e_nextMark_inr hn hQ (s7e_va hc) with hnext | ⟨w, hnext, hwe, hwp⟩
  · rw [hnext]; trivial
  · rw [hnext]
    show ¬ ContactAffected M a w.1.val
    apply s7e_persistent_of_edge_a f hsep hc huniq w (hwe.trans (s7e_va_edge hc))
    intro hwv
    rw [hwv] at hwp
    exact lt_irrefl _ hwp

include hn hQ in
/-- If the successor of the contact `a`-visit is the vertex `a + 1`, no persistent visit on edge `a`
lies beyond the contact `a`-visit. -/
theorem s7e_no_later_of_nextMark_inl (hnext : nextMark hn hQ (Sum.inr (s7e_va hc)) = Sum.inl (a + 1))
    (u : Visit Q) (hu : ¬ ContactAffected M a u.1.val) (he : u.2.val = a) :
    visitParameter u < visitParameter (s7e_va hc) := by
  by_contra hle
  have hlt : visitParameter (s7e_va hc) < visitParameter u := by
    rcases lt_or_eq_of_le (not_lt.mp hle) with hlt | heq
    · exact hlt
    · exfalso
      have := s7e_visit_eq_of_param hn hQ (s7e_va hc) u (by rw [s7e_va_edge, he]) heq
      rw [← this] at hu
      exact hu ((contactAffected_iff_leg _).mpr ⟨f, rfl⟩)
  have hb := s7e_between_mark_mark_inl hn hQ (Sum.inr (s7e_va hc)) (Sum.inr u)
    (by simp only [s7e_mEdge_inr, s7e_va_edge, he]) hlt
  simp only [s7e_mEdge_inr, s7e_va_edge] at hb
  exact nextMark_no_mark_between hn hQ hnext (Sum.inr u) hb

include hn hQ in
/-- If the successor of the contact `a`-visit is the visit `w`, then `w` is the first visit on edge
`a` beyond the contact `a`-visit. -/
theorem s7e_min_of_nextMark_inr (w : Visit Q)
    (hnext : nextMark hn hQ (Sum.inr (s7e_va hc)) = Sum.inr w) (hwe : w.2.val = a)
    (u : Visit Q) (he : u.2.val = a) (hu : visitParameter (s7e_va hc) < visitParameter u) :
    visitParameter w ≤ visitParameter u := by
  by_contra hlt
  have hb := s7e_between_same_edge hn hQ (Sum.inr (s7e_va hc)) (Sum.inr u) (Sum.inr w)
    (by simp only [s7e_mEdge_inr, s7e_va_edge, he]) (by simp only [s7e_mEdge_inr, he, hwe])
    hu (not_le.mp hlt)
  exact nextMark_no_mark_between hn hQ hnext (Sum.inr u) hb

end S7ESidePolygon

section S7ESpectator

/-! #### The spectator sector at a sliding wall (PLAN §3.3 sliding (1), sm-4:300-314): every support
of `P₋ = g.curve (g.sideTime false t)` avoiding the contact crossing `x₋` is matched with the support
of `P₊ = g.curve (g.sideTime true t)` with the same persistent crossings, and the selector-form terms
agree: decompositions correspond (U110-A), corner turns correspond (U110-A), coefficients correspond
(U110-D's record route with the RELOCATED visit map `x₋ ↦ x₊` and U110-A2's rotation equality). -/

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} {r η δ : ℝ}
  (h : g.SlidingAt M a) (hloc : s7a2_IntervalLocal hn g M a r η δ) (t : g.SideParameter)
  (ht : t.val < δ) (hη : 0 < η)

include hloc ht in
theorem s7e_hL : s7a_SideLocal hn g M a r η t := s7a2_sideLocal hn g hloc ht

include hloc ht in
theorem s7e_hs : ∀ s, ¬ ContactAffected M a s →
    (IsCrossing (g.curve (g.sideTime true t)) s ↔ IsCrossing (g.curve (g.sideTime false t)) s) :=
  s7a_side_hs hn g (s7e_hL hn g hloc t ht) false true

include hloc ht in
theorem s7e_hw (b : Bool) : ContactParameterWindows g.center (g.curve (g.sideTime b t)) M a r η :=
  (s7e_hL hn g hloc t ht b).windows

include hloc ht in
theorem s7e_hpar : ∀ (v w : Visit (g.curve (g.sideTime false t))) (hv : ¬ ContactAffected M a v.1.val)
    (hw : ¬ ContactAffected M a w.1.val), v.2.val = w.2.val →
    (visitParameter (s7a_visit (s7e_hs hn g hloc t ht) v hv) <
        visitParameter (s7a_visit (s7e_hs hn g hloc t ht) w hw) ↔
      visitParameter v < visitParameter w) :=
  s7a_side_hpar hn g (s7e_hL hn g hloc t ht) false true

omit [NeZero n] in
theorem s7e_hPm : Generic (g.curve (g.sideTime false t)) := s7a_sideGeneric g false

omit [NeZero n] in
theorem s7e_hPp : Generic (g.curve (g.sideTime true t)) := s7a_sideGeneric g true

include hn h in
theorem s7e_hxm : IsCrossing (g.curve (g.sideTime false t)) {a, contactLeg (s7e_leg g M a) M} :=
  (s7e_pattern hn h t).1

include hn h in
theorem s7e_hxp : IsCrossing (g.curve (g.sideTime true t)) {a, contactLeg (!s7e_leg g M a) M} :=
  (s7e_pattern hn h t).2.2.1

include hn h in
theorem s7e_hm : ∀ y : Crossing (g.curve (g.sideTime false t)),
    ContactAffected M a y.val → y = s7e_xm hn h t :=
  fun y hy => s7e_eq_xm_of_affected hn h t y hy

include hn h in
theorem s7e_hp : ∀ y : Crossing (g.curve (g.sideTime true t)),
    ContactAffected M a y.val → y = s7e_xp hn h t :=
  fun y hy => s7e_eq_xp_of_affected hn h t y hy

include hn h in
theorem s7e_huniq_m : ∀ y : Crossing (g.curve (g.sideTime false t)),
    ContactAffected M a y.val → y.val = {a, contactLeg (s7e_leg g M a) M} :=
  fun y hy => congrArg Subtype.val (s7e_eq_xm_of_affected hn h t y hy)

include hn h in
theorem s7e_huniq_p : ∀ y : Crossing (g.curve (g.sideTime true t)),
    ContactAffected M a y.val → y.val = {a, contactLeg (!s7e_leg g M a) M} :=
  fun y hy => congrArg Subtype.val (s7e_eq_xp_of_affected hn h t y hy)

include hn h in
theorem s7e_va_fst_xm : (s7e_va (s7e_hxm hn g h t)).1 = s7e_xm hn h t := rfl
include hn h in
theorem s7e_vl_fst_xm : (s7e_vl (s7e_hxm hn g h t)).1 = s7e_xm hn h t := s7e_vl_fst _
include hn h in
theorem s7e_va_fst_xp : (s7e_va (s7e_hxp hn g h t)).1 = s7e_xp hn h t := rfl
include hn h in
theorem s7e_vl_fst_xp : (s7e_vl (s7e_hxp hn g h t)).1 = s7e_xp hn h t := s7e_vl_fst _

include h hloc ht hη in
/-- **Sign constancy through the wall**: the side of `r` on which a persistent `a`-visit lies is the
same on `P₋` and `P₊` (the Cramer parameter is continuous and stays `3η` away from `r` on the whole
interval, lem:wall-sides (V) windows + `s7a2_pos_of_ne_zero`). -/
theorem s7e_sign_const (j : ZMod n) (hc : IsCrossing g.center {a, j})
    (hnot : ¬ ContactAffected M a {a, j}) :
    edgeParameter (g.curve (g.sideTime false t)) a j < r ↔
      edgeParameter (g.curve (g.sideTime true t)) a j < r := by
  have hcont : ∀ u : g.Parameter, |u.val| < δ →
      ContinuousAt (fun w : g.Parameter => edgeParameter (g.curve w) a j - r) u :=
    fun u hu => (s7a2_continuousAt_edgeParameter hn g h.1 hloc hu hc hnot).sub continuousAt_const
  have hne : ∀ u : g.Parameter, |u.val| < δ → edgeParameter (g.curve u) a j - r ≠ 0 := by
    intro u hu h0
    have hcr : IsCrossing (g.curve u) {a, j} := (s7a2_crossing_iff hn g hloc hu {a, j} hnot).mpr hc
    have hw := (hloc u hu).windows.2.1 none j hcr hnot
    simp only [contactWindowEdge, contactWindowCenter] at hw
    rw [h0, abs_zero] at hw
    linarith
  have habs : ∀ b : Bool, |(g.sideTime b t).val| ≤ t.val := fun b => le_of_eq (g.sideTime_val_abs b t)
  have hlt : ∀ b : Bool, |(g.sideTime b t).val| < δ := fun b => by rw [g.sideTime_val_abs]; exact ht
  constructor
  · intro h1
    by_contra h2
    have hpos : 0 < edgeParameter (g.curve (g.sideTime true t)) a j - r :=
      lt_of_le_of_ne (by linarith) (hne _ (hlt true)).symm
    have := s7a2_pos_of_ne_zero g ht hcont hne true hpos (g.sideTime false t) (habs false)
    linarith
  · intro h1
    by_contra h2
    have hpos : 0 < edgeParameter (g.curve (g.sideTime false t)) a j - r :=
      lt_of_le_of_ne (by linarith) (hne _ (hlt false)).symm
    have := s7a2_pos_of_ne_zero g ht hcont hne false hpos (g.sideTime true t) (habs true)
    linarith

include h hloc ht hη in
/-- Sign constancy for a persistent visit on edge `a` and its transport. -/
theorem s7e_side_a (u : Visit (g.curve (g.sideTime false t))) (hu : ¬ ContactAffected M a u.1.val)
    (he : u.2.val = a) :
    visitParameter u < r ↔ visitParameter (s7a_visit (s7e_hs hn g hloc t ht) u hu) < r := by
  obtain ⟨j, _, hj⟩ := crossing_support_partner u.1 u.2.val u.2.property
  have h1 : visitParameter u = edgeParameter (g.curve (g.sideTime false t)) a j := by
    rw [visitParameter_eq_of_support_pair hn (s7e_hPm g t).1 u j hj, he]
  have h2 : visitParameter (s7a_visit (s7e_hs hn g hloc t ht) u hu) =
      edgeParameter (g.curve (g.sideTime true t)) a j := by
    rw [visitParameter_eq_of_support_pair hn (s7e_hPp g t).1 (s7a_visit (s7e_hs hn g hloc t ht) u hu) j
      hj, s7a_visit_edge, he]
  have hj' : u.1.val = {a, j} := by rw [hj, he]
  have hnot : ¬ ContactAffected M a {a, j} := by rw [← hj']; exact hu
  have hc : IsCrossing g.center {a, j} :=
    (s7a2_crossing_iff hn g hloc (u := g.sideTime false t) (by rw [g.sideTime_val_abs]; exact ht)
      {a, j} hnot).mp
      (by rw [← hj']; exact u.1.property)
  rw [h1, h2]
  exact s7e_sign_const hn g h hloc t ht hη j hc hnot

include hn g h hloc ht in
/-- **The relocated visit map** `Visit P₋ → Visit P₊`: persistent visits by U110-A's `s7a_visit`
(same support, same edge), the two visits of `x₋` to the two visits of `x₊` (edge `a` to edge `a`,
leg to leg). -/
noncomputable def s7e_visitMap (v : Visit (g.curve (g.sideTime false t))) :
    Visit (g.curve (g.sideTime true t)) :=
  if hv : ContactAffected M a v.1.val then
    (if v.2.val = a then s7e_va (s7e_hxp hn g h t) else s7e_vl (s7e_hxp hn g h t))
  else s7a_visit (s7e_hs hn g hloc t ht) v hv

theorem s7e_visitMap_of_not (v : Visit (g.curve (g.sideTime false t)))
    (hv : ¬ ContactAffected M a v.1.val) :
    s7e_visitMap hn g h hloc t ht v = s7a_visit (s7e_hs hn g hloc t ht) v hv :=
  dite_eq_right hv

theorem s7e_visitMap_va :
    s7e_visitMap hn g h hloc t ht (s7e_va (s7e_hxm hn g h t)) = s7e_va (s7e_hxp hn g h t) := by
  unfold s7e_visitMap
  rw [dite_eq_left (show ContactAffected M a (s7e_va (s7e_hxm hn g h t)).1.val from
    s7e_xm_affected hn h t), ite_eq_left (s7e_va_edge _)]

theorem s7e_visitMap_vl :
    s7e_visitMap hn g h hloc t ht (s7e_vl (s7e_hxm hn g h t)) = s7e_vl (s7e_hxp hn g h t) := by
  unfold s7e_visitMap
  have hne : (s7e_vl (s7e_hxm hn g h t)).2.val ≠ a := by
    rw [s7e_vl_edge]; exact (s7e_a_ne_leg _ h.1.1).symm
  rw [dite_eq_left (by rw [s7e_vl_fst_xm]; exact s7e_xm_affected hn h t), ite_eq_right hne]

theorem s7e_visitMap_affected (v : Visit (g.curve (g.sideTime false t)))
    (hv : ContactAffected M a v.1.val) :
    ContactAffected M a (s7e_visitMap hn g h hloc t ht v).1.val := by
  unfold s7e_visitMap
  rw [dite_eq_left hv]
  split_ifs
  · exact s7e_xp_affected hn h t
  · rw [s7e_vl_fst_xp]; exact s7e_xp_affected hn h t

/-- The support bijection of the wall (`Finset.map` along `s7e_crossEquiv`). -/
noncomputable def s7e_E : Finset (Crossing (g.curve (g.sideTime false t))) ≃
    Finset (Crossing (g.curve (g.sideTime true t))) :=
  s7e_supportEquiv (s7e_hs hn g hloc t ht) (s7e_xm hn h t) (s7e_xp hn h t) (s7e_hm hn g h t)
    (s7e_hp hn g h t) (s7e_xm_affected hn h t) (s7e_xp_affected hn h t)

theorem s7e_E_hSS' (S : Finset (Crossing (g.curve (g.sideTime false t)))) :
    ∀ (v : Visit (g.curve (g.sideTime false t))) (hv : ¬ ContactAffected M a v.1.val),
      (s7a_visit (s7e_hs hn g hloc t ht) v hv).1 ∈ s7e_E hn g h hloc t ht S ↔ v.1 ∈ S :=
  s7e_supportEquiv_hSS' _ _ _ _ _ _ _ S

include hn h in
theorem s7e_E_hSp (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S) :
    ∀ x ∈ S, ¬ ContactAffected M a x.val :=
  s7e_persistent_of_not_mem _ (s7e_hm hn g h t) S hS

theorem s7e_E_hSp' (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S) :
    ∀ y ∈ s7e_E hn g h hloc t ht S, ¬ ContactAffected M a y.val :=
  s7e_supportEquiv_persistent _ _ _ _ _ _ _ S hS

theorem s7e_xp_mem_E (S : Finset (Crossing (g.curve (g.sideTime false t)))) :
    s7e_xp hn h t ∈ s7e_E hn g h hloc t ht S ↔ s7e_xm hn h t ∈ S :=
  s7e_xp_mem_supportEquiv _ _ _ _ _ _ _ S

theorem s7e_xp_notMem_E (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S) :
    s7e_xp hn h t ∉ s7e_E hn g h hloc t ht S := by
  rw [s7e_xp_mem_E]; exact hS

/-- The carrier bijection of a persistent support (U110-A's `s7a_sideComponentEquiv`). -/
noncomputable def s7e_e (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S) :
    Component hn (s7e_hPm g t) S ≃ Component hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) :=
  s7a_sideComponentEquiv hn g (s7e_hL hn g hloc t ht) false true S (s7e_E hn g h hloc t ht S)
    (s7e_E_hSS' hn g h hloc t ht S) (s7e_E_hSp hn g h t S hS) (s7e_E_hSp' hn g h hloc t ht S hS)

theorem s7e_e_owner (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S)
    (m : Mark (g.curve (g.sideTime false t))) (hm : s7a_Persistent M a m) :
    s7e_e hn g h hloc t ht S hS (owner hn (s7e_hPm g t) S m) =
      owner hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) (s7a_markMap (s7e_hs hn g hloc t ht) m) :=
  s7a_sideComponentEquiv_owner hn g _ false true S _ _ _ _ m hm

include hloc ht hη in
/-- The leg visit of `x₋` and the vertex `μ_M` share their owner on `P₋`. -/
theorem s7e_owner_vl_m (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S) :
    owner hn (s7e_hPm g t) S (Sum.inr (s7e_vl (s7e_hxm hn g h t))) = owner hn (s7e_hPm g t) S (Sum.inl M) :=
  s7e_owner_vl_eq_vertex hn (s7e_hPm g t) (s7e_leg g M a) h.1.1 hη (s7e_hw hn g hloc t ht false)
    (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) S hS

include hloc ht hη in
/-- The leg visit of `x₊` and the vertex `μ_M` share their owner on `P₊`. -/
theorem s7e_owner_vl_p (S' : Finset (Crossing (g.curve (g.sideTime true t)))) (hS' : s7e_xp hn h t ∉ S') :
    owner hn (s7e_hPp g t) S' (Sum.inr (s7e_vl (s7e_hxp hn g h t))) = owner hn (s7e_hPp g t) S' (Sum.inl M) :=
  s7e_owner_vl_eq_vertex hn (s7e_hPp g t) (!s7e_leg g M a) h.1.1 hη (s7e_hw hn g hloc t ht true)
    (s7e_hxp hn g h t) (s7e_huniq_p hn g h t) S' hS'

include hloc ht hη in
/-- **The successor of the contact `a`-visit is transported**: `nextMark (inr w_a) = markMap (nextMark
(inr v_a))` — the first persistent mark after the contact `a`-visit is the same on both sides (same
edge, same side of `r` by sign constancy, same order of persistent visits). -/
theorem s7e_nextMark_wa :
    nextMark hn (s7e_hPp g t) (Sum.inr (s7e_va (s7e_hxp hn g h t))) =
      s7a_markMap (s7e_hs hn g hloc t ht) (nextMark hn (s7e_hPm g t) (Sum.inr (s7e_va (s7e_hxm hn g h t)))) := by
  have hpers := s7e_nextMark_va_persistent hn (s7e_hPm g t) (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t)
    (s7e_huniq_m hn g h t)
  have hva := s7e_va_param_near hn (s7e_hPm g t) (s7e_leg g M a) (s7e_hw hn g hloc t ht false) (s7e_hxm hn g h t)
  have hwa := s7e_va_param_near hn (s7e_hPp g t) (!s7e_leg g M a) (s7e_hw hn g hloc t ht true) (s7e_hxp hn g h t)
  have hva1 := (abs_lt.mp hva).1
  have hva2 := (abs_lt.mp hva).2
  have hwa1 := (abs_lt.mp hwa).1
  have hwa2 := (abs_lt.mp hwa).2
  rcases s7e_nextMark_inr hn (s7e_hPm g t) (s7e_va (s7e_hxm hn g h t)) with hnext | ⟨u, hnext, hue, hup⟩
  · -- the successor is the vertex `a + 1`
    have hnext' : nextMark hn (s7e_hPm g t) (Sum.inr (s7e_va (s7e_hxm hn g h t))) = Sum.inl (a + 1) := hnext
    rw [hnext', s7a_markMap_inl]
    apply s7e_nextMark_inr_eq_inl hn (s7e_hPp g t)
    intro u' hu'e
    by_cases hu'a : u' = s7e_va (s7e_hxp hn g h t)
    · rw [hu'a]
    · have hu'p : ¬ ContactAffected M a u'.1.val :=
        s7e_persistent_of_edge_a (!s7e_leg g M a) h.1.1 (s7e_hxp hn g h t) (s7e_huniq_p hn g h t) u' hu'e hu'a
      obtain ⟨u, hu, rfl⟩ := s7a_visit_surjective (s7e_hs hn g hloc t ht) u' hu'p
      have hue : u.2.val = a := hu'e
      have hlt := s7e_no_later_of_nextMark_inl hn (s7e_hPm g t) (s7e_leg g M a) (s7e_hxm hn g h t) hnext' u hu hue
      have hu3 := s7e_persist_a hn (s7e_hPm g t) (s7e_hw hn g hloc t ht false) u hu hue
      have hur : visitParameter u < r := by
        by_contra hge
        rw [abs_of_nonneg (by linarith)] at hu3
        linarith
      have hur' := (s7e_side_a hn g h hloc t ht hη u hu hue).mp hur
      have hu3' := s7e_persist_a hn (s7e_hPp g t) (s7e_hw hn g hloc t ht true)
        (s7a_visit (s7e_hs hn g hloc t ht) u hu) hu hue
      rw [abs_of_neg (by linarith)] at hu3'
      linarith
  · -- the successor is a later visit `u` on edge `a`
    have hupers : ¬ ContactAffected M a u.1.val := by
      have := hpers; rw [hnext] at this; exact this
    have hue' : u.2.val = a := hue
    rw [hnext, s7a_markMap_inr _ u hupers]
    have hu3 := s7e_persist_a hn (s7e_hPm g t) (s7e_hw hn g hloc t ht false) u hupers hue'
    have hur : r < visitParameter u := by
      by_contra hge
      rw [abs_of_nonpos (by linarith)] at hu3
      linarith
    have hur'le : r ≤ visitParameter (s7a_visit (s7e_hs hn g hloc t ht) u hupers) :=
      not_lt.mp (fun hlt => not_lt.mpr hur.le ((s7e_side_a hn g h hloc t ht hη u hupers hue').mpr hlt))
    have hu3' := s7e_persist_a hn (s7e_hPp g t) (s7e_hw hn g hloc t ht true)
      (s7a_visit (s7e_hs hn g hloc t ht) u hupers) hupers hue'
    have hur' : r < visitParameter (s7a_visit (s7e_hs hn g hloc t ht) u hupers) :=
      lt_of_le_of_ne hur'le (fun heq => by rw [← heq, sub_self, abs_zero] at hu3'; linarith)
    rw [abs_of_pos (by linarith)] at hu3'
    apply s7e_nextMark_inr_eq_inr hn (s7e_hPp g t) (s7e_va (s7e_hxp hn g h t))
      (s7a_visit (s7e_hs hn g hloc t ht) u hupers) hue' (by linarith)
    intro u₂' he₂ hlt₂
    by_cases h₂a : u₂' = s7e_va (s7e_hxp hn g h t)
    · exfalso; rw [h₂a] at hlt₂; exact lt_irrefl _ hlt₂
    · have h₂p : ¬ ContactAffected M a u₂'.1.val :=
        s7e_persistent_of_edge_a (!s7e_leg g M a) h.1.1 (s7e_hxp hn g h t) (s7e_huniq_p hn g h t) u₂' he₂ h₂a
      obtain ⟨u₂, hu₂, rfl⟩ := s7a_visit_surjective (s7e_hs hn g hloc t ht) u₂' h₂p
      have he₂' : u₂.2.val = a := he₂
      have h₂3 := s7e_persist_a hn (s7e_hPp g t) (s7e_hw hn g hloc t ht true)
        (s7a_visit (s7e_hs hn g hloc t ht) u₂ hu₂) hu₂ he₂'
      have h₂r : r < visitParameter (s7a_visit (s7e_hs hn g hloc t ht) u₂ hu₂) := by
        by_contra hge
        rw [abs_of_nonpos (by linarith)] at h₂3
        linarith
      have h₂r'le : r ≤ visitParameter u₂ :=
        not_lt.mp (fun hlt => not_lt.mpr h₂r.le ((s7e_side_a hn g h hloc t ht hη u₂ hu₂ he₂').mp hlt))
      have h₂3m := s7e_persist_a hn (s7e_hPm g t) (s7e_hw hn g hloc t ht false) u₂ hu₂ he₂'
      have h₂r' : r < visitParameter u₂ :=
        lt_of_le_of_ne h₂r'le (fun heq => by rw [← heq, sub_self, abs_zero] at h₂3m; linarith)
      rw [abs_of_pos (by linarith)] at h₂3m
      have hle : visitParameter u ≤ visitParameter u₂ :=
        s7e_min_of_nextMark_inr hn (s7e_hPm g t) (s7e_leg g M a) (s7e_hxm hn g h t) u hnext hue' u₂ he₂'
          (by linarith)
      exact not_lt.mp (fun hlt' => not_lt.mpr hle
        ((s7e_hpar hn g hloc t ht u₂ u hu₂ hupers (he₂'.trans hue'.symm)).mp hlt'))

include hloc ht hη in
/-- **The contact crossing is a self-crossing of `q` iff `x₊` is one of `e q`** (the two contact
visits are owned, through their successors, by the same persistent marks on both sides). -/
theorem s7e_xm_mem_iff (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S)
    (q : Component hn (s7e_hPm g t) S) :
    s7e_xm hn h t ∈ carrierCrossings hn (s7e_hPm g t) S q ↔
      s7e_xp hn h t ∈ carrierCrossings hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S)
        (s7e_e hn g h hloc t ht S hS q) := by
  have hS' := s7e_xp_notMem_E hn g h hloc t ht S hS
  rw [mem_carrierCrossings, mem_carrierCrossings]
  have hm_iff : (∀ v : Visit (g.curve (g.sideTime false t)), v.1 = s7e_xm hn h t →
      owner hn (s7e_hPm g t) S (Sum.inr v) = q) ↔
      (owner hn (s7e_hPm g t) S (Sum.inr (s7e_va (s7e_hxm hn g h t))) = q ∧
        owner hn (s7e_hPm g t) S (Sum.inr (s7e_vl (s7e_hxm hn g h t))) = q) := by
    constructor
    · intro hall
      exact ⟨hall _ (s7e_va_fst_xm hn g h t), hall _ (s7e_vl_fst_xm hn g h t)⟩
    · rintro ⟨h1, h2⟩ v hv
      rcases s7e_visit_of_fst (s7e_hxm hn g h t) v (congrArg Subtype.val hv)
        (s7e_a_ne_leg _ h.1.1) with rfl | rfl
      · exact h1
      · exact h2
  have hp_iff : (∀ v : Visit (g.curve (g.sideTime true t)), v.1 = s7e_xp hn h t →
      owner hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) (Sum.inr v) = s7e_e hn g h hloc t ht S hS q) ↔
      (owner hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) (Sum.inr (s7e_va (s7e_hxp hn g h t))) =
          s7e_e hn g h hloc t ht S hS q ∧
        owner hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) (Sum.inr (s7e_vl (s7e_hxp hn g h t))) =
          s7e_e hn g h hloc t ht S hS q) := by
    constructor
    · intro hall
      exact ⟨hall _ (s7e_va_fst_xp hn g h t), hall _ (s7e_vl_fst_xp hn g h t)⟩
    · rintro ⟨h1, h2⟩ v hv
      rcases s7e_visit_of_fst (s7e_hxp hn g h t) v (congrArg Subtype.val hv)
        (s7e_a_ne_leg _ h.1.1) with rfl | rfl
      · exact h1
      · exact h2
  rw [hm_iff, hp_iff]
  have o1 : owner hn (s7e_hPm g t) S (Sum.inr (s7e_va (s7e_hxm hn g h t))) =
      owner hn (s7e_hPm g t) S (nextMark hn (s7e_hPm g t) (Sum.inr (s7e_va (s7e_hxm hn g h t)))) :=
    s7e_owner_inr_eq_next hn (s7e_hPm g t) S _ (by rw [s7e_va_fst_xm]; exact hS)
  have o2 := s7e_owner_vl_m hn g h hloc t ht hη S hS
  have o1' : owner hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) (Sum.inr (s7e_va (s7e_hxp hn g h t))) =
      owner hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S)
        (nextMark hn (s7e_hPp g t) (Sum.inr (s7e_va (s7e_hxp hn g h t)))) :=
    s7e_owner_inr_eq_next hn (s7e_hPp g t) _ _ (by rw [s7e_va_fst_xp]; exact hS')
  have o2' := s7e_owner_vl_p hn g h hloc t ht hη (s7e_E hn g h hloc t ht S) hS'
  rw [o1, o2, o1', o2', s7e_nextMark_wa hn g h hloc t ht hη]
  have hpers := s7e_nextMark_va_persistent hn (s7e_hPm g t) (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t)
    (s7e_huniq_m hn g h t)
  have e1 := s7e_e_owner hn g h hloc t ht S hS _ hpers
  have e2 := s7e_e_owner hn g h hloc t ht S hS (Sum.inl M) trivial
  rw [s7a_markMap_inl] at e2
  rw [← e1, ← e2, Equiv.apply_eq_iff_eq, Equiv.apply_eq_iff_eq]
  exact and_congr_left (fun _ => iff_of_true hS hS')

include hloc ht hη in
/-- **`hmem` of U110-D for the relocated visit map**: the visits of the carrier crossings of `e q`
are exactly the images of the visits of the carrier crossings of `q`. -/
theorem s7e_hmem (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S)
    (q : Component hn (s7e_hPm g t) S) :
    ∀ w : Visit (g.curve (g.sideTime true t)),
      w.1 ∈ carrierCrossings hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) (s7e_e hn g h hloc t ht S hS q) ↔
        ∃ v : Visit (g.curve (g.sideTime false t)), v.1 ∈ carrierCrossings hn (s7e_hPm g t) S q ∧
          s7e_visitMap hn g h hloc t ht v = w := by
  intro w
  by_cases hw : ContactAffected M a w.1.val
  · have hw1 : w.1 = s7e_xp hn h t := s7e_eq_xp_of_affected hn h t w.1 hw
    rw [hw1, ← s7e_xm_mem_iff hn g h hloc t ht hη S hS q]
    constructor
    · intro hx
      rcases s7e_visit_of_fst (s7e_hxp hn g h t) w (congrArg Subtype.val hw1)
        (s7e_a_ne_leg _ h.1.1) with rfl | rfl
      · exact ⟨s7e_va (s7e_hxm hn g h t), by rw [s7e_va_fst_xm]; exact hx, s7e_visitMap_va hn g h hloc t ht⟩
      · exact ⟨s7e_vl (s7e_hxm hn g h t), by rw [s7e_vl_fst_xm]; exact hx, s7e_visitMap_vl hn g h hloc t ht⟩
    · rintro ⟨v, hv, rfl⟩
      by_cases hva : ContactAffected M a v.1.val
      · rw [s7e_eq_xm_of_affected hn h t v.1 hva] at hv; exact hv
      · exfalso
        rw [s7e_visitMap_of_not hn g h hloc t ht v hva] at hw
        exact hva hw
  · obtain ⟨v, hv, rfl⟩ := s7a_visit_surjective (s7e_hs hn g hloc t ht) w hw
    have hiff := s7a_side_mem_carrierCrossings hn g (s7e_hL hn g hloc t ht) false true S
      (s7e_E hn g h hloc t ht S) (s7e_E_hSS' hn g h hloc t ht S) (s7e_E_hSp hn g h t S hS)
      (s7e_E_hSp' hn g h hloc t ht S hS) v.1 hv q
    constructor
    · intro hx
      exact ⟨v, hiff.mp hx, s7e_visitMap_of_not hn g h hloc t ht v hv⟩
    · rintro ⟨v', hv', hφ⟩
      by_cases hv'a : ContactAffected M a v'.1.val
      · exfalso
        have := s7e_visitMap_affected hn g h hloc t ht v' hv'a
        rw [hφ] at this
        exact hw this
      · rw [s7e_visitMap_of_not hn g h hloc t ht v' hv'a] at hφ
        have := s7a_visit_injective _ v' v hv'a hv hφ
        subst this
        exact hiff.mpr hv'

end S7ESpectator

section S7EKeys

/-! #### The key order of the visits of a side polygon relative to its two contact visits (generic
side polygon `Q` with contact crossing `{a, contactLeg f M}` and the parameter windows). -/

variable (hn : 3 ≤ n) {C Q : LabelledTuple n} (hQ : Generic Q) {M a : ZMod n} {r η : ℝ} (f : Bool)
  (hsep : ContactSeparated M a) (hη : 0 < η) (hw : ContactParameterWindows C Q M a r η)
  (hc : IsCrossing Q {a, contactLeg f M})
  (huniq : ∀ y : Crossing Q, ContactAffected M a y.val → y.val = {a, contactLeg f M})

omit [NeZero n] in
/-- The visit key of `CB.cg` is the mark key. -/
theorem s7e_gkey (v : Visit Q) : geometricVisitKey (CB.cg hn hQ) v = markKey hn hQ.1 (Sum.inr v) := rfl

include hn hQ hη hw in
/-- A persistent `a`-visit is before the contact `a`-visit iff its parameter is below `r`. -/
theorem s7e_param_lt_va_iff (u : Visit Q) (hu : ¬ ContactAffected M a u.1.val) (he : u.2.val = a) :
    visitParameter u < visitParameter (s7e_va hc) ↔ visitParameter u < r := by
  have h1 := s7e_persist_a hn hQ hw u hu he
  have h2 := abs_lt.mp (s7e_va_param_near hn hQ f hw hc)
  constructor
  · intro hlt
    by_contra hge
    rw [abs_of_nonneg (by linarith)] at h1
    linarith
  · intro hlt
    rw [abs_of_neg (by linarith)] at h1
    linarith

include hn hQ hη hw in
/-- A persistent `a`-visit is after the contact `a`-visit iff its parameter is above `r`. -/
theorem s7e_va_lt_param_iff (u : Visit Q) (hu : ¬ ContactAffected M a u.1.val) (he : u.2.val = a) :
    visitParameter (s7e_va hc) < visitParameter u ↔ r < visitParameter u := by
  have h1 := s7e_persist_a hn hQ hw u hu he
  have h2 := abs_lt.mp (s7e_va_param_near hn hQ f hw hc)
  constructor
  · intro hlt
    by_contra hge
    rw [abs_of_nonpos (by linarith)] at h1
    linarith
  · intro hlt
    rw [abs_of_pos (by linarith)] at h1
    linarith

include hn hQ hsep hη hw huniq in
/-- Leg `M − 1`: a visit is before the leg visit iff its edge label is at most `M − 1`. -/
theorem s7e_key_lt_vl_false (hf : f = false) (u : Visit Q) (hu : u ≠ s7e_vl hc) :
    markKey hn hQ.1 (Sum.inr u) < markKey hn hQ.1 (Sum.inr (s7e_vl hc)) ↔ u.2.val.val ≤ (M - 1).val := by
  subst hf
  have hℓ : (s7e_vl hc).2.val = M - 1 := by rw [s7e_vl_edge]; rfl
  rw [s7e_markKey_lt_iff hn hQ]
  simp only [s7e_mEdge_inr, s7e_mParam_inr, hℓ]
  constructor
  · rintro (h1 | ⟨h1, _⟩)
    · exact h1.le
    · rw [h1]
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl hlt
    · right
      have he : u.2.val = M - 1 := ZMod.val_injective n heq
      refine ⟨he, ?_⟩
      have hup := s7e_persistent_of_edge_leg false hsep hc huniq u (by rw [he]; rfl) hu
      have h1 := s7e_persist_M_sub_one hn hQ hw u hup he
      have h2 := s7e_vl_param_false hn hQ hw hc
      linarith

include hn hQ hsep hη hw huniq in
/-- Leg `M − 1`: a visit is after the leg visit iff its edge label exceeds `M − 1`. -/
theorem s7e_vl_lt_key_false (hf : f = false) (u : Visit Q) (hu : u ≠ s7e_vl hc) :
    markKey hn hQ.1 (Sum.inr (s7e_vl hc)) < markKey hn hQ.1 (Sum.inr u) ↔ (M - 1).val < u.2.val.val := by
  subst hf
  have hℓ : (s7e_vl hc).2.val = M - 1 := by rw [s7e_vl_edge]; rfl
  rw [s7e_markKey_lt_iff hn hQ]
  simp only [s7e_mEdge_inr, s7e_mParam_inr, hℓ]
  constructor
  · rintro (h1 | ⟨h1, h2⟩)
    · exact h1
    · exfalso
      have hup := s7e_persistent_of_edge_leg false hsep hc huniq u (by rw [← h1]; rfl) hu
      have h3 := s7e_persist_M_sub_one hn hQ hw u hup h1.symm
      have h4 := s7e_vl_param_false hn hQ hw hc
      linarith
  · intro hlt
    exact Or.inl hlt

include hn hQ hsep hη hw huniq in
/-- Leg `M`: a visit is before the leg visit iff its edge label is below `M`. -/
theorem s7e_key_lt_vl_true (hf : f = true) (u : Visit Q) (hu : u ≠ s7e_vl hc) :
    markKey hn hQ.1 (Sum.inr u) < markKey hn hQ.1 (Sum.inr (s7e_vl hc)) ↔ u.2.val.val < M.val := by
  subst hf
  have hℓ : (s7e_vl hc).2.val = M := by rw [s7e_vl_edge]; rfl
  rw [s7e_markKey_lt_iff hn hQ]
  simp only [s7e_mEdge_inr, s7e_mParam_inr, hℓ]
  constructor
  · rintro (h1 | ⟨h1, h2⟩)
    · exact h1
    · exfalso
      have hup := s7e_persistent_of_edge_leg true hsep hc huniq u (by rw [h1]; rfl) hu
      have h3 := s7e_persist_M hn hQ hw u hup h1
      have h4 := s7e_vl_param_true hn hQ hw hc
      linarith
  · intro hlt
    exact Or.inl hlt

include hn hQ hsep hη hw huniq in
/-- Leg `M`: a visit is after the leg visit iff its edge label is at least `M`. -/
theorem s7e_vl_lt_key_true (hf : f = true) (u : Visit Q) (hu : u ≠ s7e_vl hc) :
    markKey hn hQ.1 (Sum.inr (s7e_vl hc)) < markKey hn hQ.1 (Sum.inr u) ↔ M.val ≤ u.2.val.val := by
  subst hf
  have hℓ : (s7e_vl hc).2.val = M := by rw [s7e_vl_edge]; rfl
  rw [s7e_markKey_lt_iff hn hQ]
  simp only [s7e_mEdge_inr, s7e_mParam_inr, hℓ]
  constructor
  · rintro (h1 | ⟨h1, _⟩)
    · exact h1.le
    · rw [h1]
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl hlt
    · right
      have he : u.2.val = M := ZMod.val_injective n heq.symm
      refine ⟨he.symm, ?_⟩
      have hup := s7e_persistent_of_edge_leg true hsep hc huniq u (by rw [he]; rfl) hu
      have h1 := s7e_persist_M hn hQ hw u hup he
      have h2 := s7e_vl_param_true hn hQ hw hc
      linarith

include hn hQ hw in
/-- Leg `M = 0`: the leg visit has key below `η`. -/
theorem s7e_key_vl_lt_eta (hf : f = true) (hM : M = 0) :
    markKey hn hQ.1 (Sum.inr (s7e_vl hc)) < η := by
  subst hf
  have hℓ : (s7e_vl hc).2.val = M := by rw [s7e_vl_edge]; rfl
  rw [s7e_markKey_eq hn hQ]
  have h0 : (s7e_mEdge (Sum.inr (s7e_vl hc))).val = 0 := by
    rw [s7e_mEdge_inr, hℓ, hM, ZMod.val_zero]
  rw [h0, Nat.cast_zero, zero_add, s7e_mParam_inr]
  exact s7e_vl_param_true hn hQ hw hc

include hn hQ hsep hη hw huniq in
/-- Leg `M = 0`: every other visit has key at least `η`. -/
theorem s7e_eta_le_key (hf : f = true) (hM : M = 0) (hηr : 4 * η < r) (hr1 : r < 1) (u : Visit Q)
    (hu : u ≠ s7e_vl hc) : η ≤ markKey hn hQ.1 (Sum.inr u) := by
  subst hf
  rw [s7e_markKey_eq hn hQ]
  simp only [s7e_mEdge_inr, s7e_mParam_inr]
  have hp0 := s7e_visitParameter_pos hn hQ u
  by_cases he : u.2.val = M
  · have hup := s7e_persistent_of_edge_leg true hsep hc huniq u (by rw [he]; rfl) hu
    have h1 := s7e_persist_M hn hQ hw u hup he
    have h2 : (0 : ℝ) ≤ u.2.val.val := Nat.cast_nonneg _
    linarith
  · have hne : u.2.val.val ≠ 0 := by
      intro h0
      exact he ((ZMod.val_eq_zero _).mp h0 ▸ hM.symm)
    have h1 : (1 : ℝ) ≤ u.2.val.val := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    linarith

end S7EKeys

section S7ESpectatorKeys

/-! #### The relocated visit map is key-monotone up to the leg visit; the coefficient, selector and
term equalities of the spectator sector; the sector itself. -/

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} {r η δ : ℝ}
  (h : g.SlidingAt M a) (hloc : s7a2_IntervalLocal hn g M a r η δ) (t : g.SideParameter)
  (ht : t.val < δ) (hη : 0 < η)

include h hloc ht hη in
theorem s7e_side_a_gt (u : Visit (g.curve (g.sideTime false t))) (hu : ¬ ContactAffected M a u.1.val)
    (he : u.2.val = a) :
    r < visitParameter u ↔ r < visitParameter (s7a_visit (s7e_hs hn g hloc t ht) u hu) := by
  have h1 := s7e_persist_a hn (s7e_hPm g t) (s7e_hw hn g hloc t ht false) u hu he
  have h2 := s7e_persist_a hn (s7e_hPp g t) (s7e_hw hn g hloc t ht true)
    (s7a_visit (s7e_hs hn g hloc t ht) u hu) hu he
  have hiff := s7e_side_a hn g h hloc t ht hη u hu he
  constructor
  · intro hlt
    have hle : r ≤ visitParameter (s7a_visit (s7e_hs hn g hloc t ht) u hu) :=
      not_lt.mp (fun hlt' => not_lt.mpr hlt.le (hiff.mpr hlt'))
    exact lt_of_le_of_ne hle (fun heq => by rw [← heq, sub_self, abs_zero] at h2; linarith)
  · intro hlt
    have hle : r ≤ visitParameter u := not_lt.mp (fun hlt' => not_lt.mpr hlt.le (hiff.mp hlt'))
    exact lt_of_le_of_ne hle (fun heq => by rw [← heq, sub_self, abs_zero] at h1; linarith)

theorem s7e_visitMap_edge (v : Visit (g.curve (g.sideTime false t))) (hv : v ≠ s7e_vl (s7e_hxm hn g h t)) :
    (s7e_visitMap hn g h hloc t ht v).2.val = v.2.val := by
  rcases s7e_visit_cases (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) v with
    rfl | rfl | hp
  · rw [s7e_visitMap_va, s7e_va_edge, s7e_va_edge]
  · exact absurd rfl hv
  · rw [s7e_visitMap_of_not hn g h hloc t ht v hp]; rfl

theorem s7e_visitMap_ne_wl (v : Visit (g.curve (g.sideTime false t))) (hv : v ≠ s7e_vl (s7e_hxm hn g h t)) :
    s7e_visitMap hn g h hloc t ht v ≠ s7e_vl (s7e_hxp hn g h t) := by
  rcases s7e_visit_cases (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) v with
    rfl | rfl | hp
  · rw [s7e_visitMap_va]
    exact (s7e_vl_ne_va _ (s7e_a_ne_leg _ h.1.1)).symm
  · exact absurd rfl hv
  · rw [s7e_visitMap_of_not hn g h hloc t ht v hp]
    intro heq
    have : ContactAffected M a (s7a_visit (s7e_hs hn g hloc t ht) v hp).1.val := by
      rw [heq, s7e_vl_fst_xp]; exact s7e_xp_affected hn h t
    exact hp this

include hη in
/-- Key monotonicity of the relocated visit map on the visits other than the leg visit. -/
theorem s7e_key_nonleg (v w : Visit (g.curve (g.sideTime false t))) (hv : v ≠ s7e_vl (s7e_hxm hn g h t))
    (hw : w ≠ s7e_vl (s7e_hxm hn g h t))
    (hlt : geometricVisitKey (CB.cg hn (s7e_hPm g t)) v < geometricVisitKey (CB.cg hn (s7e_hPm g t)) w) :
    geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_visitMap hn g h hloc t ht v) <
      geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_visitMap hn g h hloc t ht w) := by
  rw [s7e_gkey hn (s7e_hPm g t), s7e_gkey hn (s7e_hPm g t), s7e_markKey_lt_iff hn (s7e_hPm g t)] at hlt
  rw [s7e_gkey hn (s7e_hPp g t), s7e_gkey hn (s7e_hPp g t), s7e_markKey_lt_iff hn (s7e_hPp g t)]
  simp only [s7e_mEdge_inr, s7e_mParam_inr] at hlt ⊢
  rw [s7e_visitMap_edge hn g h hloc t ht v hv, s7e_visitMap_edge hn g h hloc t ht w hw]
  rcases hlt with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · right
    refine ⟨h1, ?_⟩
    have hwm := s7e_hw hn g hloc t ht false
    have hwp := s7e_hw hn g hloc t ht true
    rcases s7e_visit_cases (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) v with
      rfl | rfl | hvp
    · rcases s7e_visit_cases (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) w with
        rfl | rfl | hwp'
      · exact absurd h2 (lt_irrefl _)
      · exact absurd rfl hw
      · rw [s7e_visitMap_va, s7e_visitMap_of_not hn g h hloc t ht w hwp']
        have hwe : w.2.val = a := h1.symm
        have h3 := (s7e_va_lt_param_iff hn (s7e_hPm g t) (s7e_leg g M a) hη hwm (s7e_hxm hn g h t)
          w hwp' hwe).mp h2
        have h4 := (s7e_side_a_gt hn g h hloc t ht hη w hwp' hwe).mp h3
        exact (s7e_va_lt_param_iff hn (s7e_hPp g t) (!s7e_leg g M a) hη hwp (s7e_hxp hn g h t)
          (s7a_visit (s7e_hs hn g hloc t ht) w hwp') hwp' hwe).mpr h4
    · exact absurd rfl hv
    · rcases s7e_visit_cases (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) w with
        rfl | rfl | hwp'
      · rw [s7e_visitMap_of_not hn g h hloc t ht v hvp, s7e_visitMap_va]
        have hve : v.2.val = a := h1
        have h3 := (s7e_param_lt_va_iff hn (s7e_hPm g t) (s7e_leg g M a) hη hwm (s7e_hxm hn g h t)
          v hvp hve).mp h2
        have h4 := (s7e_side_a hn g h hloc t ht hη v hvp hve).mp h3
        exact (s7e_param_lt_va_iff hn (s7e_hPp g t) (!s7e_leg g M a) hη hwp (s7e_hxp hn g h t)
          (s7a_visit (s7e_hs hn g hloc t ht) v hvp) hvp hve).mpr h4
      · exact absurd rfl hw
      · rw [s7e_visitMap_of_not hn g h hloc t ht v hvp, s7e_visitMap_of_not hn g h hloc t ht w hwp']
        exact (s7e_hpar hn g hloc t ht v w hvp hwp' h1).mpr h2

include hη in
/-- `M ≠ 0`: the leg visit is relocated without wrapping the key order. -/
theorem s7e_key_leg_ne (hM : M ≠ 0) (v : Visit (g.curve (g.sideTime false t)))
    (hv : v ≠ s7e_vl (s7e_hxm hn g h t)) :
    (geometricVisitKey (CB.cg hn (s7e_hPm g t)) v <
        geometricVisitKey (CB.cg hn (s7e_hPm g t)) (s7e_vl (s7e_hxm hn g h t)) →
      geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_visitMap hn g h hloc t ht v) <
        geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_vl (s7e_hxp hn g h t))) ∧
    (geometricVisitKey (CB.cg hn (s7e_hPm g t)) (s7e_vl (s7e_hxm hn g h t)) <
        geometricVisitKey (CB.cg hn (s7e_hPm g t)) v →
      geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_vl (s7e_hxp hn g h t)) <
        geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_visitMap hn g h hloc t ht v)) := by
  have hM1 : (M - 1).val + 1 = M.val := by
    have hne : M - 1 ≠ -1 := fun h' => hM (by linear_combination h')
    have := zmod_val_next_of_ne_last hne
    rw [sub_add_cancel] at this
    exact this.symm
  have hφe := s7e_visitMap_edge hn g h hloc t ht v hv
  have hφne := s7e_visitMap_ne_wl hn g h hloc t ht v hv
  have hwm := s7e_hw hn g hloc t ht false
  have hwp := s7e_hw hn g hloc t ht true
  have hsep := h.1.1
  rcases Bool.eq_false_or_eq_true (s7e_leg g M a) with hf | hf
  · have hf' : (!s7e_leg g M a) = false := by rw [hf]; rfl
    constructor
    · intro hlt
      rw [s7e_gkey hn (s7e_hPm g t), s7e_gkey hn (s7e_hPm g t), s7e_key_lt_vl_true hn (s7e_hPm g t) _ hsep hη hwm (s7e_hxm hn g h t)
        (s7e_huniq_m hn g h t) hf v hv] at hlt
      rw [s7e_gkey hn (s7e_hPp g t), s7e_gkey hn (s7e_hPp g t), s7e_key_lt_vl_false hn (s7e_hPp g t) _ hsep hη hwp (s7e_hxp hn g h t)
        (s7e_huniq_p hn g h t) hf' _ hφne, hφe]
      omega
    · intro hlt
      rw [s7e_gkey hn (s7e_hPm g t), s7e_gkey hn (s7e_hPm g t), s7e_vl_lt_key_true hn (s7e_hPm g t) _ hsep hη hwm (s7e_hxm hn g h t)
        (s7e_huniq_m hn g h t) hf v hv] at hlt
      rw [s7e_gkey hn (s7e_hPp g t), s7e_gkey hn (s7e_hPp g t), s7e_vl_lt_key_false hn (s7e_hPp g t) _ hsep hη hwp (s7e_hxp hn g h t)
        (s7e_huniq_p hn g h t) hf' _ hφne, hφe]
      omega
  · have hf' : (!s7e_leg g M a) = true := by rw [hf]; rfl
    constructor
    · intro hlt
      rw [s7e_gkey hn (s7e_hPm g t), s7e_gkey hn (s7e_hPm g t), s7e_key_lt_vl_false hn (s7e_hPm g t) _ hsep hη hwm (s7e_hxm hn g h t)
        (s7e_huniq_m hn g h t) hf v hv] at hlt
      rw [s7e_gkey hn (s7e_hPp g t), s7e_gkey hn (s7e_hPp g t), s7e_key_lt_vl_true hn (s7e_hPp g t) _ hsep hη hwp (s7e_hxp hn g h t)
        (s7e_huniq_p hn g h t) hf' _ hφne, hφe]
      omega
    · intro hlt
      rw [s7e_gkey hn (s7e_hPm g t), s7e_gkey hn (s7e_hPm g t), s7e_vl_lt_key_false hn (s7e_hPm g t) _ hsep hη hwm (s7e_hxm hn g h t)
        (s7e_huniq_m hn g h t) hf v hv] at hlt
      rw [s7e_gkey hn (s7e_hPp g t), s7e_gkey hn (s7e_hPp g t), s7e_vl_lt_key_true hn (s7e_hPp g t) _ hsep hη hwp (s7e_hxp hn g h t)
        (s7e_huniq_p hn g h t) hf' _ hφne, hφe]
      omega

include hη in
/-- `M = 0`, leg `M − 1 = −1` on `P₋`: the leg visit is the LAST visit and its image the FIRST. -/
theorem s7e_key_leg_zero_false (hM : M = 0) (hf : s7e_leg g M a = false)
    (v : Visit (g.curve (g.sideTime false t))) (hv : v ≠ s7e_vl (s7e_hxm hn g h t)) :
    geometricVisitKey (CB.cg hn (s7e_hPm g t)) v <
        geometricVisitKey (CB.cg hn (s7e_hPm g t)) (s7e_vl (s7e_hxm hn g h t)) ∧
      geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_vl (s7e_hxp hn g h t)) <
        geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_visitMap hn g h hloc t ht v) := by
  have hM1 : (M - 1).val = n - 1 := by
    rw [hM, zero_sub]
    have := last_index_val_succ (n := n)
    omega
  have hφe := s7e_visitMap_edge hn g h hloc t ht v hv
  have hφne := s7e_visitMap_ne_wl hn g h hloc t ht v hv
  have hf' : (!s7e_leg g M a) = true := by rw [hf]; rfl
  constructor
  · rw [s7e_gkey hn (s7e_hPm g t), s7e_gkey hn (s7e_hPm g t), s7e_key_lt_vl_false hn (s7e_hPm g t) _ h.1.1 hη (s7e_hw hn g hloc t ht false)
      (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) hf v hv, hM1]
    have := ZMod.val_lt v.2.val
    omega
  · have hM0 : M.val = 0 := by rw [hM, ZMod.val_zero]
    rw [s7e_gkey hn (s7e_hPp g t), s7e_gkey hn (s7e_hPp g t), s7e_vl_lt_key_true hn (s7e_hPp g t) _ h.1.1 hη (s7e_hw hn g hloc t ht true)
      (s7e_hxp hn g h t) (s7e_huniq_p hn g h t) hf' _ hφne, hM0]
    exact Nat.zero_le _

include hloc ht in
/-- `M = 0`, leg `M = 0` on `P₋`: the leg visit has key below `η`. -/
theorem s7e_key_vl_lt_eta_wall (hM : M = 0) (hf : s7e_leg g M a = true) :
    geometricVisitKey (CB.cg hn (s7e_hPm g t)) (s7e_vl (s7e_hxm hn g h t)) < η :=
  s7e_key_vl_lt_eta hn (s7e_hPm g t) _ (s7e_hw hn g hloc t ht false) (s7e_hxm hn g h t) hf hM

include hη in
/-- `M = 0`, leg `M = 0` on `P₋`: every other visit has key at least `η`, and its image precedes the
relocated leg visit (which is the LAST visit of `P₊`). -/
theorem s7e_key_leg_zero_true (hM : M = 0) (hf : s7e_leg g M a = true) (hηr : 4 * η < r) (hr1 : r < 1)
    (v : Visit (g.curve (g.sideTime false t))) (hv : v ≠ s7e_vl (s7e_hxm hn g h t)) :
    η ≤ geometricVisitKey (CB.cg hn (s7e_hPm g t)) v ∧
      geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_visitMap hn g h hloc t ht v) <
        geometricVisitKey (CB.cg hn (s7e_hPp g t)) (s7e_vl (s7e_hxp hn g h t)) := by
  have hM1 : (M - 1).val = n - 1 := by
    rw [hM, zero_sub]
    have := last_index_val_succ (n := n)
    omega
  have hφe := s7e_visitMap_edge hn g h hloc t ht v hv
  have hφne := s7e_visitMap_ne_wl hn g h hloc t ht v hv
  have hf' : (!s7e_leg g M a) = false := by rw [hf]; rfl
  refine ⟨s7e_eta_le_key hn (s7e_hPm g t) _ h.1.1 hη (s7e_hw hn g hloc t ht false) (s7e_hxm hn g h t)
    (s7e_huniq_m hn g h t) hf hM hηr hr1 v hv, ?_⟩
  rw [s7e_gkey hn (s7e_hPp g t), s7e_gkey hn (s7e_hPp g t), s7e_key_lt_vl_false hn (s7e_hPp g t) _ h.1.1 hη (s7e_hw hn g hloc t ht true)
    (s7e_hxp hn g h t) (s7e_huniq_p hn g h t) hf' _ hφne, hφe, hM1]
  have := ZMod.val_lt v.2.val
  omega

include hη in
/-- **The Gauss lists of corresponding spectator carriers are rotations of each other** along the
relocated visit map (U110-D's cut form: no wrap for `M ≠ 0`; the leg visit wraps for `M = 0`). -/
theorem s7e_isRotated (hηr : 4 * η < r) (hr1 : r < 1)
    (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S)
    (q : Component hn (s7e_hPm g t) S) :
    (CB.gaussList (CB.cg hn (s7e_hPp g t))
        (carrierCrossings hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) (s7e_e hn g h hloc t ht S hS q))).IsRotated
      ((CB.gaussList (CB.cg hn (s7e_hPm g t)) (carrierCrossings hn (s7e_hPm g t) S q)).map
        (s7e_visitMap hn g h hloc t ht)) := by
  have hmem := s7e_hmem hn g h hloc t ht hη S hS q
  by_cases hM : M = 0
  · rcases Bool.eq_false_or_eq_true (s7e_leg g M a) with hf | hf
    · exact s7e_isRotated_of_bottom_to_top _ _ _ _ _ (s7e_vl (s7e_hxm hn g h t)) η
        (s7e_key_vl_lt_eta_wall hn g h hloc t ht hM hf)
        (fun v _ hv => (s7e_key_leg_zero_true hn g h hloc t ht hη hM hf hηr hr1 v hv).1) hmem
        (fun v w _ _ hv hw => s7e_key_nonleg hn g h hloc t ht hη v w hv hw)
        (fun v _ hv => by
          rw [s7e_visitMap_vl hn g h hloc t ht]
          exact (s7e_key_leg_zero_true hn g h hloc t ht hη hM hf hηr hr1 v hv).2)
    · exact s7e_isRotated_of_top_to_bottom _ _ _ _ _ (s7e_vl (s7e_hxm hn g h t)) hmem
        (fun v w _ _ hv hw => s7e_key_nonleg hn g h hloc t ht hη v w hv hw)
        (fun v _ hv => (s7e_key_leg_zero_false hn g h hloc t ht hη hM hf v hv).1)
        (fun v _ hv => by
          rw [s7e_visitMap_vl hn g h hloc t ht]
          exact (s7e_key_leg_zero_false hn g h hloc t ht hη hM hf v hv).2)
  · apply s7e_isRotated_of_strictMono _ _ _ _ _ hmem
    intro v w _ _ hvw
    by_cases hv : v = s7e_vl (s7e_hxm hn g h t)
    · subst hv
      by_cases hw : w = s7e_vl (s7e_hxm hn g h t)
      · subst hw; exact absurd hvw (lt_irrefl _)
      · rw [s7e_visitMap_vl hn g h hloc t ht]
        exact (s7e_key_leg_ne hn g h hloc t ht hη hM w hw).2 hvw
    · by_cases hw : w = s7e_vl (s7e_hxm hn g h t)
      · subst hw
        rw [s7e_visitMap_vl hn g h hloc t ht]
        exact (s7e_key_leg_ne hn g h hloc t ht hη hM v hv).1 hvw
      · exact s7e_key_nonleg hn g h hloc t ht hη v w hv hw hvw

/-- The relocated visit map commutes with the twin. -/
theorem s7e_htwin (v : Visit (g.curve (g.sideTime false t))) :
    s7e_visitMap hn g h hloc t ht (visitTwin v) = visitTwin (s7e_visitMap hn g h hloc t ht v) := by
  have ha := s7e_a_ne_leg (s7e_leg g M a) h.1.1
  have ha' := s7e_a_ne_leg (!s7e_leg g M a) h.1.1
  rcases s7e_visit_cases (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) v with
    rfl | rfl | hp
  · rw [s7e_twin_va _ ha, s7e_visitMap_vl, s7e_visitMap_va, s7e_twin_va _ ha']
  · rw [s7e_twin_vl _ ha, s7e_visitMap_va, s7e_visitMap_vl, s7e_twin_vl _ ha']
  · rw [s7e_visitMap_of_not hn g h hloc t ht v hp, s7e_visitMap_of_not hn g h hloc t ht (visitTwin v) hp,
      s7a_visit_twin]

include h hloc ht in
/-- The crossing signs of the two contact crossings agree (`s7a_sliding_relocation_sign`), read with
the legs of the two sides. -/
theorem s7e_sgn_contact
    (htests : ∀ u : g.Parameter, |u.val| < δ → u.val ≠ 0 → ∀ forward : Bool,
      IsCrossing (g.curve u) {a, contactLeg forward M} ↔
        chi (g.curve u) a (a + 1) M * chi g.center a (a + 1) (contactNeighbour forward M) = -1) :
    crossingSign (g.curve (g.sideTime true t)) a (contactLeg (!s7e_leg g M a) M) =
      crossingSign (g.curve (g.sideTime false t)) a (contactLeg (s7e_leg g M a) M) := by
  have hL := s7e_hL hn g hloc t ht
  have htest : ∀ b : Bool, ∀ forward : Bool,
      IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg forward M} ↔
        chi (g.curve (g.sideTime b t)) a (a + 1) M *
          chi g.center a (a + 1) (contactNeighbour forward M) = -1 :=
    fun b => htests (g.sideTime b t) (by rw [g.sideTime_val_abs]; exact ht) (g.sideTime_ne_zero b t)
  have hxm := s7e_hxm hn g h t
  have hxp := s7e_hxp hn g h t
  rcases Bool.eq_false_or_eq_true (s7e_leg g M a) with hf | hf
  · rw [hf] at hxm hxp ⊢
    simp only [Bool.not_true, contactLeg, ↓reduceIte, Bool.false_eq_true] at hxm hxp ⊢
    exact (s7a_sliding_relocation_sign hn g h hL true false hxp hxm (htest true)).symm
  · rw [hf] at hxm hxp ⊢
    simp only [Bool.not_false, contactLeg, ↓reduceIte, Bool.false_eq_true] at hxm hxp ⊢
    exact s7a_sliding_relocation_sign hn g h hL false true hxm hxp (htest false)

/-- **`hbit` of U110-D**: the positive over bit is preserved by the relocated visit map (persistent
visits: `s7a_side_sgn`; contact visits: the relocation sign). -/
theorem s7e_hbit
    (htests : ∀ u : g.Parameter, |u.val| < δ → u.val ≠ 0 → ∀ forward : Bool,
      IsCrossing (g.curve u) {a, contactLeg forward M} ↔
        chi (g.curve u) a (a + 1) M * chi g.center a (a + 1) (contactNeighbour forward M) = -1)
    (v : Visit (g.curve (g.sideTime false t))) :
    CB.positiveOverBit (s7e_visitMap hn g h hloc t ht v) = CB.positiveOverBit v := by
  have hsg := s7e_sgn_contact hn g h hloc t ht htests
  have ha := s7e_a_ne_leg (s7e_leg g M a) h.1.1
  have ha' := s7e_a_ne_leg (!s7e_leg g M a) h.1.1
  rcases s7e_visit_cases (s7e_leg g M a) h.1.1 (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) v with
    rfl | rfl | hp
  · rw [s7e_visitMap_va]
    apply s7d_positiveOverBit_eq_of_crossingSign
    rw [s7e_twin_va _ ha, s7e_twin_va _ ha', s7e_va_edge, s7e_va_edge, s7e_vl_edge, s7e_vl_edge]
    exact hsg
  · rw [s7e_visitMap_vl]
    apply s7d_positiveOverBit_eq_of_crossingSign
    rw [s7e_twin_vl _ ha, s7e_twin_vl _ ha', s7e_vl_edge, s7e_vl_edge, s7e_va_edge, s7e_va_edge,
      crossingSign_swap (g.curve (g.sideTime true t)) a, crossingSign_swap (g.curve (g.sideTime false t)) a,
      hsg]
  · rw [s7e_visitMap_of_not hn g h hloc t ht v hp]
    exact s7d_positiveOverBit_eq_of_crossingSign v _
      (s7a_side_sgn hn g h.1 (s7e_hL hn g hloc t ht) false true v hp)

include hloc ht in
theorem s7e_isDecomposition_E (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S) :
    IsDecomposition hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) ↔ IsDecomposition hn (s7e_hPm g t) S :=
  s7a_side_isDecomposition_iff hn g (s7e_hL hn g hloc t ht) false true S (s7e_E hn g h hloc t ht S)
    (s7e_E_hSS' hn g h hloc t ht S) (s7e_E_hSp hn g h t S hS) (s7e_E_hSp' hn g h hloc t ht S hS)

include hη in
/-- **The coefficient equality of the spectator sector** (eq. s7c:sliding-coefficients for the
supports avoiding `x₋`): U110-D's record route with the rotated Gauss lists, twin and over-bit
compatibility, and U110-A2's rotation equality. -/
theorem s7e_coef_eq (hηr : 4 * η < r) (hr1 : r < 1)
    (htests : ∀ u : g.Parameter, |u.val| < δ → u.val ≠ 0 → ∀ forward : Bool,
      IsCrossing (g.curve u) {a, contactLeg forward M} ↔
        chi (g.curve u) a (a + 1) M * chi g.center a (a + 1) (contactNeighbour forward M) = -1)
    (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S)
    (hdec : IsDecomposition hn (s7e_hPm g t) S) (q : Component hn (s7e_hPm g t) S) :
    cornerCoefficient hn (s7e_hPm g t) S q hdec =
      cornerCoefficient hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) (s7e_e hn g h hloc t ht S hS q)
        ((s7e_isDecomposition_E hn g h hloc t ht S hS).mpr hdec) :=
  s7d_cornerCoefficient_eq_of_gaussList_rotated hn hn (s7e_hPm g t) (s7e_hPp g t) hdec q
    ((s7e_isDecomposition_E hn g h hloc t ht S hS).mpr hdec) (s7e_e hn g h hloc t ht S hS q)
    (s7e_visitMap hn g h hloc t ht) (s7e_isRotated hn g h hloc t ht hη hηr hr1 S hS q)
    (fun v _ => s7e_htwin hn g h hloc t ht v) (fun v _ => s7e_hbit hn g h hloc t ht htests v)
    (s7a2_carrierRotation_eq hn g h.1 hloc ht (s7e_hL hn g hloc t ht) false true S
      (s7e_E hn g h hloc t ht S) (s7e_E_hSS' hn g h hloc t ht S) (s7e_E_hSp hn g h t S hS)
      (s7e_E_hSp' hn g h hloc t ht S hS) hdec q)

include hloc ht in
/-- The selector weights agree (corner turns correspond index by index, U110-A). -/
theorem s7e_wind_eq (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S)
    (hdec : IsDecomposition hn (s7e_hPm g t) S) :
    wind hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) = wind hn (s7e_hPm g t) S := by
  have hdec' := (s7e_isDecomposition_E hn g h hloc t ht S hS).mpr hdec
  unfold wind
  symm
  apply Fintype.prod_equiv (s7e_e hn g h hloc t ht S hS)
  intro q
  rw [s7c_carrierWeight_eq_sel, s7c_carrierWeight_eq_sel]
  congr 1
  exact s7c_map_univ_eq_of_equiv _ _ (Equiv.cast (congrArg ZMod (s7a_ccpCornerCount_eq hn (s7e_hPm g t)
    (s7e_hPp g t) (s7e_hs hn g hloc t ht) (s7e_hpar hn g hloc t ht) S (s7e_E hn g h hloc t ht S)
    (s7e_E_hSS' hn g h hloc t ht S) (s7e_E_hSp hn g h t S hS) (s7e_E_hSp' hn g h hloc t ht S hS) q).symm))
    (fun j => s7a_turn_ccpCornerPolygon hn (s7e_hPm g t) (s7e_hPp g t) (s7e_hs hn g hloc t ht)
      (s7e_hpar hn g hloc t ht) S (s7e_E hn g h hloc t ht S) (s7e_E_hSS' hn g h hloc t ht S)
      (s7e_E_hSp hn g h t S hS) (s7e_E_hSp' hn g h hloc t ht S hS) hdec hdec'
      (s7a_side_turn hn g h.1 (s7e_hL hn g hloc t ht) false true)
      (s7a_side_sgn hn g h.1 (s7e_hL hn g hloc t ht) false true) q j)

include hη in
/-- **The spectator term equality**: for every support `S` of `P₋` avoiding `x₋`, the selector-form
term of `E S` on `P₊` equals the term of `S` on `P₋`. -/
theorem s7e_term_eq (hηr : 4 * η < r) (hr1 : r < 1)
    (htests : ∀ u : g.Parameter, |u.val| < δ → u.val ≠ 0 → ∀ forward : Bool,
      IsCrossing (g.curve u) {a, contactLeg forward M} ↔
        chi (g.curve u) a (a + 1) M * chi g.center a (a + 1) (contactNeighbour forward M) = -1)
    (S : Finset (Crossing (g.curve (g.sideTime false t)))) (hS : s7e_xm hn h t ∉ S) :
    s7e_term hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) = s7e_term hn (s7e_hPm g t) S := by
  by_cases hdec : IsDecomposition hn (s7e_hPm g t) S
  · have hdec' := (s7e_isDecomposition_E hn g h hloc t ht S hS).mpr hdec
    rw [s7e_term_of_decomposition _ _ hdec', s7e_term_of_decomposition _ _ hdec,
      s7e_wind_eq hn g h hloc t ht S hS hdec]
    congr 1
    exact (s7d_cornerProduct_eq_of_equiv hn hn (s7e_hPm g t) (s7e_hPp g t) hdec hdec'
      (s7e_e hn g h hloc t ht S hS) (fun q => s7e_coef_eq hn g h hloc t ht hη hηr hr1 htests S hS hdec q)).symm
  · have hdec' : ¬ IsDecomposition hn (s7e_hPp g t) (s7e_E hn g h hloc t ht S) :=
      fun h' => hdec ((s7e_isDecomposition_E hn g h hloc t ht S hS).mp h')
    rw [s7e_term_of_not _ _ hdec', s7e_term_of_not _ _ hdec]

include hloc ht hη in
/-- **The spectator sector at `t`.** -/
theorem s7e_spectatorSector_of (hηr : 4 * η < r) (hr1 : r < 1)
    (htests : ∀ u : g.Parameter, |u.val| < δ → u.val ≠ 0 → ∀ forward : Bool,
      IsCrossing (g.curve u) {a, contactLeg forward M} ↔
        chi (g.curve u) a (a + 1) M * chi g.center a (a + 1) (contactNeighbour forward M) = -1) :
    s7e_SpectatorSector hn h t :=
  ⟨s7e_spectatorEquiv (s7e_hs hn g hloc t ht) (s7e_xm hn h t) (s7e_xp hn h t) (s7e_hm hn g h t)
    (s7e_hp hn g h t) (s7e_xm_affected hn h t) (s7e_xp_affected hn h t),
    fun S => s7e_term_eq hn g h hloc t ht hη hηr hr1 htests S.1 S.2⟩

end S7ESpectatorKeys

section S7EAssembly

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n}

/-- **The spectator sector below a radius** (PLAN §3.3 sliding (1), PROVED): lem:wall-sides (V)
supplies the interval-local data (`s7a2_exists_intervalLocal`), the contact tests supply the
relocation sign (`vertexEdge_contact_tests`). -/
theorem s7e_exists_spectatorSector (h : g.SlidingAt M a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → s7e_SpectatorSector hn h t := by
  obtain ⟨r, η, _, hr1, _, hη, hηr, _, δ₁, hδ₁, _, hloc⟩ := s7a2_exists_intervalLocal hn g M a h.1
  obtain ⟨δ₂, hδ₂, _, htests⟩ := g.vertexEdge_contact_tests hn h.1
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht => ?_⟩
  have hloc' : s7a2_IntervalLocal hn g M a r η (min δ₁ δ₂) :=
    fun u hu => hloc u (lt_of_lt_of_le hu (min_le_left _ _))
  have htests' : ∀ u : g.Parameter, |u.val| < min δ₁ δ₂ → u.val ≠ 0 → ∀ forward : Bool,
      IsCrossing (g.curve u) {a, contactLeg forward M} ↔
        chi (g.curve u) a (a + 1) M * chi g.center a (a + 1) (contactNeighbour forward M) = -1 :=
    fun u hu hu0 => htests u (lt_of_lt_of_le hu (min_le_right _ _)) hu0
  exact s7e_spectatorSector_of hn g h hloc' t ht hη hηr hr1 htests'

/-- **The sliding law from the contact sector alone**: the spectator sector is proved, so the leaf
`s7_sliding_law_at` reduces to the contact sector below some radius (PLAN §3.3 sliding (2)-(3):
`s7b_slidingDecompositionEquiv` on both sides — which needs the interlacement transfer
`s7b_PivotSplit` — and the termwise identity, which needs `s7b_SlidingTransport.ret`, the corner
correspondence of the relocated carriers for `s7c_carrierWeight_refine`, and their rotation equality by
principal-angle addition; see W2_S7E_REPORT.md). -/
theorem s7e_sliding_law_at_of_contact (h : g.SlidingAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a))
    (hct : ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → s7e_ContactSector hn h h₁ h₂ t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) :=
  s7e_sliding_law_at_of_sectors hn h h₁ h₂ (s7e_exists_spectatorSector hn g h) hct

end S7EAssembly

section S7EContactRepack

/-! #### The contact sector, repackaged on U110-B's support bijections: given the two interlacement
transfers (`s7b_PivotSplit` on `P₋` at `x₋` and on `P₊` at `x₊`), the sector reduces to the termwise
identity along `s7b_slidingDecompositionEquiv`. -/

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} (h : g.SlidingAt M a) (t : g.SideParameter)

include hn h in
/-- The last clause of `VertexCrossingData` (lem:wall-sides (V)): persistent crossings of a side agree
with the centre's. -/
theorem s7e_hQC (b : Bool) : ∀ s, ¬ ContactAffected M a s →
    (IsCrossing (g.curve (g.sideTime b t)) s ↔ IsCrossing g.center s) := by
  intro s hs
  have := ((vertex_sides hn g h.1).2.2.2.1 t t).2.2.2 s hs
  cases b
  · exact this.2
  · exact this.1

/-- The contact sector from the two interlacement transfers and the termwise identity along U110-B's
bijections `s7b_slidingDecompositionEquiv` (eq. s7c:sliding-bijection on each side). -/
theorem s7e_contactSector_of_pivotSplit (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a))
    (hsplitm : s7b_PivotSplit (Interlaces hn (s7a_sideGeneric g false))
      (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
      (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false))
      (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false)) (s7e_xm hn h t))
    (hsplitp : s7b_PivotSplit (Interlaces hn (s7a_sideGeneric g true))
      (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
      (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true))
      (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true)) (s7e_xp hn h t))
    (hterm : ∀ q, s7e_term hn (s7a_sideGeneric g true)
        ((s7b_slidingDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true)
          (s7a_sideGeneric g true) h₁ h₂ (s7e_xp hn h t) hsplitp).symm q).1 -
      s7e_term hn (s7a_sideGeneric g false)
        ((s7b_slidingDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false)
          (s7a_sideGeneric g false) h₁ h₂ (s7e_xm hn h t) hsplitm).symm q).1 =
      (g.contactSign M a : ℤ) *
        (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ q.1.1 *
          s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ q.2.1)) :
    s7e_ContactSector hn h h₁ h₂ t :=
  ⟨_, _, hterm⟩

end S7EContactRepack

end VertexEdge

end

end SM
