import RProof.X1Rows3

/-! # G11 skeleton — HOMFLY invariance of the distinguished carrier's grouped diagram across the RIII wall

Written 2026-09-14 by the G11 architect (R lane, row 173 follow-up) on Mark's RunPod home pod. Plan:
`work/drafts/rlane2/G11_PLAN.md`. This file `import RProof.X1Rows3` (the accepted wave-3 module) and
contains ONLY the new material, all `G11_`-prefixed (namespace `RProof`). Every leaf (49) is `sorry`; the
assembled theorems `GT_G11_strong_proof`, `GT_G11_proof : GT_G11` and the row theorem
`RProof.generic_transport` are PROVED from the leaves.

The printed step being rendered (reference/R/RA/R_GENERIC_COMMON_TRANSPORT_PROOF.md:109-117): "On the
distinguished carrier, (1) makes the divide over-order of the three local strands transitive … Call the
path- and edge-side grouped diagrams `D_P, D_E`. Apply the corresponding ordinary oriented Reidemeister III
move to `D_P`, obtaining `D'`; `ax:homfly` gives `P(D') = P(D_P)`. R-LOC-2 conclusions (1) and (3), the
successor lift (2a), and the printed local words give an orientation-preserving `def:record` isomorphism
from `D'` to `D_E` … so `ax:gausscode` identifies their oriented links."

Route (no `Deform`): `D_P = D₀ ≃_Reparam M₀ –RIII→ M₁ ≅_record D_E` where
* `D₀ = geoPositiveLift hn hG hT q` is the positive diagram of the one-component corner polygon `X` of the
  distinguished carrier (`X = geoCornerPolygon`), on which the three local strands are three edges
  `m, p, q` of `X` pairwise crossing at `x_mp, x_mq, x_pq` (Unit A, `G11_Config`);
* `M₀` = `D₀` with the edge `m` subdivided by THREE flat vertices `p_in < m₀ < p_out` (`t₁ < t(x_mp) < t₂ <
  t(x_mq) < t₃`), a reparametrization (accepted CS3 `homfly_positiveDiagram_single_appendVertex` ×3 after a
  re-indexing); `M₁` = `M₀` with the ONE vertex `m₀` moved to the apex `w = m₀ + λ (x_pq − m₀)`, `λ > 1`, so the
  bent strand `[p_in, w] ∪ [w, p_out]` passes on the other side of `x_pq`: an actual `RIIIData` in the
  disc `U` = the homothetic enlargement of the triangle `Δ = conv{x_mp, x_mq, x_pq}` (Units B–D);
* the record of `M₁` is the record of `M₀` with the three adjacent transpositions `σ` (Unit E), and the
  record of `D_E` is the record of `D_P` with the same three transpositions (`ExactTriangleVisitOrders`,
  Unit F), whence `M₁ ≅ D_E` by `CV.recordIsoOfData` / `CV.gausscode_polynomial`.

**Statement finding (see G11_PLAN.md §0).** `GT_G11` as defined in X1Rows3 has NO hypothesis that the
three pairs `{e,f}, {e,g}, {f,g}` are crossings of `P`. Its consumer `GT_empty_groupedPoly_eq` has them
(`hef' heg' hfg'`). We therefore prove `GT_G11_strong` (= `GT_G11` + the three crossing hypotheses) by the
RIII route, re-derive the row `generic_transport` from it (copying the accepted 60-line assembly), and
prove the literal `GT_G11` from `GT_G11_strong` plus two branch leaves: `≤ 1` triangle crossing (a plain
record isomorphism, provable) and exactly two triangle crossings (contradictory by Gauss parity — NOT in
the library; flagged). -/

namespace RProof

open SM SM.GeoCarrier SM.Link SM.Carrier

variable {n : ℕ} [NeZero n]

/-! ## Unit A — triangle configurations of a one-component generic polygon -/

section G11Config

variable {k : ℕ} [NeZero k]

/-- The closed triangle spanned by the three double points `x_mp, x_mq, x_pq`. -/
noncomputable def G11_triangle (X : LabelledTuple k) {m p q : ZMod k} (hmp : IsCrossing X {m, p})
    (hmq : IsCrossing X {m, q}) (hpq : IsCrossing X {p, q}) : Set Plane :=
  convexHull ℝ {crossingPoint (xPair hmp), crossingPoint (xPair hmq), crossingPoint (xPair hpq)}

/-- A preconnected set meeting a set `t` and its complement meets the frontier of `t` (the two open sets
`interior t` and `(closure t)ᶜ` would otherwise disconnect it). -/
theorem G11_preconnected_meets_frontier {s t : Set Plane} (hs : IsPreconnected s)
    (h1 : (s ∩ t).Nonempty) (h2 : (s \ t).Nonempty) : (s ∩ frontier t).Nonempty := by
  by_contra hF
  have hsub : s ⊆ interior t ∪ (closure t)ᶜ := by
    intro x hx
    by_cases hxc : x ∈ closure t
    · left
      by_contra hxi
      exact hF ⟨x, hx, hxc, hxi⟩
    · exact Or.inr hxc
  obtain ⟨x, hxs, hxt⟩ := h1
  obtain ⟨y, hys, hyt⟩ := h2
  have hx' : x ∈ s ∩ interior t := by
    refine ⟨hxs, ?_⟩
    rcases hsub hxs with h | h
    · exact h
    · exact absurd (subset_closure hxt) h
  have hy' : y ∈ s ∩ (closure t)ᶜ := by
    refine ⟨hys, ?_⟩
    rcases hsub hys with h | h
    · exact absurd (interior_subset h) hyt
    · exact h
  obtain ⟨z, -, hz1, hz2⟩ := hs (interior t) (closure t)ᶜ isOpen_interior
    isClosed_closure.isOpen_compl hsub ⟨x, hx'⟩ ⟨y, hy'⟩
  exact hz2 (subset_closure (interior_subset hz1))

/-- A closed edge segment is preconnected (the continuous image of `[0, 1]`). -/
theorem G11_edgeSegment_isPreconnected {k : ℕ} (X : LabelledTuple k) (h : ZMod k) :
    IsPreconnected (edgeSegment X h) := by
  have himg : edgeSegment X h = (fun t : ℝ => edgePoint X h t) '' Set.Icc 0 1 := by
    ext x
    constructor
    · rintro ⟨t, h0, h1, rfl⟩
      exact ⟨t, ⟨h0, h1⟩, rfl⟩
    · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
      exact ⟨t, h0, h1, rfl⟩
  rw [himg]
  refine isPreconnected_Icc.image _ (Continuous.continuousOn ?_)
  unfold edgePoint
  exact continuous_const.add (continuous_id.smul continuous_const)

/-- **A triangle configuration** on a one-component generic polygon `X` with `k ≥ 3` vertices: three edges
`m` (the strand to be moved), `p`, `q` (met along `m` in this order) pairwise crossing, the divide over-order
transitive (`¬ IsAlternating`, the generic orbit), and the closed triangle meeting the polygon only along
`m, p, q` (no other edge and no vertex in it). -/
structure G11_Config (k : ℕ) [NeZero k] where
  hk : 3 ≤ k
  X : LabelledTuple k
  gen : (Shadow.single ⟨k, hk, X⟩).Generic
  m : ZMod k
  p : ZMod k
  q : ZMod k
  hmp : IsCrossing X {m, p}
  hmq : IsCrossing X {m, q}
  hpq : IsCrossing X {p, q}
  /-- `p` is met before `q` along `m` -/
  order : crossingParameter (xPair hmp) m (mem_pair_left m p) <
    crossingParameter (xPair hmq) m (mem_pair_left m q)
  /-- the divide over-order of the three strands is transitive -/
  trans : ¬ IsAlternating (crossingSign X m p) (crossingSign X m q) (crossingSign X p q)
  /-- no other edge meets the BOUNDARY of the closed triangle (the local form of the clearance: a foreign
  edge through a side would cross it strictly between two local visits, through a vertex would be a triple
  point); the closed-triangle form is the PROVED glue `G11_Config.clear_edge` -/
  clear_frontier : ∀ h : ZMod k, h ≠ m → h ≠ p → h ≠ q →
    ∀ x ∈ edgeSegment X h, x ∉ frontier (G11_triangle X hmp hmq hpq)
  /-- no vertex lies in the closed triangle -/
  clear_vertex : ∀ i : ZMod k, X i ∉ G11_triangle X hmp hmq hpq

namespace G11_Config

variable (C : G11_Config k)

/-- The polygon as a one-component `PolyComp`. -/
def comp : PolyComp := ⟨k, C.hk, C.X⟩

/-- `D₀ = D_P`: the positive diagram of `X`. -/
noncomputable def D₀ : Diagram := (Shadow.single C.comp).positiveDiagram C.gen

theorem D₀_componentCount : C.D₀.componentCount = 1 := rfl

/-- **Glue (PROVED): no other edge meets the closed triangle.** An edge with a point in the triangle and its
tail vertex outside it (`clear_vertex`) meets the frontier (`G11_preconnected_meets_frontier`), which
`clear_frontier` forbids. This is the form the geometric units (P, C, D) consume. -/
theorem clear_edge : ∀ h : ZMod k, h ≠ C.m → h ≠ C.p → h ≠ C.q →
    ∀ x ∈ edgeSegment C.X h, x ∉ G11_triangle C.X C.hmp C.hmq C.hpq := by
  intro h hm hp hq x hx hxΔ
  obtain ⟨y, hy, hyF⟩ := G11_preconnected_meets_frontier (G11_edgeSegment_isPreconnected C.X h)
    ⟨x, hx, hxΔ⟩ ⟨C.X h, ⟨0, le_rfl, zero_le_one, (edgePoint_zero C.X h).symm⟩, C.clear_vertex h⟩
  exact C.clear_frontier h hm hp hq y hy hyF

/-- the six local visits of `X`, named `v(strand)(other strand)` -/
def vmp : Visit C.X := ⟨xPair C.hmp, ⟨C.m, mem_pair_left _ _⟩⟩
def vpm : Visit C.X := ⟨xPair C.hmp, ⟨C.p, mem_pair_right _ _⟩⟩
def vmq : Visit C.X := ⟨xPair C.hmq, ⟨C.m, mem_pair_left _ _⟩⟩
def vqm : Visit C.X := ⟨xPair C.hmq, ⟨C.q, mem_pair_right _ _⟩⟩
def vpq : Visit C.X := ⟨xPair C.hpq, ⟨C.p, mem_pair_left _ _⟩⟩
def vqp : Visit C.X := ⟨xPair C.hpq, ⟨C.q, mem_pair_right _ _⟩⟩

/-- **The three adjacent transpositions** of the RIII move on the visits of `X`: the two visits on each of
the three local strands are exchanged. -/
noncomputable def σ : Equiv.Perm (Visit C.X) :=
  Equiv.swap C.vmp C.vmq * (Equiv.swap C.vpm C.vpq * Equiv.swap C.vqm C.vqp)

/-- `σ` read on the occurrences of `D₀`. -/
noncomputable def σD : Equiv.Perm C.D₀.Γ.Visit :=
  (Shadow.singleVisitEquiv C.comp).symm.permCongr C.σ

/-- the six local visits read as occurrences of `D₀` -/
noncomputable def v_mp : C.D₀.Γ.Visit := (Shadow.singleVisitEquiv C.comp).symm C.vmp
noncomputable def v_pm : C.D₀.Γ.Visit := (Shadow.singleVisitEquiv C.comp).symm C.vpm
noncomputable def v_mq : C.D₀.Γ.Visit := (Shadow.singleVisitEquiv C.comp).symm C.vmq
noncomputable def v_qm : C.D₀.Γ.Visit := (Shadow.singleVisitEquiv C.comp).symm C.vqm
noncomputable def v_pq : C.D₀.Γ.Visit := (Shadow.singleVisitEquiv C.comp).symm C.vpq
noncomputable def v_qp : C.D₀.Γ.Visit := (Shadow.singleVisitEquiv C.comp).symm C.vqp

end G11_Config

/-! ### The geometric core (Units B–E assembled): the record of `D₀` twisted by `σ` is realized by a
diagram with the same HOMFLY polynomial -/

/-- **G11 core.** For every triangle configuration there is a diagram `D₁` (= `M₁`) with `homfly D₁ = homfly
D₀` and an occurrence bijection `Ψ : D₀ ≃ D₁` carrying twins, over bits and signs, whose cyclic order is
the cyclic order of `D₀` twisted by the three transpositions `σ`. PROVED below from the unit leaves
(`G11_core_of_params`). -/
def G11_core_statement (C : G11_Config k) : Prop :=
  ∃ (D₁ : Diagram) (Ψ : C.D₀.Γ.Visit ≃ D₁.Γ.Visit),
    D₁.componentCount = 1 ∧
    homfly D₁ = homfly C.D₀ ∧
    (∀ v, Ψ (C.D₀.twin v) = D₁.twin (Ψ v)) ∧
    (∀ v, D₁.overBit (Ψ v) = C.D₀.overBit v) ∧
    (∀ v, D₁.sign (Ψ v).1 = C.D₀.sign v.1) ∧
    (∀ u v w, D₁.VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔ C.D₀.VisitBetween (C.σD u) (C.σD v) (C.σD w))

end G11Config

/-! ## Unit B/C — the flat subdivision `X₀` and the moved polygon `X₁` -/

section G11Params

variable {k : ℕ} [NeZero k]

/-- The edge `m` of `X` subdivided by three vertices at the parameters `t₁, t₂, t₃`: labels `≤ m` keep their
value, the new vertices are `m+1, m+2, m+3`, labels `> m` are shifted by `3`. -/
noncomputable def G11_subdiv (X : LabelledTuple k) (m : ZMod k) (t₁ t₂ t₃ : ℝ) :
    LabelledTuple (k + 3) := fun j =>
  if j.val ≤ m.val then X (j.val : ZMod k)
  else if j.val = m.val + 1 then edgePoint X m t₁
  else if j.val = m.val + 2 then edgePoint X m t₂
  else if j.val = m.val + 3 then edgePoint X m t₃
  else X ((j.val - 3 : ℕ) : ZMod k)

/-- The label of an old edge `i ≠ m` of `X` in `X₀` (`i ≤ m` unchanged, `i > m` shifted by `3`). -/
def G11_lab (m i : ZMod k) : ZMod (k + 3) :=
  if i.val ≤ m.val then (i.val : ZMod (k + 3)) else ((i.val + 3 : ℕ) : ZMod (k + 3))

/-- The centroid of the triangle. -/
noncomputable def G11_centroid (C : G11_Config k) : Plane :=
  (1 / 3 : ℝ) • (crossingPoint (xPair C.hmp) + crossingPoint (xPair C.hmq) + crossingPoint (xPair C.hpq))

/-- **The disc `U`**: the homothetic enlargement of the closed triangle about its centroid with ratio
`1 + r`. A compact convex set with nonempty interior (`IsDisc`, leaf `G11_disc_isDisc`); its frontier and
interior are read off the barycentric coordinates (`AffineBasis.interior_convexHull`). -/
noncomputable def G11_discOf (C : G11_Config k) (r : ℝ) : Set Plane :=
  (fun y => G11_centroid C + (1 + r) • (y - G11_centroid C)) '' G11_triangle C.X C.hmp C.hmq C.hpq

/-- **The parameters of the move**: the three subdivision parameters `t₁ < t(x_mp) < t₂ < t(x_mq) < t₃` on
the edge `m`, the apex ratio `λ > 1`, the disc margin `r > 0`, and the smallness clauses: the bent triangle
`Θ = conv{p_in, w, p_out}` lies in the open disc, and the closed disc meets no other edge and no vertex of
`X`. Existence: leaf `G11_exists_params`. -/
structure G11_Params (C : G11_Config k) where
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
  /-- the bent triangle `Θ` lies in the open disc -/
  theta_sub : convexHull ℝ {edgePoint C.X C.m t₁,
      edgePoint C.X C.m t₂ + lam • (crossingPoint (xPair C.hpq) - edgePoint C.X C.m t₂),
      edgePoint C.X C.m t₃} ⊆ interior (G11_discOf C r)
  /-- the closed disc meets no other edge -/
  disc_clear_edge : ∀ h : ZMod k, h ≠ C.m → h ≠ C.p → h ≠ C.q →
    ∀ x ∈ edgeSegment C.X h, x ∉ G11_discOf C r
  /-- the closed disc contains no vertex -/
  disc_clear_vertex : ∀ i : ZMod k, C.X i ∉ G11_discOf C r

namespace G11_Params

variable {C : G11_Config k} (π : G11_Params C)

theorem hk₃ (_π : G11_Params C) : 3 ≤ k + 3 := by omega

/-- the subdivided polygon `X₀` -/
noncomputable def X₀ : LabelledTuple (k + 3) := G11_subdiv C.X C.m π.t₁ π.t₂ π.t₃

/-- the label of the middle new vertex `m₀` -/
def mid (_π : G11_Params C) : ZMod (k + 3) := ((C.m.val + 2 : ℕ) : ZMod (k + 3))

/-- the labels of the four pieces of `m` in `X₀`: `[X m, p_in]`, `[p_in, m₀]`, `[m₀, p_out]`, `[p_out, X (m+1)]` -/
def mA (_π : G11_Params C) : ZMod (k + 3) := (C.m.val : ZMod (k + 3))
def mB (_π : G11_Params C) : ZMod (k + 3) := ((C.m.val + 1 : ℕ) : ZMod (k + 3))
def mC (_π : G11_Params C) : ZMod (k + 3) := ((C.m.val + 2 : ℕ) : ZMod (k + 3))
def mD (_π : G11_Params C) : ZMod (k + 3) := ((C.m.val + 3 : ℕ) : ZMod (k + 3))

/-- the labels of `p`, `q` in `X₀` -/
def p' (_π : G11_Params C) : ZMod (k + 3) := G11_lab C.m C.p
def q' (_π : G11_Params C) : ZMod (k + 3) := G11_lab C.m C.q

/-- the apex `w = m₀ + λ (x_pq − m₀)` -/
noncomputable def apex : Plane :=
  edgePoint C.X C.m π.t₂ + π.lam • (crossingPoint (xPair C.hpq) - edgePoint C.X C.m π.t₂)

/-- the moved polygon `X₁`: `m₀` replaced by the apex -/
noncomputable def X₁ : LabelledTuple (k + 3) := Function.update π.X₀ π.mid π.apex

/-- the disc -/
noncomputable def U : Set Plane := G11_discOf C π.r

/-! ### Unit B leaves — the flat subdivision -/

/-- **B1.** `X₀` is a generic one-component shadow (three accepted flat subdivisions
`single_generic_appendVertex` after the re-indexing `Reindexed` putting `m` last; `hoff` from the
configuration: the three new points lie on `m` only). -/
theorem X₀_generic : (Shadow.single ⟨k + 3, π.hk₃, π.X₀⟩).Generic := by
  sorry

/-- `M₀`: the positive diagram of `X₀`. -/
noncomputable def M₀ : Diagram := (Shadow.single ⟨k + 3, π.hk₃, π.X₀⟩).positiveDiagram π.X₀_generic

theorem M₀_componentCount : π.M₀.componentCount = 1 := rfl

/-- **B2.** `P(M₀) = P(D₀)`: `homfly_positiveDiagram_single_of_reindexed` + three applications of
`homfly_positiveDiagram_single_appendVertex` (planar isotopy, `homfly_planar`). -/
theorem homfly_M₀ : homfly π.M₀ = homfly C.D₀ := by
  sorry

/-- **B3.** The crossings of `X₀` carrying the three local double points: `x_mp` on `[p_in, m₀]`, `x_mq` on
`[m₀, p_out]`, `x_pq` on `p', q'` (from `t₁ < t(x_mp) < t₂ < t(x_mq) < t₃` and `edgeSegment_appendVertex_*`). -/
theorem X₀_cross_mp : IsCrossing π.X₀ {π.mB, π.p'} := by
  sorry

theorem X₀_cross_mq : IsCrossing π.X₀ {π.mC, π.q'} := by
  sorry

theorem X₀_cross_pq : IsCrossing π.X₀ {π.p', π.q'} := by
  sorry

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
  sorry

/-! ### Unit C leaves — the moved polygon -/

/-- **C1.** `X₁` is a generic one-component shadow: `regular` (the two bent edges are nonzero, not
antiparallel to their neighbours), `tail_off` (the apex is on no edge; no old vertex is on a bent edge —
both edges lie in `Θ ⊆ interior U`, which meets no vertex), `transverse` (bent edge against `p'`, `q'`:
`det ≠ 0` by the explicit formulas; against every other edge: disjoint, `Θ ⊆ interior U` and
`disc_clear_edge`; against the neighbouring `m`-pieces: adjacent), `no_triple` (the bent edges meet `p'`,
`q'` at two distinct points different from `x_pq`; nothing else enters `Θ`). -/
theorem X₁_generic : (Shadow.single ⟨k + 3, π.hk₃, π.X₁⟩).Generic := by
  sorry

/-- `M₁`: the positive diagram of `X₁`. -/
noncomputable def M₁ : Diagram := (Shadow.single ⟨k + 3, π.hk₃, π.X₁⟩).positiveDiagram π.X₁_generic

theorem M₁_componentCount : π.M₁.componentCount = 1 := rfl

/-- **C2.** The crossings of `X₁` involving a bent edge: `p'` crosses `[w, p_out]` (label `mC`) and `q'`
crosses `[p_in, w]` (label `mB`) — `p` enters `Θ` on the left half of the base, passes `x_pq` on the median
`(m₀, w)` and exits through the right side; `q` symmetrically. -/
theorem X₁_cross_pC : IsCrossing π.X₁ {π.p', π.mC} := by
  sorry

theorem X₁_cross_qB : IsCrossing π.X₁ {π.q', π.mB} := by
  sorry

/-- **C3.** Every other crossing of `X₁` is a crossing of `X₀` not involving `mB, mC`, with the same
double point (the strands are literally the same segments), and conversely. -/
theorem X₁_cross_iff (s : Finset (ZMod (k + 3))) (hs : π.mB ∉ s) (hs' : π.mC ∉ s) :
    IsCrossing π.X₁ s ↔ IsCrossing π.X₀ s := by
  sorry

/-- **C4.** The over bits at the two new crossings agree with the old ones: `sgn det(edge p', edge [w,p_out])
= sgn det(edge p, edge m)` and `sgn det(edge q', edge [p_in,w]) = sgn det(edge q, edge m)` (in the
coordinates `b = x`-axis, `x_mp = (0,0)`, `x_mq = (1,0)`, `m₀ = (μ,0)`, `x_pq = (u,h)`, `w = (μ+λ(u−μ), λh)`:
`det(d_p, p_out − w) = −h(1+ε−μ+λμ)`, `det(d_q, w − p_in) = −h(λ(1−μ)+μ+ε)`, both of the sign of
`det(d_p, d_m) = det(d_q, d_m) = −h`). -/
theorem X₁_sign_pC : crossingSign π.X₁ π.p' π.mC = crossingSign C.X C.p C.m := by
  sorry

theorem X₁_sign_qB : crossingSign π.X₁ π.q' π.mB = crossingSign C.X C.q C.m := by
  sorry

/-! ### Unit D leaves — the disc and the Reidemeister-III site -/

/-- **D1.** `U` is a disc (`IsDisc`: convex, compact, nonempty interior) — the image of the convex hull of
three affinely independent points under a homothety. -/
theorem disc_isDisc : IsDisc π.U := by
  sorry

/-- **D2.** The closed triangle lies in the open disc. -/
theorem triangle_sub_interior : G11_triangle C.X C.hmp C.hmq C.hpq ⊆ interior π.U := by
  sorry

/-- **D3.** The inner crossings of `M₀` are exactly the three local ones (every other double point lies on
an edge outside `U`, `disc_clear_edge`). -/
theorem inner_M₀ (y : π.M₀.Γ.Crossing) :
    π.M₀.Γ.crossingPoint y ∈ interior π.U ↔
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ y = xPair π.X₀_cross_mp ∨
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ y = xPair π.X₀_cross_mq ∨
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₀⟩ y = xPair π.X₀_cross_pq := by
  sorry

/-- `x_pq` is a crossing of `X₁` (unmoved strands, `X₁_cross_iff`). -/
theorem X₁_cross_pq : IsCrossing π.X₁ {π.p', π.q'} := by
  sorry

/-- **D4.** The inner crossings of `M₁` are exactly `x_pq` and the two new ones. -/
theorem inner_M₁ (y : π.M₁.Γ.Crossing) :
    π.M₁.Γ.crossingPoint y ∈ interior π.U ↔
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩ y = xPair π.X₁_cross_pC ∨
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩ y = xPair π.X₁_cross_qB ∨
      Shadow.singleCrossingEquiv ⟨k + 3, π.hk₃, π.X₁⟩ y = xPair π.X₁_cross_pq := by
  sorry

/-- **D5.** Both diagrams meet `U` cleanly (the six frontier points are distinct and traversed once; the
component leaves `U`). -/
theorem clean_M₀ : Clean π.U π.M₀ := by
  sorry

theorem clean_M₁ : Clean π.U π.M₁ := by
  sorry

/-- **D6.** The outside match with component bijection: the identity on traversal points (same labels
`ZMod (k+3)`, same parameters), `eval_eq` because only the vertex `m₀` moved and both bent edges lie in
`interior U`; directions of outside points are those of unmoved strands; outer crossings are the crossings
not involving `mB, mC` (`X₁_cross_iff`), with the same over data (positive diagrams, same `det`). -/
theorem exists_moveMatch : Nonempty (MoveMatch π.U π.M₀ π.M₁) := by
  sorry

/-- **D7.** The three arcs of `M₀` inside `U` (on `p'`, on `q'`, and the `m`-arc across the four pieces),
covering the trace of `M₀` inside `U`; and the three arcs of `M₁` (the `m`-arc now bent through the apex)
with the same six ends. Stated as the existence of the arc covers with matching ends. -/
theorem exists_arcCovers : ∃ (a b c : π.M₀.Γ.Arc) (a' b' c' : π.M₁.Γ.Arc),
    a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a' ≠ b' ∧ b' ≠ c' ∧ a' ≠ c' ∧
    π.M₀.Γ.ArcCover π.U {a, b, c} ∧ π.M₁.Γ.ArcCover π.U {a', b', c'} ∧
    π.M₁.Γ.eval a'.startPt = π.M₀.Γ.eval a.startPt ∧ π.M₁.Γ.eval a'.stopPt = π.M₀.Γ.eval a.stopPt ∧
    π.M₁.Γ.eval b'.startPt = π.M₀.Γ.eval b.startPt ∧ π.M₁.Γ.eval b'.stopPt = π.M₀.Γ.eval b.stopPt ∧
    π.M₁.Γ.eval c'.startPt = π.M₀.Γ.eval c.startPt ∧ π.M₁.Γ.eval c'.stopPt = π.M₀.Γ.eval c.stopPt := by
  sorry

/-- **D8 (assembly of the site).** `RIIIData U M₀ M₁` from D1–D7: the arcs named by height (the `trans`
clause of the configuration gives one strict height order; six cases, one instantiation per permutation of
`{m, p, q}`), `Separates`/`OverOn` from the positive diagrams and `X₁_sign_*`, the three `BeforeOn`
reversals from the explicit parameters (`x_pq` lies strictly between the two crossings of `p` (resp. `q`)
with `Θ`'s boundary along `p` (resp. `q`); along the bent strand `x_mq'` on `[p_in, w]` precedes `x_mp'`
on `[w, p_out]`). -/
theorem riii : RIII π.M₀ π.M₁ := by
  sorry

/-- `P(M₁) = P(M₀)` by `ax:homfly` (accepted `homfly_reidemeister_III`). -/
theorem homfly_M₁ : homfly π.M₁ = homfly π.M₀ :=
  (homfly_reidemeister_III π.riii).symm

/-! ### Unit E leaves — the record of `M₁` -/

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
  sorry

/-- **The core from the parameters** (Units B–E assembled): `D₁ := M₁`, `Ψ := Ψ₀.trans Ψ₁`. -/
theorem core_of_params (π : G11_Params C) : G11_core_statement C := by
  obtain ⟨Ψ₀, htw₀, hbit₀, hsgn₀, hcyc₀, hmp, hpm, hmq, hqm, hpq, hqp⟩ := π.exists_Ψ₀
  obtain ⟨Ψ₁, htw₁, hbit₁, hsgn₁, hcyc₁⟩ := π.exists_Ψ₁ Ψ₀ hcyc₀ hmp hpm hmq hqm hpq hqp
  refine ⟨π.M₁, Ψ₀.trans Ψ₁, π.M₁_componentCount, π.homfly_M₁.trans π.homfly_M₀, ?_, ?_, ?_, ?_⟩
  · intro v
    simp only [Equiv.trans_apply]
    rw [htw₀, htw₁]
  · intro v
    simp only [Equiv.trans_apply]
    rw [hbit₁, hbit₀]
  · intro v
    simp only [Equiv.trans_apply]
    rw [hsgn₁, hsgn₀]
  · intro u v w
    simp only [Equiv.trans_apply]
    exact hcyc₁ u v w

end G11_Params

/-- **Leaf (Units B–D, the choice of parameters).** Parameters exist: the subdivision parameters
between the two crossing parameters on `m`; the apex ratio `λ > 1`; the margin `r` below the clearance
(`Δ` is compact and disjoint from the finitely many other closed edges and vertices: a positive distance
`ρ`; every point of `U` is within `r · diam` of `Δ`), then `t₁, t₃, λ − 1` small enough that `Θ ⊆ interior
U`. -/
theorem G11_exists_params (C : G11_Config k) : Nonempty (G11_Params C) := by
  sorry

/-- **The geometric core**, for every triangle configuration. -/
theorem G11_core (C : G11_Config k) : G11_core_statement C :=
  (G11_exists_params C).elim fun π => π.core_of_params

end G11Params

/-! ## Unit A leaves — from the distinguished carrier to a triangle configuration -/

section G11Carrier

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P) {T : Finset (Crossing P)}
  (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)

/-- **A1.** The edge of the corner polygon `X = geoCornerPolygon` carrying a retained visit `v`: the corner
index `k` of the block of the mark `v` (`geo_mark_block`). -/
noncomputable def G11_carrierEdge (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg T q) :
    ZMod (geoCornerCount hG.cg T q) :=
  Classical.choose (geo_mark_block hn hG.cg hT q (Sum.inr v)
    (((mem_geoCarrierCrossings hG.cg T q v.1).mp hv).2 v rfl))

/-- (U1 helper) The block data behind `G11_carrierEdge`: the mark of `v` is `ρ_T^r c_k` with `r ≥ 1`
(`v` is unselected, hence not a corner), the intermediate marks are block-interior, the outgoing
slot of `c_k` is the edge of `v`, and the double point of `v` lies on the carrier edge `k`. -/
theorem gu1_carrierEdge_block (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg T q) :
    ∃ r : ℕ, 1 ≤ r ∧
      (geoSmoothingSuccessor hG.cg T ^ r)
        (geoCornerMark hG.cg T q (G11_carrierEdge hn hG hT q v hv)) = Sum.inr v ∧
      GeoBlockInterior hG.cg T q (G11_carrierEdge hn hG hT q v hv) r ∧
      (geoOutSlot hG.cg T (geoCornerMark hG.cg T q (G11_carrierEdge hn hG hT q v hv))).1 =
        v.2.val ∧
      crossingPoint v.1 ∈
        edgeSegment (geoCornerPolygon hG.cg T q) (G11_carrierEdge hn hG hT q v hv) := by
  unfold G11_carrierEdge
  obtain ⟨r, hρ, hb, hmem⟩ := Classical.choose_spec (geo_mark_block hn hG.cg hT q (Sum.inr v)
    (((mem_geoCarrierCrossings hG.cg T q v.1).mp hv).2 v rfl))
  have hvS : v.1 ∉ T := ((mem_geoCarrierCrossings hG.cg T q v.1).mp hv).1
  have hr : 1 ≤ r := by
    by_contra h
    have hr0 : r = 0 := by omega
    rw [hr0, pow_zero, Equiv.Perm.one_apply] at hρ
    have hcorner := isTrueCorner_geoCornerMark hG.cg T q
      (Classical.choose (geo_mark_block hn hG.cg hT q (Sum.inr v)
        (((mem_geoCarrierCrossings hG.cg T q v.1).mp hv).2 v rfl)))
    rw [hρ] at hcorner
    exact hvS ((isTrueCorner_visit T v).mp hcorner)
  refine ⟨r, hr, hρ, hb, (hb.visit_edge hG.cg T q hr hρ).symm, ?_⟩
  rw [← geoMarkPosition_evaluation_visit hG.cg v]
  exact hmem

/-- **A2.** The carrier edge through `v` is a positive rescaling of the original edge `v.2.val` and carries
the double point of `v` (`geoCornerPolygon_edge_smul`, `geo_mark_block`). -/
theorem G11_carrierEdge_spec (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg T q) :
    crossingPoint v.1 ∈ edgeSegment (geoCornerPolygon hG.cg T q) (G11_carrierEdge hn hG hT q v hv) ∧
    ∃ c : ℝ, 0 < c ∧ edge (geoCornerPolygon hG.cg T q) (G11_carrierEdge hn hG hT q v hv) =
      c • edge P v.2.val := by
  obtain ⟨r, -, -, -, hedge, hmem⟩ := gu1_carrierEdge_block hn hG hT q v hv
  refine ⟨hmem, ?_⟩
  obtain ⟨c, hc, he⟩ := geoCornerPolygon_edge_smul hn hG.cg hT q (G11_carrierEdge hn hG hT q v hv)
  exact ⟨c, hc, by rw [he, hedge]⟩

include hn in
/-- (U1 helper) The `ρ`-successor of a crossing visit `v` is the visit `w` on the same edge with the
next larger parameter, when no visit lies strictly between them: the successor is on the same edge
further on or is the next vertex (`geoMarkSuccessor_position_cases`), and no mark lies in the gap
(`geoMarkSuccessor_no_mark_between`). -/
theorem gu1_markSuccessor_eq_of_adjacent (hP : CrossingGeometry P) {v w : Visit P}
    (he : v.2.val = w.2.val) (hlt : visitParameter v < visitParameter w)
    (hadj : ∀ y : Visit P, y.2.val = v.2.val →
      ¬ (visitParameter v < visitParameter y ∧ visitParameter y < visitParameter w)) :
    geoMarkSuccessor hP (Sum.inr v) = Sum.inr w := by
  have hgap := geoMarkSuccessor_no_mark_between hP (Sum.inr v) (Sum.inr w)
  have hkvw : traversalKey (geoMarkPosition hP (Sum.inr v)) <
      traversalKey (geoMarkPosition hP (Sum.inr w)) :=
    (traversalKey_lt_iff _ _).mpr (Or.inr ⟨he, hlt⟩)
  rcases geoMarkSuccessor_position_cases hn hP (Sum.inr v) with ⟨hi, ht⟩ | hvert
  · obtain ⟨b, hb⟩ : ∃ b, geoMarkSuccessor hP (Sum.inr v) = b := ⟨_, rfl⟩
    rw [hb] at hi ht hgap ⊢
    cases b with
    | inl i =>
      exfalso
      have h0 : (geoMarkPosition hP (Sum.inl i)).2.val = 0 := rfl
      rw [h0] at ht
      have hv0 : 0 < visitParameter v :=
        (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).1
      change visitParameter v < 0 at ht
      linarith
    | inr y =>
      change y.2.val = v.2.val at hi
      change visitParameter v < visitParameter y at ht
      rcases lt_trichotomy (visitParameter y) (visitParameter w) with hyw | hyw | hyw
      · exact absurd ⟨ht, hyw⟩ (hadj y hi)
      · congr 1
        apply geometricVisitPosition_injective hP
        exact Prod.ext (hi.trans he) (Subtype.ext hyw)
      · exfalso
        apply hgap
        exact Or.inl ⟨hkvw,
          (traversalKey_lt_iff _ _).mpr (Or.inr ⟨he.symm.trans hi.symm, hyw⟩)⟩
  · exfalso
    apply hgap
    rw [hvert]
    change traversalBetween (geoMarkPosition hP (Sum.inr v)) (geoMarkPosition hP (Sum.inr w))
      (geoMarkPosition hP (Sum.inl (v.2.val + 1)))
    rcases Nat.lt_or_ge (v.2.val.val + 1) n with hlt' | hge
    · left
      refine ⟨hkvw, (traversalKey_lt_iff _ _).mpr (Or.inl ?_)⟩
      change w.2.val.val < (v.2.val + 1).val
      rw [zmod_val_add_one_of_lt hlt', ← he]
      omega
    · have heq : v.2.val.val + 1 = n := by
        have := ZMod.val_lt v.2.val
        omega
      right; right
      refine ⟨(traversalKey_lt_iff _ _).mpr (Or.inl ?_), hkvw⟩
      change (v.2.val + 1).val < v.2.val.val
      rw [zmod_add_one_eq_zero_of_val heq, ZMod.val_zero]
      omega

/-- (U1 helper) The ordered form of A3: `v` strictly before `w` on one edge with no visit between
puts `w` in the block of `v` (one more `ρ_T`-step), so the two blocks coincide
(`geo_block_mark_eq`). -/
theorem gu1_carrierEdge_eq_of_lt {v w : Visit P} (hv : v.1 ∈ geoCarrierCrossings hG.cg T q)
    (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) (he : v.2.val = w.2.val)
    (hlt : visitParameter v < visitParameter w)
    (hadj : ∀ y : Visit P, y.2.val = v.2.val →
      ¬ (visitParameter v < visitParameter y ∧ visitParameter y < visitParameter w)) :
    G11_carrierEdge hn hG hT q v hv = G11_carrierEdge hn hG hT q w hw := by
  obtain ⟨r, hr, hρ, hb, hedge, -⟩ := gu1_carrierEdge_block hn hG hT q v hv
  obtain ⟨r', -, hρ', hb', -, -⟩ := gu1_carrierEdge_block hn hG hT q w hw
  have hvS : v.1 ∉ T := ((mem_geoCarrierCrossings hG.cg T q v.1).mp hv).1
  have hwS : w.1 ∉ T := ((mem_geoCarrierCrossings hG.cg T q w.1).mp hw).1
  have hsucc : geoSmoothingSuccessor hG.cg T (Sum.inr v) = Sum.inr w := by
    rw [geoSmoothingSuccessor_visit_of_not_mem hG.cg T v hvS]
    exact gu1_markSuccessor_eq_of_adjacent hn hG.cg he hlt hadj
  have hρ1 : (geoSmoothingSuccessor hG.cg T ^ (r + 1))
      (geoCornerMark hG.cg T q (G11_carrierEdge hn hG hT q v hv)) = Sum.inr w := by
    rw [pow_succ', Equiv.Perm.mul_apply, hρ, hsucc]
  have hb1 : GeoBlockInterior hG.cg T q (G11_carrierEdge hn hG hT q v hv) (r + 1) := by
    intro i h1 hi
    rcases Nat.lt_or_ge i (r + 1) with hlt' | hge
    · exact hb i h1 (by omega)
    · have hi' : i = r + 1 := by omega
      subst hi'
      exact ⟨w, hρ1, hwS, by rw [hedge]; exact he.symm⟩
  exact (geo_block_mark_eq hG.cg T q hb1 hb' (hρ1.trans hρ'.symm)).1

/-- **A3.** Two retained visits on one original edge with no crossing of `P` strictly between them lie on
the same carrier edge (no corner — no `T`-crossing and no vertex — separates them). -/
theorem G11_carrierEdge_eq_of_adjacent {v w : Visit P} (hv : v.1 ∈ geoCarrierCrossings hG.cg T q)
    (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) (he : v.2.val = w.2.val)
    (hadj : ∀ y : Visit P, y.2.val = v.2.val →
      ¬ (visitParameter v < visitParameter y ∧ visitParameter y < visitParameter w) ∧
      ¬ (visitParameter w < visitParameter y ∧ visitParameter y < visitParameter v)) :
    G11_carrierEdge hn hG hT q v hv = G11_carrierEdge hn hG hT q w hw := by
  rcases lt_trichotomy (visitParameter v) (visitParameter w) with hlt | heq | hgt
  · exact gu1_carrierEdge_eq_of_lt hn hG hT q hv hw he hlt (fun y hy => (hadj y hy).1)
  · have hvw : v = w := geometricVisitPosition_injective hG.cg (Prod.ext he (Subtype.ext heq))
    subst hvw
    rfl
  · exact (gu1_carrierEdge_eq_of_lt hn hG hT q hw hv he.symm hgt
      (fun y hy => (hadj y (hy.trans he.symm)).2)).symm

/-- (U1 helper) The carrier edges of the two visits of a retained crossing are not adjacent: equal
edges would put both visits on one original edge (`visitTwin_edge_ne`); consecutive edges meet only
at their common corner (`geo_consecutive_meet`), which is the plane point of a true corner, never a
retained double point (`geo_carrier_selfIntersection_not_corner`). -/
theorem gu1_carrierEdge_remote (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg T q)
    (hv' : (visitTwin v).1 ∈ geoCarrierCrossings hG.cg T q) :
    ¬ adjacent (G11_carrierEdge hn hG hT q v hv) (G11_carrierEdge hn hG hT q (visitTwin v) hv') := by
  obtain ⟨r, hr, hρ, hb, hedge, hmem⟩ := gu1_carrierEdge_block hn hG hT q v hv
  obtain ⟨r', hr', hρ', hb', hedge', hmem'⟩ := gu1_carrierEdge_block hn hG hT q (visitTwin v) hv'
  rw [visitTwin_crossing] at hmem'
  have hnc := (geo_carrier_selfIntersection_not_corner hG T q hv).2.2.2
  set j := G11_carrierEdge hn hG hT q v hv with hj
  set j' := G11_carrierEdge hn hG hT q (visitTwin v) hv' with hj'
  intro hadj
  rcases hadj with h | h | h
  · have hjj : j = j' + 1 := by linear_combination -h
    rw [hjj] at hmem
    exact hnc _ (isTrueCorner_geoCornerMark hG.cg T q (j' + 1))
      (geo_consecutive_meet hn hG hT q j' hmem' hmem).symm
  · have hjj : j' = j := by linear_combination h
    rw [hjj] at hedge'
    exact visitTwin_edge_ne v (hedge'.symm.trans hedge)
  · have hjj : j' = j + 1 := by linear_combination h
    rw [hjj] at hmem'
    exact hnc _ (isTrueCorner_geoCornerMark hG.cg T q (j + 1))
      (geo_consecutive_meet hn hG hT q j hmem hmem').symm

/-- **A4.** The carrier edges of the two visits of a retained crossing cross in `X`, at the same double
point (`geoCarrierCrossingEquiv`, `crossingPoint_geoCarrierCrossingEquiv`). -/
theorem G11_carrierEdge_isCrossing (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg T q) :
    IsCrossing (geoCornerPolygon hG.cg T q)
      {G11_carrierEdge hn hG hT q v hv,
       G11_carrierEdge hn hG hT q (visitTwin v) (by rw [visitTwin_crossing]; exact hv)} := by
  have hv' : (visitTwin v).1 ∈ geoCarrierCrossings hG.cg T q := by
    rw [visitTwin_crossing]; exact hv
  obtain ⟨hmem, -⟩ := G11_carrierEdge_spec hn hG hT q v hv
  obtain ⟨hmem', -⟩ := G11_carrierEdge_spec hn hG hT q (visitTwin v) hv'
  rw [visitTwin_crossing] at hmem'
  exact ⟨_, _, rfl, gu1_carrierEdge_remote hn hG hT q v hv hv', ⟨crossingPoint v.1, hmem, hmem'⟩⟩

theorem G11_carrierEdge_crossingPoint (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg T q)
    (hc : IsCrossing (geoCornerPolygon hG.cg T q)
      {G11_carrierEdge hn hG hT q v hv,
       G11_carrierEdge hn hG hT q (visitTwin v) (by rw [visitTwin_crossing]; exact hv)}) :
    crossingPoint (xPair hc) = crossingPoint v.1 := by
  have hv' : (visitTwin v).1 ∈ geoCarrierCrossings hG.cg T q := by
    rw [visitTwin_crossing]; exact hv
  obtain ⟨hmem, -⟩ := G11_carrierEdge_spec hn hG hT q v hv
  obtain ⟨hmem', -⟩ := G11_carrierEdge_spec hn hG hT q (visitTwin v) hv'
  rw [visitTwin_crossing] at hmem'
  have hdet := geoCornerPolygon_transverse hn hG hT q _ _
    (gu1_carrierEdge_remote hn hG hT q v hv hv') ⟨crossingPoint v.1, hmem, hmem'⟩
  exact transverse_segments_unique hdet (crossingPoint_mem (xPair hc) _ (mem_pair_left _ _))
    (crossingPoint_mem (xPair hc) _ (mem_pair_right _ _)) hmem hmem'

/-- **A6.** The crossing sign of two carrier edges is the crossing sign of the original edges
(`geoCornerPolygon_edge_smul`, `det` bilinear, `sign_mul`). -/
theorem G11_carrierSign (v w : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg T q)
    (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    crossingSign (geoCornerPolygon hG.cg T q) (G11_carrierEdge hn hG hT q v hv)
      (G11_carrierEdge hn hG hT q w hw) = crossingSign P v.2.val w.2.val := by
  obtain ⟨-, c₁, hc₁, he₁⟩ := G11_carrierEdge_spec hn hG hT q v hv
  obtain ⟨-, c₂, hc₂, he₂⟩ := G11_carrierEdge_spec hn hG hT q w hw
  unfold crossingSign
  rw [he₁, he₂, ccp_det_smul_smul, sign_mul, sign_pos (mul_pos hc₁ hc₂), one_mul]

end G11Carrier

section G11Triangle

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P)
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {e f g : ZMod n}

omit [NeZero n] in
/-- (U1 helper) A visit on the edge `e` whose crossing contains the edge `g ≠ e` is the visit of
`x_eg` on `e` (its support is `{e, g}` by cardinality; the twin is on `g`). -/
theorem gu1_visit_eq_of_mem {e g : ZMod n} (heg : e ≠ g) (hceg : IsCrossing P {e, g})
    (y : Visit P) (hy : y.2.val = e) (hg : g ∈ y.1.val) :
    y = ⟨xPair hceg, ⟨e, mem_pair_left _ _⟩⟩ := by
  classical
  have he : e ∈ y.1.val := by rw [← hy]; exact y.2.property
  have hsub : ({e, g} : Finset (ZMod n)) ⊆ y.1.val := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact he
    · rw [Finset.mem_singleton.mp hx]; exact hg
  have hval : ({e, g} : Finset (ZMod n)) = y.1.val :=
    Finset.eq_of_subset_of_card_le hsub (by rw [crossing_card_two y.1, Finset.card_pair heg])
  have hc : y.1 = xPair hceg := Subtype.ext hval.symm
  rcases visit_eq_or_twin ⟨xPair hceg, ⟨e, mem_pair_left _ _⟩⟩ y hc with h | h
  · exact h
  · exfalso
    apply visitTwin_edge_ne (⟨xPair hceg, ⟨e, mem_pair_left _ _⟩⟩ : Visit P)
    rw [← h]
    exact hy

/-- **A7 (adjacency from R-LOC-2).** No visit of `P` on the edge `e` lies strictly between the two local
visits `x_ef`, `x_eg` on `e`: its order against both would be carried while theirs is reversed
(`ExactTriangleVisitOrders`, transitivity of `<`). -/
theorem G11_no_visit_between (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs) (y : Visit P) (hy : y.2.val = e) :
    ¬ (visitParameter (⟨xPair hcef, ⟨e, mem_pair_left _ _⟩⟩ : Visit P) < visitParameter y ∧
        visitParameter y < visitParameter (⟨xPair hceg, ⟨e, mem_pair_left _ _⟩⟩ : Visit P)) ∧
    ¬ (visitParameter (⟨xPair hceg, ⟨e, mem_pair_left _ _⟩⟩ : Visit P) < visitParameter y ∧
        visitParameter y < visitParameter (⟨xPair hcef, ⟨e, mem_pair_left _ _⟩⟩ : Visit P)) := by
  classical
  set a : Visit P := ⟨xPair hcef, ⟨e, mem_pair_left _ _⟩⟩ with ha
  set b : Visit P := ⟨xPair hceg, ⟨e, mem_pair_left _ _⟩⟩ with hb
  have hab : a.1.val ∪ b.1.val = {e, f, g} := by
    show ({e, f} : Finset (ZMod n)) ∪ {e, g} = {e, f, g}
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hba : b.1.val ∪ a.1.val = {e, f, g} := by rw [Finset.union_comm]; exact hab
  have hnua : ∀ y : Visit P, y.2.val = e → y ≠ b → a.1.val ∪ y.1.val ≠ {e, f, g} := by
    intro y hy hyb hu
    apply hyb
    apply gu1_visit_eq_of_mem heg hceg y hy
    have hg : g ∈ a.1.val ∪ y.1.val := by rw [hu]; simp
    rcases Finset.mem_union.mp hg with hg | hg
    · exfalso
      change g ∈ ({e, f} : Finset (ZMod n)) at hg
      simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with hg | hg
      · exact heg hg.symm
      · exact hfg hg.symm
    · exact hg
  have hnub : ∀ y : Visit P, y.2.val = e → y ≠ a → b.1.val ∪ y.1.val ≠ {e, f, g} := by
    intro y hy hya hu
    apply hya
    apply gu1_visit_eq_of_mem hef hcef y hy
    have hf : f ∈ b.1.val ∪ y.1.val := by rw [hu]; simp
    rcases Finset.mem_union.mp hf with hf | hf
    · exfalso
      change f ∈ ({e, g} : Finset (ZMod n)) at hf
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with hf | hf
      · exact hef hf.symm
      · exact hfg hf
    · exact hf
  constructor
  · rintro ⟨h1, h2⟩
    have hya : y ≠ a := fun h => by rw [h] at h1; exact lt_irrefl _ h1
    have hyb : y ≠ b := fun h => by rw [h] at h2; exact lt_irrefl _ h2
    have h1' := ((hX a y hy.symm).2 (hnua y hy hyb)).mp h1
    have h2' := ((hX y b hy).2 (by rw [Finset.union_comm]; exact hnub y hy hya)).mp h2
    have h3 := ((hX a b rfl).1 hab).mp (h1.trans h2)
    exact lt_irrefl _ ((h1'.trans h2').trans h3)
  · rintro ⟨h1, h2⟩
    have hya : y ≠ a := fun h => by rw [h] at h2; exact lt_irrefl _ h2
    have hyb : y ≠ b := fun h => by rw [h] at h1; exact lt_irrefl _ h1
    have h1' := ((hX b y hy.symm).2 (hnub y hy hya)).mp h1
    have h2' := ((hX y a hy).2 (by rw [Finset.union_comm]; exact hnua y hy hyb)).mp h2
    have h3 := ((hX b a rfl).1 hba).mp (h1.trans h2)
    exact lt_irrefl _ ((h1'.trans h2').trans h3)

/-- **A8 (clearance, local form).** No edge of `P` other than `e, f, g` meets the BOUNDARY of the closed
triangle `conv{x_ef, x_eg, x_fg}`: a point of a foreign edge `h` on the side `[x_ef, x_eg] ⊆ e` is a common
point of `h` and `e`, hence (`h` remote from `e`) the double point of `{h, e}`, a visit on `e` with parameter in
`[t(x_ef), t(x_eg)]` — strictly inside is excluded by A7, an endpoint by
`crossingPoint_injective_of_geometry`; `h` adjacent to `e` meets `e` only at a vertex, which is not on the open
edge. And no vertex of `P` lies in the closed triangle: a vertex on a side is on a non-incident closed edge
(`CarrierGeometry.vertex_off`) or an endpoint of `e, f, g` (on the side's line, off the side); a vertex strictly
inside would start a chain of foreign edges (its incident edges are foreign: the endpoints of `e, f, g` are
off the triangle) that never meets the frontier (the first clause) and never reaches `P e ∉ Δ` — `Nat.find`
on the first step leaving the triangle along the traversal from the vertex. -/
theorem G11_clear (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs) :
    (∀ h : ZMod n, h ≠ e → h ≠ f → h ≠ g → ∀ x ∈ edgeSegment P h,
      x ∉ frontier (convexHull ℝ
        {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)})) ∧
    (∀ i : ZMod n, P i ∉
      convexHull ℝ {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)}) := by
  sorry

/-- **A9 (relabelling).** `IsAlternating` is a property of the over-relation, invariant under exchanging
`f` and `g` (`crossingSign_swap`, `SignType` case analysis). -/
theorem G11_alt_swap (hne : ¬ IsAlternating (strandSign P e f) (strandSign P e g) (strandSign P f g)) :
    ¬ IsAlternating (strandSign P e g) (strandSign P e f) (strandSign P g f) := by
  sorry

/-- **A10 (relabelling).** `ExactTriangleVisitOrders` is symmetric in `f, g` (`{e, g, f} = {e, f, g}`). -/
theorem G11_exact_swap (hX : ExactTriangleVisitOrders P P' e f g hs) :
    ExactTriangleVisitOrders P P' e g f hs := by
  sorry

theorem G11_triangleCrossings_swap : triangleCrossings P e g f = triangleCrossings P e f g := by
  sorry

/-- **A11 (the strand signs of the configuration).** `¬ IsAlternating` in the strand-sign form of `GT_G11`
is `¬ IsAlternating` in the `crossingSign` form on `(e, f, g) = (m, p, q)`. -/
theorem G11_alt_crossingSign
    (hne : ¬ IsAlternating (strandSign P e f) (strandSign P e g) (strandSign P f g)) :
    ¬ IsAlternating (crossingSign P e f) (crossingSign P e g) (crossingSign P f g) := by
  sorry

end G11Triangle

section G11ConfigOf

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P)
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {e f g : ZMod n}
  {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)

/-- the three local visits on `e`, `f`, `g` used to name the carrier edges -/
def G11_vef (hcef : IsCrossing P {e, f}) : Visit P := ⟨xPair hcef, ⟨e, mem_pair_left _ _⟩⟩
def G11_vfe (hcef : IsCrossing P {e, f}) : Visit P := ⟨xPair hcef, ⟨f, mem_pair_right _ _⟩⟩
def G11_veg (hceg : IsCrossing P {e, g}) : Visit P := ⟨xPair hceg, ⟨e, mem_pair_left _ _⟩⟩
def G11_vge (hceg : IsCrossing P {e, g}) : Visit P := ⟨xPair hceg, ⟨g, mem_pair_right _ _⟩⟩
def G11_vfg (hcfg : IsCrossing P {f, g}) : Visit P := ⟨xPair hcfg, ⟨f, mem_pair_left _ _⟩⟩
def G11_vgf (hcfg : IsCrossing P {f, g}) : Visit P := ⟨xPair hcfg, ⟨g, mem_pair_right _ _⟩⟩

/-- **The three transpositions on the visits of `P`** (`σ_P`). -/
noncomputable def G11_σP (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g})
    (hcfg : IsCrossing P {f, g}) : Equiv.Perm (Visit P) :=
  Equiv.swap (G11_vef hcef) (G11_veg hceg) *
    (Equiv.swap (G11_vfe hcef) (G11_vfg hcfg) * Equiv.swap (G11_vge hceg) (G11_vgf hcfg))

theorem G11_mem_tri_ef (hcef : IsCrossing P {e, f})
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q) :
    (xPair hcef) ∈ geoCarrierCrossings hG.cg T q :=
  htri ((F1.mem_triangleCrossings e f g _).mpr (by simp [triangleSupports, xPair]))

theorem G11_mem_tri_eg (hceg : IsCrossing P {e, g})
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q) :
    (xPair hceg) ∈ geoCarrierCrossings hG.cg T q :=
  htri ((F1.mem_triangleCrossings e f g _).mpr (by simp [triangleSupports, xPair]))

theorem G11_mem_tri_fg (hcfg : IsCrossing P {f, g})
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q) :
    (xPair hcfg) ∈ geoCarrierCrossings hG.cg T q :=
  htri ((F1.mem_triangleCrossings e f g _).mpr (by simp [triangleSupports, xPair]))

/-- **The three carrier edges** `m, p, q` of the configuration: the carrier edges of `x_ef` on `e`, of
`x_ef` on `f`, of `x_eg` on `g`. -/
noncomputable def G11_mE (hcef : IsCrossing P {e, f})
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q) : ZMod (geoCornerCount hG.cg T q) :=
  G11_carrierEdge hn hG hT q (G11_vef hcef) (G11_mem_tri_ef hG q hcef htri)

noncomputable def G11_pE (hcef : IsCrossing P {e, f})
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q) : ZMod (geoCornerCount hG.cg T q) :=
  G11_carrierEdge hn hG hT q (G11_vfe hcef) (G11_mem_tri_ef hG q hcef htri)

noncomputable def G11_qE (hceg : IsCrossing P {e, g})
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q) : ZMod (geoCornerCount hG.cg T q) :=
  G11_carrierEdge hn hG hT q (G11_vge hceg) (G11_mem_tri_eg hG q hceg htri)

variable (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
  (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
  (hX : ExactTriangleVisitOrders P P' e f g hs)
  (halt : ¬ IsAlternating (strandSign P e f) (strandSign P e g) (strandSign P f g))
  (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q)
  (hord : crossingParameter (xPair hcef) e (mem_pair_left _ _) <
    crossingParameter (xPair hceg) e (mem_pair_left _ _))

/-- **A12 (crossings of the configuration).** `{m, p}` carries `x_ef` (A4 with `v = x_ef` on `e`); `{m, q}`
carries `x_eg` (A3: `x_eg` on `e` lies on the same carrier edge as `x_ef` on `e`, by A7; A4); `{p, q}`
carries `x_fg` (A3 on `f` and on `g`; A4). -/
theorem G11_cfg_hmp :
    IsCrossing (geoCornerPolygon hG.cg T q) {G11_mE hn hG hT q hcef htri, G11_pE hn hG hT q hcef htri} := by
  sorry

theorem G11_cfg_hmq (hX : ExactTriangleVisitOrders P P' e f g hs) :
    IsCrossing (geoCornerPolygon hG.cg T q) {G11_mE hn hG hT q hcef htri, G11_qE hn hG hT q hceg htri} := by
  sorry

theorem G11_cfg_hpq (hX : ExactTriangleVisitOrders P P' e f g hs) :
    IsCrossing (geoCornerPolygon hG.cg T q) {G11_pE hn hG hT q hcef htri, G11_qE hn hG hT q hceg htri} := by
  sorry

/-- **A13 (order along `m`).** The parameter of `x_ef` on the carrier edge `m` is below that of `x_eg`: the
carrier edge is a positive rescaling of a sub-segment of `e` (A2), so parameter orders are carried
(`hord`). -/
theorem G11_cfg_order (hX : ExactTriangleVisitOrders P P' e f g hs)
    (hord : crossingParameter (xPair hcef) e (mem_pair_left _ _) <
      crossingParameter (xPair hceg) e (mem_pair_left _ _)) :
    crossingParameter (xPair (G11_cfg_hmp hn hG hT q hcef htri)) (G11_mE hn hG hT q hcef htri)
        (mem_pair_left _ _) <
      crossingParameter (xPair (G11_cfg_hmq hn hG hs hT q hcef hceg htri hX)) (G11_mE hn hG hT q hcef htri)
        (mem_pair_left _ _) := by
  sorry

/-- **A14 (transitive heights).** `crossingSign X m p = crossingSign P e f` etc. (A6) and A11. -/
theorem G11_cfg_trans (halt : ¬ IsAlternating (strandSign P e f) (strandSign P e g) (strandSign P f g)) :
    ¬ IsAlternating (crossingSign (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) (G11_pE hn hG hT q hcef htri))
      (crossingSign (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) (G11_qE hn hG hT q hceg htri))
      (crossingSign (geoCornerPolygon hG.cg T q) (G11_pE hn hG hT q hcef htri) (G11_qE hn hG hT q hceg htri)) := by
  sorry

/-- **A15 (clearance of the carrier polygon, local form).** Every edge of `X` is a sub-segment of an edge of
`P` (`geoCornerPolygon_edgeSegment`, `geo_mark_block`); an edge of `X` other than `m, p, q` is a sub-segment of
an edge `h ≠ e, f, g` (A8, first clause) or of `e, f, g` outside the local sub-segment (cut off by a `T`-corner or
a vertex; by A7 no cut lies between the two local visits, and the line of `e` meets the triangle only in its
side), so it misses the frontier; vertices of `X` are vertices of `P` (A8, second clause) or `T` double points
(not in the triangle: on `e` between the local visits excluded by A7, elsewhere by A8 and
`crossingPoint_injective_of_geometry`). The three double points of `X` are those of `P`
(`G11_carrierEdge_crossingPoint`). -/
theorem G11_cfg_clear_frontier (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hX : ExactTriangleVisitOrders P P' e f g hs) :
    ∀ h : ZMod (geoCornerCount hG.cg T q), h ≠ G11_mE hn hG hT q hcef htri → h ≠ G11_pE hn hG hT q hcef htri →
      h ≠ G11_qE hn hG hT q hceg htri →
      ∀ x ∈ edgeSegment (geoCornerPolygon hG.cg T q) h,
        x ∉ frontier (G11_triangle (geoCornerPolygon hG.cg T q) (G11_cfg_hmp hn hG hT q hcef htri)
          (G11_cfg_hmq hn hG hs hT q hcef hceg htri hX) (G11_cfg_hpq hn hG hs hT q hcef hceg htri hX)) := by
  sorry

theorem G11_cfg_clear_vertex (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hX : ExactTriangleVisitOrders P P' e f g hs) :
    ∀ i : ZMod (geoCornerCount hG.cg T q), geoCornerPolygon hG.cg T q i ∉
      G11_triangle (geoCornerPolygon hG.cg T q) (G11_cfg_hmp hn hG hT q hcef htri)
        (G11_cfg_hmq hn hG hs hT q hcef hceg htri hX) (G11_cfg_hpq hn hG hs hT q hcef hceg htri hX) := by
  sorry

/-- **The configuration of the distinguished carrier** (`X = geoCornerPolygon`; its `D₀` is DEFINITIONALLY
`geoPositiveLift hn hG hT q`). -/
noncomputable def G11_configOf (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {e f g : ZMod n}
    {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (_hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (halt : ¬ IsAlternating (strandSign P e f) (strandSign P e g) (strandSign P f g))
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q)
    (hord : crossingParameter (xPair hcef) e (mem_pair_left _ _) <
      crossingParameter (xPair hceg) e (mem_pair_left _ _)) :
    G11_Config (geoCornerCount hG.cg T q) where
  hk := three_le_geoCornerCount hn hG hT q
  X := geoCornerPolygon hG.cg T q
  gen := geoCarrierShadow_generic hn hG hT q
  m := G11_mE hn hG hT q hcef htri
  p := G11_pE hn hG hT q hcef htri
  q := G11_qE hn hG hT q hceg htri
  hmp := G11_cfg_hmp hn hG hT q hcef htri
  hmq := G11_cfg_hmq hn hG hs hT q hcef hceg htri hX
  hpq := G11_cfg_hpq hn hG hs hT q hcef hceg htri hX
  order := G11_cfg_order hn hG hs hT q hcef hceg htri hX hord
  trans := G11_cfg_trans hn hG hT q hcef hceg htri halt
  clear_frontier := G11_cfg_clear_frontier hn hG hs hT q hcef hceg htri hef heg hfg hX
  clear_vertex := G11_cfg_clear_vertex hn hG hs hT q hcef hceg htri hef heg hfg hX

/-- Sanity: `D₀` of the configuration is the positive lift of the carrier, definitionally. -/
theorem G11_configOf_D₀ :
    (G11_configOf hn hG hs hT q hef heg hfg hcef hceg hcfg hX halt htri hord).D₀ =
      geoPositiveLift hn hG hT q := rfl

end G11ConfigOf

/-! ## Unit F — the record isomorphism `M₁ ≅ D_E` and the assembly -/

section G11Assembly

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {e f g : ZMod n}
  {T : Finset (Crossing P)} {T' : Finset (Crossing P')}
  (hT : GeoIndependent hG.cg T) (hT' : GeoIndependent hG'.cg T')
  (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T')

/-- **F1 (the twisted transport of the key order, R-LOC-2 (1)–(3)).** The traversal-key order of `P` after
the three transpositions `σ_P` is the traversal-key order of `P'` under `visitTransport`: visits on
different edges compare by label (unchanged by both maps); same-edge pairs are carried
(`AV_key_lt_of_gauss`) except the three local pairs, exactly the pairs exchanged by `σ_P`, which are
reversed; a local visit against another visit of its edge compares like its partner (adjacency,
`G11_no_visit_between`). -/
theorem G11_twisted_key_lt (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs) (u v : Visit P) :
    geometricVisitKey hG.cg (G11_σP hcef hceg hcfg u) < geometricVisitKey hG.cg (G11_σP hcef hceg hcfg v) ↔
      geometricVisitKey hG'.cg (visitTransport hs u) < geometricVisitKey hG'.cg (visitTransport hs v) := by
  sorry

/-- **F2 (the transpositions on the lift are the transpositions on the parents).** For the configuration
of the distinguished carrier, `liftVisit ∘ σD = σ_P ∘ liftVisit` (the six local occurrences of the lift have
the six local parent visits, `geoCarrierCrossingEquiv`, `liftVisit_fst`, `G11_carrierEdge_crossingPoint`). -/
theorem G11_liftVisit_σD (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (halt : ¬ IsAlternating (strandSign P e f) (strandSign P e g) (strandSign P f g))
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q)
    (hord : crossingParameter (xPair hcef) e (mem_pair_left _ _) <
      crossingParameter (xPair hceg) e (mem_pair_left _ _))
    (v : (geoPositiveLift hn hG hT q).Γ.Visit) :
    CV.liftVisit hn hG hT q
        ((G11_configOf hn hG hs hT q hef heg hfg hcef hceg hcfg hX halt htri hord).σD v) =
      G11_σP hcef hceg hcfg (CV.liftVisit hn hG hT q v) := by
  sorry

/-- **F3 (the record isomorphism `D₁ ≅ D_E`).** Given the core's output on `D₀ = geoPositiveLift q` and the
twisted key transport, the bijection `Φ = Λ ∘ Ψ⁻¹` (`Λ` the parent-visit identification of the two lifts
through `visitTransport`, as in `EXT_homfly_wall`) satisfies CV:def:record (a)–(d): (a) `visitBetween_iff_key`
on both lifts, the core's twisted clause, F2 and F1 through `GT_cyc_congr_of_lt`; (b) `liftVisit_twin`,
`visitTransport_visitTwin`; (c) the over bit of a positive lift is the divide sign, carried by `hdet`;
(d) all signs are `+1`. -/
theorem G11_recordIsoData (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (hdet : ∀ i j : ZMod n, IsCrossing P {i, j} →
      (0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i) (edge P' j)))
    (hcarr : geoCarrierCrossings hG'.cg T' q' =
      (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q)
    (D₁ : Diagram) (Ψ : (geoPositiveLift hn hG hT q).Γ.Visit ≃ D₁.Γ.Visit)
    (σ : Equiv.Perm (geoPositiveLift hn hG hT q).Γ.Visit)
    (hσ : ∀ v, CV.liftVisit hn hG hT q (σ v) = G11_σP hcef hceg hcfg (CV.liftVisit hn hG hT q v))
    (htw : ∀ v, Ψ ((geoPositiveLift hn hG hT q).twin v) = D₁.twin (Ψ v))
    (hbit : ∀ v, D₁.overBit (Ψ v) = (geoPositiveLift hn hG hT q).overBit v)
    (hsgn : ∀ v, D₁.sign (Ψ v).1 = (geoPositiveLift hn hG hT q).sign v.1)
    (hcyc : ∀ u v w, D₁.VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔
      (geoPositiveLift hn hG hT q).VisitBetween (σ u) (σ v) (σ w)) :
    ∃ Φ : D₁.Γ.Visit ≃ (geoPositiveLift hn hG' hT' q').Γ.Visit,
      CV.IsRecordIsoData D₁ (geoPositiveLift hn hG' hT' q') Φ := by
  sorry

/-- **The main case** (`f` met before `g` along `e`): `D_P = D₀ →(core) D₁ ≅ D_E`. PROVED from the leaves. -/
theorem G11_strong_case (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (hdet : ∀ i j : ZMod n, IsCrossing P {i, j} →
      (0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i) (edge P' j)))
    (halt : ¬ IsAlternating (strandSign P e f) (strandSign P e g) (strandSign P f g))
    (hcarr : geoCarrierCrossings hG'.cg T' q' =
      (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q)
    (hord : crossingParameter (xPair hcef) e (mem_pair_left _ _) <
      crossingParameter (xPair hceg) e (mem_pair_left _ _)) :
    homfly (geoPositiveLift hn hG' hT' q') = homfly (geoPositiveLift hn hG hT q) := by
  obtain ⟨D₁, Ψ, hD₁, hhom, htw, hbit, hsgn, hcyc⟩ :=
    G11_core (G11_configOf hn hG hs hT q hef heg hfg hcef hceg hcfg hX halt htri hord)
  obtain ⟨Φ, hΦ⟩ := G11_recordIsoData hn hG hG' hs hT hT' q q' hef heg hfg hcef hceg hcfg hX hdet hcarr
    htri D₁ Ψ _ (G11_liftVisit_σD hn hG hs hT q hef heg hfg hcef hceg hcfg hX halt htri hord) htw hbit
    hsgn hcyc
  have h1 : homfly D₁ = homfly (geoPositiveLift hn hG' hT' q') :=
    CV.gausscode_polynomial D₁ _ hD₁ rfl (CV.recordIsoOfData hD₁ rfl Φ hΦ)
  exact h1.symm.trans hhom

end G11Assembly

/-! ## The strong G11 (with the three crossing hypotheses), the literal `GT_G11`, and the row -/

/-- **`GT_G11` with the three crossing hypotheses** — the form the consumer `GT_empty_groupedPoly_eq`
actually has available (`hef' heg' hfg'`) and the form the RIII route proves. -/
def GT_G11_strong : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) {P P' : LabelledTuple n}
    (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (e f g : ZMod n),
    e ≠ f → e ≠ g → f ≠ g →
    IsCrossing P {e, f} → IsCrossing P {e, g} → IsCrossing P {f, g} →
    ExactTriangleVisitOrders P P' e f g hs →
    (∀ i j : ZMod n, IsCrossing P {i, j} →
      (0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i) (edge P' j))) →
    ¬ IsAlternating (strandSign P e f) (strandSign P e g) (strandSign P f g) →
    ∀ {T : Finset (Crossing P)} {T' : Finset (Crossing P')}
      (hT : GeoIndependent hG.cg T) (hT' : GeoIndependent hG'.cg T')
      (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T'),
      geoCarrierCrossings hG'.cg T' q' =
        (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding →
      triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q →
      homfly (geoPositiveLift hn hG' hT' q') = homfly (geoPositiveLift hn hG hT q)

/-- **Leaf F0.** The two local crossing parameters on `e` differ (distinct double points on one edge:
`crossingPoint_injective_of_geometry`, `edgePoint_injective`). -/
theorem G11_param_ne {P : LabelledTuple n} (hG : CarrierGeometry P) {e f g : ZMod n} (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) :
    crossingParameter (xPair hcef) e (mem_pair_left _ _) ≠
      crossingParameter (xPair hceg) e (mem_pair_left _ _) := by
  classical
  intro heq
  have h1 := (crossingParameter_spec (xPair hcef) e (mem_pair_left _ _)).2.2
  have h2 := (crossingParameter_spec (xPair hceg) e (mem_pair_left _ _)).2.2
  have hpt : crossingPoint (xPair hcef) = crossingPoint (xPair hceg) := by rw [h1, h2, heq]
  have hc := crossingPoint_injective_of_geometry hG.cg hpt
  have hval : ({e, f} : Finset (ZMod n)) = {e, g} := congrArg Subtype.val hc
  have hf : f ∈ ({e, g} : Finset (ZMod n)) := by rw [← hval]; exact mem_pair_right e f
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with hf | hf
  · have hcard := crossing_card_two (xPair hcef)
    change ({e, f} : Finset (ZMod n)).card = 2 at hcard
    rw [hf, Finset.pair_eq_singleton, Finset.card_singleton] at hcard
    exact absurd hcard (by norm_num)
  · exact hfg hf

omit [NeZero n] in
theorem G11_isCrossing_comm {P : LabelledTuple n} {f g : ZMod n} (h : IsCrossing P {f, g}) :
    IsCrossing P {g, f} := by
  rwa [Finset.pair_comm]

/-- **`GT_G11_strong` PROVED from the leaves**: relabel so that `f` is met before `g` along `e` (F0, A9, A10),
then the main case. -/
theorem GT_G11_strong_proof : GT_G11_strong := by
  intro n _ hn P P' hG hG' hs e f g hef heg hfg hcef hceg hcfg hX hdet halt T T' hT hT' q q' hcarr htri
  rcases lt_or_gt_of_ne (G11_param_ne hG hfg hcef hceg) with hord | hord
  · exact G11_strong_case hn hG hG' hs hT hT' q q' hef heg hfg hcef hceg hcfg hX hdet halt hcarr htri hord
  · exact G11_strong_case hn hG hG' hs hT hT' q q' heg hef (Ne.symm hfg) hceg hcef
      (G11_isCrossing_comm hcfg) (G11_exact_swap hs hX) hdet (G11_alt_swap halt) hcarr
      (by rw [G11_triangleCrossings_swap]; exact htri) hord

/-! ### The literal `GT_G11`: the branches where not all three local pairs are crossings -/

/-- **Leaf X1 (at most one local crossing: a plain record isomorphism).** If at most one of the three pairs is
a crossing of `P`, no same-edge pair is reversed by `ExactTriangleVisitOrders`, so `AV_key_lt_of_gauss`
carries every key order and `EXT_homfly_wall` applies. -/
theorem G11_le_one_crossing (hn : 3 ≤ n) {P P' : LabelledTuple n}
    (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (e f g : ZMod n)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (hdet : ∀ i j : ZMod n, IsCrossing P {i, j} →
      (0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i) (edge P' j)))
    {T : Finset (Crossing P)} {T' : Finset (Crossing P')}
    (hT : GeoIndependent hG.cg T) (hT' : GeoIndependent hG'.cg T')
    (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T')
    (hcarr : geoCarrierCrossings hG'.cg T' q' =
      (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)
    (hcard : (triangleCrossings P e f g).card ≤ 1) :
    homfly (geoPositiveLift hn hG' hT' q') = homfly (geoPositiveLift hn hG hT q) := by
  sorry

/-- **Leaf X2 (exactly two local crossings: impossible — FLAGGED).** With exactly two of the three pairs
crossings of `P` (and of `P'`), `ExactTriangleVisitOrders` reverses exactly ONE adjacent same-edge pair of
two distinct crossings and carries every other same-edge order, so the Gauss words of `P` and `P'` differ
by one adjacent transposition of occurrences of two distinct symbols. This violates Gauss's parity
condition for closed plane curves (an even number of occurrences between the two occurrences of every
symbol) for one of `P`, `P'`. **Gauss parity is NOT in the accepted library**; this leaf is the only one
we cannot see how to close with `work/lean` (it is true). It is NOT needed for the row: see
`generic_transport` below, which uses `GT_G11_strong` directly. -/
-- NOT ON THE ROW'S PATH: `generic_transport` is derived through `GT_G11_strong` only; this leaf is used solely
-- by the literal `GT_G11_proof` (and `generic_transport_of_GT_G11`) and may stay unproved / be dropped at port time.
theorem G11_two_crossings_absurd (hn : 3 ≤ n) {P P' : LabelledTuple n}
    (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (e f g : ZMod n)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (hcard : (triangleCrossings P e f g).card = 2) : False := by
  sorry

/-- **Leaf X3 (counting).** The three pairs are crossings iff the triangle has three members; the card is
`≤ 1`, `= 2` or `= 3`. -/
theorem G11_card_cases {P : LabelledTuple n} (e f g : ZMod n) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    (triangleCrossings P e f g).card ≤ 1 ∨ (triangleCrossings P e f g).card = 2 ∨
      (IsCrossing P {e, f} ∧ IsCrossing P {e, g} ∧ IsCrossing P {f, g}) := by
  sorry

/-- **`GT_G11` PROVED** from `GT_G11_strong` and the branch leaves X1–X3. -/
theorem GT_G11_proof : GT_G11 := by
  intro n _ hn P P' hG hG' hs e f g hef heg hfg hX hdet halt T T' hT hT' q q' hcarr htri
  rcases G11_card_cases (P := P) e f g hef heg hfg with hle | h2 | ⟨hcef, hceg, hcfg⟩
  · exact G11_le_one_crossing hn hG hG' hs e f g hef heg hfg hX hdet hT hT' q q' hcarr hle
  · exact (G11_two_crossings_absurd hn hG hG' hs e f g hef heg hfg hX h2).elim
  · exact GT_G11_strong_proof n hn hG hG' hs e f g hef heg hfg hcef hceg hcfg hX hdet halt hT hT' q q'
      hcarr htri

/-! ### The row theorem, from `GT_G11_strong` alone (the accepted assembly of X1Rows3 with the strong
hypothesis threaded through `GT_empty_groupedPoly_eq`) -/

section G11Row

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- `GT_empty_groupedPoly_eq` of X1Rows3, word for word, with `GT_G11_strong` in place of `GT_G11` (the three
crossing hypotheses `hef' heg' hfg'` are in scope there). -/
theorem G11_empty_groupedPoly_eq (hG11 : GT_G11_strong) (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hgen : ¬ ExtremeLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
    (q : GeoComponent (geomAt E t ht.1) Q) :
    CV.groupedPoly hn (genericAt E t' ht'.1) hQi' (GT_carrierEquiv (GT_empty_wall hL hR hef heg hfg ht ht' hop hs hQ) q) =
      CV.groupedPoly hn (genericAt E t ht.1) hQi q := by
  set W := GT_empty_wall hL hR hef heg hfg ht ht' hop hs hQ
  have hX := GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q
  have hdet : ∀ i j : ZMod n, IsCrossing (E.curve t) {i, j} →
      (0 < det (edge (E.curve t) i) (edge (E.curve t) j) ↔
        0 < det (edge (E.curve t') i) (edge (E.curve t') j)) :=
    fun i j hij => GT_det_pos_iff_of_sign (hR.sign_eq t t' ht ht' i j hij)
  rw [GT_groupedPoly_eq_homfly, GT_groupedPoly_eq_homfly]
  unfold CV.carrierDiagram
  by_cases htri : ∃ v : Visit (E.curve t), v.1.val ∈ triangleSupports e f g ∧
      geoOwner (geomAt E t ht.1) Q (Sum.inr v) = q
  · obtain ⟨v, hv, hvq⟩ := htri
    exact hG11 n hn (CarrierGeometry.ofDiagrammatic ((genericAt E t ht.1).diagrammatic hn))
      (CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)) hs e f g hef heg hfg
      hef' heg' hfg' (hL.gauss_words t t' ht ht' hop hs) hdet
      ((hGT.generic_iff_nonalternating t ht hef' heg' hfg').mp hgen) _ _ q _ hX
      (GT_empty_tri_subset hL hef heg hfg ht hQ hfull q hv hvq)
  · have htri' : ∀ v : Visit (E.curve t), v.1.val ∈ triangleSupports e f g →
        geoOwner (geomAt E t ht.1) Q (Sum.inr v) ≠ q := fun v hv hq => htri ⟨v, hv, hq⟩
    refine EXT_homfly_wall hn _ _ hs _ _ q _ hX ?_ ?_
    · intro v w hv hw
      have hvT : v.1.val ∉ triangleSupports e f g := fun h =>
        htri' v h (((mem_geoCarrierCrossings _ Q q v.1).mp hv).2 v rfl)
      exact W.key_lt v w (GT_not_rev_of_not_mem_left
        (fun h => hvT ((F1.mem_triangleCrossings e f g v.1).mp h)))
    · intro v _
      exact hdet _ _ (by rw [← visit_crossing_val_eq_pair v]; exact v.1.property)

/-- `GT_173_empty_row` with `GT_G11_strong`. -/
theorem G11_173_empty_row (hG11 : GT_G11_strong) (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
      (hfg' : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef' heg' hfg' →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t ht.1) Q = rowTerm hn (genericAt E t' ht'.1) (transportSupport hs Q) := by
  intro t t' ht ht' hop hs hef' heg' hfg' hgen Q hQ hfull
  have W := GT_empty_wall hL hR hef heg hfg ht ht' hop hs hQ
  have hQi : Q ∈ CV.Ind (geomAt E t ht.1) := ((F1.mem_outsideSupports _ e f g Q).mp hQ).1
  have hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1) :=
    ((F1.mem_outsideSupports _ e f g _).mp (GT_outsideSupports_transport hL ht ht' hop hs hQ)).1
  refine AV_rowTerm_eq_of_summandTransport hn (genericAt E t ht.1) (genericAt E t' ht'.1) hQi hQi'
    ⟨GT_wind_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W, GT_carrierEquiv W, fun q =>
      ⟨GT_weight_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W q,
        GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W hQi hQi' q, ?_, ?_, ?_⟩⟩
  · rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi,
      GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q, Finset.card_map]
  · exact G11_empty_groupedPoly_eq hG11 hn hL hGT hR hef heg hfg ht ht' hop hs hef' heg' hfg' hgen hQ hfull
      hQi hQi' q
  · unfold CV.Omega1 CV.slot
    rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi,
      GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q, Finset.card_map,
      GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W hQi hQi' q,
      G11_empty_groupedPoly_eq hG11 hn hL hGT hR hef heg hfg ht ht' hop hs hef' heg' hfg' hgen hQ hfull hQi hQi' q]

/-- `GT_genericTransportData` with `GT_G11_strong`. -/
theorem G11_genericTransportData (hG11 : GT_G11_strong) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) : GenericTransportData hn E e f g δ where
  canonical_branch := PRE_173_canonical_branch hGT
  empty_row := G11_173_empty_row hG11 hn hL hGT hR hef heg hfg
  endpoint_rows_canonical := GT_173_endpoint_rows_canonical hn hL hGT hR hef heg hfg
  endpoint_rows_relabelled := GT_173_endpoint_rows_relabelled hn hL hGT hR hef heg hfg

end G11Row

/-- **Row 173, R:generic_transport** (fixed name `RProof.generic_transport`, the statement shape of the
sibling rows `exterior` / `availability_zero_one`): the accepted assembly `GT_generic_transport_of_G11`
with `GT_G11_strong_proof` — the row does NOT depend on the flagged branch leaf `G11_two_crossings_absurd`. -/
theorem generic_transport (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericTransportData hn E e f g δ := by
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
  exact G11_genericTransportData GT_G11_strong_proof hn hL' hGT' hR' hef heg hfg

-- NOT ON THE ROW'S PATH (uses the flagged leaf X2 through `GT_G11_proof`); `generic_transport` above is the row.
/-- The row also follows from the literal `GT_G11` through the accepted `GT_generic_transport_of_G11`
(this path uses the flagged leaf). -/
theorem generic_transport_of_GT_G11 (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericTransportData hn E e f g δ :=
  GT_generic_transport_of_G11 GT_G11_proof hn E e f g h3 h4e h4f h4g hE

end RProof
