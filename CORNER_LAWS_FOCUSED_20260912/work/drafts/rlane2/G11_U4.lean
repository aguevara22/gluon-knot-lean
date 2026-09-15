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

/-! ### U4 helpers (general): plane algebra, labels, shadow genericity read at label level -/

theorem gu4_det_add_left (u v w : Plane) : det (u + v) w = det u w + det v w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem gu4_det_add_right (u v w : Plane) : det u (v + w) = det u v + det u w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem gu4_det_sub_left (u v w : Plane) : det (u - v) w = det u w - det v w := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem gu4_det_sub_right (u v w : Plane) : det u (v - w) = det u v - det u w := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem gu4_det_smul_left (c : ℝ) (u v : Plane) : det (c • u) v = c * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem gu4_det_smul_right (c : ℝ) (u v : Plane) : det u (c • v) = c * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem gu4_det_self (u : Plane) : det u u = 0 := by
  simp only [det]; ring

/-- Cramer's rule: a vector in the frame `(u, v)`, `det u v ≠ 0`. -/
theorem gu4_cramer (u v z : Plane) (h : det u v ≠ 0) :
    z = (det z v / det u v) • u + (det u z / det u v) • v := by
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff h]
    simp only [det]
    ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff h]
    simp only [det]
    ring

/-- Two points with the same two frame coordinates coincide. -/
theorem gu4_eq_of_det_eq {u v : Plane} (h : det u v ≠ 0) {y z : Plane}
    (h1 : det y v = det z v) (h2 : det u y = det u z) : y = z := by
  rw [gu4_cramer u v y h, gu4_cramer u v z h, h1, h2]

/-- the labels of a crossing pair are remote -/
theorem gu4_remote_of_isCrossing {j : ℕ} {Y : LabelledTuple j} {a b : ZMod j}
    (h : IsCrossing Y {a, b}) : remote a b := by
  obtain ⟨i, l, hs, hr, -⟩ := h
  have ha : a ∈ ({i, l} : Finset (ZMod j)) := hs ▸ Finset.mem_insert_self a {b}
  have hb : b ∈ ({i, l} : Finset (ZMod j)) :=
    hs ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have hi : i ∈ ({a, b} : Finset (ZMod j)) := hs ▸ Finset.mem_insert_self i {l}
  have hl : l ∈ ({a, b} : Finset (ZMod j)) :=
    hs ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self l)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hi hl
  have hil : i ≠ l := (remote_endpoints i l hr).1.symm
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · rcases hl with h | h <;> exact absurd h.symm hil
    · exact hr
  · rcases hb with rfl | rfl
    · exact remote_symm hr
    · rcases hi with h | h <;> exact absurd h hil

theorem gu4_ne_of_remote {j : ℕ} {a b : ZMod j} (h : remote a b) : a ≠ b :=
  fun he => (remote_endpoints a b h).1 he.symm

/-! shadow genericity of a one-component shadow, read at label level -/

theorem gu4_gen_regular {j : ℕ} {hj : 3 ≤ j} {Y : LabelledTuple j}
    (hY : (Shadow.single ⟨j, hj, Y⟩).Generic) : Regular Y := hY.regular 0

theorem gu4_gen_tail {j : ℕ} {hj : 3 ≤ j} {Y : LabelledTuple j}
    (hY : (Shadow.single ⟨j, hj, Y⟩).Generic) (a b : ZMod j) (h : ¬ incident a b) :
    Y a ∉ edgeSegment Y b :=
  hY.tail_off ⟨0, a⟩ ⟨0, b⟩ (fun hinc => h ((Shadow.single_incidentTail_iff _ _ _).mp hinc))

theorem gu4_gen_trans {j : ℕ} {hj : 3 ≤ j} {Y : LabelledTuple j}
    (hY : (Shadow.single ⟨j, hj, Y⟩).Generic) (a b : ZMod j) (h : ¬ adjacent a b)
    (hm : (edgeSegment Y a ∩ edgeSegment Y b).Nonempty) : det (edge Y a) (edge Y b) ≠ 0 :=
  hY.transverse ⟨0, a⟩ ⟨0, b⟩ (fun hadj => h ((Shadow.single_adjacent_iff _ _ _).mp hadj)) hm

theorem gu4_gen_triple {j : ℕ} {hj : 3 ≤ j} {Y : LabelledTuple j}
    (hY : (Shadow.single ⟨j, hj, Y⟩).Generic) :
    ¬ ∃ a b c : ZMod j, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      (edgeInterior Y a ∩ edgeInterior Y b ∩ edgeInterior Y c).Nonempty := by
  rintro ⟨a, b, c, hab, hbc, hac, hne⟩
  refine hY.no_triple ⟨⟨0, a⟩, ⟨0, b⟩, ⟨0, c⟩, ?_, ?_, ?_, hne⟩
  · exact fun h => hab (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  · exact fun h => hbc (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  · exact fun h => hac (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

/-- the double point of a crossing of a generic one-component shadow lies in the open edges -/
theorem gu4_crossingPoint_mem_interior {j : ℕ} {hj : 3 ≤ j} {Y : LabelledTuple j}
    (hY : (Shadow.single ⟨j, hj, Y⟩).Generic) {a b : ZMod j} (h : IsCrossing Y {a, b}) :
    crossingPoint (xPair h) ∈ edgeInterior Y a ∧ crossingPoint (xPair h) ∈ edgeInterior Y b := by
  let x : (Shadow.single ⟨j, hj, Y⟩).Crossing :=
    (Shadow.singleCrossingEquiv ⟨j, hj, Y⟩).symm (xPair h)
  have hx : (Shadow.single ⟨j, hj, Y⟩).crossingPoint x = crossingPoint (xPair h) := by
    rw [Shadow.single_crossingPoint _ hY x, Equiv.apply_symm_apply]
  have hmem : ∀ s : (Shadow.single ⟨j, hj, Y⟩).Strand,
      s ∈ x.val ↔ Shadow.singleStrandEquiv _ s ∈ ({a, b} : Finset (ZMod j)) := by
    intro s
    rw [← Shadow.mem_singleCrossingEquiv_iff, Equiv.apply_symm_apply]
    rfl
  constructor
  · have := hY.crossingPoint_mem_interior x ((hmem ⟨0, a⟩).mpr (Finset.mem_insert_self a {b}))
    rwa [hx] at this
  · have := hY.crossingPoint_mem_interior x ((hmem ⟨0, b⟩).mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)))
    rwa [hx] at this

/-- a crossing point is on both closed edges -/
theorem gu4_crossingPoint_mem_pair {j : ℕ} {Y : LabelledTuple j} {a b : ZMod j}
    (h : IsCrossing Y {a, b}) :
    crossingPoint (xPair h) ∈ edgeSegment Y a ∧ crossingPoint (xPair h) ∈ edgeSegment Y b :=
  ⟨crossingPoint_mem (xPair h) a (mem_pair_left _ _), crossingPoint_mem (xPair h) b (mem_pair_right _ _)⟩

/-- an edge whose ends are `Q + s₀ • u`, `Q + s₁ • u` (`s₀ < s₁`) is the parameter interval `[s₀, s₁]` -/
theorem gu4_mem_edgeSegment_iff {j : ℕ} (Y : LabelledTuple j) (i : ZMod j) {Q u : Plane}
    {s₀ s₁ : ℝ} (h0 : Y i = Q + s₀ • u) (h1 : Y (i + 1) = Q + s₁ • u) (hlt : s₀ < s₁) (y : Plane) :
    y ∈ edgeSegment Y i ↔ ∃ t, s₀ ≤ t ∧ t ≤ s₁ ∧ y = Q + t • u := by
  have hlt' : 0 < s₁ - s₀ := sub_pos.mpr hlt
  constructor
  · rintro ⟨θ, h0θ, h1θ, rfl⟩
    refine ⟨s₀ + θ * (s₁ - s₀), by nlinarith, by nlinarith, ?_⟩
    simp only [edgePoint, edge, h0, h1]
    refine Prod.ext ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul] <;> ring
  · rintro ⟨t, ht0, ht1, rfl⟩
    refine ⟨(t - s₀) / (s₁ - s₀), div_nonneg (by linarith) hlt'.le,
      (div_le_one hlt').mpr (by linarith), ?_⟩
    simp only [edgePoint, edge, h0, h1]
    refine Prod.ext ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul] <;> field_simp <;> ring

/-- the open edge, likewise -/
theorem gu4_mem_edgeInterior_iff {j : ℕ} (Y : LabelledTuple j) (i : ZMod j) {Q u : Plane}
    {s₀ s₁ : ℝ} (h0 : Y i = Q + s₀ • u) (h1 : Y (i + 1) = Q + s₁ • u) (hlt : s₀ < s₁) (y : Plane) :
    y ∈ edgeInterior Y i ↔ ∃ t, s₀ < t ∧ t < s₁ ∧ y = Q + t • u := by
  have hlt' : 0 < s₁ - s₀ := sub_pos.mpr hlt
  constructor
  · rintro ⟨θ, h0θ, h1θ, rfl⟩
    refine ⟨s₀ + θ * (s₁ - s₀), by nlinarith, by nlinarith, ?_⟩
    simp only [edgePoint, edge, h0, h1]
    refine Prod.ext ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul] <;> ring
  · rintro ⟨t, ht0, ht1, rfl⟩
    refine ⟨(t - s₀) / (s₁ - s₀), div_pos (by linarith) hlt',
      (div_lt_one hlt').mpr (by linarith), ?_⟩
    simp only [edgePoint, edge, h0, h1]
    refine Prod.ext ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul] <;> field_simp <;> ring

/-- **Convexity capture.** If a convex set `U` contains a point of the edge `i` of `Y` and a point of
its line, but neither endpoint of the edge, the point of the line lies on the edge. -/
theorem gu4_mem_edgeSegment_of_convex {j : ℕ} {Y : LabelledTuple j} {i : ZMod j} {U : Set Plane}
    (hU : Convex ℝ U) (h0 : Y i ∉ U) (h1 : Y (i + 1) ∉ U) {x : Plane} (hx : x ∈ edgeSegment Y i)
    (hxU : x ∈ U) {θ : ℝ} (hyU : Y i + θ • edge Y i ∈ U) : Y i + θ • edge Y i ∈ edgeSegment Y i := by
  obtain ⟨sx, hsx0, hsx1, rfl⟩ := hx
  rcases lt_or_ge θ 0 with hneg | hnn
  · exfalso
    apply h0
    have hd : 0 < sx - θ := by linarith
    have hmem : (sx / (sx - θ)) • (Y i + θ • edge Y i) + (-θ / (sx - θ)) • edgePoint Y i sx ∈ U :=
      hU hyU hxU (div_nonneg hsx0 hd.le) (div_nonneg (by linarith) hd.le)
        (by rw [← add_div, div_eq_one_iff_eq hd.ne']; ring)
    convert hmem using 1
    simp only [edgePoint]
    refine Prod.ext ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      field_simp <;> ring
  rcases lt_or_ge 1 θ with hgt | hle
  · exfalso
    apply h1
    have hd : 0 < θ - sx := by linarith
    have hmem : ((1 - sx) / (θ - sx)) • (Y i + θ • edge Y i) + ((θ - 1) / (θ - sx)) • edgePoint Y i sx
        ∈ U :=
      hU hyU hxU (div_nonneg (by linarith) hd.le) (div_nonneg (by linarith) hd.le)
        (by rw [← add_div, div_eq_one_iff_eq hd.ne']; ring)
    convert hmem using 1
    have he : Y (i + 1) = Y i + edge Y i := by simp [edge]
    rw [he]
    simp only [edgePoint]
    refine Prod.ext ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      field_simp <;> ring
  · exact ⟨θ, hnn, hle, rfl⟩

/-! ### U4 helpers: the frame `(a; dm, v)` of the configuration and the functionals `α, β, γ` -/

/-- the three double points `a = x_mp`, `b = x_mq`, `c = x_pq` -/
noncomputable def gu4_a (_π : G11_Params C) : Plane := crossingPoint (xPair C.hmp)
noncomputable def gu4_b (_π : G11_Params C) : Plane := crossingPoint (xPair C.hmq)
noncomputable def gu4_c (_π : G11_Params C) : Plane := crossingPoint (xPair C.hpq)
/-- the parameters of `a`, `b` on `m` -/
noncomputable def gu4_tmp (_π : G11_Params C) : ℝ :=
  crossingParameter (xPair C.hmp) C.m (mem_pair_left _ _)
noncomputable def gu4_tmq (_π : G11_Params C) : ℝ :=
  crossingParameter (xPair C.hmq) C.m (mem_pair_left _ _)
/-- the direction of `m` and the frame vector `v = c − a` -/
noncomputable def gu4_dm (_π : G11_Params C) : Plane := edge C.X C.m
noncomputable def gu4_v (π : G11_Params C) : Plane := π.gu4_c - π.gu4_a
/-- the frame determinant `E = det dm v ≠ 0` -/
noncomputable def gu4_E (π : G11_Params C) : ℝ := det π.gu4_dm π.gu4_v
/-- the frame functionals: `α` vanishes on the line `p` (through `a, c`), `β` on the line `m`, `γ` on
the line `q` (through `b, c`) -/
noncomputable def gu4_α (π : G11_Params C) (y : Plane) : ℝ := det (y - π.gu4_a) π.gu4_v
noncomputable def gu4_β (π : G11_Params C) (y : Plane) : ℝ := det π.gu4_dm (y - π.gu4_a)
noncomputable def gu4_γ (π : G11_Params C) (y : Plane) : ℝ := det (y - π.gu4_b) (π.gu4_c - π.gu4_b)
/-- the three flat vertices `p_in, m₀, p_out` -/
noncomputable def gu4_pin (π : G11_Params C) : Plane := edgePoint C.X C.m π.t₁
noncomputable def gu4_m0 (π : G11_Params C) : Plane := edgePoint C.X C.m π.t₂
noncomputable def gu4_pout (π : G11_Params C) : Plane := edgePoint C.X C.m π.t₃

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

theorem gu4_remote_mp (_π : G11_Params C) : remote C.m C.p := gu4_remote_of_isCrossing C.hmp
theorem gu4_remote_mq (_π : G11_Params C) : remote C.m C.q := gu4_remote_of_isCrossing C.hmq
theorem gu4_remote_pq (_π : G11_Params C) : remote C.p C.q := gu4_remote_of_isCrossing C.hpq

theorem gu4_det_mp (π : G11_Params C) : det (edge C.X C.m) (edge C.X C.p) ≠ 0 :=
  gu4_gen_trans C.gen _ _ π.gu4_remote_mp ⟨π.gu4_a, π.gu4_a_mem_m, π.gu4_a_mem_p⟩
theorem gu4_det_mq (π : G11_Params C) : det (edge C.X C.m) (edge C.X C.q) ≠ 0 :=
  gu4_gen_trans C.gen _ _ π.gu4_remote_mq ⟨π.gu4_b, π.gu4_b_mem_m, π.gu4_b_mem_q⟩
theorem gu4_det_pq (π : G11_Params C) : det (edge C.X C.p) (edge C.X C.q) ≠ 0 :=
  gu4_gen_trans C.gen _ _ π.gu4_remote_pq ⟨π.gu4_c, π.gu4_c_mem_p, π.gu4_c_mem_q⟩

/-- two points of one closed edge differ by a multiple of the edge -/
theorem gu4_sub_of_mem_edge {j : ℕ} {Y : LabelledTuple j} {i : ZMod j} {y z : Plane}
    (hy : y ∈ edgeSegment Y i) (hz : z ∈ edgeSegment Y i) : ∃ κ : ℝ, z - y = κ • edge Y i := by
  obtain ⟨s, -, -, rfl⟩ := hy
  obtain ⟨t, -, -, rfl⟩ := hz
  refine ⟨t - s, ?_⟩
  simp only [edgePoint, sub_smul]
  abel

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

theorem gu4_mval_lt (_π : G11_Params C) : C.m.val < k := ZMod.val_lt C.m

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

theorem gu4_p_ne_m (π : G11_Params C) : C.p ≠ C.m := (remote_endpoints _ _ π.gu4_remote_mp).1
theorem gu4_q_ne_m (π : G11_Params C) : C.q ≠ C.m := (remote_endpoints _ _ π.gu4_remote_mq).1
theorem gu4_q_ne_p (π : G11_Params C) : C.q ≠ C.p := (remote_endpoints _ _ π.gu4_remote_pq).1

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
theorem gu4_centroid_mem_Δ (_π : G11_Params C) :
    G11_centroid C ∈ G11_triangle C.X C.hmp C.hmq C.hpq := by
  unfold G11_centroid G11_triangle
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
  refine ⟨(1 / (1 + π.r)) • y + (π.r / (1 + π.r)) • G11_centroid C,
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

theorem gu4_edgePoint_m_injective (π : G11_Params C) : Function.Injective (edgePoint C.X C.m) :=
  edgePoint_injective π.gu4_dm_ne

theorem gu4_lam_pos : 0 < π.lam := zero_lt_one.trans π.hlam

/-- the parameter of `y_p` on `[w, p_out]` -/
noncomputable def gu4_σp (π : G11_Params C) : ℝ :=
  (π.lam - 1) * (π.t₂ - π.gu4_tmp) / ((π.lam - 1) * (π.t₂ - π.gu4_tmp) + (π.t₃ - π.gu4_tmp))
/-- the parameter of `y_q` on `[p_in, w]` -/
noncomputable def gu4_σq (π : G11_Params C) : ℝ :=
  (π.gu4_tmq - π.t₁) / ((π.gu4_tmq - π.t₁) + (π.lam - 1) * (π.gu4_tmq - π.t₂))
noncomputable def gu4_yp (π : G11_Params C) : Plane := π.apex + π.gu4_σp • (π.gu4_pout - π.apex)
noncomputable def gu4_yq (π : G11_Params C) : Plane := π.gu4_pin + π.gu4_σq • (π.apex - π.gu4_pin)

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

/-- **D1.** `U` is a disc (`IsDisc`: convex, compact, nonempty interior) — the image of the convex hull of
three affinely independent points under a homothety. -/
theorem disc_isDisc : IsDisc π.U := by
  sorry

/-- **D2.** The closed triangle lies in the open disc. -/
theorem triangle_sub_interior : G11_triangle C.X C.hmp C.hmq C.hpq ⊆ interior π.U := by
  sorry

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

/-- **A2.** The carrier edge through `v` is a positive rescaling of the original edge `v.2.val` and carries
the double point of `v` (`geoCornerPolygon_edge_smul`, `geo_mark_block`). -/
theorem G11_carrierEdge_spec (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg T q) :
    crossingPoint v.1 ∈ edgeSegment (geoCornerPolygon hG.cg T q) (G11_carrierEdge hn hG hT q v hv) ∧
    ∃ c : ℝ, 0 < c ∧ edge (geoCornerPolygon hG.cg T q) (G11_carrierEdge hn hG hT q v hv) =
      c • edge P v.2.val := by
  sorry

/-- **A3.** Two retained visits on one original edge with no crossing of `P` strictly between them lie on
the same carrier edge (no corner — no `T`-crossing and no vertex — separates them). -/
theorem G11_carrierEdge_eq_of_adjacent {v w : Visit P} (hv : v.1 ∈ geoCarrierCrossings hG.cg T q)
    (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) (he : v.2.val = w.2.val)
    (hadj : ∀ y : Visit P, y.2.val = v.2.val →
      ¬ (visitParameter v < visitParameter y ∧ visitParameter y < visitParameter w) ∧
      ¬ (visitParameter w < visitParameter y ∧ visitParameter y < visitParameter v)) :
    G11_carrierEdge hn hG hT q v hv = G11_carrierEdge hn hG hT q w hw := by
  sorry

/-- **A4.** The carrier edges of the two visits of a retained crossing cross in `X`, at the same double
point (`geoCarrierCrossingEquiv`, `crossingPoint_geoCarrierCrossingEquiv`). -/
theorem G11_carrierEdge_isCrossing (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg T q) :
    IsCrossing (geoCornerPolygon hG.cg T q)
      {G11_carrierEdge hn hG hT q v hv,
       G11_carrierEdge hn hG hT q (visitTwin v) (by rw [visitTwin_crossing]; exact hv)} := by
  sorry

theorem G11_carrierEdge_crossingPoint (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg T q)
    (hc : IsCrossing (geoCornerPolygon hG.cg T q)
      {G11_carrierEdge hn hG hT q v hv,
       G11_carrierEdge hn hG hT q (visitTwin v) (by rw [visitTwin_crossing]; exact hv)}) :
    crossingPoint (xPair hc) = crossingPoint v.1 := by
  sorry

/-- **A6.** The crossing sign of two carrier edges is the crossing sign of the original edges
(`geoCornerPolygon_edge_smul`, `det` bilinear, `sign_mul`). -/
theorem G11_carrierSign (v w : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg T q)
    (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    crossingSign (geoCornerPolygon hG.cg T q) (G11_carrierEdge hn hG hT q v hv)
      (G11_carrierEdge hn hG hT q w hw) = crossingSign P v.2.val w.2.val := by
  sorry

end G11Carrier

section G11Triangle

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P)
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {e f g : ZMod n}

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
  sorry

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
  sorry

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
