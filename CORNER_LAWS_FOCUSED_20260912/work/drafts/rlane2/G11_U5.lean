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

theorem gu5_edgeSegment_eq_segment {n : ℕ} (P : LabelledTuple n) (i : ZMod n) :
    edgeSegment P i = segment ℝ (P i) (P (i + 1)) := by
  rw [segment_eq_image']
  ext x
  constructor
  · rintro ⟨t, h0, h1, rfl⟩; exact ⟨t, ⟨h0, h1⟩, rfl⟩
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩; exact ⟨t, h0, h1, rfl⟩

theorem gu5_edgePoint_mem_segment {n : ℕ} (P : LabelledTuple n) (i : ZMod n) {s₁ s₂ t : ℝ}
    (h1 : s₁ ≤ t) (h2 : t ≤ s₂) (h : s₁ < s₂) :
    edgePoint P i t ∈ segment ℝ (edgePoint P i s₁) (edgePoint P i s₂) := by
  rw [segment_eq_image']
  have hpos : 0 < s₂ - s₁ := sub_pos.mpr h
  refine ⟨(t - s₁) / (s₂ - s₁), ⟨div_nonneg (by linarith) hpos.le, (div_le_one hpos).mpr (by linarith)⟩, ?_⟩
  simp only [edgePoint]
  rw [show P i + s₂ • edge P i - (P i + s₁ • edge P i) = (s₂ - s₁) • edge P i by module, smul_smul,
    div_mul_cancel₀ _ hpos.ne']
  module

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

/-- Along `t ↦ A + t • v`: if `f s₀ ∉ U` and `f s₁ ∈ interior U` (`s₀ < s₁`) there is a unique entry
parameter `a ∈ (s₀, s₁)`: on `[s₀, s₁]` the point is in `U` iff `a ≤ t` and in `interior U` iff `a < t`. -/
theorem gu5_entry {U : Set Plane} (hU : Convex ℝ U) (hcl : IsClosed U) (A v : Plane) {s₀ s₁ : ℝ}
    (hs : s₀ < s₁) (h₀ : A + s₀ • v ∉ U) (h₁ : A + s₁ • v ∈ interior U) :
    ∃ a, s₀ < a ∧ a < s₁ ∧
      (∀ t, s₀ ≤ t → t ≤ s₁ → (A + t • v ∈ U ↔ a ≤ t)) ∧
      (∀ t, s₀ ≤ t → t ≤ s₁ → (A + t • v ∈ interior U ↔ a < t)) := by
  have hfc : Continuous (fun t : ℝ => A + t • v) := continuous_const.add (continuous_id.smul continuous_const)
  set S : Set ℝ := Set.Icc s₀ s₁ ∩ (fun t : ℝ => A + t • v) ⁻¹' U with hS
  have hScl : IsClosed S := isClosed_Icc.inter (hcl.preimage hfc)
  have hSne : S.Nonempty := ⟨s₁, ⟨hs.le, le_rfl⟩, (show A + s₁ • v ∈ U from interior_subset h₁)⟩
  have hSbdd : BddBelow S := ⟨s₀, fun t ht => ht.1.1⟩
  have haS : sInf S ∈ S := hScl.csInf_mem hSne hSbdd
  set a := sInf S with ha
  have ha0 : s₀ ≤ a := haS.1.1
  have ha1 : a ≤ s₁ := haS.1.2
  have haU : A + a • v ∈ U := haS.2
  have ha0' : s₀ < a := lt_of_le_of_ne ha0 (fun h => h₀ (by rw [h]; exact haU))
  have hint : ∀ t, a < t → t ≤ s₁ → A + t • v ∈ interior U := by
    intro t hat hts
    rcases hts.lt_or_eq with hts | rfl
    · have hpos : 0 < s₁ - a := by linarith
      set c₁ := (t - a) / (s₁ - a) with hc₁
      set c₂ := (s₁ - t) / (s₁ - a) with hc₂
      have hc : c₁ + c₂ = 1 := by rw [hc₁, hc₂]; field_simp; ring
      have hc' : c₁ * s₁ + c₂ * a = t := by rw [hc₁, hc₂]; field_simp; ring
      have key : A + t • v = c₁ • (A + s₁ • v) + c₂ • (A + a • v) := by
        have e1 : c₁ • (A + s₁ • v) + c₂ • (A + a • v) = (c₁ + c₂) • A + (c₁ * s₁ + c₂ * a) • v := by
          module
        rw [e1, hc, hc', one_smul]
      rw [key]
      exact hU.combo_interior_closure_mem_interior h₁ (subset_closure haU)
        (div_pos (by linarith) hpos) (div_nonneg (by linarith) hpos.le) hc
    · exact h₁
  have hmemU : ∀ t, a ≤ t → t ≤ s₁ → A + t • v ∈ U := fun t hat hts =>
    hat.lt_or_eq.elim (fun h => interior_subset (hint t h hts)) (fun h => by rw [← h]; exact haU)
  have hnot : ∀ t, s₀ ≤ t → t < a → A + t • v ∉ U := fun t h0 hta hmem =>
    absurd (csInf_le hSbdd ⟨⟨h0, by linarith⟩, hmem⟩) (not_le.mpr hta)
  have hnotint : A + a • v ∉ interior U := by
    intro hin
    have hopen : IsOpen ((fun t : ℝ => A + t • v) ⁻¹' interior U) := isOpen_interior.preimage hfc
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hin)
    have ht0 : s₀ ≤ max s₀ (a - ε / 2) := le_max_left _ _
    have hta : max s₀ (a - ε / 2) < a := max_lt ha0' (by linarith)
    have htball : max s₀ (a - ε / 2) ∈ Metric.ball a ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [le_max_right s₀ (a - ε / 2)]
    exact hnot _ ht0 hta (interior_subset (hball htball))
  have ha1' : a < s₁ := lt_of_le_of_ne ha1 (fun h => hnotint (by rw [h]; exact h₁))
  refine ⟨a, ha0', ha1', ?_, ?_⟩
  · intro t h0 h1
    constructor
    · intro hmem; by_contra hlt; exact hnot t h0 (not_le.mp hlt) hmem
    · intro hat; exact hmemU t hat h1
  · intro t h0 h1
    constructor
    · intro hin
      by_contra hle
      rcases (not_lt.mp hle).lt_or_eq with hlt | heq
      · exact hnot t h0 hlt (interior_subset hin)
      · rw [heq] at hin; exact hnotint hin
    · intro hat; exact hint t hat h1

/-- The exit version: `f s₀ ∈ interior U`, `f s₁ ∉ U`. -/
theorem gu5_exit {U : Set Plane} (hU : Convex ℝ U) (hcl : IsClosed U) (A v : Plane) {s₀ s₁ : ℝ}
    (hs : s₀ < s₁) (h₀ : A + s₀ • v ∈ interior U) (h₁ : A + s₁ • v ∉ U) :
    ∃ b, s₀ < b ∧ b < s₁ ∧
      (∀ t, s₀ ≤ t → t ≤ s₁ → (A + t • v ∈ U ↔ t ≤ b)) ∧
      (∀ t, s₀ ≤ t → t ≤ s₁ → (A + t • v ∈ interior U ↔ t < b)) := by
  have h₀' : A + (-s₀) • (-v) ∈ interior U := by rwa [neg_smul_neg]
  have h₁' : A + (-s₁) • (-v) ∉ U := by rwa [neg_smul_neg]
  obtain ⟨a, ha1, ha0, hU', hI'⟩ := gu5_entry hU hcl A (-v) (neg_lt_neg hs) h₁' h₀'
  refine ⟨-a, by linarith, by linarith, ?_, ?_⟩
  · intro t h0 h1
    have := hU' (-t) (by linarith) (by linarith)
    rw [neg_smul_neg] at this
    rw [this]
    constructor <;> intro h <;> linarith
  · intro t h0 h1
    have := hI' (-t) (by linarith) (by linarith)
    rw [neg_smul_neg] at this
    rw [this]
    constructor <;> intro h <;> linarith

theorem gu5_edgePoint_eq {n : ℕ} (P : LabelledTuple n) (i : ZMod n) (t : ℝ) :
    edgePoint P i t = P i + t • edge P i := rfl

/-- An edge with both endpoints outside `U` and an interior point: the parameter interval `[a, b]`. -/
theorem gu5_both {n : ℕ} (P : LabelledTuple n) (i : ZMod n) {U : Set Plane} (hU : Convex ℝ U)
    (hcl : IsClosed U) (h0 : P i ∉ U) (h1 : P (i + 1) ∉ U) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hin : edgePoint P i t ∈ interior U) :
    ∃ a b, 0 < a ∧ a < b ∧ b < 1 ∧
      (∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint P i θ ∈ U ↔ a ≤ θ ∧ θ ≤ b)) ∧
      (∀ θ, 0 ≤ θ → θ ≤ 1 → (edgePoint P i θ ∈ interior U ↔ a < θ ∧ θ < b)) := by
  have h0' : P i + (0 : ℝ) • edge P i ∉ U := by rwa [zero_smul, add_zero]
  have h1' : P i + (1 : ℝ) • edge P i ∉ U := by rwa [one_smul, edge, add_sub_cancel]
  have hin' : P i + t • edge P i ∈ interior U := hin
  have ht0' : 0 < t := lt_of_le_of_ne ht0 (fun h => h0' (by rw [h]; exact interior_subset hin'))
  have ht1' : t < 1 := lt_of_le_of_ne ht1 (fun h => h1' (by rw [← h]; exact interior_subset hin'))
  obtain ⟨a, ha0, hat, hUa, hIa⟩ := gu5_entry hU hcl (P i) (edge P i) ht0' h0' hin'
  obtain ⟨b, htb, hb1, hUb, hIb⟩ := gu5_exit hU hcl (P i) (edge P i) ht1' hin' h1'
  refine ⟨a, b, ha0, hat.trans htb, hb1, ?_, ?_⟩
  · intro θ hθ0 hθ1
    rw [gu5_edgePoint_eq]
    rcases le_or_gt θ t with hθ | hθ
    · rw [hUa θ hθ0 hθ]; constructor
      · intro h; exact ⟨h, by linarith⟩
      · intro h; exact h.1
    · rw [hUb θ hθ.le hθ1]; constructor
      · intro h; exact ⟨by linarith, h⟩
      · intro h; exact h.2
  · intro θ hθ0 hθ1
    rw [gu5_edgePoint_eq]
    rcases le_or_gt θ t with hθ | hθ
    · rw [hIa θ hθ0 hθ]; constructor
      · intro h; exact ⟨h, by linarith⟩
      · intro h; exact h.1
    · rw [hIb θ hθ.le hθ1]; constructor
      · intro h; exact ⟨by linarith, h⟩
      · intro h; exact h.2

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
structure gu5_Side (π : G11_Params C) (Y : LabelledTuple (k + 3)) : Prop where
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

/-- Traversal points of a one-component shadow are determined by their edge label and parameter. -/
theorem gu5_pt_ext {C' : PolyComp} {p q : (Shadow.single C').Pt} (h : p.2 = q.2) : p = q := by
  obtain ⟨i, p⟩ := p
  obtain ⟨j, q⟩ := q
  obtain rfl : i = j := Subsingleton.elim (α := Fin 1) i j
  exact congrArg (Sigma.mk i) h

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
structure gu5_ArcParams (π : G11_Params C) where
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
theorem clean_M₀ : Clean π.U π.M₀ :=
  gu5_clean π π.X₀_generic (gu5_side₀ π)

theorem clean_M₁ : Clean π.U π.M₁ :=
  gu5_clean π π.X₁_generic (gu5_side₁ π)

/-- **D6.** The outside match with component bijection: the identity on traversal points (same labels
`ZMod (k+3)`, same parameters), `eval_eq` because only the vertex `m₀` moved and both bent edges lie in
`interior U`; directions of outside points are those of unmoved strands; outer crossings are the crossings
not involving `mB, mC` (`X₁_cross_iff`), with the same over data (positive diagrams, same `det`). -/
theorem exists_moveMatch : Nonempty (MoveMatch π.U π.M₀ π.M₁) :=
  ⟨gu5_moveMatch π⟩

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
