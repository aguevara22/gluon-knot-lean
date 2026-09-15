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

/-! #### U6 helpers for D8 (a): vertices and edges of `X₀`, `X₁`; the four inner pieces lie in `Θ` -/

omit [NeZero k] in
theorem gu6_subdiv_natCast (X : LabelledTuple k) (m : ZMod k) (t₁ t₂ t₃ : ℝ) (a : ℕ)
    (ha : a < k + 3) :
    G11_subdiv X m t₁ t₂ t₃ (a : ZMod (k + 3)) =
      if a ≤ m.val then X (a : ZMod k)
      else if a = m.val + 1 then edgePoint X m t₁
      else if a = m.val + 2 then edgePoint X m t₂
      else if a = m.val + 3 then edgePoint X m t₃
      else X ((a - 3 : ℕ) : ZMod k) := by
  simp only [G11_subdiv, ZMod.val_natCast_of_lt ha]

theorem gu6_lab_val (m i : ZMod k) :
    (G11_lab m i).val = if i.val ≤ m.val then i.val else i.val + 3 := by
  have hi := i.val_lt
  unfold G11_lab
  split_ifs with h
  · exact ZMod.val_natCast_of_lt (by omega)
  · exact ZMod.val_natCast_of_lt (by omega)

theorem gu6_subdiv_lab (X : LabelledTuple k) (m : ZMod k) (t₁ t₂ t₃ : ℝ) (i : ZMod k) :
    G11_subdiv X m t₁ t₂ t₃ (G11_lab m i) = X i := by
  have hi := i.val_lt
  by_cases h : i.val ≤ m.val
  · rw [G11_lab, ite_eq_left h, gu6_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_left h,
      ZMod.natCast_zmod_val]
  · rw [G11_lab, ite_eq_right h, gu6_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel,
      ZMod.natCast_zmod_val]

theorem gu6_subdiv_lab_succ (X : LabelledTuple k) (m : ZMod k) (t₁ t₂ t₃ : ℝ) {i : ZMod k}
    (hi : i ≠ m) : G11_subdiv X m t₁ t₂ t₃ (G11_lab m i + 1) = X (i + 1) := by
  have hik := i.val_lt
  have hmk := m.val_lt
  have him : i.val ≠ m.val := fun h => hi (ZMod.val_injective k h)
  have hcast : i + 1 = ((i.val + 1 : ℕ) : ZMod k) := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  by_cases h : i.val ≤ m.val
  · rw [G11_lab, ite_eq_left h, ← Nat.cast_add_one, gu6_subdiv_natCast X m t₁ t₂ t₃ _ (by omega),
      ite_eq_left (by omega), hcast]
  · rw [G11_lab, ite_eq_right h, ← Nat.cast_add_one]
    by_cases hk : i.val + 1 < k
    · rw [gu6_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), hcast]
      congr 2
    · rw [show i.val + 3 + 1 = k + 3 by omega, ZMod.natCast_self, hcast,
        show i.val + 1 = k by omega, ZMod.natCast_self,
        show (0 : ZMod (k + 3)) = ((0 : ℕ) : ZMod (k + 3)) from Nat.cast_zero.symm,
        gu6_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_left (Nat.zero_le _), Nat.cast_zero]

theorem gu6_subdiv_mA (X : LabelledTuple k) (m : ZMod k) (t₁ t₂ t₃ : ℝ) :
    G11_subdiv X m t₁ t₂ t₃ (m.val : ZMod (k + 3)) = X m := by
  have := m.val_lt
  rw [gu6_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_left le_rfl, ZMod.natCast_zmod_val]

theorem gu6_subdiv_mB (X : LabelledTuple k) (m : ZMod k) (t₁ t₂ t₃ : ℝ) :
    G11_subdiv X m t₁ t₂ t₃ ((m.val + 1 : ℕ) : ZMod (k + 3)) = edgePoint X m t₁ := by
  have := m.val_lt
  rw [gu6_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_right (by omega), ite_eq_left rfl]

theorem gu6_subdiv_mC (X : LabelledTuple k) (m : ZMod k) (t₁ t₂ t₃ : ℝ) :
    G11_subdiv X m t₁ t₂ t₃ ((m.val + 2 : ℕ) : ZMod (k + 3)) = edgePoint X m t₂ := by
  have := m.val_lt
  rw [gu6_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left rfl]

theorem gu6_subdiv_mD (X : LabelledTuple k) (m : ZMod k) (t₁ t₂ t₃ : ℝ) :
    G11_subdiv X m t₁ t₂ t₃ ((m.val + 3 : ℕ) : ZMod (k + 3)) = edgePoint X m t₃ := by
  have := m.val_lt
  rw [gu6_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left rfl]

theorem gu6_subdiv_mD_succ (X : LabelledTuple k) (m : ZMod k) (t₁ t₂ t₃ : ℝ) :
    G11_subdiv X m t₁ t₂ t₃ (((m.val + 3 : ℕ) : ZMod (k + 3)) + 1) = X (m + 1) := by
  have hmk := m.val_lt
  have hcast : m + 1 = ((m.val + 1 : ℕ) : ZMod k) := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  rw [← Nat.cast_add_one]
  by_cases hk : m.val + 1 < k
  · rw [gu6_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), hcast]
    congr 2
  · rw [show m.val + 3 + 1 = k + 3 by omega, ZMod.natCast_self, hcast,
      show m.val + 1 = k by omega, ZMod.natCast_self,
      show (0 : ZMod (k + 3)) = ((0 : ℕ) : ZMod (k + 3)) from Nat.cast_zero.symm,
      gu6_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_left (Nat.zero_le _), Nat.cast_zero]

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

omit [NeZero k] in
/-- a point of an edge line as an affine combination of two other points of the line -/
theorem gu6_edgePoint_comb {N : ℕ} (P : LabelledTuple N) (i : ZMod N) {a b : ℝ} (hab : a ≠ b) (t : ℝ) :
    edgePoint P i t = edgePoint P i a + ((t - a) / (b - a)) • (edgePoint P i b - edgePoint P i a) := by
  have h1 : edgePoint P i b - edgePoint P i a = (b - a) • edge P i := by
    simp only [edgePoint, sub_smul]; abel
  rw [h1, smul_smul, div_mul_cancel₀ _ (sub_ne_zero.mpr hab.symm)]
  simp only [edgePoint]
  rw [add_assoc, ← add_smul, add_sub_cancel]

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

omit [NeZero k] in
theorem gu6_tb_same_edge {N : ℕ} [NeZero N] (a : ZMod N) (θ₁ θ₂ : Set.Ico (0:ℝ) 1)
    (h : θ₁.val < θ₂.val) (r : TraversalPoint N) :
    traversalBetween (a, θ₁) r (a, θ₂) ↔ r.1 = a ∧ θ₁.val < r.2.val ∧ r.2.val < θ₂.val := by
  obtain ⟨b, θ⟩ := r
  have hθ1 := θ₁.2.1
  have hθ1' := θ₁.2.2
  have hθ2 := θ₂.2.1
  have hθ2' := θ₂.2.2
  have hθ := θ.2.1
  have hθ' := θ.2.2
  simp only [traversalBetween, traversalKey]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have h3 : b.val < a.val + 1 := by
        have : (b.val : ℝ) < a.val + 1 := by linarith
        exact_mod_cast this
      have h4 : a.val < b.val + 1 := by
        have : (a.val : ℝ) < b.val + 1 := by linarith
        exact_mod_cast this
      have hb : b.val = a.val := by omega
      have hab : b = a := ZMod.val_injective N hb
      subst hab
      exact ⟨rfl, by linarith, by linarith⟩
    · exfalso; linarith
    · exfalso; linarith
  · rintro ⟨rfl, h1, h2⟩
    exact Or.inl ⟨by linarith, by linarith⟩

omit [NeZero k] in
/-- betweenness across two consecutive edges `a`, `b = a + 1` (no wrap) -/
theorem gu6_tb_span_one {N : ℕ} [NeZero N] (a b : ZMod N) (hab : a.val + 1 = b.val)
    (θ₁ θ₂ : Set.Ico (0:ℝ) 1) (r : TraversalPoint N) :
    traversalBetween (a, θ₁) r (b, θ₂) ↔
      (r.1 = a ∧ θ₁.val < r.2.val) ∨ (r.1 = b ∧ r.2.val < θ₂.val) := by
  obtain ⟨c, θ⟩ := r
  have hθ1 := θ₁.2.1
  have hθ1' := θ₁.2.2
  have hθ2 := θ₂.2.1
  have hθ2' := θ₂.2.2
  have hθ := θ.2.1
  have hθ' := θ.2.2
  have hbr : (b.val : ℝ) = a.val + 1 := by exact_mod_cast hab.symm
  simp only [traversalBetween, traversalKey]
  constructor
  · rintro (⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩)
    · have h5 : a.val < c.val + 1 := by
        have : (a.val : ℝ) < c.val + 1 := by linarith
        exact_mod_cast this
      have h6 : c.val < a.val + 2 := by
        have : (c.val : ℝ) < a.val + 2 := by linarith
        exact_mod_cast this
      rcases (by omega : c.val = a.val ∨ c.val = a.val + 1) with hc | hc
      · have hca : c = a := ZMod.val_injective N hc
        subst hca
        exact Or.inl ⟨rfl, by linarith⟩
      · have hcb : c = b := ZMod.val_injective N (hc.trans hab)
        subst hcb
        exact Or.inr ⟨rfl, by linarith⟩
    · exfalso; linarith
    · exfalso; linarith
  · rintro (⟨rfl, h3⟩ | ⟨rfl, h3⟩)
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith⟩

omit [NeZero k] in
/-- the start of an edge `j` lies strictly between a point of another edge and a point of `j`
with positive parameter -/
theorem gu6_tb_edge_start {N : ℕ} [NeZero N] {i j : ZMod N} (hij : i ≠ j)
    (t s : Set.Ico (0:ℝ) 1) (hs : 0 < s.val) :
    traversalBetween (i, t) (j, ⟨0, le_rfl, zero_lt_one⟩) (j, s) := by
  have ht := t.2.1
  have ht' := t.2.2
  have hs' := s.2.2
  have hij' : i.val ≠ j.val := fun h => hij (ZMod.val_injective N h)
  simp only [traversalBetween, traversalKey]
  rcases Nat.lt_or_gt_of_ne hij' with h | h
  · have : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h
    exact Or.inl ⟨by linarith, by linarith⟩
  · have : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast h
    exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)

omit [NeZero k] in
/-- the start of the edge `a` lies strictly between a point of an edge `j` outside the range
`[a, b]` and a point of the edge `b > a` -/
theorem gu6_tb_vertex_between {N : ℕ} [NeZero N] {j a b : ZMod N} (hab : a.val < b.val)
    (hj : j.val < a.val ∨ b.val < j.val) (s t : Set.Ico (0:ℝ) 1) :
    traversalBetween (j, s) (a, ⟨0, le_rfl, zero_lt_one⟩) (b, t) := by
  have hs := s.2.1
  have hs' := s.2.2
  have ht := t.2.1
  have ht' := t.2.2
  have hab' : (a.val : ℝ) + 1 ≤ b.val := by exact_mod_cast hab
  simp only [traversalBetween, traversalKey]
  rcases hj with h | h
  · have : (j.val : ℝ) + 1 ≤ a.val := by exact_mod_cast h
    exact Or.inl ⟨by linarith, by linarith⟩
  · have : (b.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h
    exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)

/-! #### U6 helpers for D8 (c): cyclic-order lemmas and the position of arc ends -/

omit [NeZero k] in
/-- an outside point `Z` and an inner point `R` of the cyclic interval `[S, T]`: `S` lies strictly
between `Z` and `R` -/
theorem gu6_cyc_start_of_outside {S R T Z : ℝ} (hR : cycBetween S R T) (hZ : ¬ cycBetween S Z T)
    (hZS : Z ≠ S) (hZT : Z ≠ T) : cycBetween Z S R := by
  unfold cycBetween at *
  rcases hR with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases lt_or_gt_of_ne hZS with h3 | h3 <;>
    rcases lt_or_gt_of_ne hZT with h4 | h4 <;> rcases lt_trichotomy Z R with h5 | h5 | h5
  all_goals first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
    | exact absurd (Or.inl ⟨by linarith, by linarith⟩) hZ
    | exact absurd (Or.inr (Or.inl ⟨by linarith, by linarith⟩)) hZ
    | exact absurd (Or.inr (Or.inr ⟨by linarith, by linarith⟩)) hZ

omit [NeZero k] in
/-- an outside point `Z` and an inner point `R` of `[S, T]`: `T` lies strictly between `R` and `Z` -/
theorem gu6_cyc_stop_of_outside {S R T Z : ℝ} (hR : cycBetween S R T) (hZ : ¬ cycBetween S Z T)
    (hZS : Z ≠ S) (hZT : Z ≠ T) : cycBetween R T Z := by
  unfold cycBetween at *
  rcases hR with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases lt_or_gt_of_ne hZS with h3 | h3 <;>
    rcases lt_or_gt_of_ne hZT with h4 | h4 <;> rcases lt_trichotomy Z R with h5 | h5 | h5
  all_goals first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
    | exact absurd (Or.inl ⟨by linarith, by linarith⟩) hZ
    | exact absurd (Or.inr (Or.inl ⟨by linarith, by linarith⟩)) hZ
    | exact absurd (Or.inr (Or.inr ⟨by linarith, by linarith⟩)) hZ

omit [NeZero k] in
/-- an outside point `Z` of `[S, T]` (`S ≠ T`): `T` lies strictly between `S` and `Z` -/
theorem gu6_cyc_stop_of_outside' {S T Z : ℝ} (hST : S ≠ T) (hZ : ¬ cycBetween S Z T)
    (hZS : Z ≠ S) (hZT : Z ≠ T) : cycBetween S T Z := by
  unfold cycBetween at *
  rcases lt_or_gt_of_ne hST with h1 | h1 <;> rcases lt_or_gt_of_ne hZS with h3 | h3 <;>
    rcases lt_or_gt_of_ne hZT with h4 | h4
  all_goals first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
    | exact absurd (Or.inl ⟨by linarith, by linarith⟩) hZ
    | exact absurd (Or.inr (Or.inl ⟨by linarith, by linarith⟩)) hZ
    | exact absurd (Or.inr (Or.inr ⟨by linarith, by linarith⟩)) hZ

omit [NeZero k] in
/-- points strictly between two inner points (in the forward order) of `[S, T]` are inner -/
theorem gu6_cyc_inner_path {S R Z W T : ℝ} (hR : cycBetween S R T) (hZ : cycBetween S Z T)
    (hRZ : cycBetween S R Z) (hW : cycBetween R W Z) : cycBetween S W T := by
  unfold cycBetween at *
  rcases hR with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hZ with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rcases hRZ with ⟨h5, h6⟩ | ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> rcases hW with ⟨h7, h8⟩ | ⟨h7, h8⟩ | ⟨h7, h8⟩
  all_goals first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

omit [NeZero k] in
/-- membership in a closed arc, for a point of its component -/
theorem gu6_arc_mem_iff {Γ : Shadow} (a : Γ.Arc) (r : TraversalPoint (Γ.comp a.i).k) :
    a.Mem ⟨a.i, r⟩ ↔ r = a.start ∨ r = a.stop ∨ traversalBetween a.start r a.stop := by
  unfold Shadow.Arc.Mem
  rw [Shadow.Arc.inner_mk_iff]
  have h1 : (⟨a.i, r⟩ : Γ.Pt) = a.startPt ↔ r = a.start := by
    constructor
    · intro h; rw [Sigma.mk.inj_iff] at h; exact eq_of_heq h.2
    · intro h; rw [h]; rfl
  have h2 : (⟨a.i, r⟩ : Γ.Pt) = a.stopPt ↔ r = a.stop := by
    constructor
    · intro h; rw [Sigma.mk.inj_iff] at h; exact eq_of_heq h.2
    · intro h; rw [h]; rfl
  rw [h1, h2]

omit [NeZero k] in
/-- the points of an arc of a closed region `U` evaluate into `U` -/
theorem gu6_isArc_eval_mem {Γ : Shadow} {U : Set Plane} {a : Γ.Arc} (ha : Γ.IsArc U a)
    (hU : IsClosed U) {p : Γ.Pt} (hp : a.Mem p) : Γ.eval p ∈ U := by
  rcases hp with rfl | rfl | hp
  · exact hU.frontier_subset ha.start_frontier
  · exact hU.frontier_subset ha.stop_frontier
  · exact interior_subset (ha.inner_interior _ hp)

omit [NeZero k] in
/-- a point of an arc evaluating into the open region is an inner point -/
theorem gu6_isArc_inner_of_interior {Γ : Shadow} {U : Set Plane} {a : Γ.Arc} (ha : Γ.IsArc U a)
    {p : Γ.Pt} (hp : a.Mem p) (hin : Γ.eval p ∈ interior U) : a.Inner p := by
  rcases hp with rfl | rfl | hp
  · exact absurd hin ha.start_frontier.2
  · exact absurd hin ha.stop_frontier.2
  · exact hp

omit [NeZero k] in
/-- the start of an arc lies strictly between an outside point and an inner point -/
theorem gu6_arc_start_between {Γ : Shadow} {U : Set Plane} {a : Γ.Arc} (ha : Γ.IsArc U a)
    (hU : IsClosed U) {r z : TraversalPoint (Γ.comp a.i).k} (hr : a.Inner ⟨a.i, r⟩)
    (hz : Γ.eval ⟨a.i, z⟩ ∉ U) : traversalBetween z a.start r := by
  have hzm : ¬ a.Mem ⟨a.i, z⟩ := fun h => hz (gu6_isArc_eval_mem ha hU h)
  rw [gu6_arc_mem_iff] at hzm
  push Not at hzm
  rw [Shadow.Arc.inner_mk_iff] at hr
  exact gu6_cyc_start_of_outside hr hzm.2.2 (fun h => hzm.1 (traversalKey_injective h))
    (fun h => hzm.2.1 (traversalKey_injective h))

omit [NeZero k] in
/-- the stop of an arc lies strictly between an inner point and an outside point -/
theorem gu6_arc_stop_between {Γ : Shadow} {U : Set Plane} {a : Γ.Arc} (ha : Γ.IsArc U a)
    (hU : IsClosed U) {r z : TraversalPoint (Γ.comp a.i).k} (hr : a.Inner ⟨a.i, r⟩)
    (hz : Γ.eval ⟨a.i, z⟩ ∉ U) : traversalBetween r a.stop z := by
  have hzm : ¬ a.Mem ⟨a.i, z⟩ := fun h => hz (gu6_isArc_eval_mem ha hU h)
  rw [gu6_arc_mem_iff] at hzm
  push Not at hzm
  rw [Shadow.Arc.inner_mk_iff] at hr
  exact gu6_cyc_stop_of_outside hr hzm.2.2 (fun h => hzm.1 (traversalKey_injective h))
    (fun h => hzm.2.1 (traversalKey_injective h))

omit [NeZero k] in
/-- the stop of an arc lies strictly between its start and an outside point -/
theorem gu6_arc_stop_between' {Γ : Shadow} {U : Set Plane} {a : Γ.Arc} (ha : Γ.IsArc U a)
    (hU : IsClosed U) {z : TraversalPoint (Γ.comp a.i).k} (hz : Γ.eval ⟨a.i, z⟩ ∉ U) :
    traversalBetween a.start a.stop z := by
  have hzm : ¬ a.Mem ⟨a.i, z⟩ := fun h => hz (gu6_isArc_eval_mem ha hU h)
  rw [gu6_arc_mem_iff] at hzm
  push Not at hzm
  exact gu6_cyc_stop_of_outside' (fun h => ha.start_ne_stop (traversalKey_injective h)) hzm.2.2
    (fun h => hzm.1 (traversalKey_injective h)) (fun h => hzm.2.1 (traversalKey_injective h))

omit [NeZero k] in
/-- a point reached from an inner point through the open region is inner (forward) -/
theorem gu6_arc_inner_of_path_fwd {Γ : Shadow} {U : Set Plane} {a : Γ.Arc} (ha : Γ.IsArc U a) {r s : TraversalPoint (Γ.comp a.i).k} (hr : a.Inner ⟨a.i, r⟩)
    (hs : Γ.eval ⟨a.i, s⟩ ∈ interior U)
    (hpath : ∀ z, traversalBetween r z s → Γ.eval ⟨a.i, z⟩ ∈ interior U) : a.Inner ⟨a.i, s⟩ := by
  by_contra hcon
  have hsm : ¬ a.Mem ⟨a.i, s⟩ := fun h => hcon (gu6_isArc_inner_of_interior ha h hs)
  rw [gu6_arc_mem_iff] at hsm
  push Not at hsm
  rw [Shadow.Arc.inner_mk_iff] at hr
  have hb : traversalBetween r a.stop s :=
    gu6_cyc_stop_of_outside hr hsm.2.2 (fun h => hsm.1 (traversalKey_injective h))
      (fun h => hsm.2.1 (traversalKey_injective h))
  exact ha.stop_frontier.2 (hpath _ hb)

omit [NeZero k] in
/-- a point from which an inner point is reached through the open region is inner (backward) -/
theorem gu6_arc_inner_of_path_bwd {Γ : Shadow} {U : Set Plane} {a : Γ.Arc} (ha : Γ.IsArc U a) {r s : TraversalPoint (Γ.comp a.i).k} (hr : a.Inner ⟨a.i, r⟩)
    (hs : Γ.eval ⟨a.i, s⟩ ∈ interior U)
    (hpath : ∀ z, traversalBetween s z r → Γ.eval ⟨a.i, z⟩ ∈ interior U) : a.Inner ⟨a.i, s⟩ := by
  by_contra hcon
  have hsm : ¬ a.Mem ⟨a.i, s⟩ := fun h => hcon (gu6_isArc_inner_of_interior ha h hs)
  rw [gu6_arc_mem_iff] at hsm
  push Not at hsm
  rw [Shadow.Arc.inner_mk_iff] at hr
  have hb : traversalBetween s a.start r :=
    gu6_cyc_start_of_outside hr hsm.2.2 (fun h => hsm.1 (traversalKey_injective h))
      (fun h => hsm.2.1 (traversalKey_injective h))
  exact ha.start_frontier.2 (hpath _ hb)

omit [NeZero k] in
/-- a point reached from the start through the open region is inner -/
theorem gu6_arc_inner_of_path_start {Γ : Shadow} {U : Set Plane} {a : Γ.Arc} (ha : Γ.IsArc U a) {s : TraversalPoint (Γ.comp a.i).k} (hs : Γ.eval ⟨a.i, s⟩ ∈ interior U)
    (hpath : ∀ z, traversalBetween a.start z s → Γ.eval ⟨a.i, z⟩ ∈ interior U) :
    a.Inner ⟨a.i, s⟩ := by
  by_contra hcon
  have hsm : ¬ a.Mem ⟨a.i, s⟩ := fun h => hcon (gu6_isArc_inner_of_interior ha h hs)
  rw [gu6_arc_mem_iff] at hsm
  push Not at hsm
  have hb : traversalBetween a.start a.stop s :=
    gu6_cyc_stop_of_outside' (fun h => ha.start_ne_stop (traversalKey_injective h)) hsm.2.2
      (fun h => hsm.1 (traversalKey_injective h)) (fun h => hsm.2.1 (traversalKey_injective h))
  exact ha.stop_frontier.2 (hpath _ hb)

omit [NeZero k] in
/-- an arc containing two inner points contains one of the two open paths between them -/
theorem gu6_arc_two_paths {Γ : Shadow} {a : Γ.Arc} {r s : TraversalPoint (Γ.comp a.i).k}
    (hr : a.Inner ⟨a.i, r⟩) (hs : a.Inner ⟨a.i, s⟩) (hrs : r ≠ s) :
    (∀ z, traversalBetween r z s → a.Inner ⟨a.i, z⟩) ∨
      (∀ z, traversalBetween s z r → a.Inner ⟨a.i, z⟩) := by
  rw [Shadow.Arc.inner_mk_iff] at hr hs
  have hk : traversalKey r ≠ traversalKey s := fun h => hrs (traversalKey_injective h)
  rcases traversalBetween_total_inner hr hs hk with h | h
  · left
    intro z hz
    rw [Shadow.Arc.inner_mk_iff]
    exact gu6_cyc_inner_path hr hs h hz
  · right
    intro z hz
    rw [Shadow.Arc.inner_mk_iff]
    exact gu6_cyc_inner_path hs hr h hz

/-! #### U6 helpers for D8 (d): occurrences of a positive one-component diagram -/

section GU6Single

variable {Cp : PolyComp}

omit [NeZero k] in
theorem gu6_single_eval (i : Fin 1) (r : TraversalPoint Cp.k) :
    (Shadow.single Cp).eval ⟨i, r⟩ = edgePoint Cp.P r.1 r.2.val := rfl

omit [NeZero k] in
theorem gu6_single_pt_eta (q : (Shadow.single Cp).Pt) (i : Fin 1) : q = ⟨i, q.2⟩ := by
  obtain ⟨j, r⟩ := q
  obtain rfl : j = i := Subsingleton.elim _ _
  rfl

omit [NeZero k] in
theorem gu6_sv_strand (y : Crossing Cp.P) {i : ZMod Cp.k} (hi : i ∈ y.val) :
    ((Shadow.singleVisitEquiv Cp).symm ⟨y, ⟨i, hi⟩⟩).2.val = ⟨0, i⟩ := by
  have h := Shadow.singleVisitEquiv_snd Cp ((Shadow.singleVisitEquiv Cp).symm ⟨y, ⟨i, hi⟩⟩)
  rw [Equiv.apply_symm_apply] at h
  change i = ((Shadow.singleVisitEquiv Cp).symm ⟨y, ⟨i, hi⟩⟩).2.val.2 at h
  rw [← Shadow.single_strand_eta Cp ((Shadow.singleVisitEquiv Cp).symm ⟨y, ⟨i, hi⟩⟩).2.val, ← h]

omit [NeZero k] in
theorem gu6_sv_strand_label (y : Crossing Cp.P) {i : ZMod Cp.k} (hi : i ∈ y.val) :
    Shadow.singleStrandEquiv Cp ((Shadow.singleVisitEquiv Cp).symm ⟨y, ⟨i, hi⟩⟩).2.val = i := by
  rw [gu6_sv_strand]; rfl

omit [NeZero k] in
theorem gu6_sv_fst (y : Crossing Cp.P) {i : ZMod Cp.k} (hi : i ∈ y.val) :
    Shadow.singleCrossingEquiv Cp ((Shadow.singleVisitEquiv Cp).symm ⟨y, ⟨i, hi⟩⟩).1 = y := by
  have h := Shadow.singleVisitEquiv_fst Cp ((Shadow.singleVisitEquiv Cp).symm ⟨y, ⟨i, hi⟩⟩)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

omit [NeZero k] in
theorem gu6_sv_fst_eq (y : Crossing Cp.P) {i : ZMod Cp.k} (hi : i ∈ y.val) :
    ((Shadow.singleVisitEquiv Cp).symm ⟨y, ⟨i, hi⟩⟩).1 = (Shadow.singleCrossingEquiv Cp).symm y := by
  rw [Equiv.eq_symm_apply, gu6_sv_fst]

omit [NeZero k] in
theorem gu6_sv_crossingPoint (hΓ : (Shadow.single Cp).Generic) (y : Crossing Cp.P) {i : ZMod Cp.k}
    (hi : i ∈ y.val) :
    (Shadow.single Cp).crossingPoint ((Shadow.singleVisitEquiv Cp).symm ⟨y, ⟨i, hi⟩⟩).1 =
      crossingPoint y := by
  rw [Shadow.single_crossingPoint Cp hΓ, gu6_sv_fst]

omit [NeZero k] in
theorem gu6_sv_visitPt_snd (hΓ : (Shadow.single Cp).Generic) (y : Crossing Cp.P) {i : ZMod Cp.k}
    (hi : i ∈ y.val) :
    (((Shadow.single Cp).positiveDiagram hΓ).visitPt ((Shadow.singleVisitEquiv Cp).symm ⟨y, ⟨i, hi⟩⟩)).2 =
      (i, ⟨((Shadow.single Cp).positiveDiagram hΓ).crossingParam _ ((Shadow.singleVisitEquiv Cp).symm ⟨y, ⟨i, hi⟩⟩).2.2,
        (((Shadow.single Cp).positiveDiagram hΓ).crossingParam_pos _ _).le,
        ((Shadow.single Cp).positiveDiagram hΓ).crossingParam_lt_one _ _⟩) := by
  refine Prod.ext ?_ (Subtype.ext rfl)
  exact gu6_sv_strand_label y hi

omit [NeZero k] in
theorem gu6_sv_param_spec (hΓ : (Shadow.single Cp).Generic) (y : Crossing Cp.P) {i : ZMod Cp.k}
    (hi : i ∈ y.val) :
    crossingPoint y = edgePoint Cp.P i
      (((Shadow.single Cp).positiveDiagram hΓ).crossingParam _
        ((Shadow.singleVisitEquiv Cp).symm ⟨y, ⟨i, hi⟩⟩).2.2) := by
  have h := (((Shadow.single Cp).positiveDiagram hΓ).crossingParam_spec _
    ((Shadow.singleVisitEquiv Cp).symm ⟨y, ⟨i, hi⟩⟩).2.2).2.2
  change (Shadow.single Cp).crossingPoint _ =
    edgePoint Cp.P (Shadow.singleStrandEquiv Cp ((Shadow.singleVisitEquiv Cp).symm ⟨y, ⟨i, hi⟩⟩).2.val) _ at h
  rw [gu6_sv_crossingPoint hΓ, gu6_sv_strand_label] at h
  exact h

omit [NeZero k] in
/-- an occurrence of a shadow is determined by its crossing and its strand -/
theorem gu6_svisit_ext {Γ : Shadow} {u w : Γ.Visit} (h1 : u.1 = w.1) (h2 : u.2.val = w.2.val) : u = w := by
  obtain ⟨c, i⟩ := u
  obtain ⟨d, j⟩ := w
  change c = d at h1
  subst h1
  change i.val = j.val at h2
  rw [Subtype.ext h2]

omit [NeZero k] in
/-- the over strand of a positive diagram is the strand with positive determinant -/
theorem gu6_overStrand_eq (hΓ : (Shadow.single Cp).Generic) (y : (Shadow.single Cp).Crossing)
    {s : (Shadow.single Cp).Strand} (hs : s ∈ y.val)
    (hpos : 0 < det ((Shadow.single Cp).dir s) ((Shadow.single Cp).dir ((Shadow.single Cp).other y hs))) :
    ((Shadow.single Cp).positiveDiagram hΓ).overStrand y = s := by
  rcases (((Shadow.single Cp).positiveDiagram hΓ).mem_iff y s).mp hs with h | h
  · exact h.symm
  · exfalso
    have hd : 0 < det ((Shadow.single Cp).dir (((Shadow.single Cp).positiveDiagram hΓ).overStrand y))
        ((Shadow.single Cp).dir (((Shadow.single Cp).positiveDiagram hΓ).underStrand y)) :=
      Shadow.positiveDiagram_det_pos (Shadow.single Cp) hΓ y
    have hother : (Shadow.single Cp).other y hs = ((Shadow.single Cp).positiveDiagram hΓ).overStrand y := by
      have h1 := ((Shadow.single Cp).positiveDiagram hΓ).eq_over_of_mem_of_ne y
        ((Shadow.single Cp).other_mem y hs) (fun h' => (Shadow.single Cp).other_ne y hs (h'.trans h.symm))
      exact h1
    rw [hother, h] at hpos
    rw [det_swap] at hpos
    linarith

omit [NeZero k] in
theorem gu6_overVisit_eq (hΓ : (Shadow.single Cp).Generic) (y : Crossing Cp.P) {i : ZMod Cp.k}
    (hi : i ∈ y.val)
    (hpos : 0 < det ((Shadow.single Cp).dir ⟨0, i⟩)
      ((Shadow.single Cp).dir ((Shadow.single Cp).other ((Shadow.singleCrossingEquiv Cp).symm y)
        ((Shadow.mem_singleCrossingEquiv_iff Cp _ ⟨0, i⟩).mp (by rw [Equiv.apply_symm_apply]; exact hi))))) :
    ((Shadow.single Cp).positiveDiagram hΓ).overVisit ((Shadow.singleCrossingEquiv Cp).symm y) =
      (Shadow.singleVisitEquiv Cp).symm ⟨y, ⟨i, hi⟩⟩ := by
  have hs := gu6_overStrand_eq hΓ ((Shadow.singleCrossingEquiv Cp).symm y) _ hpos
  apply gu6_svisit_ext
  · exact (gu6_sv_fst_eq y hi).symm
  · rw [gu6_sv_strand]
    exact hs

omit [NeZero k] in
/-- a common point of the two edges of a crossing of a generic one-component polygon is its double
point -/
theorem gu6_common_eq_single (hΓ : (Shadow.single Cp).Generic) {i j : ZMod Cp.k}
    (h : IsCrossing Cp.P {i, j}) {x : Plane} (hi : x ∈ edgeSegment Cp.P i) (hj : x ∈ edgeSegment Cp.P j) :
    x = crossingPoint (xPair h) := by
  have hx := hΓ.common_point_unique ((Shadow.singleCrossingEquiv Cp).symm (xPair h)) (p := x) ?_
  · rw [hx, Shadow.single_crossingPoint Cp hΓ, Equiv.apply_symm_apply]
  · intro s hs
    have hs' := (Shadow.mem_singleCrossingEquiv_iff Cp _ s).mpr hs
    rw [Equiv.apply_symm_apply] at hs'
    change Shadow.singleStrandEquiv Cp s ∈ ({i, j} : Finset (ZMod Cp.k)) at hs'
    rw [Finset.mem_insert, Finset.mem_singleton] at hs'
    rw [Shadow.single_seg]
    rcases hs' with hs' | hs'
    · rw [hs']; exact hi
    · rw [hs']; exact hj

end GU6Single

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

omit [NeZero k] in
/-- coefficients in a basis of two independent vectors of the plane -/
theorem gu6_coeff_eq {d u : Plane} (hdu : det d u ≠ 0) {α β α' β' : ℝ}
    (h : α • d + β • u = α' • d + β' • u) : α = α' ∧ β = β' := by
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2
  have hα : (α - α') * det d u = 0 := by
    unfold det
    linear_combination u.2 * e1 - u.1 * e2
  have hα' : α = α' := by
    have := (mul_eq_zero.mp hα).resolve_right hdu
    linarith
  subst hα'
  have hβ : (β - β') * det d u = 0 := by
    unfold det
    linear_combination d.1 * e2 - d.2 * e1
  have := (mul_eq_zero.mp hβ).resolve_right hdu
  exact ⟨rfl, by linarith⟩

section GU6Single2

variable {Cp : PolyComp}

omit [NeZero k] in
theorem gu6_cp_injective_single (hΓ : (Shadow.single Cp).Generic) {y₁ y₂ : Crossing Cp.P}
    (h : crossingPoint y₁ = crossingPoint y₂) : y₁ = y₂ := by
  have h' : (Shadow.single Cp).crossingPoint ((Shadow.singleCrossingEquiv Cp).symm y₁) =
      (Shadow.single Cp).crossingPoint ((Shadow.singleCrossingEquiv Cp).symm y₂) := by
    rw [Shadow.single_crossingPoint Cp hΓ, Shadow.single_crossingPoint Cp hΓ, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    exact h
  exact (Shadow.singleCrossingEquiv Cp).symm.injective (hΓ.crossingPoint_injective h')

omit [NeZero k] in
theorem gu6_strand_mem_symm (y : Crossing Cp.P) {i : ZMod Cp.k} (hi : i ∈ y.val) :
    (⟨0, i⟩ : (Shadow.single Cp).Strand) ∈ ((Shadow.singleCrossingEquiv Cp).symm y).val :=
  (Shadow.mem_singleCrossingEquiv_iff Cp _ ⟨0, i⟩).mp (by rw [Equiv.apply_symm_apply]; exact hi)

omit [NeZero k] in
theorem gu6_strand_ne {i j : ZMod Cp.k} (hij : i ≠ j) :
    (⟨0, i⟩ : (Shadow.single Cp).Strand) ≠ ⟨0, j⟩ :=
  fun e => hij (eq_of_heq (Sigma.mk.inj_iff.mp e).2)

omit [NeZero k] in
/-- transversality of the two edges of a crossing -/
theorem gu6_det_ne_zero_single (hΓ : (Shadow.single Cp).Generic) {i j : ZMod Cp.k}
    (h : IsCrossing Cp.P {i, j}) : det (edge Cp.P i) (edge Cp.P j) ≠ 0 := by
  have hij : i ≠ j := P1.ne_of_isCrossing_pair h
  have hi := gu6_strand_mem_symm (xPair h) (mem_pair_left i j)
  have hj := gu6_strand_mem_symm (xPair h) (mem_pair_right i j)
  obtain ⟨hna, hmeet⟩ := (Shadow.single Cp).crossing_pair_spec _ hi hj (gu6_strand_ne hij)
  exact hΓ.transverse _ _ hna hmeet

omit [NeZero k] in
/-- the over and under occurrences of a positive diagram at a crossing `{i, j}` with
`det(edge i, edge j) > 0`: `i` is over -/
theorem gu6_over_under_of_pos (hΓ : (Shadow.single Cp).Generic) {i j : ZMod Cp.k}
    (h : IsCrossing Cp.P {i, j}) (hpos : 0 < det (edge Cp.P i) (edge Cp.P j)) :
    ((Shadow.single Cp).positiveDiagram hΓ).overVisit ((Shadow.singleCrossingEquiv Cp).symm (xPair h)) =
        (Shadow.singleVisitEquiv Cp).symm ⟨xPair h, ⟨i, mem_pair_left _ _⟩⟩ ∧
      ((Shadow.single Cp).positiveDiagram hΓ).underVisit ((Shadow.singleCrossingEquiv Cp).symm (xPair h)) =
        (Shadow.singleVisitEquiv Cp).symm ⟨xPair h, ⟨j, mem_pair_right _ _⟩⟩ := by
  have hij : i ≠ j := P1.ne_of_isCrossing_pair h
  have hi := gu6_strand_mem_symm (xPair h) (mem_pair_left i j)
  have hj := gu6_strand_mem_symm (xPair h) (mem_pair_right i j)
  have hother : (Shadow.single Cp).other _ hi = ⟨0, j⟩ :=
    ((Shadow.single Cp).eq_other_of_mem_of_ne _ hi hj (gu6_strand_ne hij.symm)).symm
  have hpos' : 0 < det ((Shadow.single Cp).dir ⟨0, i⟩)
      ((Shadow.single Cp).dir ((Shadow.single Cp).other _ hi)) := by
    rw [hother]; exact hpos
  have hs : ((Shadow.single Cp).positiveDiagram hΓ).overStrand _ = (⟨0, i⟩ : (Shadow.single Cp).Strand) :=
    gu6_overStrand_eq hΓ _ hi hpos'
  refine ⟨gu6_overVisit_eq hΓ (xPair h) (mem_pair_left i j) hpos', ?_⟩
  apply gu6_svisit_ext
  · exact (gu6_sv_fst_eq _ _).symm
  · refine Eq.trans ?_ (gu6_sv_strand (xPair h) (mem_pair_right i j)).symm
    show (Shadow.single Cp).other _ (((Shadow.single Cp).positiveDiagram hΓ).over_mem _) = ⟨0, j⟩
    exact ((Shadow.single Cp).eq_other_of_mem_of_ne _ _ hj (by rw [hs]; exact gu6_strand_ne hij.symm)).symm

omit [NeZero k] in
/-- ... and with `det(edge i, edge j) < 0`: `j` is over -/
theorem gu6_over_under_of_neg (hΓ : (Shadow.single Cp).Generic) {i j : ZMod Cp.k}
    (h : IsCrossing Cp.P {i, j}) (hneg : det (edge Cp.P i) (edge Cp.P j) < 0) :
    ((Shadow.single Cp).positiveDiagram hΓ).overVisit ((Shadow.singleCrossingEquiv Cp).symm (xPair h)) =
        (Shadow.singleVisitEquiv Cp).symm ⟨xPair h, ⟨j, mem_pair_right _ _⟩⟩ ∧
      ((Shadow.single Cp).positiveDiagram hΓ).underVisit ((Shadow.singleCrossingEquiv Cp).symm (xPair h)) =
        (Shadow.singleVisitEquiv Cp).symm ⟨xPair h, ⟨i, mem_pair_left _ _⟩⟩ := by
  have hij : i ≠ j := P1.ne_of_isCrossing_pair h
  have hi := gu6_strand_mem_symm (xPair h) (mem_pair_left i j)
  have hj := gu6_strand_mem_symm (xPair h) (mem_pair_right i j)
  have hother : (Shadow.single Cp).other _ hj = ⟨0, i⟩ :=
    ((Shadow.single Cp).eq_other_of_mem_of_ne _ hj hi (gu6_strand_ne hij)).symm
  have hpos' : 0 < det ((Shadow.single Cp).dir ⟨0, j⟩)
      ((Shadow.single Cp).dir ((Shadow.single Cp).other _ hj)) := by
    rw [hother]
    change 0 < det (edge Cp.P j) (edge Cp.P i)
    rw [det_swap]; linarith
  have hs : ((Shadow.single Cp).positiveDiagram hΓ).overStrand _ = (⟨0, j⟩ : (Shadow.single Cp).Strand) :=
    gu6_overStrand_eq hΓ _ hj hpos'
  refine ⟨gu6_overVisit_eq hΓ (xPair h) (mem_pair_right i j) hpos', ?_⟩
  apply gu6_svisit_ext
  · exact (gu6_sv_fst_eq _ _).symm
  · refine Eq.trans ?_ (gu6_sv_strand (xPair h) (mem_pair_left i j)).symm
    show (Shadow.single Cp).other _ (((Shadow.single Cp).positiveDiagram hΓ).over_mem _) = ⟨0, i⟩
    exact ((Shadow.single Cp).eq_other_of_mem_of_ne _ _ hi (by rw [hs]; exact gu6_strand_ne hij)).symm

end GU6Single2

omit [NeZero k] in
/-- **D9 (core, the strand `p`).** In the basis `(d, e)` (`d` the base direction, `e` the direction
of `p`), the entry `x_mp = Xm + a d` (`a < t₂`), the double point `z` and the exit `x_mp'` on the side
`[w, p_out]` of `Θ` satisfy `x_mp' − x_mp = ρ (z − x_mp)` with `ρ = (1−μ) λ > 1`: `z` lies strictly
between `x_mp` and `x_mp'` along `p`. -/
theorem gu6_D9_core_p (Xm Xp d e z : Plane) (a t₂ t₃ lam μ s₁ s₂ s₃ : ℝ)
    (hde : det d e ≠ 0) (ha : a < t₂) (h23 : t₂ < t₃) (hlam : 1 < lam) (hμ0 : 0 ≤ μ)
    (h1 : Xp + s₁ • e = Xm + a • d) (h2 : Xp + s₂ • e = z)
    (h3 : Xp + s₃ • e = (Xm + t₂ • d + lam • (z - (Xm + t₂ • d))) +
      μ • ((Xm + t₃ • d) - (Xm + t₂ • d + lam • (z - (Xm + t₂ • d))))) :
    (s₁ < s₂ ↔ s₂ < s₃) := by
  have key : (a - t₂) • d + (s₃ - s₁) • e =
      (μ * (t₃ - t₂) + (1 - μ) * lam * (a - t₂)) • d + ((1 - μ) * lam * (s₂ - s₁)) • e := by
    have h1a := congrArg Prod.fst h1
    have h1b := congrArg Prod.snd h1
    have h2a := congrArg Prod.fst h2
    have h2b := congrArg Prod.snd h2
    have h3a := congrArg Prod.fst h3
    have h3b := congrArg Prod.snd h3
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at h1a h1b h2a h2b h3a h3b
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      linear_combination h3a - ((1 - μ) * lam) * h2a - (1 - (1 - μ) * lam) * h1a
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      linear_combination h3b - ((1 - μ) * lam) * h2b - (1 - (1 - μ) * lam) * h1b
  obtain ⟨c1, c2⟩ := gu6_coeff_eq hde key
  have e1 : (a - t₂) * (1 - (1 - μ) * lam) = μ * (t₃ - t₂) := by linear_combination c1
  have hnn : 0 ≤ μ * (t₃ - t₂) := mul_nonneg hμ0 (by linarith)
  have hρ1 : 1 < (1 - μ) * lam := by
    have hle : 1 - (1 - μ) * lam ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have : (a - t₂) * (1 - (1 - μ) * lam) < 0 := mul_neg_of_neg_of_pos (by linarith) hcon
      linarith
    rcases hle.lt_or_eq with hlt | heq
    · linarith
    · exfalso
      have hμ : μ * (t₃ - t₂) = 0 := by rw [← e1, heq, mul_zero]
      have hμ0' : μ = 0 := by
        rcases mul_eq_zero.mp hμ with h' | h'
        · exact h'
        · linarith
      rw [hμ0'] at heq
      linarith
  constructor
  · intro h
    have : 0 < ((1 - μ) * lam - 1) * (s₂ - s₁) := mul_pos (by linarith) (by linarith)
    nlinarith [c2]
  · intro h
    by_contra hcon
    push Not at hcon
    have : 0 ≤ ((1 - μ) * lam - 1) * (s₁ - s₂) := mul_nonneg (by linarith) (by linarith)
    nlinarith [c2]

omit [NeZero k] in
/-- **D9 (core, the strand `q`)**: the entry `x_mq = Xm + b d` (`b > t₂`), the double point `z` and
the exit `x_mq'` on the side `[p_in, w]` satisfy `x_mq' − x_mq = ρ (z − x_mq)` with `ρ = μ λ > 1`. -/
theorem gu6_D9_core_q (Xm Xq d e z : Plane) (b t₁ t₂ lam μ s₁ s₂ s₃ : ℝ)
    (hde : det d e ≠ 0) (hb : t₂ < b) (h12 : t₁ < t₂) (hlam : 1 < lam) (hμ1 : μ ≤ 1)
    (h1 : Xq + s₁ • e = Xm + b • d) (h2 : Xq + s₂ • e = z)
    (h3 : Xq + s₃ • e = (Xm + t₁ • d) +
      μ • ((Xm + t₂ • d + lam • (z - (Xm + t₂ • d))) - (Xm + t₁ • d))) :
    (s₁ < s₂ ↔ s₂ < s₃) := by
  have key : (b - t₂) • d + (s₃ - s₁) • e =
      ((t₁ - t₂) + μ * (t₂ - t₁) + μ * lam * (b - t₂)) • d + (μ * lam * (s₂ - s₁)) • e := by
    have h1a := congrArg Prod.fst h1
    have h1b := congrArg Prod.snd h1
    have h2a := congrArg Prod.fst h2
    have h2b := congrArg Prod.snd h2
    have h3a := congrArg Prod.fst h3
    have h3b := congrArg Prod.snd h3
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at h1a h1b h2a h2b h3a h3b
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      linear_combination h3a - (μ * lam) * h2a - (1 - μ * lam) * h1a
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      linear_combination h3b - (μ * lam) * h2b - (1 - μ * lam) * h1b
  obtain ⟨c1, c2⟩ := gu6_coeff_eq hde key
  have e1 : (b - t₂) * (1 - μ * lam) = -((1 - μ) * (t₂ - t₁)) := by linear_combination c1
  have hnn : 0 ≤ (1 - μ) * (t₂ - t₁) := mul_nonneg (by linarith) (by linarith)
  have hρ1 : 1 < μ * lam := by
    have hle : 1 - μ * lam ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have : 0 < (b - t₂) * (1 - μ * lam) := mul_pos (by linarith) hcon
      linarith
    rcases hle.lt_or_eq with hlt | heq
    · linarith
    · exfalso
      have hμ : (1 - μ) * (t₂ - t₁) = 0 := by
        have := e1
        rw [heq, mul_zero] at this
        linarith
      have hμ1' : μ = 1 := by
        rcases mul_eq_zero.mp hμ with h' | h'
        · linarith
        · linarith
      rw [hμ1'] at heq
      linarith
  constructor
  · intro h
    have : 0 < (μ * lam - 1) * (s₂ - s₁) := mul_pos (by linarith) (by linarith)
    nlinarith [c2]
  · intro h
    by_contra hcon
    push Not at hcon
    have : 0 ≤ (μ * lam - 1) * (s₁ - s₂) := mul_nonneg (by linarith) (by linarith)
    nlinarith [c2]

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

omit [NeZero k] in
/-- convexity along an edge: from a point of `U` towards an interior point, every point strictly
after the first (up to the second) is interior -/
theorem gu6_edge_interior_of_convex {U : Set Plane} (hU : Convex ℝ U) {N : ℕ} (P : LabelledTuple N)
    (i : ZMod N) {θ₀ θ₁ θ : ℝ} (h0 : edgePoint P i θ₀ ∈ U) (h1 : edgePoint P i θ₁ ∈ interior U)
    (hθ : (θ₀ < θ ∧ θ ≤ θ₁) ∨ (θ₁ ≤ θ ∧ θ < θ₀)) : edgePoint P i θ ∈ interior U := by
  have hne : θ₀ ≠ θ₁ := by rcases hθ with ⟨h, h'⟩ | ⟨h, h'⟩ <;> linarith
  rw [gu6_edgePoint_comb P i hne θ]
  refine hU.add_smul_sub_mem_interior' (subset_closure h0) h1 ⟨?_, ?_⟩
  · rcases hθ with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact div_pos (by linarith) (by linarith)
    · rw [← neg_sub θ₀ θ, ← neg_sub θ₀ θ₁, neg_div_neg_eq]
      exact div_pos (by linarith) (by linarith)
  · rcases hθ with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact (div_le_one (by linarith)).mpr (by linarith)
    · rw [← neg_sub θ₀ θ, ← neg_sub θ₀ θ₁, neg_div_neg_eq]
      exact (div_le_one (by linarith)).mpr (by linarith)

omit [NeZero k] in
/-- convexity along an edge: between two interior points everything is interior -/
theorem gu6_edge_interior_of_convex' {U : Set Plane} (hU : Convex ℝ U) {N : ℕ} (P : LabelledTuple N)
    (i : ZMod N) {θ₀ θ₁ θ : ℝ} (h0 : edgePoint P i θ₀ ∈ interior U) (h1 : edgePoint P i θ₁ ∈ interior U)
    (hθ : (θ₀ ≤ θ ∧ θ ≤ θ₁) ∨ (θ₁ ≤ θ ∧ θ ≤ θ₀)) : edgePoint P i θ ∈ interior U := by
  rcases eq_or_ne θ₀ θ₁ with heq | hne
  · subst heq
    have : θ = θ₀ := by rcases hθ with ⟨h, h'⟩ | ⟨h, h'⟩ <;> linarith
    rw [this]; exact h0
  rw [gu6_edgePoint_comb P i hne θ]
  refine hU.interior.add_smul_sub_mem h0 h1 ⟨?_, ?_⟩
  · rcases hθ with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact div_nonneg (by linarith) (by linarith)
    · rw [← neg_sub θ₀ θ, ← neg_sub θ₀ θ₁, neg_div_neg_eq]
      exact div_nonneg (by linarith) (by linarith)
  · rcases hθ with ⟨h, h'⟩ | ⟨h, h'⟩
    · have hlt : θ₀ < θ₁ := lt_of_le_of_ne (by linarith) hne
      exact (div_le_one (by linarith)).mpr (by linarith)
    · have hlt : θ₁ < θ₀ := lt_of_le_of_ne (by linarith) hne.symm
      rw [← neg_sub θ₀ θ, ← neg_sub θ₀ θ₁, neg_div_neg_eq]
      exact (div_le_one (by linarith)).mpr (by linarith)

omit [NeZero k] in
/-- betweenness across three consecutive edges `a`, `b = a + 1`, `c = a + 2` (no wrap) -/
theorem gu6_tb_span_two {N : ℕ} [NeZero N] (a b c : ZMod N) (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (θ₁ θ₂ : Set.Ico (0:ℝ) 1) (r : TraversalPoint N) :
    traversalBetween (a, θ₁) r (c, θ₂) ↔
      (r.1 = a ∧ θ₁.val < r.2.val) ∨ r.1 = b ∨ (r.1 = c ∧ r.2.val < θ₂.val) := by
  obtain ⟨e, θ⟩ := r
  have hθ1 := θ₁.2.1
  have hθ1' := θ₁.2.2
  have hθ2 := θ₂.2.1
  have hθ2' := θ₂.2.2
  have hθ := θ.2.1
  have hθ' := θ.2.2
  have hbr : (b.val : ℝ) = a.val + 1 := by exact_mod_cast hab.symm
  have hcr : (c.val : ℝ) = a.val + 2 := by
    have : c.val = a.val + 2 := by omega
    exact_mod_cast this
  simp only [traversalBetween, traversalKey]
  constructor
  · rintro (⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩)
    · have h5 : a.val < e.val + 1 := by
        have : (a.val : ℝ) < e.val + 1 := by linarith
        exact_mod_cast this
      have h6 : e.val < a.val + 3 := by
        have : (e.val : ℝ) < a.val + 3 := by linarith
        exact_mod_cast this
      rcases (by omega : e.val = a.val ∨ e.val = a.val + 1 ∨ e.val = a.val + 2) with he | he | he
      · have hea : e = a := ZMod.val_injective N he
        subst hea
        exact Or.inl ⟨rfl, by linarith⟩
      · exact Or.inr (Or.inl (ZMod.val_injective N (he.trans hab)))
      · have hec : e = c := ZMod.val_injective N (by omega)
        subst hec
        refine Or.inr (Or.inr ⟨rfl, ?_⟩)
        linarith
    · exfalso; linarith
    · exfalso; linarith
  · rintro (⟨rfl, h3⟩ | rfl | ⟨rfl, h3⟩)
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith⟩

omit [NeZero k] in
/-- along an arc starting on the edge `a` at `θ₀`, two later points of `a` are ordered by parameter -/
theorem gu6_tb_same_edge_of_start {N : ℕ} [NeZero N] (a : ZMod N) (θ₀ s₁ s₂ : Set.Ico (0:ℝ) 1)
    (h1 : θ₀.val < s₁.val) (h2 : θ₀.val < s₂.val) :
    traversalBetween (a, θ₀) (a, s₁) (a, s₂) ↔ s₁.val < s₂.val := by
  simp only [traversalBetween, traversalKey]
  constructor
  · rintro (⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩)
    · linarith
    · exfalso; linarith
    · exfalso; linarith
  · intro h
    exact Or.inl ⟨by linarith, by linarith⟩

omit [NeZero k] in
/-- `Before` along an arc, for two inner points of its component -/
theorem gu6_before_iff {Γ : Shadow} (a : Γ.Arc) (r s : TraversalPoint (Γ.comp a.i).k)
    (hr : a.Inner ⟨a.i, r⟩) (hs : a.Inner ⟨a.i, s⟩) :
    a.Before ⟨a.i, r⟩ ⟨a.i, s⟩ ↔ traversalBetween a.start r s := by
  constructor
  · rintro ⟨-, -, r', s', hr', hs', h⟩
    rw [Sigma.mk.inj_iff] at hr' hs'
    rw [eq_of_heq hr'.2, eq_of_heq hs'.2]
    exact h
  · intro h
    exact ⟨hr, hs, r, s, rfl, rfl, h⟩

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

omit [NeZero k] in
/-- an occurrence whose double point is in the open region lies (as an inner point) on some arc of
a cover -/
theorem gu6_exists_arc_of_interior {D : Diagram} {U : Set Plane} {A : Set D.Γ.Arc}
    (cover : D.Γ.ArcCover U A) (v : D.Γ.Visit) (hv : D.Γ.crossingPoint v.1 ∈ interior U) :
    ∃ a ∈ A, a.Inner (D.visitPt v) := by
  obtain ⟨a, ha, hmem⟩ := (cover.mem_iff (D.visitPt v)).mp
    (by rw [Diagram.eval_visitPt]; exact interior_subset hv)
  exact ⟨a, ha, gu6_isArc_inner_of_interior (cover.isArc a ha) hmem
    (by rw [Diagram.eval_visitPt]; exact hv)⟩

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

omit [NeZero k] in
theorem gu6_decode_start_same {N : ℕ} [NeZero N] (j : ZMod N) (s : Set.Ico (0:ℝ) 1) (hs0 : 0 < s.val)
    (r : TraversalPoint N) (hb : traversalBetween (j, ⟨0, le_rfl, zero_lt_one⟩) r (j, s)) :
    ∃ θ : Set.Ico (0:ℝ) 1, 0 < θ.val ∧ θ.val < s.val ∧ r = (j, θ) := by
  rw [gu6_tb_same_edge j _ _ hs0] at hb
  obtain ⟨h1, h2, h3⟩ := hb
  exact ⟨r.2, h2, h3, Prod.ext h1 rfl⟩

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

omit [NeZero k] in
/-- the constructor of `RIIIData`, with the separations spelled out as over/under memberships -/
theorem gu6_riii_build {U : Set Plane} {D D' : Diagram} (frame : LocalFrame U D D') (out : MoveMatch U D D')
    (a b c : D.Γ.Arc) (a' b' c' : D'.Γ.Arc) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hab' : a' ≠ b') (hbc' : b' ≠ c') (hac' : a' ≠ c')
    (cover : D.Γ.ArcCover U {a, b, c}) (cover' : D'.Γ.ArcCover U {a', b', c'})
    (a_start : D'.Γ.eval a'.startPt = D.Γ.eval a.startPt) (a_stop : D'.Γ.eval a'.stopPt = D.Γ.eval a.stopPt)
    (b_start : D'.Γ.eval b'.startPt = D.Γ.eval b.startPt) (b_stop : D'.Γ.eval b'.stopPt = D.Γ.eval b.stopPt)
    (c_start : D'.Γ.eval c'.startPt = D.Γ.eval c.startPt) (c_stop : D'.Γ.eval c'.stopPt = D.Γ.eval c.stopPt)
    (xab xac xbc : D.Γ.Crossing) (h1 : xab ≠ xac) (h2 : xab ≠ xbc) (h3 : xac ≠ xbc)
    (inner_iff : ∀ y, D.Γ.crossingPoint y ∈ interior U ↔ y = xab ∨ y = xac ∨ y = xbc)
    (xab' xac' xbc' : D'.Γ.Crossing) (h1' : xab' ≠ xac') (h2' : xab' ≠ xbc') (h3' : xac' ≠ xbc')
    (inner_iff' : ∀ y, D'.Γ.crossingPoint y ∈ interior U ↔ y = xab' ∨ y = xac' ∨ y = xbc')
    (top_ab : D.OverOn a xab) (und_ab : D.UnderOn b xab) (top_ac : D.OverOn a xac) (und_ac : D.UnderOn c xac)
    (mid_bc : D.OverOn b xbc) (und_bc : D.UnderOn c xbc)
    (top_ab' : D'.OverOn a' xab') (und_ab' : D'.UnderOn b' xab') (top_ac' : D'.OverOn a' xac')
    (und_ac' : D'.UnderOn c' xac') (mid_bc' : D'.OverOn b' xbc') (und_bc' : D'.UnderOn c' xbc')
    (rev_a : D.BeforeOn a xab xac ↔ D'.BeforeOn a' xac' xab')
    (rev_b : D.BeforeOn b xab xbc ↔ D'.BeforeOn b' xbc' xab')
    (rev_c : D.BeforeOn c xac xbc ↔ D'.BeforeOn c' xbc' xac') : Nonempty (RIIIData U D D') :=
  ⟨{ frame := frame, out := out, a := a, b := b, c := c, a' := a', b' := b', c' := c',
     ab := hab, bc := hbc, ac := hac, ab' := hab', bc' := hbc', ac' := hac',
     cover := cover, cover' := cover',
     a_start := a_start, a_stop := a_stop, b_start := b_start, b_stop := b_stop,
     c_start := c_start, c_stop := c_stop,
     xab := xab, xac := xac, xbc := xbc, xab_ne_xac := h1, xab_ne_xbc := h2, xac_ne_xbc := h3,
     inner_iff := inner_iff,
     sep_ab := Or.inl ⟨top_ab, und_ab⟩, sep_ac := Or.inl ⟨top_ac, und_ac⟩, sep_bc := Or.inl ⟨mid_bc, und_bc⟩,
     xab' := xab', xac' := xac', xbc' := xbc', xab_ne_xac' := h1', xab_ne_xbc' := h2', xac_ne_xbc' := h3',
     inner_iff' := inner_iff',
     sep_ab' := Or.inl ⟨top_ab', und_ab'⟩, sep_ac' := Or.inl ⟨top_ac', und_ac'⟩,
     sep_bc' := Or.inl ⟨mid_bc', und_bc'⟩,
     top_ab := top_ab, top_ac := top_ac, mid_bc := mid_bc,
     top_ab' := top_ab', top_ac' := top_ac', mid_bc' := mid_bc',
     rev_a := rev_a, rev_b := rev_b, rev_c := rev_c }⟩

omit [NeZero k] in
/-- the reversal clause read in the other order -/
theorem gu6_rev_swap {U : Set Plane} {D D' : Diagram} {A : Set D.Γ.Arc} {A' : Set D'.Γ.Arc}
    (cover : D.Γ.ArcCover U A) (cover' : D'.Γ.ArcCover U A')
    {a b c : D.Γ.Arc} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hab : a ≠ b) (hac : a ≠ c)
    {x y : D.Γ.Crossing} (hxy : x ≠ y) (hx : D.Γ.crossingPoint x ∈ interior U)
    (hy : D.Γ.crossingPoint y ∈ interior U) (sepx : D.Separates a b x) (sepy : D.Separates a c y)
    {a' b' c' : D'.Γ.Arc} (ha' : a' ∈ A') (hb' : b' ∈ A') (hc' : c' ∈ A') (hab' : a' ≠ b') (hac' : a' ≠ c')
    {x' y' : D'.Γ.Crossing} (hxy' : x' ≠ y') (hx' : D'.Γ.crossingPoint x' ∈ interior U)
    (hy' : D'.Γ.crossingPoint y' ∈ interior U) (sepx' : D'.Separates a' b' x') (sepy' : D'.Separates a' c' y')
    (h : D.BeforeOn a x y ↔ D'.BeforeOn a' y' x') : D.BeforeOn a y x ↔ D'.BeforeOn a' x' y' := by
  rw [D.beforeOn_swap_iff cover ha hb hc hab hac hxy hx hy sepx sepy,
    D'.beforeOn_swap_iff cover' ha' hc' hb' hac' hab' hxy'.symm hy' hx' sepy' sepx', h]

omit [NeZero k] in
theorem gu6_set3_perm₁ {α : Type*} (x y z : α) : ({x, z, y} : Set α) = {x, y, z} := by
  ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
omit [NeZero k] in
theorem gu6_set3_perm₂ {α : Type*} (x y z : α) : ({y, x, z} : Set α) = {x, y, z} := by
  ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
omit [NeZero k] in
theorem gu6_set3_perm₃ {α : Type*} (x y z : α) : ({y, z, x} : Set α) = {x, y, z} := by
  ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
omit [NeZero k] in
theorem gu6_set3_perm₄ {α : Type*} (x y z : α) : ({z, x, y} : Set α) = {x, y, z} := by
  ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
omit [NeZero k] in
theorem gu6_set3_perm₅ {α : Type*} (x y z : α) : ({z, y, x} : Set α) = {x, y, z} := by
  ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

omit [NeZero k] in
/-- three distinct members of a three-element set are the set -/
theorem gu6_triple_eq {α : Type*} {a b c x y z : α} (hx : x = a ∨ x = b ∨ x = c)
    (hy : y = a ∨ y = b ∨ y = c) (hz : z = a ∨ z = b ∨ z = c) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ({x, y, z} : Set α) = {a, b, c} := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hxy
    | exact absurd rfl hyz
    | exact absurd rfl hxz
    | (ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto)

omit [NeZero k] in
/-- the permutations of a three-fold disjunction -/
theorem gu6_or3 (a b c : Prop) :
    (a ∨ b ∨ c ↔ b ∨ a ∨ c) ∧ (a ∨ b ∨ c ↔ b ∨ c ∨ a) ∧ (a ∨ b ∨ c ↔ a ∨ c ∨ b) ∧
      (a ∨ b ∨ c ↔ c ∨ a ∨ b) ∧ (a ∨ b ∨ c ↔ c ∨ b ∨ a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> tauto

omit [NeZero k] in
/-- **the Reidemeister-III site from strand-named data**: three arcs on each side named by strand
(`m, p, q`), the six inner crossings, the over/under memberships governed by the three over relations
`Rmp, Rmq, Rpq` (identical on both sides), transitivity, and the three reversals. The arcs are renamed
by height (six cases). -/
theorem gu6_riii_of_strands {U : Set Plane} {D D' : Diagram} (frame : LocalFrame U D D')
    (out : MoveMatch U D D') (Am Ap Aq : D.Γ.Arc) (Am' Ap' Aq' : D'.Γ.Arc)
    (hmp : Am ≠ Ap) (hmq : Am ≠ Aq) (hpq : Ap ≠ Aq) (hmp' : Am' ≠ Ap') (hmq' : Am' ≠ Aq') (hpq' : Ap' ≠ Aq')
    (cover : D.Γ.ArcCover U {Am, Ap, Aq}) (cover' : D'.Γ.ArcCover U {Am', Ap', Aq'})
    (hm_s : D'.Γ.eval Am'.startPt = D.Γ.eval Am.startPt) (hm_e : D'.Γ.eval Am'.stopPt = D.Γ.eval Am.stopPt)
    (hp_s : D'.Γ.eval Ap'.startPt = D.Γ.eval Ap.startPt) (hp_e : D'.Γ.eval Ap'.stopPt = D.Γ.eval Ap.stopPt)
    (hq_s : D'.Γ.eval Aq'.startPt = D.Γ.eval Aq.startPt) (hq_e : D'.Γ.eval Aq'.stopPt = D.Γ.eval Aq.stopPt)
    (y_mp y_mq y_pq : D.Γ.Crossing) (n1 : y_mp ≠ y_mq) (n2 : y_mp ≠ y_pq) (n3 : y_mq ≠ y_pq)
    (inner0 : ∀ y, D.Γ.crossingPoint y ∈ interior U ↔ y = y_mp ∨ y = y_mq ∨ y = y_pq)
    (y'_pC y'_qB y'_pq : D'.Γ.Crossing) (n1' : y'_pC ≠ y'_qB) (n2' : y'_pC ≠ y'_pq) (n3' : y'_qB ≠ y'_pq)
    (inner1 : ∀ y, D'.Γ.crossingPoint y ∈ interior U ↔ y = y'_pC ∨ y = y'_qB ∨ y = y'_pq)
    (Rmp Rmq Rpq : Prop)
    (hov_mp : (Rmp → D.OverOn Am y_mp ∧ D.UnderOn Ap y_mp) ∧ (¬ Rmp → D.OverOn Ap y_mp ∧ D.UnderOn Am y_mp))
    (hov_mq : (Rmq → D.OverOn Am y_mq ∧ D.UnderOn Aq y_mq) ∧ (¬ Rmq → D.OverOn Aq y_mq ∧ D.UnderOn Am y_mq))
    (hov_pq : (Rpq → D.OverOn Ap y_pq ∧ D.UnderOn Aq y_pq) ∧ (¬ Rpq → D.OverOn Aq y_pq ∧ D.UnderOn Ap y_pq))
    (hov_mp' : (Rmp → D'.OverOn Am' y'_pC ∧ D'.UnderOn Ap' y'_pC) ∧
      (¬ Rmp → D'.OverOn Ap' y'_pC ∧ D'.UnderOn Am' y'_pC))
    (hov_mq' : (Rmq → D'.OverOn Am' y'_qB ∧ D'.UnderOn Aq' y'_qB) ∧
      (¬ Rmq → D'.OverOn Aq' y'_qB ∧ D'.UnderOn Am' y'_qB))
    (hov_pq' : (Rpq → D'.OverOn Ap' y'_pq ∧ D'.UnderOn Aq' y'_pq) ∧
      (¬ Rpq → D'.OverOn Aq' y'_pq ∧ D'.UnderOn Ap' y'_pq))
    (htrans : ¬ (Rmp ∧ Rpq ∧ ¬ Rmq) ∧ ¬ (¬ Rmp ∧ ¬ Rpq ∧ Rmq))
    (rev_m : D.BeforeOn Am y_mp y_mq ↔ D'.BeforeOn Am' y'_qB y'_pC)
    (rev_p : D.BeforeOn Ap y_mp y_pq ↔ D'.BeforeOn Ap' y'_pq y'_pC)
    (rev_q : D.BeforeOn Aq y_mq y_pq ↔ D'.BeforeOn Aq' y'_pq y'_qB) :
    Nonempty (RIIIData U D D') := by
  classical
  have mAm : Am ∈ ({Am, Ap, Aq} : Set D.Γ.Arc) := Set.mem_insert _ _
  have mAp : Ap ∈ ({Am, Ap, Aq} : Set D.Γ.Arc) := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have mAq : Aq ∈ ({Am, Ap, Aq} : Set D.Γ.Arc) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have mAm' : Am' ∈ ({Am', Ap', Aq'} : Set D'.Γ.Arc) := Set.mem_insert _ _
  have mAp' : Ap' ∈ ({Am', Ap', Aq'} : Set D'.Γ.Arc) := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have mAq' : Aq' ∈ ({Am', Ap', Aq'} : Set D'.Γ.Arc) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have sep_mp : D.Separates Am Ap y_mp := by
    by_cases h : Rmp
    · exact Or.inl (hov_mp.1 h)
    · exact Or.inr (hov_mp.2 h)
  have sep_mq : D.Separates Am Aq y_mq := by
    by_cases h : Rmq
    · exact Or.inl (hov_mq.1 h)
    · exact Or.inr (hov_mq.2 h)
  have sep_pq : D.Separates Ap Aq y_pq := by
    by_cases h : Rpq
    · exact Or.inl (hov_pq.1 h)
    · exact Or.inr (hov_pq.2 h)
  have sep_mp' : D'.Separates Am' Ap' y'_pC := by
    by_cases h : Rmp
    · exact Or.inl (hov_mp'.1 h)
    · exact Or.inr (hov_mp'.2 h)
  have sep_mq' : D'.Separates Am' Aq' y'_qB := by
    by_cases h : Rmq
    · exact Or.inl (hov_mq'.1 h)
    · exact Or.inr (hov_mq'.2 h)
  have sep_pq' : D'.Separates Ap' Aq' y'_pq := by
    by_cases h : Rpq
    · exact Or.inl (hov_pq'.1 h)
    · exact Or.inr (hov_pq'.2 h)
  have i_mp : D.Γ.crossingPoint y_mp ∈ interior U := (inner0 _).mpr (Or.inl rfl)
  have i_mq : D.Γ.crossingPoint y_mq ∈ interior U := (inner0 _).mpr (Or.inr (Or.inl rfl))
  have i_pq : D.Γ.crossingPoint y_pq ∈ interior U := (inner0 _).mpr (Or.inr (Or.inr rfl))
  have i_pC : D'.Γ.crossingPoint y'_pC ∈ interior U := (inner1 _).mpr (Or.inl rfl)
  have i_qB : D'.Γ.crossingPoint y'_qB ∈ interior U := (inner1 _).mpr (Or.inr (Or.inl rfl))
  have i_pq' : D'.Γ.crossingPoint y'_pq ∈ interior U := (inner1 _).mpr (Or.inr (Or.inr rfl))
  have rev_m' : D.BeforeOn Am y_mq y_mp ↔ D'.BeforeOn Am' y'_pC y'_qB :=
    gu6_rev_swap cover cover' mAm mAp mAq hmp hmq n1 i_mp i_mq sep_mp sep_mq mAm' mAp' mAq' hmp' hmq'
      n1' i_pC i_qB sep_mp' sep_mq' rev_m
  have rev_p' : D.BeforeOn Ap y_pq y_mp ↔ D'.BeforeOn Ap' y'_pC y'_pq :=
    gu6_rev_swap cover cover' mAp mAm mAq hmp.symm hpq n2 i_mp i_pq sep_mp.symm sep_pq mAp' mAm' mAq'
      hmp'.symm hpq' n2' i_pC i_pq' sep_mp'.symm sep_pq' rev_p
  have rev_q' : D.BeforeOn Aq y_pq y_mq ↔ D'.BeforeOn Aq' y'_qB y'_pq :=
    gu6_rev_swap cover cover' mAq mAm mAp hmq.symm hpq.symm n3 i_mq i_pq sep_mq.symm sep_pq.symm mAq'
      mAm' mAp' hmq'.symm hpq'.symm n3' i_qB i_pq' sep_mq'.symm sep_pq'.symm rev_q
  by_cases h1 : Rmp <;> by_cases h2 : Rmq <;> by_cases h3 : Rpq
  · -- m > p > q
    exact gu6_riii_build frame out Am Ap Aq Am' Ap' Aq' hmp hpq hmq hmp' hpq' hmq' cover cover'
      hm_s hm_e hp_s hp_e hq_s hq_e y_mp y_mq y_pq n1 n2 n3 inner0 y'_pC y'_qB y'_pq n1' n2' n3' inner1
      (hov_mp.1 h1).1 (hov_mp.1 h1).2 (hov_mq.1 h2).1 (hov_mq.1 h2).2 (hov_pq.1 h3).1 (hov_pq.1 h3).2
      (hov_mp'.1 h1).1 (hov_mp'.1 h1).2 (hov_mq'.1 h2).1 (hov_mq'.1 h2).2 (hov_pq'.1 h3).1 (hov_pq'.1 h3).2
      rev_m rev_p rev_q
  · -- m > q > p
    exact gu6_riii_build frame out Am Aq Ap Am' Aq' Ap' hmq hpq.symm hmp hmq' hpq'.symm hmp'
      (by rw [gu6_set3_perm₁]; exact cover) (by rw [gu6_set3_perm₁]; exact cover')
      hm_s hm_e hq_s hq_e hp_s hp_e y_mq y_mp y_pq n1.symm n3 n2
      (fun y => (inner0 y).trans (gu6_or3 _ _ _).1) y'_qB y'_pC y'_pq n1'.symm n3' n2'
      (fun y => (inner1 y).trans (gu6_or3 _ _ _).1)
      (hov_mq.1 h2).1 (hov_mq.1 h2).2 (hov_mp.1 h1).1 (hov_mp.1 h1).2 (hov_pq.2 h3).1 (hov_pq.2 h3).2
      (hov_mq'.1 h2).1 (hov_mq'.1 h2).2 (hov_mp'.1 h1).1 (hov_mp'.1 h1).2 (hov_pq'.2 h3).1 (hov_pq'.2 h3).2
      rev_m' rev_q rev_p
  · -- m > p, p > q, q > m : alternating
    exact absurd ⟨h1, h3, h2⟩ htrans.1
  · -- q > m > p
    exact gu6_riii_build frame out Aq Am Ap Aq' Am' Ap' hmq.symm hmp hpq.symm hmq'.symm hmp' hpq'.symm
      (by rw [gu6_set3_perm₄]; exact cover) (by rw [gu6_set3_perm₄]; exact cover')
      hq_s hq_e hm_s hm_e hp_s hp_e y_mq y_pq y_mp n3 n1.symm n2.symm
      (fun y => (inner0 y).trans (gu6_or3 _ _ _).2.1) y'_qB y'_pq y'_pC n3' n1'.symm n2'.symm
      (fun y => (inner1 y).trans (gu6_or3 _ _ _).2.1)
      (hov_mq.2 h2).1 (hov_mq.2 h2).2 (hov_pq.2 h3).1 (hov_pq.2 h3).2 (hov_mp.1 h1).1 (hov_mp.1 h1).2
      (hov_mq'.2 h2).1 (hov_mq'.2 h2).2 (hov_pq'.2 h3).1 (hov_pq'.2 h3).2 (hov_mp'.1 h1).1 (hov_mp'.1 h1).2
      rev_q rev_m' rev_p'
  · -- p > m > q
    exact gu6_riii_build frame out Ap Am Aq Ap' Am' Aq' hmp.symm hmq hpq hmp'.symm hmq' hpq'
      (by rw [gu6_set3_perm₂]; exact cover) (by rw [gu6_set3_perm₂]; exact cover')
      hp_s hp_e hm_s hm_e hq_s hq_e y_mp y_pq y_mq n2 n1 n3.symm
      (fun y => (inner0 y).trans (gu6_or3 _ _ _).2.2.1) y'_pC y'_pq y'_qB n2' n1' n3'.symm
      (fun y => (inner1 y).trans (gu6_or3 _ _ _).2.2.1)
      (hov_mp.2 h1).1 (hov_mp.2 h1).2 (hov_pq.1 h3).1 (hov_pq.1 h3).2 (hov_mq.1 h2).1 (hov_mq.1 h2).2
      (hov_mp'.2 h1).1 (hov_mp'.2 h1).2 (hov_pq'.1 h3).1 (hov_pq'.1 h3).2 (hov_mq'.1 h2).1 (hov_mq'.1 h2).2
      rev_p rev_m rev_q'
  · -- p > m, m > q, q > p : alternating
    exact absurd ⟨h1, h3, h2⟩ htrans.2
  · -- p > q > m
    exact gu6_riii_build frame out Ap Aq Am Ap' Aq' Am' hpq hmq.symm hmp.symm hpq' hmq'.symm hmp'.symm
      (by rw [gu6_set3_perm₃]; exact cover) (by rw [gu6_set3_perm₃]; exact cover')
      hp_s hp_e hq_s hq_e hm_s hm_e y_pq y_mp y_mq n2.symm n3.symm n1
      (fun y => (inner0 y).trans (gu6_or3 _ _ _).2.2.2.1) y'_pq y'_pC y'_qB n2'.symm n3'.symm n1'
      (fun y => (inner1 y).trans (gu6_or3 _ _ _).2.2.2.1)
      (hov_pq.1 h3).1 (hov_pq.1 h3).2 (hov_mp.2 h1).1 (hov_mp.2 h1).2 (hov_mq.2 h2).1 (hov_mq.2 h2).2
      (hov_pq'.1 h3).1 (hov_pq'.1 h3).2 (hov_mp'.2 h1).1 (hov_mp'.2 h1).2 (hov_mq'.2 h2).1 (hov_mq'.2 h2).2
      rev_p' rev_q' rev_m
  · -- q > p > m
    exact gu6_riii_build frame out Aq Ap Am Aq' Ap' Am' hpq.symm hmp.symm hmq.symm hpq'.symm hmp'.symm
      hmq'.symm (by rw [gu6_set3_perm₅]; exact cover) (by rw [gu6_set3_perm₅]; exact cover')
      hq_s hq_e hp_s hp_e hm_s hm_e y_pq y_mq y_mp n3.symm n2.symm n1.symm
      (fun y => (inner0 y).trans (gu6_or3 _ _ _).2.2.2.2) y'_pq y'_qB y'_pC n3'.symm n2'.symm n1'.symm
      (fun y => (inner1 y).trans (gu6_or3 _ _ _).2.2.2.2)
      (hov_pq.2 h3).1 (hov_pq.2 h3).2 (hov_mq.2 h2).1 (hov_mq.2 h2).2 (hov_mp.2 h1).1 (hov_mp.2 h1).2
      (hov_pq'.2 h3).1 (hov_pq'.2 h3).2 (hov_mq'.2 h2).1 (hov_mq'.2 h2).2 (hov_mp'.2 h1).1 (hov_mp'.2 h1).2
      rev_q' rev_p' rev_m'

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

omit [NeZero k] in
/-- two pair-crossings with different supports are different -/
theorem gu6_xPair_ne_of_not_mem {Cp : PolyComp} {i j i' j' : ZMod Cp.k} (h : IsCrossing Cp.P {i, j})
    (h' : IsCrossing Cp.P {i', j'}) (hi : i ≠ i') (hj : i ≠ j') :
    (Shadow.singleCrossingEquiv Cp).symm (xPair h) ≠ (Shadow.singleCrossingEquiv Cp).symm (xPair h') := by
  intro e
  have e1 := (Shadow.singleCrossingEquiv Cp).symm.injective e
  have e2 := congrArg Subtype.val e1
  change ({i, j} : Finset (ZMod Cp.k)) = {i', j'} at e2
  have : i ∈ ({i', j'} : Finset (ZMod Cp.k)) := by rw [← e2]; exact mem_pair_left _ _
  rw [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h
  · exact hi h
  · exact hj h

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

/-- transitivity of the heights, in the form used by the assembly -/
theorem gu6_htrans :
    ¬ (0 < det (edge C.X C.m) (edge C.X C.p) ∧ 0 < det (edge C.X C.p) (edge C.X C.q) ∧
        ¬ 0 < det (edge C.X C.m) (edge C.X C.q)) ∧
      ¬ (¬ 0 < det (edge C.X C.m) (edge C.X C.p) ∧ ¬ 0 < det (edge C.X C.p) (edge C.X C.q) ∧
        0 < det (edge C.X C.m) (edge C.X C.q)) := by
  constructor
  · rintro ⟨h1, h3, h2⟩
    have h2' : det (edge C.X C.m) (edge C.X C.q) < 0 := lt_of_le_of_ne (not_lt.mp h2) (gu6_det_mq_ne (C := C))
    apply C.trans
    unfold IsAlternating crossingSign
    rw [sign_pos h1, sign_pos h3, sign_neg h2']
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h3, h2⟩
    have h1' : det (edge C.X C.m) (edge C.X C.p) < 0 := lt_of_le_of_ne (not_lt.mp h1) (gu6_det_mp_ne (C := C))
    have h3' : det (edge C.X C.p) (edge C.X C.q) < 0 := lt_of_le_of_ne (not_lt.mp h3) (gu6_det_pq_ne (C := C))
    apply C.trans
    unfold IsAlternating crossingSign
    rw [sign_neg h1', sign_neg h3', sign_pos h2]
    exact ⟨rfl, rfl⟩

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

/-- **D8 (assembly of the site).** `RIIIData U M₀ M₁` from D1–D7: the arcs named by height (the `trans`
clause of the configuration gives one strict height order; six cases, one instantiation per permutation of
`{m, p, q}`), `Separates`/`OverOn` from the positive diagrams and `X₁_sign_*`, the three `BeforeOn`
reversals from the explicit parameters (`x_pq` lies strictly between the two crossings of `p` (resp. `q`)
with `Θ`'s boundary along `p` (resp. `q`); along the bent strand `x_mq'` on `[p_in, w]` precedes `x_mp'`
on `[w, p_out]`). -/
theorem riii : RIII π.M₀ π.M₁ := by
  classical
  obtain ⟨a, b, c, a', b', c', hab, hbc, hac, hab', hbc', hac', cover, cover',
    ha_s, ha_e, hb_s, hb_e, hc_s, hc_e⟩ := π.exists_arcCovers
  obtain ⟨mm⟩ := π.exists_moveMatch
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
  have hov_mp : (0 < det (edge C.X C.m) (edge C.X C.p) →
        π.M₀.OverOn Am π.gu6_y_mp ∧ π.M₀.UnderOn Ap π.gu6_y_mp) ∧
      (¬ 0 < det (edge C.X C.m) (edge C.X C.p) →
        π.M₀.OverOn Ap π.gu6_y_mp ∧ π.M₀.UnderOn Am π.gu6_y_mp) := by
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := π.gu6_ov_mp_pos h
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hm1.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hp1.mem⟩
    · intro h
      obtain ⟨h1, h2⟩ := π.gu6_ov_mp_neg h
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hp1.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hm1.mem⟩
  have hov_mq : (0 < det (edge C.X C.m) (edge C.X C.q) →
        π.M₀.OverOn Am π.gu6_y_mq ∧ π.M₀.UnderOn Aq π.gu6_y_mq) ∧
      (¬ 0 < det (edge C.X C.m) (edge C.X C.q) →
        π.M₀.OverOn Aq π.gu6_y_mq ∧ π.M₀.UnderOn Am π.gu6_y_mq) := by
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := π.gu6_ov_mq_pos h
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hm2.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hq1.mem⟩
    · intro h
      obtain ⟨h1, h2⟩ := π.gu6_ov_mq_neg h
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hq1.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hm2.mem⟩
  have hov_pq : (0 < det (edge C.X C.p) (edge C.X C.q) →
        π.M₀.OverOn Ap π.gu6_y_pq ∧ π.M₀.UnderOn Aq π.gu6_y_pq) ∧
      (¬ 0 < det (edge C.X C.p) (edge C.X C.q) →
        π.M₀.OverOn Aq π.gu6_y_pq ∧ π.M₀.UnderOn Ap π.gu6_y_pq) := by
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := π.gu6_ov_pq_pos h
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hp2.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hq2.mem⟩
    · intro h
      obtain ⟨h1, h2⟩ := π.gu6_ov_pq_neg h
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hq2.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hp2.mem⟩
  have hov_mp' : (0 < det (edge C.X C.m) (edge C.X C.p) →
        π.M₁.OverOn Am' π.gu6_y'_pC ∧ π.M₁.UnderOn Ap' π.gu6_y'_pC) ∧
      (¬ 0 < det (edge C.X C.m) (edge C.X C.p) →
        π.M₁.OverOn Ap' π.gu6_y'_pC ∧ π.M₁.UnderOn Am' π.gu6_y'_pC) := by
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := π.gu6_ov_pC_pos h
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hCp.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hpC.mem⟩
    · intro h
      obtain ⟨h1, h2⟩ := π.gu6_ov_pC_neg h
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hpC.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hCp.mem⟩
  have hov_mq' : (0 < det (edge C.X C.m) (edge C.X C.q) →
        π.M₁.OverOn Am' π.gu6_y'_qB ∧ π.M₁.UnderOn Aq' π.gu6_y'_qB) ∧
      (¬ 0 < det (edge C.X C.m) (edge C.X C.q) →
        π.M₁.OverOn Aq' π.gu6_y'_qB ∧ π.M₁.UnderOn Am' π.gu6_y'_qB) := by
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := π.gu6_ov_qB_pos h
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hBq.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hqB.mem⟩
    · intro h
      obtain ⟨h1, h2⟩ := π.gu6_ov_qB_neg h
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hqB.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hBq.mem⟩
  have hov_pq' : (0 < det (edge C.X C.p) (edge C.X C.q) →
        π.M₁.OverOn Ap' π.gu6_y'_pq ∧ π.M₁.UnderOn Aq' π.gu6_y'_pq) ∧
      (¬ 0 < det (edge C.X C.p) (edge C.X C.q) →
        π.M₁.OverOn Aq' π.gu6_y'_pq ∧ π.M₁.UnderOn Ap' π.gu6_y'_pq) := by
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := π.gu6_ov_pq'_pos h
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hpq2.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hqp2.mem⟩
    · intro h
      obtain ⟨h1, h2⟩ := π.gu6_ov_pq'_neg h
      exact ⟨by unfold Diagram.OverOn; rw [h1]; exact hqp2.mem,
        by unfold Diagram.UnderOn; rw [h2]; exact hpq2.mem⟩
  -- separations used for the reversal clauses
  have sepPM : π.M₀.Separates Ap Am π.gu6_y_mp := by
    by_cases h : 0 < det (edge C.X C.m) (edge C.X C.p)
    · exact Or.inr (hov_mp.1 h)
    · exact Or.inl (hov_mp.2 h)
  have sepPQ : π.M₀.Separates Ap Aq π.gu6_y_pq := by
    by_cases h : 0 < det (edge C.X C.p) (edge C.X C.q)
    · exact Or.inl (hov_pq.1 h)
    · exact Or.inr (hov_pq.2 h)
  have sepQM : π.M₀.Separates Aq Am π.gu6_y_mq := by
    by_cases h : 0 < det (edge C.X C.m) (edge C.X C.q)
    · exact Or.inr (hov_mq.1 h)
    · exact Or.inl (hov_mq.2 h)
  have sepQP : π.M₀.Separates Aq Ap π.gu6_y_pq := sepPQ.symm
  have sepPM' : π.M₁.Separates Ap' Am' π.gu6_y'_pC := by
    by_cases h : 0 < det (edge C.X C.m) (edge C.X C.p)
    · exact Or.inr (hov_mp'.1 h)
    · exact Or.inl (hov_mp'.2 h)
  have sepPQ' : π.M₁.Separates Ap' Aq' π.gu6_y'_pq := by
    by_cases h : 0 < det (edge C.X C.p) (edge C.X C.q)
    · exact Or.inl (hov_pq'.1 h)
    · exact Or.inr (hov_pq'.2 h)
  have sepQM' : π.M₁.Separates Aq' Am' π.gu6_y'_qB := by
    by_cases h : 0 < det (edge C.X C.m) (edge C.X C.q)
    · exact Or.inr (hov_mq'.1 h)
    · exact Or.inl (hov_mq'.2 h)
  have sepQP' : π.M₁.Separates Aq' Ap' π.gu6_y'_pq := sepPQ'.symm
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
  have rev_m : π.M₀.BeforeOn Am π.gu6_y_mp π.gu6_y_mq ↔ π.M₁.BeforeOn Am' π.gu6_y'_qB π.gu6_y'_pC :=
    iff_of_true ⟨π.w_mp, π.w_mq, π.gu6_w_mp_fst, π.gu6_w_mq_fst, hbef_m⟩
      ⟨π.gu6_w'_Bq, π.gu6_w'_Cp, π.gu6_w'_Bq_fst, π.gu6_w'_Cp_fst, hbef_m'⟩
  -- the reversal along `p` (D9)
  have hbp : π.M₀.BeforeOn Ap π.gu6_y_mp π.gu6_y_pq ↔
      Ap.Before (π.M₀.visitPt π.w_pm) (π.M₀.visitPt π.w_pq) :=
    π.M₀.beforeOn_iff_before cover hAp hAm hAq hmp.symm hpq sepPM sepPQ π.gu6_w_pm_fst π.gu6_w_pq_fst
      hp1.mem hp2.mem
  have hbp' : π.M₁.BeforeOn Ap' π.gu6_y'_pq π.gu6_y'_pC ↔
      Ap'.Before (π.M₁.visitPt π.gu6_w'_pq) (π.M₁.visitPt π.gu6_w'_pC) :=
    π.M₁.beforeOn_iff_before cover' hAp' hAq' hAm' hpq' hmp'.symm sepPQ' sepPM' π.gu6_w'_pq_fst
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
  have rev_p : π.M₀.BeforeOn Ap π.gu6_y_mp π.gu6_y_pq ↔ π.M₁.BeforeOn Ap' π.gu6_y'_pq π.gu6_y'_pC := by
    rw [hbp, hbp', hbp2, hbp2', gu6_s'_pq_eq]
    exact π.gu6_D9_p
  -- the reversal along `q` (D9)
  have hbq : π.M₀.BeforeOn Aq π.gu6_y_mq π.gu6_y_pq ↔
      Aq.Before (π.M₀.visitPt π.w_qm) (π.M₀.visitPt π.w_qp) :=
    π.M₀.beforeOn_iff_before cover hAq hAm hAp hmq.symm hpq.symm sepQM sepQP π.gu6_w_qm_fst
      π.gu6_w_qp_fst hq1.mem hq2.mem
  have hbq' : π.M₁.BeforeOn Aq' π.gu6_y'_pq π.gu6_y'_qB ↔
      Aq'.Before (π.M₁.visitPt π.gu6_w'_qp) (π.M₁.visitPt π.gu6_w'_qB) :=
    π.M₁.beforeOn_iff_before cover' hAq' hAp' hAm' hpq'.symm hmq'.symm sepQP' sepQM' π.gu6_w'_qp_fst
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
  have rev_q : π.M₀.BeforeOn Aq π.gu6_y_mq π.gu6_y_pq ↔ π.M₁.BeforeOn Aq' π.gu6_y'_pq π.gu6_y'_qB := by
    rw [hbq, hbq', hbq2, hbq2', gu6_s'_qp_eq]
    exact π.gu6_D9_q
  -- assembly
  exact ⟨π.U, Or.inl (gu6_riii_of_strands ⟨π.disc_isDisc, π.clean_M₀, π.clean_M₁⟩ mm Am Ap Aq Am' Ap' Aq'
    hmp hmq hpq hmp' hmq' hpq' cover₀ cover₁ hm_s hm_e hp_s hp_e hq_s hq_e
    π.gu6_y_mp π.gu6_y_mq π.gu6_y_pq π.gu6_y_mp_ne_mq π.gu6_y_mp_ne_pq π.gu6_y_mq_ne_pq π.gu6_inner0
    π.gu6_y'_pC π.gu6_y'_qB π.gu6_y'_pq π.gu6_y'_pC_ne_qB π.gu6_y'_pC_ne_pq π.gu6_y'_qB_ne_pq π.gu6_inner1
    _ _ _ hov_mp hov_mq hov_pq hov_mp' hov_mq' hov_pq' (gu6_htrans (C := C)) rev_m rev_p rev_q)⟩

/-- `P(M₁) = P(M₀)` by `ax:homfly` (accepted `homfly_reidemeister_III`). -/
theorem homfly_M₁ : homfly π.M₁ = homfly π.M₀ :=
  (homfly_reidemeister_III π.riii).symm

/-! ### Unit E leaves — the record of `M₁` -/

/-! #### U6 helpers for E1 (a): the occurrence bijection `Ψ₁ : M₀ ≃ M₁` -/

omit [NeZero n] in
/-- U6 helper: two visits with different edges are different. -/
theorem gu6_visit_ne_of_edge {P : LabelledTuple n} {u v : Visit P} (h : u.2.val ≠ v.2.val) : u ≠ v :=
  fun h' => h (by rw [h'])

omit [NeZero n] in
/-- U6 helper: a swap of two visits on one edge preserves the edge of every visit. -/
theorem gu6_swap_edge {P : LabelledTuple n} (a b : Visit P) (h : a.2.val = b.2.val) (x : Visit P) :
    (Equiv.swap a b x).2.val = x.2.val := by
  by_cases h1 : x = a
  · subst h1; rw [Equiv.swap_apply_left]; exact h.symm
  · by_cases h2 : x = b
    · subst h2; rw [Equiv.swap_apply_right]; exact h
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

omit [NeZero n] in
/-- U6 helper: a visit is determined by its crossing and its edge. -/
theorem gu6_visit_ext {P : LabelledTuple n} {u w : Visit P} (h1 : u.1 = w.1) (h2 : u.2.val = w.2.val) :
    u = w := by
  obtain ⟨c, i⟩ := u
  obtain ⟨d, j⟩ := w
  change c = d at h1
  subst h1
  change i.val = j.val at h2
  rw [Subtype.ext h2]

omit [NeZero n] in
theorem gu6_isCrossing_comm {P : LabelledTuple n} {i j : ZMod n} (h : IsCrossing P {i, j}) :
    IsCrossing P {j, i} := by
  rwa [Finset.pair_comm]

/-- U6 helper: on a visit of the strand `m`, `σ` is the swap `x_mp ↔ x_mq`. -/
theorem gu6_σ_on_m {k : ℕ} [NeZero k] (C : G11_Config k) (x : Visit C.X) (hx : x.2.val = C.m) :
    C.σ x = Equiv.swap C.vmp C.vmq x := by
  have hmp : C.m ≠ C.p := P1.ne_of_isCrossing_pair C.hmp
  have hmq : C.m ≠ C.q := P1.ne_of_isCrossing_pair C.hmq
  have h1 : x ≠ C.vqm := gu6_visit_ne_of_edge (by rw [hx]; exact hmq)
  have h2 : x ≠ C.vqp := gu6_visit_ne_of_edge (by rw [hx]; exact hmq)
  have h3 : x ≠ C.vpm := gu6_visit_ne_of_edge (by rw [hx]; exact hmp)
  have h4 : x ≠ C.vpq := gu6_visit_ne_of_edge (by rw [hx]; exact hmp)
  unfold G11_Config.σ
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2,
    Equiv.swap_apply_of_ne_of_ne h3 h4]

/-- U6 helper: on a visit of the strand `p`, `σ` is the swap `x_pm ↔ x_pq`. -/
theorem gu6_σ_on_p {k : ℕ} [NeZero k] (C : G11_Config k) (x : Visit C.X) (hx : x.2.val = C.p) :
    C.σ x = Equiv.swap C.vpm C.vpq x := by
  have hmp : C.m ≠ C.p := P1.ne_of_isCrossing_pair C.hmp
  have hpq : C.p ≠ C.q := P1.ne_of_isCrossing_pair C.hpq
  have h1 : x ≠ C.vqm := gu6_visit_ne_of_edge (by rw [hx]; exact hpq)
  have h2 : x ≠ C.vqp := gu6_visit_ne_of_edge (by rw [hx]; exact hpq)
  have h3 : Equiv.swap C.vpm C.vpq x ≠ C.vmp :=
    gu6_visit_ne_of_edge (by rw [gu6_swap_edge C.vpm C.vpq rfl, hx]; exact hmp.symm)
  have h4 : Equiv.swap C.vpm C.vpq x ≠ C.vmq :=
    gu6_visit_ne_of_edge (by rw [gu6_swap_edge C.vpm C.vpq rfl, hx]; exact hmp.symm)
  unfold G11_Config.σ
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2,
    Equiv.swap_apply_of_ne_of_ne h3 h4]

/-- U6 helper: on a visit of the strand `q`, `σ` is the swap `x_qm ↔ x_qp`. -/
theorem gu6_σ_on_q {k : ℕ} [NeZero k] (C : G11_Config k) (x : Visit C.X) (hx : x.2.val = C.q) :
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
  unfold G11_Config.σ
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h3 h4,
    Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- U6 helper: the six values of `σ` on the local visits. -/
theorem gu6_σ_vmp {k : ℕ} [NeZero k] (C : G11_Config k) : C.σ C.vmp = C.vmq := by
  rw [gu6_σ_on_m C _ rfl, Equiv.swap_apply_left]

theorem gu6_σ_vmq {k : ℕ} [NeZero k] (C : G11_Config k) : C.σ C.vmq = C.vmp := by
  rw [gu6_σ_on_m C _ rfl, Equiv.swap_apply_right]

theorem gu6_σ_vpm {k : ℕ} [NeZero k] (C : G11_Config k) : C.σ C.vpm = C.vpq := by
  rw [gu6_σ_on_p C _ rfl, Equiv.swap_apply_left]

theorem gu6_σ_vpq {k : ℕ} [NeZero k] (C : G11_Config k) : C.σ C.vpq = C.vpm := by
  rw [gu6_σ_on_p C _ rfl, Equiv.swap_apply_right]

theorem gu6_σ_vqm {k : ℕ} [NeZero k] (C : G11_Config k) : C.σ C.vqm = C.vqp := by
  rw [gu6_σ_on_q C _ rfl, Equiv.swap_apply_left]

theorem gu6_σ_vqp {k : ℕ} [NeZero k] (C : G11_Config k) : C.σ C.vqp = C.vqm := by
  rw [gu6_σ_on_q C _ rfl, Equiv.swap_apply_right]

/-- U6 helper: `σ` fixes every visit other than the six local ones. -/
theorem gu6_σ_of_not_local {k : ℕ} [NeZero k] (C : G11_Config k) (x : Visit C.X)
    (h1 : x ≠ C.vmp) (h2 : x ≠ C.vmq) (h3 : x ≠ C.vpm) (h4 : x ≠ C.vpq) (h5 : x ≠ C.vqm)
    (h6 : x ≠ C.vqp) : C.σ x = x := by
  unfold G11_Config.σ
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h5 h6,
    Equiv.swap_apply_of_ne_of_ne h3 h4, Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- U6 helper: `σD` read through `singleVisitEquiv`. -/
theorem gu6_σD_apply {k : ℕ} [NeZero k] (C : G11_Config k) (x : Visit C.X) :
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

omit [NeZero k] in
theorem gu6_sv_strand' {Cp : PolyComp} (w : Visit Cp.P) :
    ((Shadow.singleVisitEquiv Cp).symm w).2.val = ⟨0, w.2.val⟩ := by
  obtain ⟨y, ⟨i, hi⟩⟩ := w
  exact gu6_sv_strand y hi

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

omit [NeZero k] in
/-- the over bit of a positive one-component diagram is the sign of `det(own strand, twin strand)` -/
theorem gu6_overBit_iff_det {Cp : PolyComp} (hΓ : (Shadow.single Cp).Generic)
    (v : ((Shadow.single Cp).positiveDiagram hΓ).Γ.Visit) :
    ((Shadow.single Cp).positiveDiagram hΓ).overBit v = true ↔
      0 < det ((Shadow.single Cp).dir v.2.val)
        ((Shadow.single Cp).dir (((Shadow.single Cp).positiveDiagram hΓ).twin v).2.val) := by
  rw [Diagram.overBit_eq_true_iff]
  constructor
  · intro h
    have hd := Shadow.positiveDiagram_det_pos (Shadow.single Cp) hΓ v.1
    have e : (((Shadow.single Cp).positiveDiagram hΓ).twin v).2.val =
        ((Shadow.single Cp).positiveDiagram hΓ).underStrand v.1 :=
      ((Shadow.single Cp).eq_other_of_mem_of_ne v.1 v.2.2
        (((Shadow.single Cp).positiveDiagram hΓ).under_mem v.1)
        (fun e => ((Shadow.single Cp).positiveDiagram hΓ).under_ne_over v.1 (e.trans h))).symm
    rw [e]
    change 0 < det ((Shadow.single Cp).dir v.2.val)
      ((Shadow.single Cp).dir ((Shadow.single Cp).other v.1
        (((Shadow.single Cp).positiveDiagram hΓ).over_mem v.1)))
    have h' : v.2.val = ((Shadow.single Cp).positiveDiagram hΓ).overStrand v.1 := h
    rw [h']
    exact hd
  · intro hpos
    exact (gu6_overStrand_eq hΓ v.1 v.2.2 hpos).symm

omit [NeZero k] in
/-- `0 < A ↔ 0 < B` for nonzero `A, B` gives `A < 0 ↔ B < 0` -/
theorem gu6_neg_iff_of_pos_iff {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (h : 0 < A ↔ 0 < B) :
    A < 0 ↔ B < 0 := by
  constructor
  · intro h1
    rcases lt_trichotomy B 0 with h2 | h2 | h2
    · exact h2
    · exact absurd h2 hB
    · exact absurd (h.mpr h2) (lt_asymm h1)
  · intro h1
    rcases lt_trichotomy A 0 with h2 | h2 | h2
    · exact h2
    · exact absurd h2 hA
    · exact absurd (h.mp h2) (lt_asymm h1)

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

omit [NeZero k] in
theorem gu6_strand_eq_iff {Cp : PolyComp} (l : ZMod Cp.k) (s : (Shadow.single Cp).Strand) :
    (⟨0, l⟩ : (Shadow.single Cp).Strand) = s ↔ l = s.2 := by
  constructor
  · intro h; rw [← h]
  · intro h; exact Sigma.ext (Subsingleton.elim _ _) (heq_of_eq h)

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

omit [NeZero k] in
theorem gu6_coord_eq (D : Diagram) (v : D.Γ.Visit) :
    D.visitCoord v = ((D.visitPt v).2.1.val : ℝ) + (D.visitPt v).2.2.val := rfl

theorem gu6_label₀ (v : π.M₀.Γ.Visit) : (π.M₀.visitPt v).2.1 = v.2.val.2 := rfl
theorem gu6_label₁ (v : π.M₁.Γ.Visit) : (π.M₁.visitPt v).2.1 = v.2.val.2 := rfl

theorem gu6_Ψ₁_label (v : π.M₀.Γ.Visit) : (π.M₁.visitPt (π.gu6_Ψ₁ v)).2.1 = π.gu6_σ₁ v.2.val.2 :=
  congrArg (Shadow.singleStrandEquiv ⟨k + 3, π.hk₃, π.X₁⟩) (π.gu6_Ψ₁_strand v)

omit [NeZero k] in
theorem gu6_sv_fst' {Cp : PolyComp} (w : Visit Cp.P) :
    Shadow.singleCrossingEquiv Cp ((Shadow.singleVisitEquiv Cp).symm w).1 = w.1 := by
  obtain ⟨y, ⟨i, hi⟩⟩ := w
  exact gu6_sv_fst y hi

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

omit [NeZero k] in
/-- an outside parameter compares alike with any two inside parameters of one edge -/
theorem gu6_outside_cmp {U : Set Plane} (hU : Convex ℝ U) {N : ℕ} (P : LabelledTuple N) (i : ZMod N)
    {sa sb sz : ℝ} (ha : edgePoint P i sa ∈ interior U) (hb : edgePoint P i sb ∈ interior U)
    (hz : edgePoint P i sz ∉ interior U) : (sa < sz ↔ sb < sz) ∧ (sz < sa ↔ sz < sb) := by
  have k1 : ¬ (sa ≤ sz ∧ sz ≤ sb) := fun h => hz (gu6_edge_interior_of_convex' hU P i ha hb (Or.inl h))
  have k2 : ¬ (sb ≤ sz ∧ sz ≤ sa) := fun h => hz (gu6_edge_interior_of_convex' hU P i ha hb (Or.inr h))
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra h'
    push Not at h'
    exact k1 ⟨h.le, h'⟩
  · by_contra h'
    push Not at h'
    exact k2 ⟨h.le, h'⟩
  · by_contra h'
    push Not at h'
    exact k2 ⟨h', h.le⟩
  · by_contra h'
    push Not at h'
    exact k1 ⟨h', h.le⟩

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

omit [NeZero k] in
theorem gu6_sv_ne {Cp : PolyComp} (y : Crossing Cp.P) {i j : ZMod Cp.k} (hi : i ∈ y.val) (hj : j ∈ y.val)
    (hij : i ≠ j) :
    (Shadow.singleVisitEquiv Cp).symm ⟨y, ⟨i, hi⟩⟩ ≠ (Shadow.singleVisitEquiv Cp).symm ⟨y, ⟨j, hj⟩⟩ := by
  intro e
  have := congrArg (fun w : (Shadow.single Cp).Visit => w.2.val) e
  rw [gu6_sv_strand, gu6_sv_strand] at this
  exact hij (eq_of_heq (Sigma.mk.inj_iff.mp this).2)

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
  unfold G11_Config.v_mp G11_Config.v_mq
  rw [gu6_σD_apply, gu6_σ_vmp]
theorem gu6_σD_v_mq : C.σD C.v_mq = C.v_mp := by
  unfold G11_Config.v_mq G11_Config.v_mp
  rw [gu6_σD_apply, gu6_σ_vmq]
theorem gu6_σD_v_pm : C.σD C.v_pm = C.v_pq := by
  unfold G11_Config.v_pm G11_Config.v_pq
  rw [gu6_σD_apply, gu6_σ_vpm]
theorem gu6_σD_v_pq : C.σD C.v_pq = C.v_pm := by
  unfold G11_Config.v_pq G11_Config.v_pm
  rw [gu6_σD_apply, gu6_σ_vpq]
theorem gu6_σD_v_qm : C.σD C.v_qm = C.v_qp := by
  unfold G11_Config.v_qm G11_Config.v_qp
  rw [gu6_σD_apply, gu6_σ_vqm]
theorem gu6_σD_v_qp : C.σD C.v_qp = C.v_qm := by
  unfold G11_Config.v_qp G11_Config.v_qm
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

/-! #### U6 helpers for F1: the action of `σ_P` on visits -/

omit [NeZero n] in
/-- U6 helper: `σ_P` preserves the edge of every visit. -/
theorem gu6_σP_edge {P : LabelledTuple n} {e f g : ZMod n} (hcef : IsCrossing P {e, f})
    (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g}) (u : Visit P) :
    (G11_σP hcef hceg hcfg u).2.val = u.2.val := by
  unfold G11_σP
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    G11_Params.gu6_swap_edge (G11_vef hcef) (G11_veg hceg) rfl, G11_Params.gu6_swap_edge (G11_vfe hcef) (G11_vfg hcfg) rfl,
    G11_Params.gu6_swap_edge (G11_vge hceg) (G11_vgf hcfg) rfl]

omit [NeZero n] in
/-- U6 helper: a visit of a triangle crossing is one of the six local visits. -/
theorem gu6_local_cases {P : LabelledTuple n} {e f g : ZMod n} (hcef : IsCrossing P {e, f})
    (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g}) (u : Visit P)
    (hu : u.1.val ∈ triangleSupports e f g) :
    u = G11_vef hcef ∨ u = G11_vfe hcef ∨ u = G11_veg hceg ∨ u = G11_vge hceg ∨
      u = G11_vfg hcfg ∨ u = G11_vgf hcfg := by
  obtain ⟨⟨s, hcs⟩, ⟨i, hi⟩⟩ := u
  change s ∈ triangleSupports e f g at hu
  rw [P1.mem_triangleSupports] at hu
  rcases hu with rfl | rfl | rfl
  · have hi' : i = e ∨ i = f := by simpa using hi
    rcases hi' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · have hi' : i = e ∨ i = g := by simpa using hi
    rcases hi' with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · have hi' : i = f ∨ i = g := by simpa using hi
    rcases hi' with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

omit [NeZero n] in
/-- U6 helper: `σ_P` fixes every visit off the triangle. -/
theorem gu6_σP_of_not_local {P : LabelledTuple n} {e f g : ZMod n} (hcef : IsCrossing P {e, f})
    (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g}) (u : Visit P)
    (hu : u.1.val ∉ triangleSupports e f g) : G11_σP hcef hceg hcfg u = u := by
  have h1 : u ≠ G11_vef hcef := fun h => hu (by rw [h, P1.mem_triangleSupports]; exact Or.inl rfl)
  have h2 : u ≠ G11_veg hceg := fun h => hu (by rw [h, P1.mem_triangleSupports]; exact Or.inr (Or.inl rfl))
  have h3 : u ≠ G11_vfe hcef := fun h => hu (by rw [h, P1.mem_triangleSupports]; exact Or.inl rfl)
  have h4 : u ≠ G11_vfg hcfg := fun h => hu (by rw [h, P1.mem_triangleSupports]; exact Or.inr (Or.inr rfl))
  have h5 : u ≠ G11_vge hceg := fun h => hu (by rw [h, P1.mem_triangleSupports]; exact Or.inr (Or.inl rfl))
  have h6 : u ≠ G11_vgf hcfg := fun h => hu (by rw [h, P1.mem_triangleSupports]; exact Or.inr (Or.inr rfl))
  unfold G11_σP
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h5 h6,
    Equiv.swap_apply_of_ne_of_ne h3 h4, Equiv.swap_apply_of_ne_of_ne h1 h2]

omit [NeZero n] in
/-- U6 helper: on a visit of the edge `e`, `σ_P` is the swap `x_ef ↔ x_eg`. -/
theorem gu6_σP_on_e {P : LabelledTuple n} {e f g : ZMod n} (hef : e ≠ f) (heg : e ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (u : Visit P) (hu : u.2.val = e) :
    G11_σP hcef hceg hcfg u = Equiv.swap (G11_vef hcef) (G11_veg hceg) u := by
  have h1 : u ≠ G11_vge hceg := G11_Params.gu6_visit_ne_of_edge (by rw [hu]; exact heg)
  have h2 : u ≠ G11_vgf hcfg := G11_Params.gu6_visit_ne_of_edge (by rw [hu]; exact heg)
  have h3 : u ≠ G11_vfe hcef := G11_Params.gu6_visit_ne_of_edge (by rw [hu]; exact hef)
  have h4 : u ≠ G11_vfg hcfg := G11_Params.gu6_visit_ne_of_edge (by rw [hu]; exact hef)
  unfold G11_σP
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2,
    Equiv.swap_apply_of_ne_of_ne h3 h4]

omit [NeZero n] in
/-- U6 helper: on a visit of the edge `f`, `σ_P` is the swap `x_fe ↔ x_fg`. -/
theorem gu6_σP_on_f {P : LabelledTuple n} {e f g : ZMod n} (hef : e ≠ f) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (u : Visit P) (hu : u.2.val = f) :
    G11_σP hcef hceg hcfg u = Equiv.swap (G11_vfe hcef) (G11_vfg hcfg) u := by
  have h1 : u ≠ G11_vge hceg := G11_Params.gu6_visit_ne_of_edge (by rw [hu]; exact hfg)
  have h2 : u ≠ G11_vgf hcfg := G11_Params.gu6_visit_ne_of_edge (by rw [hu]; exact hfg)
  have h3 : Equiv.swap (G11_vfe hcef) (G11_vfg hcfg) u ≠ G11_vef hcef :=
    G11_Params.gu6_visit_ne_of_edge (by rw [G11_Params.gu6_swap_edge (G11_vfe hcef) (G11_vfg hcfg) rfl, hu]; exact hef.symm)
  have h4 : Equiv.swap (G11_vfe hcef) (G11_vfg hcfg) u ≠ G11_veg hceg :=
    G11_Params.gu6_visit_ne_of_edge (by rw [G11_Params.gu6_swap_edge (G11_vfe hcef) (G11_vfg hcfg) rfl, hu]; exact hef.symm)
  unfold G11_σP
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2,
    Equiv.swap_apply_of_ne_of_ne h3 h4]

omit [NeZero n] in
/-- U6 helper: on a visit of the edge `g`, `σ_P` is the swap `x_ge ↔ x_gf`. -/
theorem gu6_σP_on_g {P : LabelledTuple n} {e f g : ZMod n} (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (u : Visit P) (hu : u.2.val = g) :
    G11_σP hcef hceg hcfg u = Equiv.swap (G11_vge hceg) (G11_vgf hcfg) u := by
  have h3 : Equiv.swap (G11_vge hceg) (G11_vgf hcfg) u ≠ G11_vfe hcef :=
    G11_Params.gu6_visit_ne_of_edge (by rw [G11_Params.gu6_swap_edge (G11_vge hceg) (G11_vgf hcfg) rfl, hu]; exact hfg.symm)
  have h4 : Equiv.swap (G11_vge hceg) (G11_vgf hcfg) u ≠ G11_vfg hcfg :=
    G11_Params.gu6_visit_ne_of_edge (by rw [G11_Params.gu6_swap_edge (G11_vge hceg) (G11_vgf hcfg) rfl, hu]; exact hfg.symm)
  have h1 : Equiv.swap (G11_vge hceg) (G11_vgf hcfg) u ≠ G11_vef hcef :=
    G11_Params.gu6_visit_ne_of_edge (by rw [G11_Params.gu6_swap_edge (G11_vge hceg) (G11_vgf hcfg) rfl, hu]; exact heg.symm)
  have h2 : Equiv.swap (G11_vge hceg) (G11_vgf hcfg) u ≠ G11_veg hceg :=
    G11_Params.gu6_visit_ne_of_edge (by rw [G11_Params.gu6_swap_edge (G11_vge hceg) (G11_vgf hcfg) rfl, hu]; exact heg.symm)
  unfold G11_σP
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h3 h4,
    Equiv.swap_apply_of_ne_of_ne h1 h2]

omit [NeZero n] in
/-- U6 helper: the six values of `σ_P` on the local visits. -/
theorem gu6_σP_vef {P : LabelledTuple n} {e f g : ZMod n} (hef : e ≠ f) (heg : e ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g}) :
    G11_σP hcef hceg hcfg (G11_vef hcef) = G11_veg hceg := by
  rw [gu6_σP_on_e hef heg hcef hceg hcfg _ rfl, Equiv.swap_apply_left]

omit [NeZero n] in
theorem gu6_σP_veg {P : LabelledTuple n} {e f g : ZMod n} (hef : e ≠ f) (heg : e ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g}) :
    G11_σP hcef hceg hcfg (G11_veg hceg) = G11_vef hcef := by
  rw [gu6_σP_on_e hef heg hcef hceg hcfg _ rfl, Equiv.swap_apply_right]

omit [NeZero n] in
theorem gu6_σP_vfe {P : LabelledTuple n} {e f g : ZMod n} (hef : e ≠ f) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g}) :
    G11_σP hcef hceg hcfg (G11_vfe hcef) = G11_vfg hcfg := by
  rw [gu6_σP_on_f hef hfg hcef hceg hcfg _ rfl, Equiv.swap_apply_left]

omit [NeZero n] in
theorem gu6_σP_vfg {P : LabelledTuple n} {e f g : ZMod n} (hef : e ≠ f) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g}) :
    G11_σP hcef hceg hcfg (G11_vfg hcfg) = G11_vfe hcef := by
  rw [gu6_σP_on_f hef hfg hcef hceg hcfg _ rfl, Equiv.swap_apply_right]

omit [NeZero n] in
theorem gu6_σP_vge {P : LabelledTuple n} {e f g : ZMod n} (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g}) :
    G11_σP hcef hceg hcfg (G11_vge hceg) = G11_vgf hcfg := by
  rw [gu6_σP_on_g heg hfg hcef hceg hcfg _ rfl, Equiv.swap_apply_left]

omit [NeZero n] in
theorem gu6_σP_vgf {P : LabelledTuple n} {e f g : ZMod n} (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g}) :
    G11_σP hcef hceg hcfg (G11_vgf hcfg) = G11_vge hceg := by
  rw [gu6_σP_on_g heg hfg hcef hceg hcfg _ rfl, Equiv.swap_apply_right]

omit [NeZero n] in
/-- U6 helper: the six unions of two local supports on one edge. -/
theorem gu6_union_ef_eg (e f g : ZMod n) : ({e, f} : Finset (ZMod n)) ∪ {e, g} = {e, f, g} := by
  ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto

omit [NeZero n] in
theorem gu6_union_eg_ef (e f g : ZMod n) : ({e, g} : Finset (ZMod n)) ∪ {e, f} = {e, f, g} := by
  ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto

omit [NeZero n] in
theorem gu6_union_ef_fg (e f g : ZMod n) : ({e, f} : Finset (ZMod n)) ∪ {f, g} = {e, f, g} := by
  ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto

omit [NeZero n] in
theorem gu6_union_fg_ef (e f g : ZMod n) : ({f, g} : Finset (ZMod n)) ∪ {e, f} = {e, f, g} := by
  ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto

omit [NeZero n] in
theorem gu6_union_eg_fg (e f g : ZMod n) : ({e, g} : Finset (ZMod n)) ∪ {f, g} = {e, f, g} := by
  ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto

omit [NeZero n] in
theorem gu6_union_fg_eg (e f g : ZMod n) : ({f, g} : Finset (ZMod n)) ∪ {e, g} = {e, f, g} := by
  ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto

omit [NeZero n] in
/-- U6 helper: two visits on one edge with the same parameter are visits of one crossing
(`crossingParameter_spec`, `crossingPoint_injective_of_geometry`). -/
theorem gu6_crossing_eq_of_param {P : LabelledTuple n} (hcg : CrossingGeometry P) {u v : Visit P}
    (he : u.2.val = v.2.val) (hp : visitParameter u = visitParameter v) : u.1 = v.1 := by
  apply crossingPoint_injective_of_geometry hcg
  rw [(crossingParameter_spec u.1 u.2.val u.2.property).2.2,
    (crossingParameter_spec v.1 v.2.val v.2.property).2.2]
  change edgePoint P u.2.val (visitParameter u) = edgePoint P v.2.val (visitParameter v)
  rw [he, hp]

omit [NeZero n] in
/-- U6 helper (A7 in its symmetric form): no visit `v` off the triangle lies strictly between two
local visits `u, u'` of one edge whose supports cover the triangle (`ExactTriangleVisitOrders`:
the pair `(u, u')` is reversed while `(u, v)` and `(v, u')` are carried; transitivity). -/
theorem gu6_not_between {P P' : LabelledTuple n} {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s}
    {e f g : ZMod n} (hX : ExactTriangleVisitOrders P P' e f g hs) {u u' v : Visit P}
    (he : u.2.val = u'.2.val) (hun : u.1.val ∪ u'.1.val = {e, f, g}) (hv : u.2.val = v.2.val)
    (hvu : u.1.val ∪ v.1.val ≠ {e, f, g}) (hvu' : v.1.val ∪ u'.1.val ≠ {e, f, g}) :
    ¬ (visitParameter u < visitParameter v ∧ visitParameter v < visitParameter u') := by
  rintro ⟨h1, h2⟩
  have h3 : visitParameter (visitTransport hs u') < visitParameter (visitTransport hs u) :=
    ((hX u u' he).1 hun).mp (h1.trans h2)
  have h4 := ((hX u v hv).2 hvu).mp h1
  have h5 := ((hX v u' (hv.symm.trans he)).2 hvu').mp h2
  exact lt_irrefl _ (h3.trans (h4.trans h5))

omit [NeZero n] in
/-- U6 helper: a visit off the triangle compares alike with the two adjacent local visits of its
edge (left form). -/
theorem gu6_adj_left {P P' : LabelledTuple n} (hcg : CrossingGeometry P)
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hX : ExactTriangleVisitOrders P P' e f g hs) {u u' v : Visit P}
    (he : u.2.val = u'.2.val) (hun : u.1.val ∪ u'.1.val = {e, f, g}) (hv : u.2.val = v.2.val)
    (hvn : v.1.val ∉ triangleSupports e f g) :
    visitParameter u < visitParameter v ↔ visitParameter u' < visitParameter v := by
  have hvu : u.1.val ∪ v.1.val ≠ {e, f, g} := fun h => hvn (AV_triangle_of_union hef heg hfg u v h).2.1
  have hvu' : v.1.val ∪ u'.1.val ≠ {e, f, g} := fun h => hvn (AV_triangle_of_union hef heg hfg v u' h).1
  have hu'v : u'.1.val ∪ v.1.val ≠ {e, f, g} := fun h => hvn (AV_triangle_of_union hef heg hfg u' v h).2.1
  have hvu'' : v.1.val ∪ u.1.val ≠ {e, f, g} := fun h => hvn (AV_triangle_of_union hef heg hfg v u h).1
  have hun' : u'.1.val ∪ u.1.val = {e, f, g} := by rw [Finset.union_comm]; exact hun
  have hnb1 := gu6_not_between hX he hun hv hvu hvu'
  have hnb2 := gu6_not_between hX he.symm hun' (he.symm.trans hv) hu'v hvu''
  have hloc := AV_triangle_of_union hef heg hfg u u' hun
  have hvne : visitParameter v ≠ visitParameter u := fun h =>
    hvn (by rw [gu6_crossing_eq_of_param hcg hv.symm h]; exact hloc.1)
  have hvne' : visitParameter v ≠ visitParameter u' := fun h =>
    hvn (by rw [gu6_crossing_eq_of_param hcg (hv.symm.trans he) h]; exact hloc.2.1)
  constructor
  · intro h
    rcases lt_trichotomy (visitParameter u') (visitParameter v) with h' | h' | h'
    · exact h'
    · exact absurd h'.symm hvne'
    · exact absurd ⟨h, h'⟩ hnb1
  · intro h
    rcases lt_trichotomy (visitParameter u) (visitParameter v) with h' | h' | h'
    · exact h'
    · exact absurd h'.symm hvne
    · exact absurd ⟨h, h'⟩ hnb2

omit [NeZero n] in
/-- U6 helper: the right form of `gu6_adj_left`. -/
theorem gu6_adj_right {P P' : LabelledTuple n} (hcg : CrossingGeometry P)
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hX : ExactTriangleVisitOrders P P' e f g hs) {u u' v : Visit P}
    (he : u.2.val = u'.2.val) (hun : u.1.val ∪ u'.1.val = {e, f, g}) (hv : u.2.val = v.2.val)
    (hvn : v.1.val ∉ triangleSupports e f g) :
    visitParameter v < visitParameter u ↔ visitParameter v < visitParameter u' := by
  have hvu : u.1.val ∪ v.1.val ≠ {e, f, g} := fun h => hvn (AV_triangle_of_union hef heg hfg u v h).2.1
  have hvu' : v.1.val ∪ u'.1.val ≠ {e, f, g} := fun h => hvn (AV_triangle_of_union hef heg hfg v u' h).1
  have hu'v : u'.1.val ∪ v.1.val ≠ {e, f, g} := fun h => hvn (AV_triangle_of_union hef heg hfg u' v h).2.1
  have hvu'' : v.1.val ∪ u.1.val ≠ {e, f, g} := fun h => hvn (AV_triangle_of_union hef heg hfg v u h).1
  have hun' : u'.1.val ∪ u.1.val = {e, f, g} := by rw [Finset.union_comm]; exact hun
  have hnb1 := gu6_not_between hX he hun hv hvu hvu'
  have hnb2 := gu6_not_between hX he.symm hun' (he.symm.trans hv) hu'v hvu''
  have hloc := AV_triangle_of_union hef heg hfg u u' hun
  have hvne : visitParameter v ≠ visitParameter u := fun h =>
    hvn (by rw [gu6_crossing_eq_of_param hcg hv.symm h]; exact hloc.1)
  have hvne' : visitParameter v ≠ visitParameter u' := fun h =>
    hvn (by rw [gu6_crossing_eq_of_param hcg (hv.symm.trans he) h]; exact hloc.2.1)
  constructor
  · intro h
    rcases lt_trichotomy (visitParameter v) (visitParameter u') with h' | h' | h'
    · exact h'
    · exact absurd h' hvne'
    · exact absurd ⟨h', h⟩ hnb2
  · intro h
    rcases lt_trichotomy (visitParameter v) (visitParameter u) with h' | h' | h'
    · exact h'
    · exact absurd h' hvne
    · exact absurd ⟨h', h⟩ hnb1

omit [NeZero n] in
/-- U6 helper: the mixed case of F1 — `u` local with partner `u' = σ_P u`, `v` off the triangle. -/
theorem gu6_mixed_left {P P' : LabelledTuple n} (hcg : CrossingGeometry P)
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs) {u u' v : Visit P}
    (hσ : G11_σP hcef hceg hcfg u = u') (he : u.2.val = u'.2.val) (hun : u.1.val ∪ u'.1.val = {e, f, g})
    (hv : u.2.val = v.2.val) (hvn : v.1.val ∉ triangleSupports e f g) :
    visitParameter (G11_σP hcef hceg hcfg u) < visitParameter (G11_σP hcef hceg hcfg v) ↔
      visitParameter (visitTransport hs u) < visitParameter (visitTransport hs v) := by
  rw [hσ, gu6_σP_of_not_local hcef hceg hcfg v hvn, ← gu6_adj_left hcg hef heg hfg hX he hun hv hvn]
  exact (hX u v hv).2 fun h => hvn (AV_triangle_of_union hef heg hfg u v h).2.1

omit [NeZero n] in
/-- U6 helper: the mixed case of F1 — `u` off the triangle, `v` local with partner `v' = σ_P v`. -/
theorem gu6_mixed_right {P P' : LabelledTuple n} (hcg : CrossingGeometry P)
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs) {u v v' : Visit P}
    (hσ : G11_σP hcef hceg hcfg v = v') (he : v.2.val = v'.2.val) (hun : v.1.val ∪ v'.1.val = {e, f, g})
    (hv : v.2.val = u.2.val) (hun' : u.1.val ∉ triangleSupports e f g) :
    visitParameter (G11_σP hcef hceg hcfg u) < visitParameter (G11_σP hcef hceg hcfg v) ↔
      visitParameter (visitTransport hs u) < visitParameter (visitTransport hs v) := by
  rw [hσ, gu6_σP_of_not_local hcef hceg hcfg u hun', ← gu6_adj_right hcg hef heg hfg hX he hun hv hun']
  exact (hX u v hv.symm).2 fun h => hun' (AV_triangle_of_union hef heg hfg u v h).1

omit [NeZero n] in
/-- U6 helper: `σ_P` is an involution. -/
theorem gu6_σP_σP {P : LabelledTuple n} {e f g : ZMod n} (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g}) (u : Visit P) :
    G11_σP hcef hceg hcfg (G11_σP hcef hceg hcfg u) = u := by
  by_cases hu : u.1.val ∈ triangleSupports e f g
  · rcases gu6_local_cases hcef hceg hcfg u hu with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [gu6_σP_vef hef heg hcef hceg hcfg, gu6_σP_veg hef heg hcef hceg hcfg]
    · rw [gu6_σP_vfe hef hfg hcef hceg hcfg, gu6_σP_vfg hef hfg hcef hceg hcfg]
    · rw [gu6_σP_veg hef heg hcef hceg hcfg, gu6_σP_vef hef heg hcef hceg hcfg]
    · rw [gu6_σP_vge heg hfg hcef hceg hcfg, gu6_σP_vgf heg hfg hcef hceg hcfg]
    · rw [gu6_σP_vfg hef hfg hcef hceg hcfg, gu6_σP_vfe hef hfg hcef hceg hcfg]
    · rw [gu6_σP_vgf heg hfg hcef hceg hcfg, gu6_σP_vge heg hfg hcef hceg hcfg]
  · rw [gu6_σP_of_not_local hcef hceg hcfg u hu, gu6_σP_of_not_local hcef hceg hcfg u hu]

omit [NeZero n] in
/-- U6 helper: the supports of a local visit and of its `σ_P`-partner cover the triangle. -/
theorem gu6_union_σP {P : LabelledTuple n} {e f g : ZMod n} (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g}) (u : Visit P)
    (hu : u.1.val ∈ triangleSupports e f g) :
    u.1.val ∪ (G11_σP hcef hceg hcfg u).1.val = {e, f, g} := by
  rcases gu6_local_cases hcef hceg hcfg u hu with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [gu6_σP_vef hef heg hcef hceg hcfg]; exact gu6_union_ef_eg e f g
  · rw [gu6_σP_vfe hef hfg hcef hceg hcfg]; exact gu6_union_ef_fg e f g
  · rw [gu6_σP_veg hef heg hcef hceg hcfg]; exact gu6_union_eg_ef e f g
  · rw [gu6_σP_vge heg hfg hcef hceg hcfg]; exact gu6_union_eg_fg e f g
  · rw [gu6_σP_vfg hef hfg hcef hceg hcfg]; exact gu6_union_fg_ef e f g
  · rw [gu6_σP_vgf heg hfg hcef hceg hcfg]; exact gu6_union_fg_eg e f g

omit [NeZero n] in
/-- U6 helper: two local visits on one edge are equal or `σ_P`-partners. -/
theorem gu6_local_pair {P : LabelledTuple n} {e f g : ZMod n} (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g}) (u v : Visit P)
    (hu : u.1.val ∈ triangleSupports e f g) (hv : v.1.val ∈ triangleSupports e f g)
    (he : u.2.val = v.2.val) : u = v ∨ G11_σP hcef hceg hcfg u = v := by
  rcases gu6_local_cases hcef hceg hcfg u hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases gu6_local_cases hcef hceg hcfg v hv with rfl | rfl | rfl | rfl | rfl | rfl
  -- u = x_ef on e
  · exact Or.inl rfl
  · exact absurd he hef
  · exact Or.inr (gu6_σP_vef hef heg hcef hceg hcfg)
  · exact absurd he heg
  · exact absurd he hef
  · exact absurd he heg
  -- u = x_ef on f
  · exact absurd he.symm hef
  · exact Or.inl rfl
  · exact absurd he.symm hef
  · exact absurd he hfg
  · exact Or.inr (gu6_σP_vfe hef hfg hcef hceg hcfg)
  · exact absurd he hfg
  -- u = x_eg on e
  · exact Or.inr (gu6_σP_veg hef heg hcef hceg hcfg)
  · exact absurd he hef
  · exact Or.inl rfl
  · exact absurd he heg
  · exact absurd he hef
  · exact absurd he heg
  -- u = x_eg on g
  · exact absurd he.symm heg
  · exact absurd he.symm hfg
  · exact absurd he.symm heg
  · exact Or.inl rfl
  · exact absurd he.symm hfg
  · exact Or.inr (gu6_σP_vge heg hfg hcef hceg hcfg)
  -- u = x_fg on f
  · exact absurd he.symm hef
  · exact Or.inr (gu6_σP_vfg hef hfg hcef hceg hcfg)
  · exact absurd he.symm hef
  · exact absurd he hfg
  · exact Or.inl rfl
  · exact absurd he hfg
  -- u = x_fg on g
  · exact absurd he.symm heg
  · exact absurd he.symm hfg
  · exact absurd he.symm heg
  · exact Or.inr (gu6_σP_vgf heg hfg hcef hceg hcfg)
  · exact absurd he.symm hfg
  · exact Or.inl rfl

omit [NeZero n] in
/-- U6 helper: the same-edge clause of F1 — parameters after `σ_P` compare like the transported
parameters. -/
theorem gu6_param_twisted {P P' : LabelledTuple n} (hcg : CrossingGeometry P)
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs) (u v : Visit P) (he : u.2.val = v.2.val) :
    visitParameter (G11_σP hcef hceg hcfg u) < visitParameter (G11_σP hcef hceg hcfg v) ↔
      visitParameter (visitTransport hs u) < visitParameter (visitTransport hs v) := by
  by_cases hu : u.1.val ∈ triangleSupports e f g <;> by_cases hv : v.1.val ∈ triangleSupports e f g
  · rcases gu6_local_pair hef heg hfg hcef hceg hcfg u v hu hv he with rfl | hσ
    · exact iff_of_false (lt_irrefl _) (lt_irrefl _)
    · have hun := gu6_union_σP hef heg hfg hcef hceg hcfg u hu
      rw [hσ] at hun
      have hσ' : G11_σP hcef hceg hcfg v = u := by
        rw [← hσ, gu6_σP_σP hef heg hfg hcef hceg hcfg]
      rw [hσ, hσ']
      exact (hX v u he.symm).1 (by rw [Finset.union_comm]; exact hun)
  · exact gu6_mixed_left hcg hef heg hfg hcef hceg hcfg hX rfl
      (gu6_σP_edge hcef hceg hcfg u).symm (gu6_union_σP hef heg hfg hcef hceg hcfg u hu) he hv
  · exact gu6_mixed_right hcg hef heg hfg hcef hceg hcfg hX rfl
      (gu6_σP_edge hcef hceg hcfg v).symm (gu6_union_σP hef heg hfg hcef hceg hcfg v hv) he.symm hu
  · rw [gu6_σP_of_not_local hcef hceg hcfg u hu, gu6_σP_of_not_local hcef hceg hcfg v hv]
    exact (hX u v he).2 fun h => hu (AV_triangle_of_union hef heg hfg u v h).1

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
  rw [CV.geometricVisitKey_lt_iff, CV.geometricVisitKey_lt_iff, gu6_σP_edge, gu6_σP_edge,
    visitTransport_edge, visitTransport_edge]
  exact or_congr Iff.rfl (and_congr_right fun he =>
    gu6_param_twisted hG.cg hef heg hfg hcef hceg hcfg hX u v he)

/-! #### U6 helpers for F2: `σ` on the visits of a configuration and the parents of the six local
occurrences of the lift -/

/-- U6 helper: the out-slot edge of the block of a retained visit (the block whose corner index is
`G11_carrierEdge`) is the visit's own edge (`geo_mark_block`, `GeoBlockInterior.visit_edge`; the
block position is `≥ 1` because a corner mark is a true corner while the visit is retained). -/
theorem gu6_carrierEdge_outSlot (w : Visit P) (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    (geoOutSlot hG.cg T (geoCornerMark hG.cg T q (G11_carrierEdge hn hG hT q w hw))).1 = w.2.val := by
  obtain ⟨r, hr, hb, -⟩ := Classical.choose_spec (geo_mark_block hn hG.cg hT q (Sum.inr w)
    (((mem_geoCarrierCrossings hG.cg T q w.1).mp hw).2 w rfl))
  have hr' : (geoSmoothingSuccessor hG.cg T ^ r)
      (geoCornerMark hG.cg T q (G11_carrierEdge hn hG hT q w hw)) = Sum.inr w := hr
  have hb' : GeoBlockInterior hG.cg T q (G11_carrierEdge hn hG hT q w hw) r := hb
  have hr1 : 1 ≤ r := by
    by_contra h
    have hr0 : r = 0 := by omega
    rw [hr0, pow_zero, Equiv.Perm.one_apply] at hr'
    have hcorner := isTrueCorner_geoCornerMark hG.cg T q (G11_carrierEdge hn hG hT q w hw)
    rw [hr'] at hcorner
    exact ((mem_geoCarrierCrossings hG.cg T q w.1).mp hw).1 ((isTrueCorner_visit T _).mp hcorner)
  exact (hb'.visit_edge hG.cg T q hr1 hr').symm

/-- U6 helper: an occurrence of the lift whose strand is the carrier edge of a retained visit `w`
has its parent visit on the edge of `w` (`liftVisit_edge`). -/
theorem gu6_liftVisit_edge_eq (v : (geoPositiveLift hn hG hT q).Γ.Visit) (w : Visit P)
    (hw : w.1 ∈ geoCarrierCrossings hG.cg T q)
    (hk : Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q) v.2.val =
      G11_carrierEdge hn hG hT q w hw) :
    (CV.liftVisit hn hG hT q v).2.val = w.2.val := by
  rw [CV.liftVisit_edge, ← gu6_carrierEdge_outSlot hn hG hT q w hw, ← hk]
  rfl

/-- U6 helper: two occurrences of one double point of the lift whose parents lie on the edges `i`
and `j` have the parent crossing `x_ij`. -/
theorem gu6_liftVisit_fst_eq (v v' : (geoPositiveLift hn hG hT q).Γ.Visit) (hvv : v.1 = v'.1)
    {i j : ZMod n} (hij : IsCrossing P {i, j})
    (hi : (CV.liftVisit hn hG hT q v).2.val = i) (hj : (CV.liftVisit hn hG hT q v').2.val = j) :
    (CV.liftVisit hn hG hT q v).1 = xPair hij := by
  have h1 : (CV.liftVisit hn hG hT q v').1 = (CV.liftVisit hn hG hT q v).1 := by
    rw [CV.liftVisit_fst, CV.liftVisit_fst]
    unfold CV.parentCrossing
    rw [hvv]
  apply Subtype.ext
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [P1.xPair_val, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · rw [hx, ← hi]; exact (CV.liftVisit hn hG hT q v).2.property
    · rw [hx, ← hj, ← h1]; exact (CV.liftVisit hn hG hT q v').2.property
  · simp only [crossing_card_two, le_refl]

/-- U6 helper: the parent of a local occurrence. `x, x'` are the two visits of one crossing of the
corner polygon, on the carrier edges of the retained visits `u, u'`; the parent of the occurrence
`x` is the visit `w` of `x_{u.edge, u'.edge}` on the edge of `u`. -/
theorem gu6_liftVisit_symm_eq (x x' : Visit (geoCornerPolygon hG.cg T q)) (hxx : x.1 = x'.1)
    (u u' : Visit P) (hu : u.1 ∈ geoCarrierCrossings hG.cg T q) (hu' : u'.1 ∈ geoCarrierCrossings hG.cg T q)
    (hx : x.2.val = G11_carrierEdge hn hG hT q u hu) (hx' : x'.2.val = G11_carrierEdge hn hG hT q u' hu')
    (hij : IsCrossing P {u.2.val, u'.2.val}) (w : Visit P) (hw1 : w.1 = xPair hij)
    (hw2 : w.2.val = u.2.val) :
    CV.liftVisit hn hG hT q ((Shadow.singleVisitEquiv (geoCarrierPolyComp hn hG hT q)).symm x) = w := by
  have hvv : ((Shadow.singleVisitEquiv (geoCarrierPolyComp hn hG hT q)).symm x).1 =
      ((Shadow.singleVisitEquiv (geoCarrierPolyComp hn hG hT q)).symm x').1 := by
    apply (Shadow.singleCrossingEquiv _).injective
    rw [← Shadow.singleVisitEquiv_fst, ← Shadow.singleVisitEquiv_fst, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    exact hxx
  have he : (CV.liftVisit hn hG hT q
      ((Shadow.singleVisitEquiv (geoCarrierPolyComp hn hG hT q)).symm x)).2.val = u.2.val := by
    apply gu6_liftVisit_edge_eq hn hG hT q _ u hu
    rw [← Shadow.singleVisitEquiv_snd, Equiv.apply_symm_apply]
    exact hx
  have he' : (CV.liftVisit hn hG hT q
      ((Shadow.singleVisitEquiv (geoCarrierPolyComp hn hG hT q)).symm x')).2.val = u'.2.val := by
    apply gu6_liftVisit_edge_eq hn hG hT q _ u' hu'
    rw [← Shadow.singleVisitEquiv_snd, Equiv.apply_symm_apply]
    exact hx'
  apply G11_Params.gu6_visit_ext
  · rw [hw1]
    exact gu6_liftVisit_fst_eq hn hG hT q _ _ hvv hij he he'
  · rw [hw2]
    exact he

/-- U6 helper: the parents of the six local occurrences of the lift of the distinguished carrier
are the six local visits of `P`. -/
theorem gu6_lift_six (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs)
    (halt : ¬ IsAlternating (strandSign P e f) (strandSign P e g) (strandSign P f g))
    (htri : triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q)
    (hord : crossingParameter (xPair hcef) e (mem_pair_left _ _) <
      crossingParameter (xPair hceg) e (mem_pair_left _ _)) :
    let C := G11_configOf hn hG hs hT q hef heg hfg hcef hceg hcfg hX halt htri hord
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
  obtain ⟨h_mp, h_pm, h_mq, h_qm, h_pq, h_qp⟩ :=
    gu6_lift_six hn hG hs hT q hef heg hfg hcef hceg hcfg hX halt htri hord
  set C := G11_configOf hn hG hs hT q hef heg hfg hcef hceg hcfg hX halt htri hord with hC
  by_cases hloc : (CV.liftVisit hn hG hT q v).1.val ∈ triangleSupports e f g
  · rcases gu6_local_cases hcef hceg hcfg _ hloc with h | h | h | h | h | h
    · have hv := CV.liftVisit_injective hn hG hT q (h.trans h_mp.symm)
      rw [h, gu6_σP_vef hef heg hcef hceg hcfg, hv, G11_Params.gu6_σD_apply, G11_Params.gu6_σ_vmp, h_mq]
    · have hv := CV.liftVisit_injective hn hG hT q (h.trans h_pm.symm)
      rw [h, gu6_σP_vfe hef hfg hcef hceg hcfg, hv, G11_Params.gu6_σD_apply, G11_Params.gu6_σ_vpm, h_pq]
    · have hv := CV.liftVisit_injective hn hG hT q (h.trans h_mq.symm)
      rw [h, gu6_σP_veg hef heg hcef hceg hcfg, hv, G11_Params.gu6_σD_apply, G11_Params.gu6_σ_vmq, h_mp]
    · have hv := CV.liftVisit_injective hn hG hT q (h.trans h_qm.symm)
      rw [h, gu6_σP_vge heg hfg hcef hceg hcfg, hv, G11_Params.gu6_σD_apply, G11_Params.gu6_σ_vqm, h_qp]
    · have hv := CV.liftVisit_injective hn hG hT q (h.trans h_pq.symm)
      rw [h, gu6_σP_vfg hef hfg hcef hceg hcfg, hv, G11_Params.gu6_σD_apply, G11_Params.gu6_σ_vpq, h_pm]
    · have hv := CV.liftVisit_injective hn hG hT q (h.trans h_qp.symm)
      rw [h, gu6_σP_vgf heg hfg hcef hceg hcfg, hv, G11_Params.gu6_σD_apply, G11_Params.gu6_σ_vqp, h_qm]
  · rw [gu6_σP_of_not_local hcef hceg hcfg _ hloc]
    have hne : ∀ (x : Visit C.X) (w : Visit P),
        CV.liftVisit hn hG hT q ((Shadow.singleVisitEquiv C.comp).symm x) = w →
        w.1.val ∈ triangleSupports e f g → Shadow.singleVisitEquiv C.comp v ≠ x := by
      intro x w hw hwt h
      apply hloc
      rw [← Equiv.symm_apply_apply (Shadow.singleVisitEquiv C.comp) v, h, hw]
      exact hwt
    have hσ := G11_Params.gu6_σ_of_not_local C _
      (hne _ _ h_mp (by rw [P1.mem_triangleSupports]; exact Or.inl rfl))
      (hne _ _ h_mq (by rw [P1.mem_triangleSupports]; exact Or.inr (Or.inl rfl)))
      (hne _ _ h_pm (by rw [P1.mem_triangleSupports]; exact Or.inl rfl))
      (hne _ _ h_pq (by rw [P1.mem_triangleSupports]; exact Or.inr (Or.inr rfl)))
      (hne _ _ h_qm (by rw [P1.mem_triangleSupports]; exact Or.inr (Or.inl rfl)))
      (hne _ _ h_qp (by rw [P1.mem_triangleSupports]; exact Or.inr (Or.inr rfl)))
    have hfix : C.σD v = v := by
      have h1 : C.σD ((Shadow.singleVisitEquiv C.comp).symm ((Shadow.singleVisitEquiv C.comp) v)) =
          (Shadow.singleVisitEquiv C.comp).symm (C.σ ((Shadow.singleVisitEquiv C.comp) v)) :=
        G11_Params.gu6_σD_apply C _
      have h2 : (Shadow.singleVisitEquiv C.comp).symm ((Shadow.singleVisitEquiv C.comp) v) = v :=
        Equiv.symm_apply_apply _ _
      rw [h2, hσ, h2] at h1
      exact h1
    rw [hfix]

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
  have hmem : ∀ v, (CV.liftVisit hn hG hT q v).1 ∈ geoCarrierCrossings hG.cg T q :=
    CV.liftVisit_mem hn hG hT q
  have hΛtw : ∀ v, Λ ((geoPositiveLift hn hG hT q).twin v) = (geoPositiveLift hn hG' hT' q').twin (Λ v) := by
    intro v
    apply CV.liftVisit_injective hn hG' hT' q'
    rw [hΛ, CV.liftVisit_twin, CV.liftVisit_twin, hΛ, visitTransport_visitTwin]
  have hΨtw : ∀ v, Ψ.symm (D₁.twin v) = (geoPositiveLift hn hG hT q).twin (Ψ.symm v) := by
    intro v
    rw [Equiv.symm_apply_eq, htw, Equiv.apply_symm_apply]
  refine ⟨Ψ.symm.trans Λ,
    { cyclic_order := ?_, double_points := ?_, over_under := ?_, signs := ?_ }⟩
  · intro v w u hb
    simp only [Equiv.trans_apply]
    have hb' : D₁.VisitBetween (Ψ (Ψ.symm v)) (Ψ (Ψ.symm w)) (Ψ (Ψ.symm u)) := by
      rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [hcyc, CV.visitBetween_iff_key, hσ, hσ, hσ] at hb'
    rw [CV.visitBetween_iff_key, hΛ, hΛ, hΛ]
    exact (GT_cyc_congr_of_lt
      (G11_twisted_key_lt hG hG' hs hef heg hfg hcef hceg hcfg hX _ _)
      (G11_twisted_key_lt hG hG' hs hef heg hfg hcef hceg hcfg hX _ _)
      (G11_twisted_key_lt hG hG' hs hef heg hfg hcef hceg hcfg hX _ _)).mp hb'
  · refine (CV.carriesDoublePoints_iff (ρ := D₁.record)
      (ρ' := (geoPositiveLift hn hG' hT' q').record) (Ψ.symm.trans Λ)).2 fun v => ?_
    change Λ (Ψ.symm (D₁.twin v)) = (geoPositiveLift hn hG' hT' q').twin (Λ (Ψ.symm v))
    rw [hΨtw, hΛtw]
  · refine (CV.carriesOverUnder_iff (ρ := D₁.record)
      (ρ' := (geoPositiveLift hn hG' hT' q').record) (Ψ.symm.trans Λ)).2 fun v => ?_
    change (geoPositiveLift hn hG' hT' q').overBit (Λ (Ψ.symm v)) = D₁.overBit v
    conv_rhs => rw [← Equiv.apply_symm_apply Ψ v]
    rw [hbit, Bool.eq_iff_iff, CV.overBit_eq_true_iff_parent, CV.overBit_eq_true_iff_parent, hΛ,
      visitTransport_edge, ← visitTransport_visitTwin, visitTransport_edge]
    exact (hdet _ _ (by rw [← visit_crossing_val_eq_pair]; exact (CV.liftVisit hn hG hT q _).1.property)).symm
  · intro v
    change (geoPositiveLift hn hG' hT' q').sign (Λ (Ψ.symm v)).1 = D₁.sign v.1
    conv_rhs => rw [← Equiv.apply_symm_apply Ψ v]
    rw [hsgn, geoPositiveLift_sign, geoPositiveLift_sign]

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
