import RProof.X1Rows3
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

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

/-! ### U2 helpers — the triangle as an affine basis (barycentric coordinates)

The closed triangle `convexHull ℝ {a, b, c}` of three non-collinear points: membership, interior and
frontier through the barycentric coordinates of the affine basis `![a, b, c]`
(`AffineBasis.convexHull_eq_nonneg_coord`, `AffineBasis.interior_convexHull`); a point of the triangle with a
vanishing coordinate lies on the opposite side; the coordinate of a vertex vanishes on the line through the
two other vertices. -/

theorem gu2_det_smul_smul (r s : ℝ) (u v : Plane) : det (r • u) (s • v) = (r * s) * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem gu2_det_smul_right (u v : Plane) (t : ℝ) : det u (t • v) = t * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem gu2_det_self (v : Plane) : det v v = 0 := by
  simp only [det]; ring

theorem gu2_det_self_smul (v : Plane) (r s : ℝ) : det (r • v) (s • v) = 0 := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- three points of the plane with `det (b - a) (c - a) ≠ 0` are affinely independent -/
theorem gu2_affineIndependent {a b c : Plane} (h : det (b - a) (c - a) ≠ 0) :
    AffineIndependent ℝ ![a, b, c] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro hcol
  rw [collinear_iff_of_mem (p₀ := a) (by simp)] at hcol
  obtain ⟨v, hv⟩ := hcol
  obtain ⟨r, hr⟩ := hv b (by simp)
  obtain ⟨s, hs⟩ := hv c (by simp)
  apply h
  rw [vadd_eq_add] at hr hs
  rw [hr, hs, add_sub_cancel_right, add_sub_cancel_right]
  exact gu2_det_self_smul v r s

theorem gu2_finrank_plane : Module.finrank ℝ Plane = 2 := by
  simp [Module.finrank_prod, Module.finrank_self]

/-- the affine basis of the plane given by three non-collinear points -/
noncomputable def gu2_triBasis (a b c : Plane) (h : det (b - a) (c - a) ≠ 0) :
    AffineBasis (Fin 3) ℝ Plane :=
  ⟨![a, b, c], gu2_affineIndependent h,
    (gu2_affineIndependent h).affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
      (by rw [Fintype.card_fin, gu2_finrank_plane])⟩

theorem gu2_triBasis_coe (a b c : Plane) (h : det (b - a) (c - a) ≠ 0) :
    (⇑(gu2_triBasis a b c h) : Fin 3 → Plane) = ![a, b, c] := rfl

theorem gu2_triBasis_range (a b c : Plane) (h : det (b - a) (c - a) ≠ 0) :
    Set.range (gu2_triBasis a b c h) = {a, b, c} := by
  rw [gu2_triBasis_coe]
  ext x
  simp only [Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty,
    Set.mem_insert_iff, Set.mem_singleton_iff]

theorem gu2_triBasis_zero (a b c : Plane) (h : det (b - a) (c - a) ≠ 0) :
    gu2_triBasis a b c h 0 = a := rfl
theorem gu2_triBasis_one (a b c : Plane) (h : det (b - a) (c - a) ≠ 0) :
    gu2_triBasis a b c h 1 = b := rfl
theorem gu2_triBasis_two (a b c : Plane) (h : det (b - a) (c - a) ≠ 0) :
    gu2_triBasis a b c h 2 = c := rfl

/-- membership in the closed triangle: all barycentric coordinates nonnegative -/
theorem gu2_mem_tri_iff (a b c : Plane) (h : det (b - a) (c - a) ≠ 0) (x : Plane) :
    x ∈ convexHull ℝ ({a, b, c} : Set Plane) ↔ ∀ i, 0 ≤ (gu2_triBasis a b c h).coord i x := by
  rw [← gu2_triBasis_range a b c h, AffineBasis.convexHull_eq_nonneg_coord]
  rfl

/-- membership in the open triangle: all barycentric coordinates positive -/
theorem gu2_mem_interior_iff (a b c : Plane) (h : det (b - a) (c - a) ≠ 0) (x : Plane) :
    x ∈ interior (convexHull ℝ ({a, b, c} : Set Plane)) ↔
      ∀ i, 0 < (gu2_triBasis a b c h).coord i x := by
  rw [← gu2_triBasis_range a b c h, AffineBasis.interior_convexHull]
  rfl

theorem gu2_tri_isClosed (a b c : Plane) : IsClosed (convexHull ℝ ({a, b, c} : Set Plane)) :=
  (Set.toFinite _).isClosed_convexHull ℝ

/-- a frontier point of the triangle has all coordinates nonnegative and one of them zero -/
theorem gu2_frontier_coord (a b c : Plane) (h : det (b - a) (c - a) ≠ 0) {x : Plane}
    (hx : x ∈ frontier (convexHull ℝ ({a, b, c} : Set Plane))) :
    (∀ i, 0 ≤ (gu2_triBasis a b c h).coord i x) ∧ ∃ i, (gu2_triBasis a b c h).coord i x = 0 := by
  have hcl : x ∈ convexHull ℝ ({a, b, c} : Set Plane) := by
    have := frontier_subset_closure hx
    rwa [(gu2_tri_isClosed a b c).closure_eq] at this
  have hnn := (gu2_mem_tri_iff a b c h x).mp hcl
  refine ⟨hnn, ?_⟩
  have hni : x ∉ interior (convexHull ℝ ({a, b, c} : Set Plane)) := hx.2
  rw [gu2_mem_interior_iff a b c h] at hni
  push Not at hni
  obtain ⟨i, hi⟩ := hni
  exact ⟨i, le_antisymm hi (hnn i)⟩

/-- a point of the triangle with a vanishing coordinate is on the opposite side (three forms) -/
theorem gu2_mem_segment_of_coord0 (a b c : Plane) (h : det (b - a) (c - a) ≠ 0) {x : Plane}
    (hx : ∀ i, 0 ≤ (gu2_triBasis a b c h).coord i x) (h0 : (gu2_triBasis a b c h).coord 0 x = 0) :
    x ∈ segment ℝ b c := by
  have hsum := (gu2_triBasis a b c h).sum_coord_apply_eq_one x
  have hcomb := (gu2_triBasis a b c h).linear_combination_coord_eq_self x
  rw [Fin.sum_univ_three] at hsum hcomb
  rw [h0, zero_smul, zero_add, gu2_triBasis_one, gu2_triBasis_two] at hcomb
  rw [h0, zero_add] at hsum
  exact ⟨_, _, hx 1, hx 2, hsum, hcomb⟩

theorem gu2_mem_segment_of_coord1 (a b c : Plane) (h : det (b - a) (c - a) ≠ 0) {x : Plane}
    (hx : ∀ i, 0 ≤ (gu2_triBasis a b c h).coord i x) (h1 : (gu2_triBasis a b c h).coord 1 x = 0) :
    x ∈ segment ℝ a c := by
  have hsum := (gu2_triBasis a b c h).sum_coord_apply_eq_one x
  have hcomb := (gu2_triBasis a b c h).linear_combination_coord_eq_self x
  rw [Fin.sum_univ_three] at hsum hcomb
  rw [h1, zero_smul, add_zero, gu2_triBasis_zero, gu2_triBasis_two] at hcomb
  rw [h1, add_zero] at hsum
  exact ⟨_, _, hx 0, hx 2, hsum, hcomb⟩

theorem gu2_mem_segment_of_coord2 (a b c : Plane) (h : det (b - a) (c - a) ≠ 0) {x : Plane}
    (hx : ∀ i, 0 ≤ (gu2_triBasis a b c h).coord i x) (h2 : (gu2_triBasis a b c h).coord 2 x = 0) :
    x ∈ segment ℝ a b := by
  have hsum := (gu2_triBasis a b c h).sum_coord_apply_eq_one x
  have hcomb := (gu2_triBasis a b c h).linear_combination_coord_eq_self x
  rw [Fin.sum_univ_three] at hsum hcomb
  rw [h2, zero_smul, add_zero, gu2_triBasis_zero, gu2_triBasis_one] at hcomb
  rw [h2, add_zero] at hsum
  exact ⟨_, _, hx 0, hx 1, hsum, hcomb⟩

/-- the coordinate of a vertex vanishes on the line through the two other vertices -/
theorem gu2_coord_eq_zero_of_line (B : AffineBasis (Fin 3) ℝ Plane) {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (t : ℝ) : B.coord i (B j + t • (B k - B j)) = 0 := by
  have : B j + t • (B k - B j) = AffineMap.lineMap (B j) (B k) t := by
    rw [AffineMap.lineMap_apply_module']; abel
  rw [this, AffineMap.apply_lineMap, B.coord_apply_ne hij, B.coord_apply_ne hik,
    AffineMap.lineMap_same_apply]

/-- the frontier of the triangle is contained in the union of its three sides -/
theorem gu2_frontier_subset_sides (a b c : Plane) (h : det (b - a) (c - a) ≠ 0) {x : Plane}
    (hx : x ∈ frontier (convexHull ℝ ({a, b, c} : Set Plane))) :
    x ∈ segment ℝ a b ∨ x ∈ segment ℝ a c ∨ x ∈ segment ℝ b c := by
  obtain ⟨hnn, i, hi⟩ := gu2_frontier_coord a b c h hx
  fin_cases i
  · exact Or.inr (Or.inr (gu2_mem_segment_of_coord0 a b c h hnn hi))
  · exact Or.inr (Or.inl (gu2_mem_segment_of_coord1 a b c h hnn hi))
  · exact Or.inl (gu2_mem_segment_of_coord2 a b c h hnn hi)

/-- a point of the closed triangle on the line `ab` is on the side `ab` (and the two other lines) -/
theorem gu2_mem_segment_ab_of_line (a b c : Plane) (h : det (b - a) (c - a) ≠ 0) {x : Plane}
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set Plane)) {t : ℝ} (ht : x = a + t • (b - a)) :
    x ∈ segment ℝ a b := by
  refine gu2_mem_segment_of_coord2 a b c h ((gu2_mem_tri_iff a b c h x).mp hx) ?_
  rw [ht]
  exact gu2_coord_eq_zero_of_line (gu2_triBasis a b c h) (i := 2) (j := 0) (k := 1)
    (by decide) (by decide) t

theorem gu2_mem_segment_ac_of_line (a b c : Plane) (h : det (b - a) (c - a) ≠ 0) {x : Plane}
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set Plane)) {t : ℝ} (ht : x = a + t • (c - a)) :
    x ∈ segment ℝ a c := by
  refine gu2_mem_segment_of_coord1 a b c h ((gu2_mem_tri_iff a b c h x).mp hx) ?_
  rw [ht]
  exact gu2_coord_eq_zero_of_line (gu2_triBasis a b c h) (i := 1) (j := 0) (k := 2)
    (by decide) (by decide) t

theorem gu2_mem_segment_bc_of_line (a b c : Plane) (h : det (b - a) (c - a) ≠ 0) {x : Plane}
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set Plane)) {t : ℝ} (ht : x = b + t • (c - b)) :
    x ∈ segment ℝ b c := by
  refine gu2_mem_segment_of_coord0 a b c h ((gu2_mem_tri_iff a b c h x).mp hx) ?_
  rw [ht]
  exact gu2_coord_eq_zero_of_line (gu2_triBasis a b c h) (i := 0) (j := 1) (k := 2)
    (by decide) (by decide) t

/-! ### U2 helpers — labels, edges and visits of `P` -/

/-- a remote pair of labels forces `3 ≤ n` -/
theorem gu2_three_le_of_remote {i j : ZMod n} (h : remote i j) : 3 ≤ n := by
  by_contra hlt
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hadj : adjacent i j := by
    clear h
    interval_cases n
    · exact (by decide : ∀ i j : ZMod 1, j - i = -1 ∨ j - i = 0 ∨ j - i = 1) i j
    · exact (by decide : ∀ i j : ZMod 2, j - i = -1 ∨ j - i = 0 ∨ j - i = 1) i j
  exact h hadj

omit [NeZero n] in
theorem gu2_remote_of_isCrossing {i j : ZMod n} (h : IsCrossing P {i, j}) : remote i j := by
  have hij : i ≠ j := P1.ne_of_isCrossing_pair h
  obtain ⟨a, b, hs, hr, -⟩ := h
  have hi : i ∈ ({a, b} : Finset (ZMod n)) := hs ▸ mem_pair_left i j
  have hj : j ∈ ({a, b} : Finset (ZMod n)) := hs ▸ mem_pair_right i j
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact absurd rfl hij
  · exact hr
  · exact remote_symm hr
  · exact absurd rfl hij

omit [NeZero n] in
theorem gu2_isCrossing_comm {i j : ZMod n} (h : IsCrossing P {i, j}) : IsCrossing P {j, i} := by
  rwa [Finset.pair_comm]

omit [NeZero n] in
theorem gu2_xPair_comm {i j : ZMod n} (h : IsCrossing P {i, j}) :
    xPair (gu2_isCrossing_comm h) = xPair h := Subtype.ext (Finset.pair_comm j i)

omit [NeZero n] in
/-- a visit is determined by its crossing (up to a propositional equality) and its edge -/
theorem gu2_visit_congr {c c' : Crossing P} (h : c = c') {i : ZMod n} (hi : i ∈ c.val)
    (hi' : i ∈ c'.val) : (⟨c, ⟨i, hi⟩⟩ : Visit P) = ⟨c', ⟨i, hi'⟩⟩ := by
  subst h; rfl

/-- `ExactTriangleVisitOrders` depends on `e f g` only through the set `{e, f, g}` -/
theorem gu2_exact_of_eq {e' f' g' : ZMod n} (h : ({e, f, g} : Finset (ZMod n)) = {e', f', g'})
    (hX : ExactTriangleVisitOrders P P' e f g hs) : ExactTriangleVisitOrders P P' e' f' g' hs := by
  unfold ExactTriangleVisitOrders at hX ⊢
  rw [← h]
  exact hX

omit [NeZero n] in
theorem gu2_triple_perm_feg : ({f, e, g} : Finset (ZMod n)) = {e, f, g} := Finset.insert_comm f e {g}

omit [NeZero n] in
theorem gu2_triple_perm_gef : ({g, e, f} : Finset (ZMod n)) = {e, f, g} := by
  rw [Finset.insert_comm g e, Finset.pair_comm g f]

omit [NeZero n] in
/-- the difference of two points of one edge -/
theorem gu2_edgePoint_sub (a : ZMod n) (s t : ℝ) :
    edgePoint P a t - edgePoint P a s = (t - s) • edge P a := by
  simp only [edgePoint]
  rw [add_sub_add_left_eq_sub, sub_smul]

omit [NeZero n] in
/-- any point of the line of an edge as an affine combination of two distinct points of it -/
theorem gu2_edgePoint_comb (a : ZMod n) {ta tb : ℝ} (h : ta ≠ tb) (t : ℝ) :
    edgePoint P a t =
      edgePoint P a ta + ((t - ta) / (tb - ta)) • (edgePoint P a tb - edgePoint P a ta) := by
  have hne : tb - ta ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  simp only [edgePoint]
  rw [add_sub_add_left_eq_sub, ← sub_smul, smul_smul, div_mul_cancel₀ _ hne, add_assoc, ← add_smul,
    add_sub_cancel]

omit [NeZero n] in
/-- a point of the segment between two points of an edge is a point of the edge with parameter between -/
theorem gu2_segment_edgePoint (a : ZMod n) (ta tb : ℝ) {x : Plane}
    (hx : x ∈ segment ℝ (edgePoint P a ta) (edgePoint P a tb)) :
    ∃ t ∈ Set.uIcc ta tb, x = edgePoint P a t := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hx
  refine ⟨α * ta + β * tb, ?_, ?_⟩
  · rw [← segment_eq_uIcc]
    exact ⟨α, β, hα, hβ, hαβ, rfl⟩
  · have h1 : α • P a + β • P a = P a := by rw [← add_smul, hαβ, one_smul]
    simp only [edgePoint, smul_add, smul_smul, add_smul]
    calc _ = (α • P a + β • P a) + ((α * ta) • edge P a + (β * tb) • edge P a) := by abel
      _ = _ := by rw [h1]

omit [NeZero n] in
/-- a closed edge segment is convex -/
theorem gu2_edgeSegment_convex {a : ZMod n} {u v x : Plane} (hu : u ∈ edgeSegment P a)
    (hv : v ∈ edgeSegment P a) (hx : x ∈ segment ℝ u v) : x ∈ edgeSegment P a := by
  obtain ⟨s, hs0, hs1, rfl⟩ := hu
  obtain ⟨s', hs'0, hs'1, rfl⟩ := hv
  obtain ⟨t, ht, rfl⟩ := gu2_segment_edgePoint a s s' hx
  rw [Set.mem_uIcc] at ht
  refine ⟨t, ?_, ?_, rfl⟩ <;> rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

omit [NeZero n] in
/-- the crossing point of a pair as an edge point (`crossingParameter_spec`) -/
theorem gu2_xpt (c : Crossing P) (i : ZMod n) (hi : i ∈ c.val) :
    crossingPoint c = edgePoint P i (crossingParameter c i hi) := (crossingParameter_spec c i hi).2.2

include hG in
/-- the tail of an edge is not between two interior points of the edge -/
theorem gu2_tail_not_mem_segment {a : ZMod n} {ta tb : ℝ} (h0a : 0 < ta) (h0b : 0 < tb)
    (hmem : P a ∈ segment ℝ (edgePoint P a ta) (edgePoint P a tb)) : False := by
  obtain ⟨t, ht, hPt⟩ := gu2_segment_edgePoint a ta tb hmem
  have h0 : edgePoint P a 0 = edgePoint P a t := by rw [edgePoint_zero]; exact hPt
  have := edgePoint_injective (hG.cg.1 a) h0
  rw [Set.mem_uIcc] at ht
  rcases ht with ⟨h1, -⟩ | ⟨h1, -⟩ <;> linarith

include hG in
/-- distinct crossings on one edge have distinct parameters -/
theorem gu2_param_ne_of_xPair_ne {a : ZMod n} {c c' : Crossing P} (hne : c ≠ c') (hc : a ∈ c.val)
    (hc' : a ∈ c'.val) : crossingParameter c a hc ≠ crossingParameter c' a hc' := by
  intro h
  apply hne
  apply crossingPoint_injective_of_geometry hG.cg
  rw [gu2_xpt c a hc, gu2_xpt c' a hc', h]

include hG in
theorem gu2_ne_e (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g}) :
    crossingParameter (xPair hcef) e (mem_pair_left e f) ≠
      crossingParameter (xPair hceg) e (mem_pair_left e g) :=
  gu2_param_ne_of_xPair_ne hG (P1.xPair_ef_ne_eg hcef hceg hcfg) _ _

include hG in
theorem gu2_ne_f (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g}) :
    crossingParameter (xPair hcef) f (mem_pair_right e f) ≠
      crossingParameter (xPair hcfg) f (mem_pair_left f g) :=
  gu2_param_ne_of_xPair_ne hG (P1.xPair_ef_ne_fg hcef hceg hcfg) _ _

include hG in
theorem gu2_ne_g (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g}) :
    crossingParameter (xPair hceg) g (mem_pair_right e g) ≠
      crossingParameter (xPair hcfg) g (mem_pair_right f g) :=
  gu2_param_ne_of_xPair_ne hG (P1.xPair_eg_ne_fg hcef hceg hcfg) _ _

include hG in
/-- the three double points of the triangle are not collinear -/
theorem gu2_tri_det (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g}) :
    det (crossingPoint (xPair hceg) - crossingPoint (xPair hcef))
      (crossingPoint (xPair hcfg) - crossingPoint (xPair hcef)) ≠ 0 := by
  have h1 : crossingPoint (xPair hceg) - crossingPoint (xPair hcef) =
      (crossingParameter (xPair hceg) e (mem_pair_left e g) -
        crossingParameter (xPair hcef) e (mem_pair_left e f)) • edge P e := by
    rw [gu2_xpt (xPair hceg) e (mem_pair_left e g), gu2_xpt (xPair hcef) e (mem_pair_left e f),
      gu2_edgePoint_sub]
  have h2 : crossingPoint (xPair hcfg) - crossingPoint (xPair hcef) =
      (crossingParameter (xPair hcfg) f (mem_pair_left f g) -
        crossingParameter (xPair hcef) f (mem_pair_right e f)) • edge P f := by
    rw [gu2_xpt (xPair hcfg) f (mem_pair_left f g), gu2_xpt (xPair hcef) f (mem_pair_right e f),
      gu2_edgePoint_sub]
  rw [h1, h2, gu2_det_smul_smul]
  have hdet : det (edge P e) (edge P f) ≠ 0 :=
    (hG.cg.2.1 e f (gu2_remote_of_isCrossing hcef) _
      (crossingPoint_mem (xPair hcef) e (mem_pair_left e f))
      (crossingPoint_mem (xPair hcef) f (mem_pair_right e f))).2.2
  refine mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr ?_) (sub_ne_zero.mpr ?_)) hdet
  · exact (gu2_ne_e hG hcef hceg hcfg).symm
  · exact (gu2_ne_f hG hcef hceg hcfg).symm

include hG in
/-- a point of the closed triangle on the line of `e` lies on the side `[x_ef, x_eg]` -/
theorem gu2_line_e_mem_segment (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g})
    (hcfg : IsCrossing P {f, g}) {x : Plane}
    (hx : x ∈ convexHull ℝ {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)})
    {t : ℝ} (hxt : x = edgePoint P e t) :
    x ∈ segment ℝ (crossingPoint (xPair hcef)) (crossingPoint (xPair hceg)) := by
  have h := gu2_edgePoint_comb (P := P) e (gu2_ne_e hG hcef hceg hcfg) t
  rw [← gu2_xpt (xPair hcef) e (mem_pair_left e f), ← gu2_xpt (xPair hceg) e (mem_pair_left e g),
    ← hxt] at h
  exact gu2_mem_segment_ab_of_line _ _ _ (gu2_tri_det hG hcef hceg hcfg) hx h

include hG in
/-- a point of the closed triangle on the line of `f` lies on the side `[x_ef, x_fg]` -/
theorem gu2_line_f_mem_segment (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g})
    (hcfg : IsCrossing P {f, g}) {x : Plane}
    (hx : x ∈ convexHull ℝ {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)})
    {t : ℝ} (hxt : x = edgePoint P f t) :
    x ∈ segment ℝ (crossingPoint (xPair hcef)) (crossingPoint (xPair hcfg)) := by
  have h := gu2_edgePoint_comb (P := P) f (gu2_ne_f hG hcef hceg hcfg) t
  rw [← gu2_xpt (xPair hcef) f (mem_pair_right e f), ← gu2_xpt (xPair hcfg) f (mem_pair_left f g),
    ← hxt] at h
  exact gu2_mem_segment_ac_of_line _ _ _ (gu2_tri_det hG hcef hceg hcfg) hx h

include hG in
/-- a point of the closed triangle on the line of `g` lies on the side `[x_eg, x_fg]` -/
theorem gu2_line_g_mem_segment (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g})
    (hcfg : IsCrossing P {f, g}) {x : Plane}
    (hx : x ∈ convexHull ℝ {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)})
    {t : ℝ} (hxt : x = edgePoint P g t) :
    x ∈ segment ℝ (crossingPoint (xPair hceg)) (crossingPoint (xPair hcfg)) := by
  have h := gu2_edgePoint_comb (P := P) g (gu2_ne_g hG hcef hceg hcfg) t
  rw [← gu2_xpt (xPair hceg) g (mem_pair_right e g), ← gu2_xpt (xPair hcfg) g (mem_pair_right f g),
    ← hxt] at h
  exact gu2_mem_segment_bc_of_line _ _ _ (gu2_tri_det hG hcef hceg hcfg) hx h

include hG hs in
/-- **one side is clear**: no edge of `P` other than `a, b, c` meets the side `[x_ab, x_ac] ⊆ a` of the
triangle (the common point would be the double point of `{h, a}`, a visit on `a` between or at the two
local visits — excluded by `G11_no_visit_between` and the injectivity of double points; an adjacent `h`
meets `a` only at a vertex, off the open edge). -/
theorem gu2_side_clear {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcab : IsCrossing P {a, b}) (hcac : IsCrossing P {a, c})
    (hX : ExactTriangleVisitOrders P P' a b c hs) {h : ZMod n} (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c)
    {x : Plane} (hx : x ∈ edgeSegment P h)
    (hxs : x ∈ segment ℝ (crossingPoint (xPair hcab)) (crossingPoint (xPair hcac))) : False := by
  rw [gu2_xpt (xPair hcab) a (mem_pair_left a b), gu2_xpt (xPair hcac) a (mem_pair_left a c)] at hxs
  obtain ⟨t, ht, rfl⟩ := gu2_segment_edgePoint a _ _ hxs
  have hta01 := crossingParameter_interior_of_geometry hG.cg (xPair hcab) a (mem_pair_left a b)
  have htc01 := crossingParameter_interior_of_geometry hG.cg (xPair hcac) a (mem_pair_left a c)
  rw [Set.mem_uIcc] at ht
  have ht0 : 0 < t := by rcases ht with ⟨h1, -⟩ | ⟨h1, -⟩ <;> linarith [hta01.1, htc01.1]
  have ht1 : t < 1 := by rcases ht with ⟨-, h2⟩ | ⟨-, h2⟩ <;> linarith [hta01.2, htc01.2]
  have hxa' : edgePoint P a t ∈ edgeSegment P a := ⟨t, ht0.le, ht1.le, rfl⟩
  have hn3 : 3 ≤ n := gu2_three_le_of_remote (gu2_remote_of_isCrossing hcab)
  have hea : edge P a ≠ 0 := hG.cg.1 a
  by_cases hadj : adjacent h a
  · rcases hG.adjacent_edges_meet hn3 hha hadj with ⟨-, hmeet⟩ | ⟨hh, hmeet⟩
    · have hmem : edgePoint P a t ∈ edgeSegment P h ∩ edgeSegment P a := ⟨hx, hxa'⟩
      rw [hmeet] at hmem
      have h0 : edgePoint P a t = edgePoint P a 0 := by rw [edgePoint_zero]; exact hmem
      exact ht0.ne' (edgePoint_injective hea h0)
    · have hmem : edgePoint P a t ∈ edgeSegment P h ∩ edgeSegment P a := ⟨hx, hxa'⟩
      rw [hmeet] at hmem
      have h1 : edgePoint P a t = edgePoint P a 1 := by rw [edgePoint_one, ← hh]; exact hmem
      exact ht1.ne (edgePoint_injective hea h1)
  · have hcha : IsCrossing P {h, a} := (isCrossing_pair P h a hadj).mpr ⟨_, hx, hxa'⟩
    have hpt : edgePoint P a t = crossingPoint (xPair hcha) := by
      apply crossingPoint_unique_of_geometry hG.cg (xPair hcha)
      intro i hi
      change i ∈ ({h, a} : Finset (ZMod n)) at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hx
      · exact hxa'
    have hy : crossingParameter (xPair hcha) a (mem_pair_right h a) = t :=
      edgePoint_injective hea ((gu2_xpt (xPair hcha) a (mem_pair_right h a)).symm.trans hpt.symm)
    have hnb := G11_no_visit_between hs hab hac hbc hcab hcac hX ⟨xPair hcha, ⟨a, mem_pair_right h a⟩⟩ rfl
    have hnb' : ¬ (crossingParameter (xPair hcab) a (mem_pair_left a b) < t ∧
          t < crossingParameter (xPair hcac) a (mem_pair_left a c)) ∧
        ¬ (crossingParameter (xPair hcac) a (mem_pair_left a c) < t ∧
          t < crossingParameter (xPair hcab) a (mem_pair_left a b)) := by
      rw [← hy]
      exact hnb
    have hkey : ∀ (c' : Crossing P) (hc' : a ∈ c'.val), t = crossingParameter c' a hc' →
        ({h, a} : Finset (ZMod n)) = c'.val := by
      intro c' hc' ht'
      have hinj : xPair hcha = c' := crossingPoint_injective_of_geometry hG.cg
        (show crossingPoint (xPair hcha) = crossingPoint c' by rw [← hpt, gu2_xpt c' a hc', ht'])
      exact congrArg Subtype.val hinj
    have hcases : t = crossingParameter (xPair hcab) a (mem_pair_left a b) ∨
        t = crossingParameter (xPair hcac) a (mem_pair_left a c) := by
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases h1.lt_or_eq with h1 | h1
        · rcases h2.lt_or_eq with h2 | h2
          · exact (hnb'.1 ⟨h1, h2⟩).elim
          · exact Or.inr h2
        · exact Or.inl h1.symm
      · rcases h1.lt_or_eq with h1 | h1
        · rcases h2.lt_or_eq with h2 | h2
          · exact (hnb'.2 ⟨h1, h2⟩).elim
          · exact Or.inl h2
        · exact Or.inr h1.symm
    rcases hcases with ht' | ht'
    · have hh : h ∈ (xPair hcab).val := by rw [← hkey _ _ ht']; exact mem_pair_left h a
      change h ∈ ({a, b} : Finset (ZMod n)) at hh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with hh | hh
      · exact hha hh
      · exact hhb hh
    · have hh : h ∈ (xPair hcac).val := by rw [← hkey _ _ ht']; exact mem_pair_left h a
      change h ∈ ({a, c} : Finset (ZMod n)) at hh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with hh | hh
      · exact hha hh
      · exact hhc hh

/-- **the walk**: if every edge whose tail lies in `Δ` misses the frontier of `Δ`, and some vertex is off
`Δ`, then no vertex lies in `Δ` (`Nat.find` on the first step leaving `Δ` along the polygon from a vertex
inside; that edge would meet the frontier, `G11_preconnected_meets_frontier`). -/
theorem gu2_no_vertex_of_walk {Δ : Set Plane}
    (hfr : ∀ h : ZMod n, P h ∈ Δ → ∀ x ∈ edgeSegment P h, x ∉ frontier Δ)
    {e : ZMod n} (he : P e ∉ Δ) (i : ZMod n) : P i ∉ Δ := by
  intro hi
  classical
  have hex : ∃ k : ℕ, P (i + (k : ZMod n)) ∉ Δ :=
    ⟨(e - i).val, by rw [ZMod.natCast_zmod_val, add_sub_cancel]; exact he⟩
  have hk : P (i + ((Nat.find hex : ℕ) : ZMod n)) ∉ Δ := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hk
    exact hk (by simpa using hi)
  obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hk'mem : P (i + (k' : ZMod n)) ∈ Δ := by
    by_contra hnot
    exact Nat.find_min hex (show k' < Nat.find hex by omega) hnot
  have hj1 : i + (k' : ZMod n) + 1 = i + ((Nat.find hex : ℕ) : ZMod n) := by
    rw [hk', Nat.cast_succ, add_assoc]
  obtain ⟨y, hy, hyF⟩ := G11_preconnected_meets_frontier
    (G11_edgeSegment_isPreconnected P (i + (k' : ZMod n)))
    ⟨P (i + (k' : ZMod n)), ⟨0, le_rfl, zero_le_one, (edgePoint_zero P _).symm⟩, hk'mem⟩
    ⟨P (i + (k' : ZMod n) + 1), ⟨1, zero_le_one, le_rfl, (edgePoint_one P _).symm⟩,
      by rw [hj1]; exact hk⟩
  exact hfr _ hk'mem y hy hyF

include hG hs in
/-- **A8 with the geometric hypothesis `hG : CarrierGeometry P`.** The frozen leaf `G11_clear` below does
not have `hG` in scope (the section variable is not mentioned in its statement) and is false without it
(a degenerate polygon with four edges through one point and `P' = P` satisfies all its hypotheses); this
is the statement actually consumed by the configuration leaves. Clause (i): a frontier point lies on a
side (`gu2_frontier_subset_sides`), cleared by `gu2_side_clear` in the three labellings. Clause (ii): the
tails `P e, P f, P g` are off the triangle (on the line of a side, off the side), then the walk. -/
theorem gu2_clear (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs) :
    (∀ h : ZMod n, h ≠ e → h ≠ f → h ≠ g → ∀ x ∈ edgeSegment P h,
      x ∉ frontier (convexHull ℝ
        {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)})) ∧
    (∀ i : ZMod n, P i ∉
      convexHull ℝ {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)}) := by
  have hdet := gu2_tri_det hG hcef hceg hcfg
  have hcfe : IsCrossing P {f, e} := gu2_isCrossing_comm hcef
  have hcge : IsCrossing P {g, e} := gu2_isCrossing_comm hceg
  have hcgf : IsCrossing P {g, f} := gu2_isCrossing_comm hcfg
  have hA : crossingPoint (xPair hcfe) = crossingPoint (xPair hcef) :=
    congrArg crossingPoint (gu2_xPair_comm hcef)
  have hB : crossingPoint (xPair hcge) = crossingPoint (xPair hceg) :=
    congrArg crossingPoint (gu2_xPair_comm hceg)
  have hC : crossingPoint (xPair hcgf) = crossingPoint (xPair hcfg) :=
    congrArg crossingPoint (gu2_xPair_comm hcfg)
  have hXf : ExactTriangleVisitOrders P P' f e g hs := gu2_exact_of_eq hs gu2_triple_perm_feg.symm hX
  have hXg : ExactTriangleVisitOrders P P' g e f hs := gu2_exact_of_eq hs gu2_triple_perm_gef.symm hX
  have h1 : ∀ h : ZMod n, h ≠ e → h ≠ f → h ≠ g → ∀ x ∈ edgeSegment P h,
      x ∉ frontier (convexHull ℝ
        {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)}) := by
    intro h hhe hhf hhg x hx hxF
    rcases gu2_frontier_subset_sides _ _ _ hdet hxF with hAB | hAC | hBC
    · exact gu2_side_clear hG hs hef heg hfg hcef hceg hX hhe hhf hhg hx hAB
    · refine gu2_side_clear hG hs hef.symm hfg heg hcfe hcfg hXf hhf hhe hhg hx ?_
      rw [hA]; exact hAC
    · refine gu2_side_clear hG hs heg.symm hfg.symm hef hcge hcgf hXg hhg hhe hhf hx ?_
      rw [hB, hC]; exact hBC
  have hPe : P e ∉ convexHull ℝ
      {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)} := by
    intro hmem
    have hseg := gu2_line_e_mem_segment hG hcef hceg hcfg hmem (edgePoint_zero P e).symm
    rw [gu2_xpt (xPair hcef) e (mem_pair_left e f), gu2_xpt (xPair hceg) e (mem_pair_left e g)] at hseg
    exact gu2_tail_not_mem_segment hG
      (crossingParameter_interior_of_geometry hG.cg (xPair hcef) e (mem_pair_left e f)).1
      (crossingParameter_interior_of_geometry hG.cg (xPair hceg) e (mem_pair_left e g)).1 hseg
  have hPf : P f ∉ convexHull ℝ
      {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)} := by
    intro hmem
    have hseg := gu2_line_f_mem_segment hG hcef hceg hcfg hmem (edgePoint_zero P f).symm
    rw [gu2_xpt (xPair hcef) f (mem_pair_right e f), gu2_xpt (xPair hcfg) f (mem_pair_left f g)] at hseg
    exact gu2_tail_not_mem_segment hG
      (crossingParameter_interior_of_geometry hG.cg (xPair hcef) f (mem_pair_right e f)).1
      (crossingParameter_interior_of_geometry hG.cg (xPair hcfg) f (mem_pair_left f g)).1 hseg
  have hPg : P g ∉ convexHull ℝ
      {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)} := by
    intro hmem
    have hseg := gu2_line_g_mem_segment hG hcef hceg hcfg hmem (edgePoint_zero P g).symm
    rw [gu2_xpt (xPair hceg) g (mem_pair_right e g), gu2_xpt (xPair hcfg) g (mem_pair_right f g)] at hseg
    exact gu2_tail_not_mem_segment hG
      (crossingParameter_interior_of_geometry hG.cg (xPair hceg) g (mem_pair_right e g)).1
      (crossingParameter_interior_of_geometry hG.cg (xPair hcfg) g (mem_pair_right f g)).1 hseg
  refine ⟨h1, ?_⟩
  exact gu2_no_vertex_of_walk
    (fun h hh => h1 h (fun heq => hPe (heq ▸ hh)) (fun heq => hPf (heq ▸ hh)) (fun heq => hPg (heq ▸ hh)))
    hPe

include hG hs in
/-- the closed form of `gu2_clear`: no edge of `P` other than `e, f, g` meets the closed triangle (as
`G11_Config.clear_edge`: its tail is off the triangle, so it would meet the frontier). -/
theorem gu2_clear_closed (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hcef : IsCrossing P {e, f}) (hceg : IsCrossing P {e, g}) (hcfg : IsCrossing P {f, g})
    (hX : ExactTriangleVisitOrders P P' e f g hs) :
    ∀ h : ZMod n, h ≠ e → h ≠ f → h ≠ g → ∀ x ∈ edgeSegment P h,
      x ∉ convexHull ℝ {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)} := by
  intro h hhe hhf hhg x hx hxΔ
  obtain ⟨hfr, hv⟩ := gu2_clear hG hs hef heg hfg hcef hceg hcfg hX
  obtain ⟨y, hy, hyF⟩ := G11_preconnected_meets_frontier (G11_edgeSegment_isPreconnected P h)
    ⟨x, hx, hxΔ⟩ ⟨P h, ⟨0, le_rfl, zero_le_one, (edgePoint_zero P h).symm⟩, hv h⟩
  exact hfr h hhe hhf hhg y hy hyF

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
  rw [show strandSign P g f = -strandSign P f g from crossingSign_swap P f g]
  unfold IsAlternating at hne ⊢
  generalize strandSign P e f = sa at *
  generalize strandSign P e g = sb at *
  generalize strandSign P f g = sc at *
  revert hne sa sb sc
  decide

/-- **A10 (relabelling).** `ExactTriangleVisitOrders` is symmetric in `f, g` (`{e, g, f} = {e, f, g}`). -/
theorem G11_exact_swap (hX : ExactTriangleVisitOrders P P' e f g hs) :
    ExactTriangleVisitOrders P P' e g f hs := by
  have h : ({e, g, f} : Finset (ZMod n)) = {e, f, g} := by rw [Finset.pair_comm g f]
  unfold ExactTriangleVisitOrders at hX ⊢
  rw [h]
  exact hX

theorem G11_triangleCrossings_swap : triangleCrossings P e g f = triangleCrossings P e f g := by
  have h : triangleSupports e g f = triangleSupports e f g := by
    unfold triangleSupports
    ext s
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [Finset.pair_comm g f]
    tauto
  unfold triangleCrossings
  rw [h]

/-- **A11 (the strand signs of the configuration).** `¬ IsAlternating` in the strand-sign form of `GT_G11`
is `¬ IsAlternating` in the `crossingSign` form on `(e, f, g) = (m, p, q)`. -/
theorem G11_alt_crossingSign
    (hne : ¬ IsAlternating (strandSign P e f) (strandSign P e g) (strandSign P f g)) :
    ¬ IsAlternating (crossingSign P e f) (crossingSign P e g) (crossingSign P f g) := by
  exact hne

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

/-! ### U2 helpers — the edges of the corner polygon inside the edges of `P` -/

include hn hT in
/-- an edge of the corner polygon lies inside the original edge of the outgoing slot of its starting
corner (both corners lie on that original edge: `geo_evaluation_eq_outSlot`,
`geoCornerPolygon_outEdge_eq_inEdge_of_independent`, `geoMarkSuccessor_on_edge`; the segment is convex). -/
theorem gu2_edgeSegment_sub (k : ZMod (geoCornerCount hG.cg T q)) :
    edgeSegment (geoCornerPolygon hG.cg T q) k ⊆
      edgeSegment P (geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).1 := by
  have h1 : geoCornerPolygon hG.cg T q k ∈
      edgeSegment P (geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).1 := by
    rw [geoCornerPolygon_apply, geo_evaluation_eq_outSlot]
    exact ⟨_, (geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).2.property.1,
      (geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).2.property.2.le, rfl⟩
  have h2 : geoCornerPolygon hG.cg T q (k + 1) ∈
      edgeSegment P (geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).1 := by
    rw [geoCornerPolygon_outEdge_eq_inEdge_of_independent hn hG.cg hT q k, geoCornerPolygon_apply]
    unfold geoInEdge
    obtain ⟨t, ht0, ht1, hev⟩ := geoMarkSuccessor_on_edge hG.cg
      ((geoMarkSuccessor hG.cg).symm (geoCornerMark hG.cg T q (k + 1)))
    rw [Equiv.apply_symm_apply] at hev
    exact ⟨t, ((geoMarkPosition hG.cg _).2.property.1).trans ht0, ht1, hev⟩
  intro x hx
  obtain ⟨t, ht0, ht1, rfl⟩ := hx
  obtain ⟨s₁, hs₁0, hs₁1, hX1⟩ := h1
  obtain ⟨s₂, hs₂0, hs₂1, hX2⟩ := h2
  refine ⟨s₁ + t * (s₂ - s₁), ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · show geoCornerPolygon hG.cg T q k +
      t • (geoCornerPolygon hG.cg T q (k + 1) - geoCornerPolygon hG.cg T q k) = _
    rw [hX1, hX2, gu2_edgePoint_sub, smul_smul]
    simp only [edgePoint]
    rw [add_assoc, ← add_smul]

/-- the carrier edge of a retained visit lies inside the original edge of that visit (its double point
is interior to that edge; a second original edge through it would be adjacent — meeting only at a vertex
— or remote and transverse, while the carrier edge is parallel to both). -/
theorem gu2_carrierEdge_label (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg T q) :
    (geoOutSlot hG.cg T (geoCornerMark hG.cg T q (G11_carrierEdge hn hG hT q v hv))).1 = v.2.val := by
  obtain ⟨hmem, c, hc, hedge⟩ := G11_carrierEdge_spec hn hG hT q v hv
  obtain ⟨c', hc', hedge'⟩ := geoCornerPolygon_edge_smul hn hG.cg hT q (G11_carrierEdge hn hG hT q v hv)
  have hx₀ := gu2_edgeSegment_sub hn hG hT q _ hmem
  have hxa : crossingPoint v.1 ∈ edgeInterior P v.2.val :=
    crossingPoint_interior_of_geometry hG.cg v.1 v.2.val v.2.property
  have hxa' : crossingPoint v.1 ∈ edgeSegment P v.2.val := edgeInterior_subset_edgeSegment _ _ hxa
  by_contra hne
  by_cases hadj : adjacent (geoOutSlot hG.cg T (geoCornerMark hG.cg T q
      (G11_carrierEdge hn hG hT q v hv))).1 v.2.val
  · rcases hG.adjacent_edges_meet hn hne hadj with ⟨-, hmeet⟩ | ⟨-, hmeet⟩
    · have hm : crossingPoint v.1 ∈ edgeSegment P _ ∩ edgeSegment P _ := ⟨hx₀, hxa'⟩
      rw [hmeet] at hm
      exact cg_crossingPoint_ne_vertex hG v.1 _ hm
    · have hm : crossingPoint v.1 ∈ edgeSegment P _ ∩ edgeSegment P _ := ⟨hx₀, hxa'⟩
      rw [hmeet] at hm
      exact cg_crossingPoint_ne_vertex hG v.1 _ hm
  · have hdet := (hG.cg.2.1 _ _ hadj _ hx₀ hxa').2.2
    apply hdet
    have h3 : edge P v.2.val = (c⁻¹ * c') • edge P (geoOutSlot hG.cg T (geoCornerMark hG.cg T q
        (G11_carrierEdge hn hG hT q v hv))).1 := by
      rw [mul_smul, ← hedge', hedge, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    rw [h3, gu2_det_smul_right, gu2_det_self, mul_zero]

/-- the carrier edges `m, p, q` of the configuration lie inside `e, f, g` -/
theorem gu2_mE_sub :
    edgeSegment (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) ⊆ edgeSegment P e := by
  have h := gu2_edgeSegment_sub hn hG hT q
    (G11_carrierEdge hn hG hT q (G11_vef hcef) (G11_mem_tri_ef hG q hcef htri))
  rw [gu2_carrierEdge_label hn hG hT q (G11_vef hcef) (G11_mem_tri_ef hG q hcef htri)] at h
  exact h

theorem gu2_pE_sub :
    edgeSegment (geoCornerPolygon hG.cg T q) (G11_pE hn hG hT q hcef htri) ⊆ edgeSegment P f := by
  have h := gu2_edgeSegment_sub hn hG hT q
    (G11_carrierEdge hn hG hT q (G11_vfe hcef) (G11_mem_tri_ef hG q hcef htri))
  rw [gu2_carrierEdge_label hn hG hT q (G11_vfe hcef) (G11_mem_tri_ef hG q hcef htri)] at h
  exact h

theorem gu2_qE_sub :
    edgeSegment (geoCornerPolygon hG.cg T q) (G11_qE hn hG hT q hceg htri) ⊆ edgeSegment P g := by
  have h := gu2_edgeSegment_sub hn hG hT q
    (G11_carrierEdge hn hG hT q (G11_vge hceg) (G11_mem_tri_eg hG q hceg htri))
  rw [gu2_carrierEdge_label hn hG hT q (G11_vge hceg) (G11_mem_tri_eg hG q hceg htri)] at h
  exact h

/-- the double points of the configuration are the double points of `P` (a common point of a
sub-segment of `e` and a sub-segment of `f` is the double point of `{e, f}`) -/
theorem gu2_xmp_eq (hmp : IsCrossing (geoCornerPolygon hG.cg T q)
    {G11_mE hn hG hT q hcef htri, G11_pE hn hG hT q hcef htri}) :
    crossingPoint (xPair hmp) = crossingPoint (xPair hcef) := by
  apply crossingPoint_unique_of_geometry hG.cg (xPair hcef)
  intro i hi
  change i ∈ ({e, f} : Finset (ZMod n)) at hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact gu2_mE_sub hn hG hT q hcef htri (crossingPoint_mem (xPair hmp) _ (mem_pair_left _ _))
  · exact gu2_pE_sub hn hG hT q hcef htri (crossingPoint_mem (xPair hmp) _ (mem_pair_right _ _))

theorem gu2_xmq_eq (hmq : IsCrossing (geoCornerPolygon hG.cg T q)
    {G11_mE hn hG hT q hcef htri, G11_qE hn hG hT q hceg htri}) :
    crossingPoint (xPair hmq) = crossingPoint (xPair hceg) := by
  apply crossingPoint_unique_of_geometry hG.cg (xPair hceg)
  intro i hi
  change i ∈ ({e, g} : Finset (ZMod n)) at hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact gu2_mE_sub hn hG hT q hcef htri (crossingPoint_mem (xPair hmq) _ (mem_pair_left _ _))
  · exact gu2_qE_sub hn hG hT q hceg htri (crossingPoint_mem (xPair hmq) _ (mem_pair_right _ _))

theorem gu2_xpq_eq (hpq : IsCrossing (geoCornerPolygon hG.cg T q)
    {G11_pE hn hG hT q hcef htri, G11_qE hn hG hT q hceg htri}) :
    crossingPoint (xPair hpq) = crossingPoint (xPair hcfg) := by
  apply crossingPoint_unique_of_geometry hG.cg (xPair hcfg)
  intro i hi
  change i ∈ ({f, g} : Finset (ZMod n)) at hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact gu2_pE_sub hn hG hT q hcef htri (crossingPoint_mem (xPair hpq) _ (mem_pair_left _ _))
  · exact gu2_qE_sub hn hG hT q hceg htri (crossingPoint_mem (xPair hpq) _ (mem_pair_right _ _))

/-- a crossing `{p, q}` of the configuration forces `f ≠ g` and the crossing `{f, g}` of `P` (the
frozen `G11_cfg_hpq` does not have `hcfg` in scope; this is how its consumers recover it) -/
theorem gu2_hcfg_of_hpq (hpq : IsCrossing (geoCornerPolygon hG.cg T q)
    {G11_pE hn hG hT q hcef htri, G11_qE hn hG hT q hceg htri}) :
    f ≠ g ∧ IsCrossing P {f, g} := by
  have hrem := gu2_remote_of_isCrossing hpq
  have hfg : f ≠ g := by
    rintro rfl
    exact hrem (Or.inr (Or.inl (sub_self _)))
  refine ⟨hfg, ?_⟩
  have hx_p : crossingPoint (xPair hpq) ∈ edgeSegment P f :=
    gu2_pE_sub hn hG hT q hcef htri (crossingPoint_mem (xPair hpq) _ (mem_pair_left _ _))
  have hx_q : crossingPoint (xPair hpq) ∈ edgeSegment P g :=
    gu2_qE_sub hn hG hT q hceg htri (crossingPoint_mem (xPair hpq) _ (mem_pair_right _ _))
  by_cases hadj : adjacent f g
  · exfalso
    obtain ⟨c, -, hxc⟩ := geo_nonadjacent_meet_crossing hn hG hT q hrem
      (crossingPoint_mem (xPair hpq) _ (mem_pair_left _ _))
      (crossingPoint_mem (xPair hpq) _ (mem_pair_right _ _))
    have hm : crossingPoint (xPair hpq) ∈ edgeSegment P f ∩ edgeSegment P g := ⟨hx_p, hx_q⟩
    rcases hG.adjacent_edges_meet hn hfg hadj with ⟨-, hmeet⟩ | ⟨-, hmeet⟩
    · rw [hmeet] at hm
      exact cg_crossingPoint_ne_vertex hG c _ (by rw [← hxc]; exact hm)
    · rw [hmeet] at hm
      exact cg_crossingPoint_ne_vertex hG c _ (by rw [← hxc]; exact hm)
  · exact (isCrossing_pair P f g hadj).mpr ⟨_, hx_p, hx_q⟩

/-- the carrier edge does not depend on the presentation of the visit -/
theorem gu2_carrierEdge_congr {v w : Visit P} (hvw : v = w) (hv : v.1 ∈ geoCarrierCrossings hG.cg T q)
    (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    G11_carrierEdge hn hG hT q v hv = G11_carrierEdge hn hG hT q w hw := by
  subst hvw; rfl

/-- the twins of the six local visits -/
theorem gu2_visitTwin_vef : visitTwin (G11_vef hcef) = G11_vfe hcef :=
  (visitTwin_unique (G11_vef hcef) (G11_vfe hcef) rfl
    (fun h => P1.ne_of_isCrossing_pair hcef (congrArg (fun w : Visit P => w.2.val) h).symm)).symm

theorem gu2_visitTwin_veg : visitTwin (G11_veg hceg) = G11_vge hceg :=
  (visitTwin_unique (G11_veg hceg) (G11_vge hceg) rfl
    (fun h => P1.ne_of_isCrossing_pair hceg (congrArg (fun w : Visit P => w.2.val) h).symm)).symm

theorem gu2_visitTwin_vfg : visitTwin (G11_vfg hcfg) = G11_vgf hcfg :=
  (visitTwin_unique (G11_vfg hcfg) (G11_vgf hcfg) rfl
    (fun h => P1.ne_of_isCrossing_pair hcfg (congrArg (fun w : Visit P => w.2.val) h).symm)).symm

/-- **A12 (crossings of the configuration).** `{m, p}` carries `x_ef` (A4 with `v = x_ef` on `e`); `{m, q}`
carries `x_eg` (A3: `x_eg` on `e` lies on the same carrier edge as `x_ef` on `e`, by A7; A4); `{p, q}`
carries `x_fg` (A3 on `f` and on `g`; A4). -/
theorem G11_cfg_hmp :
    IsCrossing (geoCornerPolygon hG.cg T q) {G11_mE hn hG hT q hcef htri, G11_pE hn hG hT q hcef htri} := by
  have h := G11_carrierEdge_isCrossing hn hG hT q (G11_vef hcef) (G11_mem_tri_ef hG q hcef htri)
  rw [gu2_carrierEdge_congr hn hG hT q (gu2_visitTwin_vef hcef) _ (G11_mem_tri_ef hG q hcef htri)] at h
  exact h

theorem G11_cfg_hmq (hX : ExactTriangleVisitOrders P P' e f g hs) :
    IsCrossing (geoCornerPolygon hG.cg T q) {G11_mE hn hG hT q hcef htri, G11_qE hn hG hT q hceg htri} := by
  by_cases hfg : f = g
  · subst hfg
    exact G11_cfg_hmp hn hG hT q hcef htri
  · have hnb := G11_no_visit_between hs (P1.ne_of_isCrossing_pair hcef) (P1.ne_of_isCrossing_pair hceg)
      hfg hcef hceg hX
    have hme : G11_carrierEdge hn hG hT q (G11_veg hceg) (G11_mem_tri_eg hG q hceg htri) =
        G11_mE hn hG hT q hcef htri :=
      (G11_carrierEdge_eq_of_adjacent hn hG hT q (v := G11_vef hcef) (w := G11_veg hceg)
        (G11_mem_tri_ef hG q hcef htri) (G11_mem_tri_eg hG q hceg htri) rfl (fun y hy => hnb y hy)).symm
    have h := G11_carrierEdge_isCrossing hn hG hT q (G11_veg hceg) (G11_mem_tri_eg hG q hceg htri)
    rw [gu2_carrierEdge_congr hn hG hT q (gu2_visitTwin_veg hceg) _ (G11_mem_tri_eg hG q hceg htri),
      hme] at h
    exact h

theorem G11_cfg_hpq (hX : ExactTriangleVisitOrders P P' e f g hs) :
    IsCrossing (geoCornerPolygon hG.cg T q) {G11_pE hn hG hT q hcef htri, G11_qE hn hG hT q hceg htri} := by
  sorry

/-- **A12 for `{p, q}` with the crossing hypothesis.** The frozen `G11_cfg_hpq` above does not have `hcfg`
(nor `hfg`) in scope — its statement mentions neither — and its conclusion forces `IsCrossing P {f, g}`
(`gu2_hcfg_of_hpq`), which is not derivable from the remaining hypotheses in the library; this is the
provable form. `p` carries `x_ef` and `x_fg` (A3 on `f`), `q` carries `x_eg` and `x_fg` (A3 on `g`), and
A4 at `x_fg`. -/
theorem gu2_cfg_hpq (hfg : f ≠ g) (hcfg : IsCrossing P {f, g}) (hX : ExactTriangleVisitOrders P P' e f g hs) :
    IsCrossing (geoCornerPolygon hG.cg T q) {G11_pE hn hG hT q hcef htri, G11_qE hn hG hT q hceg htri} := by
  have hef := P1.ne_of_isCrossing_pair hcef
  have heg := P1.ne_of_isCrossing_pair hceg
  have hcfe : IsCrossing P {f, e} := gu2_isCrossing_comm hcef
  have hcge : IsCrossing P {g, e} := gu2_isCrossing_comm hceg
  have hcgf : IsCrossing P {g, f} := gu2_isCrossing_comm hcfg
  have hXf : ExactTriangleVisitOrders P P' f e g hs := gu2_exact_of_eq hs gu2_triple_perm_feg.symm hX
  have hXg : ExactTriangleVisitOrders P P' g e f hs := gu2_exact_of_eq hs gu2_triple_perm_gef.symm hX
  have hvfe : (⟨xPair hcfe, ⟨f, mem_pair_left f e⟩⟩ : Visit P) = G11_vfe hcef :=
    gu2_visit_congr (gu2_xPair_comm hcef) _ _
  have hvge : (⟨xPair hcge, ⟨g, mem_pair_left g e⟩⟩ : Visit P) = G11_vge hceg :=
    gu2_visit_congr (gu2_xPair_comm hceg) _ _
  have hvgf : (⟨xPair hcgf, ⟨g, mem_pair_left g f⟩⟩ : Visit P) = G11_vgf hcfg :=
    gu2_visit_congr (gu2_xPair_comm hcfg) _ _
  have hmfg : (G11_vfg hcfg).1 ∈ geoCarrierCrossings hG.cg T q := G11_mem_tri_fg hG q hcfg htri
  have hmgf : (G11_vgf hcfg).1 ∈ geoCarrierCrossings hG.cg T q := G11_mem_tri_fg hG q hcfg htri
  have hpf : G11_carrierEdge hn hG hT q (G11_vfg hcfg) hmfg = G11_pE hn hG hT q hcef htri := by
    refine (G11_carrierEdge_eq_of_adjacent hn hG hT q (v := G11_vfe hcef) (w := G11_vfg hcfg)
      (G11_mem_tri_ef hG q hcef htri) hmfg rfl ?_).symm
    intro y hy
    have h := G11_no_visit_between hs hef.symm hfg heg hcfe hcfg hXf y hy
    rw [hvfe] at h
    exact h
  have hqg : G11_carrierEdge hn hG hT q (G11_vgf hcfg) hmgf = G11_qE hn hG hT q hceg htri := by
    refine (G11_carrierEdge_eq_of_adjacent hn hG hT q (v := G11_vge hceg) (w := G11_vgf hcfg)
      (G11_mem_tri_eg hG q hceg htri) hmgf rfl ?_).symm
    intro y hy
    have h := G11_no_visit_between hs heg.symm hfg.symm hef hcge hcgf hXg y hy
    rw [hvge, hvgf] at h
    exact h
  have h := G11_carrierEdge_isCrossing hn hG hT q (G11_vfg hcfg) hmfg
  rw [gu2_carrierEdge_congr hn hG hT q (gu2_visitTwin_vfg hcfg) _ hmgf, hpf, hqg] at h
  exact h

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
  have hmp := G11_cfg_hmp hn hG hT q hcef htri
  have hmq := G11_cfg_hmq hn hG hs hT q hcef hceg htri hX
  obtain ⟨-, c, hc, hedge⟩ := G11_carrierEdge_spec hn hG hT q (G11_vef hcef) (G11_mem_tri_ef hG q hcef htri)
  have hedge' : edge (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) = c • edge P e := hedge
  have hx1 := gu2_xmp_eq hn hG hT q hcef htri hmp
  have hx2 := gu2_xmq_eq hn hG hT q hcef hceg htri hmq
  rw [gu2_xpt (xPair hmp) (G11_mE hn hG hT q hcef htri) (mem_pair_left _ _),
    gu2_xpt (xPair hcef) e (mem_pair_left e f)] at hx1
  rw [gu2_xpt (xPair hmq) (G11_mE hn hG hT q hcef htri) (mem_pair_left _ _),
    gu2_xpt (xPair hceg) e (mem_pair_left e g)] at hx2
  have hsub : edgePoint (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri)
        (crossingParameter (xPair hmq) (G11_mE hn hG hT q hcef htri) (mem_pair_left _ _)) -
      edgePoint (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri)
        (crossingParameter (xPair hmp) (G11_mE hn hG hT q hcef htri) (mem_pair_left _ _)) =
      edgePoint P e (crossingParameter (xPair hceg) e (mem_pair_left e g)) -
        edgePoint P e (crossingParameter (xPair hcef) e (mem_pair_left e f)) := by
    rw [hx1, hx2]
  rw [gu2_edgePoint_sub, gu2_edgePoint_sub, hedge', smul_smul] at hsub
  have hinj : (crossingParameter (xPair hmq) (G11_mE hn hG hT q hcef htri) (mem_pair_left _ _) -
      crossingParameter (xPair hmp) (G11_mE hn hG hT q hcef htri) (mem_pair_left _ _)) * c =
      crossingParameter (xPair hceg) e (mem_pair_left e g) -
        crossingParameter (xPair hcef) e (mem_pair_left e f) := by
    apply edgePoint_injective (hG.cg.1 e)
    show P e + _ • edge P e = P e + _ • edge P e
    rw [hsub]
  have hpos : 0 < (crossingParameter (xPair hmq) (G11_mE hn hG hT q hcef htri) (mem_pair_left _ _) -
      crossingParameter (xPair hmp) (G11_mE hn hG hT q hcef htri) (mem_pair_left _ _)) * c := by
    rw [hinj]; linarith
  have := (mul_pos_iff_of_pos_right hc).mp hpos
  linarith

/-- **A14 (transitive heights).** `crossingSign X m p = crossingSign P e f` etc. (A6) and A11. -/
theorem G11_cfg_trans (halt : ¬ IsAlternating (strandSign P e f) (strandSign P e g) (strandSign P f g)) :
    ¬ IsAlternating (crossingSign (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) (G11_pE hn hG hT q hcef htri))
      (crossingSign (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) (G11_qE hn hG hT q hceg htri))
      (crossingSign (geoCornerPolygon hG.cg T q) (G11_pE hn hG hT q hcef htri) (G11_qE hn hG hT q hceg htri)) := by
  have h1 := G11_carrierSign hn hG hT q (G11_vef hcef) (G11_vfe hcef) (G11_mem_tri_ef hG q hcef htri)
    (G11_mem_tri_ef hG q hcef htri)
  have h2 := G11_carrierSign hn hG hT q (G11_vef hcef) (G11_vge hceg) (G11_mem_tri_ef hG q hcef htri)
    (G11_mem_tri_eg hG q hceg htri)
  have h3 := G11_carrierSign hn hG hT q (G11_vfe hcef) (G11_vge hceg) (G11_mem_tri_ef hG q hcef htri)
    (G11_mem_tri_eg hG q hceg htri)
  have h := G11_alt_crossingSign halt
  unfold G11_mE G11_pE G11_qE
  rw [h1, h2, h3]
  exact h

/-- two labels among `e, f, g` form a support of the triangle -/
theorem gu2_pair_mem_triangleSupports {a b : ZMod n} (hab : a ≠ b) (ha : a = e ∨ a = f ∨ a = g)
    (hb : b = e ∨ b = f ∨ b = g) : ({a, b} : Finset (ZMod n)) ∈ triangleSupports e f g := by
  unfold triangleSupports
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hab
    | exact Finset.mem_insert_self _ _
    | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    | (rw [Finset.pair_comm a b]; first
        | exact Finset.mem_insert_self _ _
        | exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        | exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))

include hn hT in
/-- two distinct edges of the corner polygon parallel to one original edge meet only at a corner
(non-adjacent meeting edges are transverse, `geoCornerPolygon_transverse`; adjacent ones meet at their
common corner, `meet_next_eq_corner_of_vertex_off` with `geoCornerPolygon_tail_off`) -/
theorem gu2_parallel_meet_vertex {k k' : ZMod (geoCornerCount hG.cg T q)} (hkk : k ≠ k') {a : ZMod n}
    {c c' : ℝ} (hk : edge (geoCornerPolygon hG.cg T q) k = c • edge P a)
    (hk' : edge (geoCornerPolygon hG.cg T q) k' = c' • edge P a) {x : Plane}
    (hxk : x ∈ edgeSegment (geoCornerPolygon hG.cg T q) k)
    (hxk' : x ∈ edgeSegment (geoCornerPolygon hG.cg T q) k') :
    ∃ i, x = geoCornerPolygon hG.cg T q i := by
  by_cases hadj : adjacent k k'
  · have hk3 := three_le_geoCornerCount hn hG hT q
    rcases adjacent_distinct_cases hkk hadj with hkk' | hkk'
    · subst hkk'
      exact ⟨k + 1, meet_next_eq_corner_of_vertex_off hk3
        (fun i j hij => geoCornerPolygon_tail_off hn hG hT q i j hij) k hxk hxk'⟩
    · subst hkk'
      exact ⟨k' + 1, meet_next_eq_corner_of_vertex_off hk3
        (fun i j hij => geoCornerPolygon_tail_off hn hG hT q i j hij) k' hxk' hxk⟩
  · exfalso
    have hdet := geoCornerPolygon_transverse hn hG hT q k k' hadj ⟨x, hxk, hxk'⟩
    rw [hk, hk', gu2_det_smul_smul, gu2_det_self, mul_zero] at hdet
    exact hdet rfl

/-- **A15, vertex clause, as a helper** (used by both `G11_cfg_clear_frontier`, which precedes the
leaf in the file, and `G11_cfg_clear_vertex`): a corner of `X` is a vertex of `P` (off the triangle by
`gu2_clear`) or the double point of a selected crossing, which has an edge outside `{e, f, g}` (it is
not a triangle crossing, those being retained) and so is off the closed triangle (`gu2_clear_closed`). -/
theorem gu2_cfg_clear_vertex (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hX : ExactTriangleVisitOrders P P' e f g hs) :
    ∀ i : ZMod (geoCornerCount hG.cg T q), geoCornerPolygon hG.cg T q i ∉
      G11_triangle (geoCornerPolygon hG.cg T q) (G11_cfg_hmp hn hG hT q hcef htri)
        (G11_cfg_hmq hn hG hs hT q hcef hceg htri hX) (G11_cfg_hpq hn hG hs hT q hcef hceg htri hX) := by
  intro i hi
  obtain ⟨-, hcfg⟩ := gu2_hcfg_of_hpq hn hG hT q hcef hceg htri (G11_cfg_hpq hn hG hs hT q hcef hceg htri hX)
  have hΔ : G11_triangle (geoCornerPolygon hG.cg T q) (G11_cfg_hmp hn hG hT q hcef htri)
      (G11_cfg_hmq hn hG hs hT q hcef hceg htri hX) (G11_cfg_hpq hn hG hs hT q hcef hceg htri hX) =
      convexHull ℝ {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)} := by
    unfold G11_triangle
    rw [gu2_xmp_eq hn hG hT q hcef htri, gu2_xmq_eq hn hG hT q hcef hceg htri,
      gu2_xpq_eq hn hG hT q hcef hceg hcfg htri]
  rw [hΔ] at hi
  have hcl := gu2_clear hG hs hef heg hfg hcef hceg hcfg hX
  have hcorner := isTrueCorner_geoCornerMark hG.cg T q i
  rw [geoCornerPolygon_apply] at hi
  rcases hmark : geoCornerMark hG.cg T q i with j | v
  · rw [hmark, geoMarkPosition_evaluation_vertex] at hi
    exact hcl.2 j hi
  · rw [hmark, geoMarkPosition_evaluation_visit] at hi
    rw [hmark, isTrueCorner_visit] at hcorner
    have hnot : v.1 ∉ triangleCrossings P e f g := fun hmem =>
      ((mem_geoCarrierCrossings hG.cg T q v.1).mp (htri hmem)).1 hcorner
    rw [F1.mem_triangleCrossings, visit_crossing_val_eq_pair v] at hnot
    have hfor : (v.2.val ≠ e ∧ v.2.val ≠ f ∧ v.2.val ≠ g) ∨
        ((visitTwin v).2.val ≠ e ∧ (visitTwin v).2.val ≠ f ∧ (visitTwin v).2.val ≠ g) := by
      by_contra hcon
      apply hnot
      apply gu2_pair_mem_triangleSupports (visitTwin_edge_ne v).symm
      · by_contra ha
        exact hcon (Or.inl ⟨fun h => ha (Or.inl h), fun h => ha (Or.inr (Or.inl h)),
          fun h => ha (Or.inr (Or.inr h))⟩)
      · by_contra hb
        exact hcon (Or.inr ⟨fun h => hb (Or.inl h), fun h => hb (Or.inr (Or.inl h)),
          fun h => hb (Or.inr (Or.inr h))⟩)
    have hclosed := gu2_clear_closed hG hs hef heg hfg hcef hceg hcfg hX
    rcases hfor with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact hclosed _ h1 h2 h3 _ (crossingPoint_mem v.1 _ v.2.property) hi
    · exact hclosed _ h1 h2 h3 _ (crossingPoint_mem v.1 _ (visitTwin v).2.property) hi

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
  intro h hhm hhp hhq x hx hxF
  obtain ⟨-, hcfg⟩ := gu2_hcfg_of_hpq hn hG hT q hcef hceg htri (G11_cfg_hpq hn hG hs hT q hcef hceg htri hX)
  have hΔ : G11_triangle (geoCornerPolygon hG.cg T q) (G11_cfg_hmp hn hG hT q hcef htri)
      (G11_cfg_hmq hn hG hs hT q hcef hceg htri hX) (G11_cfg_hpq hn hG hs hT q hcef hceg htri hX) =
      convexHull ℝ {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)} := by
    unfold G11_triangle
    rw [gu2_xmp_eq hn hG hT q hcef htri, gu2_xmq_eq hn hG hT q hcef hceg htri,
      gu2_xpq_eq hn hG hT q hcef hceg hcfg htri]
  have hxΔ' : x ∈ G11_triangle (geoCornerPolygon hG.cg T q) (G11_cfg_hmp hn hG hT q hcef htri)
      (G11_cfg_hmq hn hG hs hT q hcef hceg htri hX) (G11_cfg_hpq hn hG hs hT q hcef hceg htri hX) := by
    have := frontier_subset_closure hxF
    rw [hΔ] at this ⊢
    rwa [(gu2_tri_isClosed _ _ _).closure_eq] at this
  rw [hΔ] at hxF
  have hxΔ : x ∈ convexHull ℝ
      {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)} := by
    rw [← hΔ]; exact hxΔ'
  have hcl := gu2_clear hG hs hef heg hfg hcef hceg hcfg hX
  have hvert := gu2_cfg_clear_vertex hn hG hs hT q hcef hceg htri hef heg hfg hX
  have hx₀ := gu2_edgeSegment_sub hn hG hT q h hx
  obtain ⟨c₀, hc₀, hedge₀⟩ := geoCornerPolygon_edge_smul hn hG.cg hT q h
  have hxmp := gu2_xmp_eq hn hG hT q hcef htri (G11_cfg_hmp hn hG hT q hcef htri)
  have hxmq := gu2_xmq_eq hn hG hT q hcef hceg htri (G11_cfg_hmq hn hG hs hT q hcef hceg htri hX)
  have hxpq := gu2_xpq_eq hn hG hT q hcef hceg hcfg htri (G11_cfg_hpq hn hG hs hT q hcef hceg htri hX)
  by_cases hh₀e : (geoOutSlot hG.cg T (geoCornerMark hG.cg T q h)).1 = e
  · rw [hh₀e] at hx₀ hedge₀
    obtain ⟨t, -, -, hxt⟩ := hx₀
    have hseg := gu2_line_e_mem_segment hG hcef hceg hcfg hxΔ hxt
    obtain ⟨-, c, hc, hedge⟩ :=
      G11_carrierEdge_spec hn hG hT q (G11_vef hcef) (G11_mem_tri_ef hG q hcef htri)
    have hedge' : edge (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) = c • edge P e := hedge
    have hA : crossingPoint (xPair hcef) ∈ edgeSegment (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) :=
      (G11_carrierEdge_spec hn hG hT q (G11_vef hcef) (G11_mem_tri_ef hG q hcef htri)).1
    have hB : crossingPoint (xPair hceg) ∈ edgeSegment (geoCornerPolygon hG.cg T q) (G11_mE hn hG hT q hcef htri) := by
      rw [← hxmq]; exact crossingPoint_mem _ _ (mem_pair_left _ _)
    obtain ⟨i, hi⟩ := gu2_parallel_meet_vertex hn hG hT q hhm hedge₀ hedge' hx
      (gu2_edgeSegment_convex hA hB hseg)
    exact hvert i (hi ▸ hxΔ')
  by_cases hh₀f : (geoOutSlot hG.cg T (geoCornerMark hG.cg T q h)).1 = f
  · rw [hh₀f] at hx₀ hedge₀
    obtain ⟨t, -, -, hxt⟩ := hx₀
    have hseg := gu2_line_f_mem_segment hG hcef hceg hcfg hxΔ hxt
    obtain ⟨-, c, hc, hedge⟩ :=
      G11_carrierEdge_spec hn hG hT q (G11_vfe hcef) (G11_mem_tri_ef hG q hcef htri)
    have hedge' : edge (geoCornerPolygon hG.cg T q) (G11_pE hn hG hT q hcef htri) = c • edge P f := hedge
    have hA : crossingPoint (xPair hcef) ∈ edgeSegment (geoCornerPolygon hG.cg T q) (G11_pE hn hG hT q hcef htri) :=
      (G11_carrierEdge_spec hn hG hT q (G11_vfe hcef) (G11_mem_tri_ef hG q hcef htri)).1
    have hC : crossingPoint (xPair hcfg) ∈ edgeSegment (geoCornerPolygon hG.cg T q) (G11_pE hn hG hT q hcef htri) := by
      rw [← hxpq]; exact crossingPoint_mem _ _ (mem_pair_left _ _)
    obtain ⟨i, hi⟩ := gu2_parallel_meet_vertex hn hG hT q hhp hedge₀ hedge' hx
      (gu2_edgeSegment_convex hA hC hseg)
    exact hvert i (hi ▸ hxΔ')
  by_cases hh₀g : (geoOutSlot hG.cg T (geoCornerMark hG.cg T q h)).1 = g
  · rw [hh₀g] at hx₀ hedge₀
    obtain ⟨t, -, -, hxt⟩ := hx₀
    have hseg := gu2_line_g_mem_segment hG hcef hceg hcfg hxΔ hxt
    obtain ⟨-, c, hc, hedge⟩ :=
      G11_carrierEdge_spec hn hG hT q (G11_vge hceg) (G11_mem_tri_eg hG q hceg htri)
    have hedge' : edge (geoCornerPolygon hG.cg T q) (G11_qE hn hG hT q hceg htri) = c • edge P g := hedge
    have hB : crossingPoint (xPair hceg) ∈ edgeSegment (geoCornerPolygon hG.cg T q) (G11_qE hn hG hT q hceg htri) := by
      rw [← hxmq]; exact crossingPoint_mem _ _ (mem_pair_right _ _)
    have hC : crossingPoint (xPair hcfg) ∈ edgeSegment (geoCornerPolygon hG.cg T q) (G11_qE hn hG hT q hceg htri) := by
      rw [← hxpq]; exact crossingPoint_mem _ _ (mem_pair_right _ _)
    obtain ⟨i, hi⟩ := gu2_parallel_meet_vertex hn hG hT q hhq hedge₀ hedge' hx
      (gu2_edgeSegment_convex hB hC hseg)
    exact hvert i (hi ▸ hxΔ')
  exact hcl.1 _ hh₀e hh₀f hh₀g x hx₀ hxF

theorem G11_cfg_clear_vertex (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hX : ExactTriangleVisitOrders P P' e f g hs) :
    ∀ i : ZMod (geoCornerCount hG.cg T q), geoCornerPolygon hG.cg T q i ∉
      G11_triangle (geoCornerPolygon hG.cg T q) (G11_cfg_hmp hn hG hT q hcef htri)
        (G11_cfg_hmq hn hG hs hT q hcef hceg htri hX) (G11_cfg_hpq hn hG hs hT q hcef hceg htri hX) := by
  exact gu2_cfg_clear_vertex hn hG hs hT q hcef hceg htri hef heg hfg hX

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
  refine EXT_homfly_wall hn hG hG' hs hT hT' q q' hcarr ?_ ?_
  · intro v w _ _
    refine AV_key_lt_of_gauss hG.cg hG'.cg hs hef heg hfg hX v w ?_
    rintro ⟨hv, hw, hne, -⟩
    exact hne (Finset.card_le_one.mp hcard _ hv _ hw)
  · intro v _
    exact hdet _ _ (by rw [← visit_crossing_val_eq_pair v]; exact v.1.property)

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

/-- a support of the triangle that is not a crossing bounds the triangle by two crossings -/
theorem gu2_card_le_two {P : LabelledTuple n} (e f g : ZMod n) {s₀ : Finset (ZMod n)}
    (hs₀ : s₀ ∈ triangleSupports e f g) (hn₀ : ¬ IsCrossing P s₀) :
    (triangleCrossings P e f g).card ≤ 2 := by
  classical
  have hle : (triangleCrossings P e f g).card ≤ ((triangleSupports e f g).erase s₀).card := by
    refine Finset.card_le_card_of_injOn (fun x : Crossing P => x.val) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_erase]
      refine ⟨fun h => hn₀ (h ▸ x.property), ?_⟩
      exact (F1.mem_triangleCrossings e f g x).mp hx
    · intro x _ y _ h
      exact Subtype.ext h
  refine hle.trans ?_
  rw [Finset.card_erase_of_mem hs₀]
  have := Finset.card_le_three (a := ({e, f} : Finset (ZMod n))) (b := {e, g}) (c := {f, g})
  unfold triangleSupports
  omega

/-- **Leaf X3 (counting).** The three pairs are crossings iff the triangle has three members; the card is
`≤ 1`, `= 2` or `= 3`. -/
theorem G11_card_cases {P : LabelledTuple n} (e f g : ZMod n) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    (triangleCrossings P e f g).card ≤ 1 ∨ (triangleCrossings P e f g).card = 2 ∨
      (IsCrossing P {e, f} ∧ IsCrossing P {e, g} ∧ IsCrossing P {f, g}) := by
  by_cases h : IsCrossing P {e, f} ∧ IsCrossing P {e, g} ∧ IsCrossing P {f, g}
  · exact Or.inr (Or.inr h)
  · have key : ∃ s₀ ∈ triangleSupports e f g, ¬ IsCrossing P s₀ := by
      by_contra hall
      push Not at hall
      exact h ⟨hall _ (by simp [triangleSupports]), hall _ (by simp [triangleSupports]),
        hall _ (by simp [triangleSupports])⟩
    obtain ⟨s₀, hs₀, hns₀⟩ := key
    have hle := gu2_card_le_two (P := P) e f g hs₀ hns₀
    omega

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
