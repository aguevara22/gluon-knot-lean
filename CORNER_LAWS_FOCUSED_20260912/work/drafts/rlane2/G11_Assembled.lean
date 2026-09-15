import RProof.X1Rows3
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import SM.CS3

/-! # G11 — HOMFLY invariance of the distinguished carrier's grouped diagram across the RIII wall

Skeleton written 2026-09-14 by the G11 architect (R lane, row 173 follow-up) on Mark's RunPod home pod;
assembled the same day from the six unit files `G11_U1`–`G11_U6` (`work/drafts/rlane2/G11_ASSEMBLY_REPORT.md`,
built by `G11_assemble.py`). Plan: `work/drafts/rlane2/G11_PLAN.md`. This file `import RProof.X1Rows3` (the
accepted wave-3 module; plus `SM.CS3` and two Mathlib affine-basis files) and contains ONLY the new material,
all `G11_`-prefixed (namespace `RProof`; the unit helpers are `gu1_`–`gu6_`-prefixed). Every leaf is proved;
`GT_G11_strong_proof` and the row theorem `RProof.generic_transport` are proved from the leaves with no axiom
beyond those of the accepted sibling rows (`propext`, `Classical.choice`, `Quot.sound`, `SM.lit_homfly`,
`SM.lp_lm`, `SM.lp_lm_uniqueness`). Two skeleton leaves (`G11_clear`, `G11_cfg_hpq`) had section hypotheses
missing from their statements (`hG`; `hfg hcfg`) and are stated with `include … in`; see the assembly report.

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
RIII route and re-derive the row `generic_transport` from it (copying the accepted 60-line assembly). The
literal `GT_G11` would additionally need the two branch cases `≤ 1` triangle crossing (a plain record
isomorphism, proved below as `G11_le_one_crossing`) and exactly two triangle crossings (contradictory by
Gauss parity, which is NOT in the library); that branch is not on the row's path and is omitted here. -/

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

/-! ### U3 helpers (Block A) — label arithmetic of the subdivision, the off-edge facts, and the
`appendVertex` chain `X ≅ shift (m+1) X → +p_in → +m₀ → +p_out ≅ X₀` -/

/-- Adjacency of two natural labels below `N`, read in `ZMod N`, as a statement about the naturals. -/
theorem gu3_adjacent_natCast_iff {N : ℕ} [NeZero N] {a b : ℕ} (ha : a < N) (hb : b < N) :
    adjacent (a : ZMod N) (b : ZMod N) ↔
      (b + 1 = a ∨ (b + 1 = N ∧ a = 0)) ∨ a = b ∨ (a + 1 = b ∨ (a + 1 = N ∧ b = 0)) := by
  have key : ∀ x y : ℕ, x < N → y ≤ N →
      (((y : ℕ) : ZMod N) = (x : ZMod N) ↔ (y = x ∨ (y = N ∧ x = 0))) := by
    intro x y hx hy
    rcases hy.lt_or_eq with hy | hy
    · rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hx]
      constructor
      · exact fun h => Or.inl h
      · rintro (h | ⟨h, -⟩)
        · exact h
        · omega
    · subst hy
      rw [ZMod.natCast_self]
      constructor
      · intro h
        right
        refine ⟨rfl, ?_⟩
        have h' := congrArg ZMod.val h
        rw [ZMod.val_zero, ZMod.val_natCast_of_lt hx] at h'
        exact h'.symm
      · rintro (h | ⟨-, h⟩)
        · omega
        · rw [h, Nat.cast_zero]
  have h1 : ((b : ZMod N) - a = -1) ↔ ((b + 1 : ℕ) : ZMod N) = (a : ZMod N) := by
    rw [Nat.cast_add, Nat.cast_one]
    constructor <;> intro h <;> linear_combination h
  have h2 : ((b : ZMod N) - a = 0) ↔ (b : ZMod N) = (a : ZMod N) := sub_eq_zero
  have h3 : ((b : ZMod N) - a = 1) ↔ ((a + 1 : ℕ) : ZMod N) = (b : ZMod N) := by
    rw [Nat.cast_add, Nat.cast_one]
    constructor <;> intro h <;> linear_combination -h
  have h2' : ((b : ZMod N) = (a : ZMod N)) ↔ a = b := by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ha]
    exact eq_comm
  unfold adjacent
  rw [h1, h2, h3, key a (b + 1) ha (by omega), key b (a + 1) hb (by omega), h2']

theorem gu3_remote_natCast_iff {N : ℕ} [NeZero N] {a b : ℕ} (ha : a < N) (hb : b < N) :
    remote (a : ZMod N) (b : ZMod N) ↔
      ¬ ((b + 1 = a ∨ (b + 1 = N ∧ a = 0)) ∨ a = b ∨ (a + 1 = b ∨ (a + 1 = N ∧ b = 0))) :=
  not_congr (gu3_adjacent_natCast_iff ha hb)

/-- the value of an old label read in `X₀` -/
theorem gu3_lab_val (m i : ZMod k) :
    (G11_lab m i).val = if i.val ≤ m.val then i.val else i.val + 3 := by
  have hi := i.val_lt
  unfold G11_lab
  split_ifs with h
  · exact ZMod.val_natCast_of_lt (by omega)
  · exact ZMod.val_natCast_of_lt (by omega)

/-- remoteness of two old labels is kept in `X₀` -/
theorem gu3_remote_lab {m i j : ZMod k} (h : remote i j) : remote (G11_lab m i) (G11_lab m j) := by
  have hij := (gu3_remote_natCast_iff i.val_lt j.val_lt).mp
    (by rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])
  have hik := i.val_lt
  have hjk := j.val_lt
  have hmk := m.val_lt
  rw [← ZMod.natCast_zmod_val (G11_lab m i), ← ZMod.natCast_zmod_val (G11_lab m j),
    gu3_remote_natCast_iff (ZMod.val_lt _) (ZMod.val_lt _), gu3_lab_val, gu3_lab_val]
  split_ifs <;> first | omega | (simp only [and_false, or_false]; omega)

omit [NeZero k] in
/-- `X₀` read at a natural label. -/
theorem gu3_subdiv_natCast (X : LabelledTuple k) (m : ZMod k) (t₁ t₂ t₃ : ℝ) (a : ℕ)
    (ha : a < k + 3) :
    G11_subdiv X m t₁ t₂ t₃ (a : ZMod (k + 3)) =
      if a ≤ m.val then X (a : ZMod k)
      else if a = m.val + 1 then edgePoint X m t₁
      else if a = m.val + 2 then edgePoint X m t₂
      else if a = m.val + 3 then edgePoint X m t₃
      else X ((a - 3 : ℕ) : ZMod k) := by
  simp only [G11_subdiv, ZMod.val_natCast_of_lt ha]

theorem gu3_subdiv_lab (X : LabelledTuple k) (m : ZMod k) (t₁ t₂ t₃ : ℝ) (i : ZMod k) :
    G11_subdiv X m t₁ t₂ t₃ (G11_lab m i) = X i := by
  have hi := i.val_lt
  by_cases h : i.val ≤ m.val
  · rw [G11_lab, ite_eq_left h, gu3_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_left h,
      ZMod.natCast_zmod_val]
  · rw [G11_lab, ite_eq_right h, gu3_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel,
      ZMod.natCast_zmod_val]

theorem gu3_subdiv_lab_succ (X : LabelledTuple k) (m : ZMod k) (t₁ t₂ t₃ : ℝ) {i : ZMod k}
    (hi : i ≠ m) : G11_subdiv X m t₁ t₂ t₃ (G11_lab m i + 1) = X (i + 1) := by
  have hik := i.val_lt
  have hmk := m.val_lt
  have him : i.val ≠ m.val := fun h => hi (ZMod.val_injective k h)
  have hcast : i + 1 = ((i.val + 1 : ℕ) : ZMod k) := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  by_cases h : i.val ≤ m.val
  · rw [G11_lab, ite_eq_left h, ← Nat.cast_add_one, gu3_subdiv_natCast X m t₁ t₂ t₃ _ (by omega),
      ite_eq_left (by omega), hcast]
  · rw [G11_lab, ite_eq_right h, ← Nat.cast_add_one]
    by_cases hk : i.val + 1 < k
    · rw [gu3_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), hcast]
      congr 2
    · rw [show i.val + 3 + 1 = k + 3 by omega, ZMod.natCast_self, hcast,
        show i.val + 1 = k by omega, ZMod.natCast_self,
        show (0 : ZMod (k + 3)) = ((0 : ℕ) : ZMod (k + 3)) from Nat.cast_zero.symm,
        gu3_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_left (Nat.zero_le _), Nat.cast_zero]

theorem gu3_subdiv_mA (X : LabelledTuple k) (m : ZMod k) (t₁ t₂ t₃ : ℝ) :
    G11_subdiv X m t₁ t₂ t₃ (m.val : ZMod (k + 3)) = X m := by
  have := m.val_lt
  rw [gu3_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_left le_rfl, ZMod.natCast_zmod_val]

theorem gu3_subdiv_mB (X : LabelledTuple k) (m : ZMod k) (t₁ t₂ t₃ : ℝ) :
    G11_subdiv X m t₁ t₂ t₃ ((m.val + 1 : ℕ) : ZMod (k + 3)) = edgePoint X m t₁ := by
  have := m.val_lt
  rw [gu3_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_right (by omega), ite_eq_left rfl]

theorem gu3_subdiv_mC (X : LabelledTuple k) (m : ZMod k) (t₁ t₂ t₃ : ℝ) :
    G11_subdiv X m t₁ t₂ t₃ ((m.val + 2 : ℕ) : ZMod (k + 3)) = edgePoint X m t₂ := by
  have := m.val_lt
  rw [gu3_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left rfl]

theorem gu3_subdiv_mD (X : LabelledTuple k) (m : ZMod k) (t₁ t₂ t₃ : ℝ) :
    G11_subdiv X m t₁ t₂ t₃ ((m.val + 3 : ℕ) : ZMod (k + 3)) = edgePoint X m t₃ := by
  have := m.val_lt
  rw [gu3_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left rfl]

theorem gu3_subdiv_mD_succ (X : LabelledTuple k) (m : ZMod k) (t₁ t₂ t₃ : ℝ) :
    G11_subdiv X m t₁ t₂ t₃ (((m.val + 3 : ℕ) : ZMod (k + 3)) + 1) = X (m + 1) := by
  have hmk := m.val_lt
  have hcast : m + 1 = ((m.val + 1 : ℕ) : ZMod k) := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  rw [← Nat.cast_add_one]
  by_cases hk : m.val + 1 < k
  · rw [gu3_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), hcast]
    congr 2
  · rw [show m.val + 3 + 1 = k + 3 by omega, ZMod.natCast_self, hcast,
      show m.val + 1 = k by omega, ZMod.natCast_self,
      show (0 : ZMod (k + 3)) = ((0 : ℕ) : ZMod (k + 3)) from Nat.cast_zero.symm,
      gu3_subdiv_natCast X m t₁ t₂ t₃ _ (by omega), ite_eq_left (Nat.zero_le _), Nat.cast_zero]

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

theorem gu3_edge_ne_zero (C : G11_Config k) (i : ZMod k) : edge C.X i ≠ 0 :=
  ((regular_iff_edges C.X).mp (C.gen.regular 0) i).1

theorem gu3_geometry (C : G11_Config k) : CrossingGeometry C.X :=
  crossingGeometry_of_single_generic C.hk C.gen

/-- a common point of the two edges of a crossing is its double point -/
theorem gu3_common_eq (C : G11_Config k) {i j : ZMod k} (h : IsCrossing C.X {i, j}) {x : Plane}
    (hi : x ∈ edgeSegment C.X i) (hj : x ∈ edgeSegment C.X j) : x = crossingPoint (xPair h) := by
  apply crossingPoint_unique_of_geometry (gu3_geometry C) (xPair h) x
  intro l hl
  rcases Finset.mem_insert.mp hl with rfl | hl
  · exact hi
  · rw [Finset.mem_singleton.mp hl]
    exact hj

theorem gu3_param_interior (C : G11_Config k) {i j : ZMod k} (h : IsCrossing C.X {i, j}) :
    0 < crossingParameter (xPair h) i (mem_pair_left i j) ∧
      crossingParameter (xPair h) i (mem_pair_left i j) < 1 :=
  crossingParameter_interior_of_geometry (gu3_geometry C) (xPair h) i (mem_pair_left i j)

omit [NeZero k] in
theorem gu3_remote_of_isCrossing {X : LabelledTuple k} {i j : ZMod k} (h : IsCrossing X {i, j}) :
    remote i j := by
  obtain ⟨a, b, hab, hr, -⟩ := h
  have hne : a ≠ b := fun e => hr (adjacent_of_eq e)
  have hi : i ∈ ({a, b} : Finset (ZMod k)) := hab ▸ mem_pair_left i j
  have hj : j ∈ ({a, b} : Finset (ZMod k)) := hab ▸ mem_pair_right i j
  have ha : a ∈ ({i, j} : Finset (ZMod k)) := hab ▸ mem_pair_left a b
  have hb : b ∈ ({i, j} : Finset (ZMod k)) := hab ▸ mem_pair_right a b
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj ha hb
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exfalso
    rcases hb with h | h <;> exact hne h.symm
  · exact hr
  · exact remote_symm hr
  · exfalso
    rcases ha with h | h <;> exact hne h

theorem gu3_p_ne_m (C : G11_Config k) : C.p ≠ C.m :=
  fun h => gu3_remote_of_isCrossing C.hmp (adjacent_of_eq h.symm)
theorem gu3_q_ne_m (C : G11_Config k) : C.q ≠ C.m :=
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
noncomputable def gu3_Y (C : G11_Config k) : LabelledTuple k := shift (C.m + 1) C.X

theorem gu3_Y_generic (C : G11_Config k) : (Shadow.single ⟨k, C.hk, gu3_Y C⟩).Generic :=
  single_generic_shift C.hk C.X (C.m + 1) C.gen

theorem gu3_Y_neg_one (C : G11_Config k) : gu3_Y C (-1) = C.X C.m := by
  show C.X (-1 + (C.m + 1)) = C.X C.m
  congr 1
  ring

theorem gu3_edge_Y (C : G11_Config k) : edge (gu3_Y C) (-1) = edge C.X C.m := by
  rw [gu3_Y, edge_shift]
  congr 1
  ring

theorem gu3_edgePoint_Y (C : G11_Config k) (t : ℝ) :
    edgePoint (gu3_Y C) (-1) t = edgePoint C.X C.m t := by
  rw [gu3_Y, edgePoint_shift]
  congr 1
  ring

theorem gu3_edgeSegment_Y (C : G11_Config k) (e : ZMod k) :
    edgeSegment (gu3_Y C) e = edgeSegment C.X (e + (C.m + 1)) :=
  edgeSegment_shift _ _ _

/-- the rescaled parameters of the second and third flat vertices -/
noncomputable def gu3_u₂ (π : G11_Params C) : ℝ := (π.t₂ - π.t₁) / (1 - π.t₁)
noncomputable def gu3_u₃ (π : G11_Params C) : ℝ := (π.t₃ - π.t₂) / (1 - π.t₂)

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
noncomputable def gu3_Y₁ (π : G11_Params C) : LabelledTuple (k + 1) := appendVertex (gu3_Y C) π.t₁
noncomputable def gu3_Y₂ (π : G11_Params C) : LabelledTuple (k + 2) := appendVertex π.gu3_Y₁ π.gu3_u₂
noncomputable def gu3_Y₃ (π : G11_Params C) : LabelledTuple (k + 3) := appendVertex π.gu3_Y₂ π.gu3_u₃

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

theorem gu3_cast_add_m (C : G11_Config k) (a : ℕ) :
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

theorem gu3_reparam₁ (C : G11_Config k) :
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

theorem gu3_homfly_of_reparam {D D' : Diagram} (h : Reparam D D') : homfly D = homfly D' :=
  homfly_planar (PlanarIsotopic.of_reparam h)

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

/-- points of the parameter circles are determined by strand and parameter -/
theorem gu3_pt_ext {Γ : Shadow} {q q' : Γ.Pt}
    (hst : (⟨q.1, q.2.1⟩ : Γ.Strand) = ⟨q'.1, q'.2.1⟩) (hpar : q.2.2.val = q'.2.2.val) : q = q' := by
  obtain ⟨i, a, τ⟩ := q
  obtain ⟨j, b, σ⟩ := q'
  obtain ⟨rfl, hab⟩ := Sigma.mk.inj_iff.mp hst
  have hab' := eq_of_heq hab
  subst hab'
  simp only at hpar
  rw [Subtype.ext hpar]

/-- A traversal point tracing the double point of `x` is the traversal point of one of the two
occurrences of `x` (no triple points; at a tail both strands of `x` would be incident to it, hence
adjacent). -/
theorem gu3_pt_of_eval_eq_crossingPoint (D : Diagram) (x : D.Γ.Crossing) (q : D.Γ.Pt)
    (hq : D.Γ.eval q = D.Γ.crossingPoint x) :
    q = D.visitPt (D.overVisit x) ∨ q = D.visitPt (D.underVisit x) := by
  obtain ⟨i, a, τ, hτ0, hτ1⟩ := q
  have hq' : edgePoint (D.Γ.comp i).P a τ = D.Γ.crossingPoint x := hq
  have hover := D.generic.crossingPoint_mem_interior x (D.over_mem x)
  have hunder := D.generic.crossingPoint_mem_interior x (D.under_mem x)
  have key : ∀ (s : D.Γ.Strand) (hs : s ∈ x.val), (⟨i, a⟩ : D.Γ.Strand) = s →
      (⟨i, (a, ⟨τ, hτ0, hτ1⟩)⟩ : D.Γ.Pt) = D.visitPt ⟨x, ⟨s, hs⟩⟩ := by
    rintro s hs rfl
    have hspec := (D.crossingParam_spec x hs).2.2
    rw [← hq'] at hspec
    have hedge : edge (D.Γ.comp i).P a ≠ 0 := ((regular_iff_edges _).mp (D.generic.regular i) a).1
    have hpar := edgePoint_injective hedge hspec
    subst hpar
    rfl
  have hs : (⟨i, a⟩ : D.Γ.Strand) = D.overStrand x ∨ (⟨i, a⟩ : D.Γ.Strand) = D.underStrand x := by
    by_contra hne
    rw [not_or] at hne
    rcases hτ0.lt_or_eq with h0 | h0
    · exact D.generic.no_triple ⟨⟨i, a⟩, D.overStrand x, D.underStrand x, hne.1, D.over_ne_under x,
        hne.2, D.Γ.crossingPoint x, ⟨⟨τ, h0, hτ1, hq'.symm⟩, hover⟩, hunder⟩
    · have htail : D.Γ.tail ⟨i, a⟩ = D.Γ.crossingPoint x := by
        rw [← hq']
        show (D.Γ.comp i).P a = edgePoint (D.Γ.comp i).P a τ
        rw [← h0, edgePoint_zero]
      have hinc : ∀ t : D.Γ.Strand, t ∈ x.val → D.Γ.IncidentTail ⟨i, a⟩ t := by
        intro t ht
        by_contra hn
        exact D.generic.tail_off ⟨i, a⟩ t hn (by rw [htail]; exact D.Γ.crossingPoint_mem x ht)
      have hlab : ∀ t : D.Γ.Strand, t ∈ x.val → (⟨i, a⟩ : D.Γ.Strand) ≠ t → t = ⟨i, a - 1⟩ := by
        intro t ht hne'
        obtain ⟨j, b, c, h1, h2, hinc'⟩ := hinc t ht
        obtain ⟨rfl, hb⟩ := Sigma.mk.inj_iff.mp h1
        have hb' := eq_of_heq hb
        subst hb'
        rcases hinc' with hc | hc
        · rw [h2, hc]
        · exact absurd (h2.trans (by rw [hc])).symm hne'
      exact D.over_ne_under x
        ((hlab _ (D.over_mem x) hne.1).trans (hlab _ (D.under_mem x) hne.2).symm)
  rcases hs with h | h
  · exact Or.inl (key _ (D.over_mem x) h)
  · exact Or.inr (key _ (D.under_mem x) h)

theorem gu3_mapPt_injective {D D' : Diagram} (r : ReparamData D D') :
    Function.Injective r.mapPt := by
  rintro ⟨i, p⟩ ⟨j, q⟩ h
  simp only [ReparamData.mapPt] at h
  obtain ⟨hij, hpq⟩ := Sigma.mk.inj_iff.mp h
  have hij' : i = j := r.e.injective hij
  subst hij'
  rw [(r.φ i).injective (eq_of_heq hpq)]

/-- the under occurrence follows the over occurrence under a reparametrization -/
theorem gu3_mapPt_under {D D' : Diagram} (r : ReparamData D D') (x : D.Γ.Crossing)
    (x' : D'.Γ.Crossing) (h : r.mapPt (D.visitPt (D.overVisit x)) = D'.visitPt (D'.overVisit x')) :
    r.mapPt (D.visitPt (D.underVisit x)) = D'.visitPt (D'.underVisit x') := by
  have e1 : D'.Γ.eval (D'.visitPt (D'.overVisit x')) = D'.Γ.crossingPoint x' := D'.eval_visitPt _
  have e2 : D.Γ.eval (D.visitPt (D.overVisit x)) = D.Γ.crossingPoint x := D.eval_visitPt _
  have e3 : D.Γ.eval (D.visitPt (D.underVisit x)) = D.Γ.crossingPoint x := D.eval_visitPt _
  have hcp : D'.Γ.crossingPoint x' = D.Γ.crossingPoint x := by
    rw [← e1, ← h, r.eval_mapPt, e2]
  have heval : D'.Γ.eval (r.mapPt (D.visitPt (D.underVisit x))) = D'.Γ.crossingPoint x' := by
    rw [r.eval_mapPt, e3, hcp]
  rcases gu3_pt_of_eval_eq_crossingPoint D' x' _ heval with h1 | h1
  · exfalso
    rw [← h] at h1
    exact D.overVisit_ne_underVisit x (D.visitPt_injective (gu3_mapPt_injective r h1)).symm
  · exact h1

/-- **the occurrence bijection of a reparametrization**: `visitPt (Ψ v) = mapPt (visitPt v)`. -/
theorem gu3_exists_visitEquiv {D D' : Diagram} (r : ReparamData D D') :
    ∃ Ψ : D.Γ.Visit ≃ D'.Γ.Visit, ∀ v, D'.visitPt (Ψ v) = r.mapPt (D.visitPt v) := by
  classical
  choose x' hx' using r.over_map
  have hx'' : ∀ x, r.mapPt (D.visitPt (D.overVisit x)) = D'.visitPt (D'.overVisit (x' x)) := hx'
  let f : D.Γ.Visit → D'.Γ.Visit := fun v =>
    if D.overBit v = true then D'.overVisit (x' v.1) else D'.underVisit (x' v.1)
  have hf : ∀ v, D'.visitPt (f v) = r.mapPt (D.visitPt v) := by
    intro v
    rcases D.visit_eq_over_or_under v with hv | hv
    · have hb : D.overBit v = true := by rw [hv]; exact D.overBit_overVisit _
      have hfv : f v = D'.overVisit (x' v.1) := by simp only [f, hb, ite_true]
      rw [hfv]
      conv_rhs => rw [hv]
      exact (hx'' v.1).symm
    · have hb : D.overBit v = false := by rw [hv]; exact D.overBit_underVisit _
      have hfv : f v = D'.underVisit (x' v.1) := by simp only [f, hb, Bool.false_eq_true, ite_false]
      rw [hfv]
      conv_rhs => rw [hv]
      exact (gu3_mapPt_under r v.1 (x' v.1) (hx'' v.1)).symm
  have hinj : Function.Injective f := fun v w h =>
    D.visitPt_injective (gu3_mapPt_injective r (by rw [← hf v, ← hf w, h]))
  have hsurj : Function.Surjective f := by
    intro v'
    obtain ⟨x, hx⟩ := r.over_surj v'.1
    have hxx : x' x = v'.1 := by
      have h1 : D'.visitPt (D'.overVisit (x' x)) = D'.visitPt (D'.overVisit v'.1) :=
        (hx'' x).symm.trans hx
      exact congrArg Sigma.fst (D'.visitPt_injective h1)
    rcases D'.visit_eq_over_or_under v' with hv' | hv'
    · refine ⟨D.overVisit x, ?_⟩
      have hfv : f (D.overVisit x) = D'.overVisit (x' x) := by
        simp only [f, D.overBit_overVisit, ite_true, Diagram.overVisit_fst]
      rw [hfv, hxx]
      exact hv'.symm
    · refine ⟨D.underVisit x, ?_⟩
      have hfv : f (D.underVisit x) = D'.underVisit (x' x) := by
        simp only [f, D.overBit_underVisit, Bool.false_eq_true, ite_false, Diagram.underVisit_fst]
      rw [hfv, hxx]
      exact hv'.symm
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

/-- the record-level properties of an occurrence bijection carried through the U3 chain -/
def gu3_IsVisitIso {D D' : Diagram} (Ψ : D.Γ.Visit ≃ D'.Γ.Visit) : Prop :=
  (∀ v, Ψ (D.twin v) = D'.twin (Ψ v)) ∧ (∀ v, D'.overBit (Ψ v) = D.overBit v) ∧
  (∀ u v w, D'.VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔ D.VisitBetween u v w) ∧
  (∀ v, D'.Γ.crossingPoint (Ψ v).1 = D.Γ.crossingPoint v.1)

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

theorem gu3_crossingPoint_of_visitPt {D D' : Diagram} (r : ReparamData D D')
    (Ψ : D.Γ.Visit ≃ D'.Γ.Visit) (hΨ : ∀ v, D'.visitPt (Ψ v) = r.mapPt (D.visitPt v))
    (v : D.Γ.Visit) : D'.Γ.crossingPoint (Ψ v).1 = D.Γ.crossingPoint v.1 := by
  rw [← D'.eval_visitPt, hΨ, r.eval_mapPt, D.eval_visitPt]

/-- two distinct occurrences of one crossing are twins -/
theorem gu3_eq_twin_of_ne (D : Diagram) {v w : D.Γ.Visit} (h1 : v.1 = w.1) (h2 : v ≠ w) :
    w = D.twin v := by
  obtain ⟨x, s, hs⟩ := v
  obtain ⟨y, t, ht⟩ := w
  have hxy : x = y := h1
  subst hxy
  have hts : t ≠ s := fun e => h2 (by subst e; rfl)
  have := D.Γ.eq_other_of_mem_of_ne x hs ht hts
  show (⟨x, ⟨t, ht⟩⟩ : D.Γ.Visit) = ⟨x, ⟨D.Γ.other x hs, D.Γ.other_mem x hs⟩⟩
  congr 1
  exact Subtype.ext this

theorem gu3_twin_of_visitPt {D D' : Diagram} (r : ReparamData D D') (Ψ : D.Γ.Visit ≃ D'.Γ.Visit)
    (hΨ : ∀ v, D'.visitPt (Ψ v) = r.mapPt (D.visitPt v)) (v : D.Γ.Visit) :
    Ψ (D.twin v) = D'.twin (Ψ v) := by
  have hcp : (Ψ v).1 = (Ψ (D.twin v)).1 := by
    apply D'.generic.crossingPoint_injective
    rw [gu3_crossingPoint_of_visitPt r Ψ hΨ, gu3_crossingPoint_of_visitPt r Ψ hΨ, D.twin_fst]
  have hne : Ψ v ≠ Ψ (D.twin v) := fun h => D.twin_ne v (Ψ.injective h).symm
  exact gu3_eq_twin_of_ne D' hcp hne

theorem gu3_overBit_of_visitPt {D D' : Diagram} (r : ReparamData D D') (Ψ : D.Γ.Visit ≃ D'.Γ.Visit)
    (hΨ : ∀ v, D'.visitPt (Ψ v) = r.mapPt (D.visitPt v)) (v : D.Γ.Visit) :
    D'.overBit (Ψ v) = D.overBit v := by
  obtain ⟨x', hx'⟩ := r.over_map v.1
  have hx'' : r.mapPt (D.visitPt (D.overVisit v.1)) = D'.visitPt (D'.overVisit x') := hx'
  rcases D.visit_eq_over_or_under v with hv | hv
  · have : Ψ v = D'.overVisit x' := by
      apply D'.visitPt_injective
      rw [hΨ, ← hx'']
      conv_lhs => rw [hv]
    rw [this, hv, D'.overBit_overVisit, D.overBit_overVisit]
  · have : Ψ v = D'.underVisit x' := by
      apply D'.visitPt_injective
      rw [hΨ, ← gu3_mapPt_under r v.1 x' hx'']
      conv_lhs => rw [hv]
    rw [this, hv, D'.overBit_underVisit, D.overBit_underVisit]

theorem gu3_cyc_of_not {a b c : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h : ¬ cycBetween a b c) : cycBetween a c b := by
  unfold cycBetween at h ⊢
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
    rcases lt_or_gt_of_ne hac with h3 | h3
  · exact absurd (Or.inl ⟨h1, h2⟩) h
  · exact absurd (Or.inl ⟨h1, h2⟩) h
  · exact Or.inl ⟨h3, h2⟩
  · exact absurd (Or.inr (Or.inr ⟨h3, h1⟩)) h
  · exact Or.inr (Or.inr ⟨h1, h3⟩)
  · exact absurd (Or.inr (Or.inl ⟨h2, h3⟩)) h
  · exfalso
    linarith
  · exact Or.inr (Or.inl ⟨h2, h1⟩)

/-- a bijection of parameter circles preserving the strict cyclic order preserves it both ways -/
theorem gu3_traversalBetween_iff {n n' : ℕ} [NeZero n] [NeZero n']
    (φ : TraversalPoint n ≃ TraversalPoint n')
    (hφ : ∀ p q r, traversalBetween p q r → traversalBetween (φ p) (φ q) (φ r))
    (p q r : TraversalPoint n) :
    traversalBetween (φ p) (φ q) (φ r) ↔ traversalBetween p q r := by
  refine ⟨fun h => ?_, hφ p q r⟩
  rw [traversalBetween_iff_cycBetween] at h ⊢
  by_contra hn
  rcases eq_or_ne p q with rfl | hpq
  · exact not_cycBetween_self_left _ _ h
  rcases eq_or_ne q r with rfl | hqr
  · exact not_cycBetween_self_mid _ _ h
  rcases eq_or_ne p r with rfl | hpr
  · exact not_cycBetween_self_right _ _ h
  have h' := hφ p r q ((traversalBetween_iff_cycBetween _ _ _).mpr
    (gu3_cyc_of_not (fun e => hpq (traversalKey_injective e))
      (fun e => hqr (traversalKey_injective e)) (fun e => hpr (traversalKey_injective e)) hn))
  rw [traversalBetween_iff_cycBetween] at h'
  unfold cycBetween at h h'
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases h' with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> linarith

/-- the cyclic order clause, for one-component positive diagrams (all occurrences on component `0`) -/
theorem gu3_visitBetween_of_visitPt (A B : PolyComp) (hA : (Shadow.single A).Generic)
    (hB : (Shadow.single B).Generic)
    (r : ReparamData ((Shadow.single A).positiveDiagram hA) ((Shadow.single B).positiveDiagram hB))
    (Ψ : ((Shadow.single A).positiveDiagram hA).Γ.Visit ≃
      ((Shadow.single B).positiveDiagram hB).Γ.Visit)
    (hΨ : ∀ v, ((Shadow.single B).positiveDiagram hB).visitPt (Ψ v) =
      r.mapPt (((Shadow.single A).positiveDiagram hA).visitPt v))
    (u v w : ((Shadow.single A).positiveDiagram hA).Γ.Visit) :
    ((Shadow.single B).positiveDiagram hB).VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔
      ((Shadow.single A).positiveDiagram hA).VisitBetween u v w := by
  let φ₀ : TraversalPoint A.k ≃ TraversalPoint B.k := r.φ ⟨0, Nat.one_pos⟩
  let P : ((Shadow.single A).positiveDiagram hA).Γ.Visit → TraversalPoint A.k :=
    fun z => (((Shadow.single A).positiveDiagram hA).visitPt z).2
  have hφ : ∀ (i : Fin ((Shadow.single A).positiveDiagram hA).Γ.c) (p : TraversalPoint A.k),
      r.φ i p = φ₀ p := by
    intro i p
    have hi : i = ⟨0, Nat.one_pos⟩ := Fin.ext (Nat.lt_one_iff.mp (i.isLt : i.val < 1))
    subst hi
    rfl
  have e : ∀ z, traversalKey (((Shadow.single B).positiveDiagram hB).visitPt (Ψ z)).2 =
      traversalKey (φ₀ (P z)) := by
    intro z
    rw [hΨ z]
    exact congrArg traversalKey (hφ (((Shadow.single A).positiveDiagram hA).visitPt z).1 (P z))
  have e' : ∀ z, traversalKey (((Shadow.single A).positiveDiagram hA).visitPt z).2 =
      traversalKey (P z) := fun _ => rfl
  show cycBetween (traversalKey (((Shadow.single B).positiveDiagram hB).visitPt (Ψ u)).2)
      (traversalKey (((Shadow.single B).positiveDiagram hB).visitPt (Ψ v)).2)
      (traversalKey (((Shadow.single B).positiveDiagram hB).visitPt (Ψ w)).2) ↔
    cycBetween (traversalKey (((Shadow.single A).positiveDiagram hA).visitPt u).2)
      (traversalKey (((Shadow.single A).positiveDiagram hA).visitPt v).2)
      (traversalKey (((Shadow.single A).positiveDiagram hA).visitPt w).2)
  rw [e u, e v, e w, e' u, e' v, e' w, ← traversalBetween_iff_cycBetween,
    ← traversalBetween_iff_cycBetween]
  exact gu3_traversalBetween_iff φ₀ (fun p q s h => r.between ⟨0, Nat.one_pos⟩ p q s h) _ _ _

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

theorem gu3_other_congr {Γ : Shadow} (x : Γ.Crossing) {s t : Γ.Strand} (h : s = t)
    (hs : s ∈ x.val) (ht : t ∈ x.val) : Γ.other x hs = Γ.other x ht := by
  subst h
  rfl

/-- an occurrence of the positive diagram is over iff its strand makes a positive determinant with
the other strand -/
theorem gu3_isOver_iff_det_pos (A : PolyComp) (hA : (Shadow.single A).Generic)
    (v : (Shadow.single A).Visit) :
    ((Shadow.single A).positiveDiagram hA).isOver v ↔
      0 < det (edge A.P v.2.val.2) (edge A.P ((Shadow.single A).other v.1 v.2.2).2) := by
  set D := (Shadow.single A).positiveDiagram hA with hD
  constructor
  · intro hv
    have hv' : v.2.val = D.overStrand v.1 := hv
    have hpos := (Shadow.single A).positiveDiagram_det_pos hA v.1
    rw [gu3_other_congr v.1 hv'.symm (D.over_mem v.1) v.2.2, ← hv'] at hpos
    exact hpos
  · intro hpos
    by_contra hn
    have hn' : v.2.val ≠ D.overStrand v.1 := hn
    have hover : D.overStrand v.1 = (Shadow.single A).other v.1 v.2.2 :=
      (Shadow.single A).eq_other_of_mem_of_ne v.1 v.2.2 (D.over_mem v.1) (Ne.symm hn')
    have h2 := (Shadow.single A).positiveDiagram_det_pos hA v.1
    rw [gu3_other_congr v.1 hover (D.over_mem v.1) ((Shadow.single A).other_mem v.1 v.2.2),
      (Shadow.single A).other_other v.1 v.2.2, hover] at h2
    have h3 : det (edge A.P ((Shadow.single A).other v.1 v.2.2).2) (edge A.P v.2.val.2) =
        - det (edge A.P v.2.val.2) (edge A.P ((Shadow.single A).other v.1 v.2.2).2) := det_swap _ _
    have h2' : 0 < det (edge A.P ((Shadow.single A).other v.1 v.2.2).2) (edge A.P v.2.val.2) := h2
    linarith

/-- the over bit of the occurrence of the crossing `{i, j}` on its strand `l` -/
theorem gu3_overBit_pair (A : PolyComp) (hA : (Shadow.single A).Generic) {i j l l' : ZMod A.k}
    (hij : IsCrossing A.P {i, j}) (hl : l ∈ ({i, j} : Finset (ZMod A.k)))
    (hl' : l' ∈ ({i, j} : Finset (ZMod A.k))) (hne : l ≠ l') :
    ((Shadow.single A).positiveDiagram hA).overBit
      ((Shadow.singleVisitEquiv A).symm ⟨xPair hij, ⟨l, hl⟩⟩) = true ↔
    0 < det (edge A.P l) (edge A.P l') := by
  set v := (Shadow.singleVisitEquiv A).symm ⟨xPair hij, ⟨l, hl⟩⟩ with hv
  have hv1 : Shadow.singleCrossingEquiv A v.1 = xPair hij := by
    rw [← Shadow.singleVisitEquiv_fst, hv, Equiv.apply_symm_apply]
  have hv2 : Shadow.singleStrandEquiv A v.2.val = l := by
    rw [← Shadow.singleVisitEquiv_snd, hv, Equiv.apply_symm_apply]
  have hv2' : v.2.val = ⟨0, l⟩ := by
    rw [← Shadow.single_strand_eta A v.2.val]
    exact congrArg (fun a => (⟨0, a⟩ : (Shadow.single A).Strand)) hv2
  have hl'mem : (⟨0, l'⟩ : (Shadow.single A).Strand) ∈ v.1.val := by
    rw [← Shadow.mem_singleCrossingEquiv_iff, hv1]
    exact hl'
  have hne' : (⟨0, l'⟩ : (Shadow.single A).Strand) ≠ v.2.val := by
    rw [hv2']
    intro e
    exact hne (eq_of_heq (Sigma.mk.inj_iff.mp e).2).symm
  have hother : (Shadow.single A).other v.1 v.2.2 = ⟨0, l'⟩ :=
    ((Shadow.single A).eq_other_of_mem_of_ne v.1 v.2.2 hl'mem hne').symm
  refine (Diagram.overBit_eq_true_iff _ _).trans ((gu3_isOver_iff_det_pos A hA v).trans ?_)
  rw [hother, hv2']

theorem gu3_bool_eq_of_iff {a b : Bool} (h : (a = true) ↔ (b = true)) : a = b := by
  cases a <;> cases b <;> simp_all

/-- two occurrences of one crossing with the same over bit coincide -/
theorem gu3_visit_ext (D : Diagram) {v w : D.Γ.Visit} (h1 : v.1 = w.1)
    (h2 : D.overBit v = D.overBit w) : v = w := by
  rcases D.visit_eq_over_or_under v with hv | hv <;> rcases D.visit_eq_over_or_under w with hw | hw
  · rw [hv, hw, h1]
  · exfalso
    rw [hv, hw, D.overBit_overVisit, D.overBit_underVisit] at h2
    exact Bool.noConfusion h2
  · exfalso
    rw [hv, hw, D.overBit_underVisit, D.overBit_overVisit] at h2
    exact Bool.noConfusion h2
  · rw [hv, hw, h1]

/-- the double point of an occurrence of a one-component positive diagram -/
theorem gu3_crossingPoint_symm (A : PolyComp) (hA : (Shadow.single A).Generic) (c : Crossing A.P)
    {l : ZMod A.k} (hl : l ∈ c.val) :
    ((Shadow.single A).positiveDiagram hA).Γ.crossingPoint
      ((Shadow.singleVisitEquiv A).symm ⟨c, ⟨l, hl⟩⟩).1 = crossingPoint c := by
  simp only [Shadow.positiveDiagram_Γ]
  rw [Shadow.single_crossingPoint A hA, ← Shadow.singleVisitEquiv_fst, Equiv.apply_symm_apply]

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

/-! ### U3 helpers (Block E) — the triangle `Δ`, its centroid, and the homothetic disc `U` -/

theorem gu3_a_ne_d (C : G11_Config k) :
    crossingPoint (xPair C.hmp) ≠ crossingPoint (xPair C.hpq) := by
  intro h
  have h1 := crossingPoint_injective_of_geometry (gu3_geometry C) h
  have hval : ({C.m, C.p} : Finset (ZMod k)) = {C.p, C.q} := congrArg Subtype.val h1
  have hm : C.m ∈ ({C.p, C.q} : Finset (ZMod k)) := hval ▸ mem_pair_left C.m C.p
  rcases Finset.mem_insert.mp hm with h2 | h2
  · exact gu3_p_ne_m C h2.symm
  · exact gu3_q_ne_m C (Finset.mem_singleton.mp h2).symm

omit [NeZero k] in
theorem gu3_edgePoint_sub (X : LabelledTuple k) (i : ZMod k) (s t : ℝ) :
    edgePoint X i t - edgePoint X i s = (t - s) • edge X i := by
  simp only [edgePoint, sub_smul]
  abel

/-- the three double points are not collinear -/
theorem gu3_det_triangle (C : G11_Config k) :
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

omit [NeZero k] in
/-- a point with nonnegative barycentric coordinates lies in the triangle -/
theorem gu3_mem_convexHull_three (a u v : Plane) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α + β ≤ 1) : a + α • u + β • v ∈ convexHull ℝ ({a, a + u, a + v} : Set Plane) := by
  have hs : ({a, a + u, a + v} : Set Plane) ⊆ convexHull ℝ {a, a + u, a + v} := subset_convexHull ℝ _
  have ha : a ∈ convexHull ℝ ({a, a + u, a + v} : Set Plane) := hs (by simp)
  have hb : a + u ∈ convexHull ℝ ({a, a + u, a + v} : Set Plane) := hs (by simp)
  have hd : a + v ∈ convexHull ℝ ({a, a + u, a + v} : Set Plane) := hs (by simp)
  have h := (convex_convexHull ℝ ({a, a + u, a + v} : Set Plane)).sum_mem (t := Finset.univ)
    (w := ![1 - α - β, α, β]) (z := ![a, a + u, a + v]) ?_ ?_ ?_
  · convert h using 1
    simp [Fin.sum_univ_three]
    module
  · intro i _
    fin_cases i <;> simp <;> linarith
  · simp [Fin.sum_univ_three]
    ring
  · intro i _
    fin_cases i <;> simp [ha, hb, hd]

omit [NeZero k] in
theorem gu3_cramer_core (u v h : Plane) : det h v • u + det u h • v = det u v • h := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  obtain ⟨h1, h2⟩ := h
  simp only [det]
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

omit [NeZero k] in
/-- the barycentric coordinates of a point near the centroid (Cramer) -/
theorem gu3_cramer (a u v h : Plane) (hD : det u v ≠ 0) :
    a + (1/3 : ℝ) • u + (1/3 : ℝ) • v + h =
      a + ((det u v / 3 + det h v) / det u v) • u + ((det u v / 3 + det u h) / det u v) • v := by
  have e1 : det u v * ((det u v / 3 + det h v) / det u v) = det u v / 3 + det h v := by
    field_simp
  have e2 : det u v * ((det u v / 3 + det u h) / det u v) = det u v / 3 + det u h := by
    field_simp
  have key : ((det u v / 3 + det h v) / det u v) • u + ((det u v / 3 + det u h) / det u v) • v =
      (1/3 : ℝ) • u + (1/3 : ℝ) • v + h := by
    apply smul_right_injective Plane hD
    show det u v • (_ + _) = det u v • (_ + _ + _)
    rw [smul_add, smul_smul, smul_smul, e1, e2]
    have hc := gu3_cramer_core u v h
    have hdiff : (det u v / 3 + det h v) • u + (det u v / 3 + det u h) • v -
        det u v • ((1/3 : ℝ) • u + (1/3 : ℝ) • v + h) =
        (det h v • u + det u h • v) - det u v • h := by module
    rw [← sub_eq_zero, hdiff, hc, sub_self]
  have e : a + (1/3 : ℝ) • u + (1/3 : ℝ) • v + h = a + ((1/3 : ℝ) • u + (1/3 : ℝ) • v + h) := by
    abel
  rw [e, ← key]
  abel

omit [NeZero k] in
/-- **a ball about the centroid lies in the triangle** -/
theorem gu3_centroid_ball_subset (a u v : Plane) (hD : det u v ≠ 0) :
    ∃ ε > 0, Metric.ball (a + (1/3 : ℝ) • u + (1/3 : ℝ) • v) ε ⊆
      convexHull ℝ ({a, a + u, a + v} : Set Plane) := by
  have hDpos : 0 < |det u v| := abs_pos.mpr hD
  have hK : 0 ≤ |u.1| + |u.2| + |v.1| + |v.2| := by positivity
  have hεK : |det u v| / (3 * (|u.1| + |u.2| + |v.1| + |v.2| + 1)) *
      (|u.1| + |u.2| + |v.1| + |v.2|) < |det u v| / 3 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    have : |det u v| / 3 * (3 * (|u.1| + |u.2| + |v.1| + |v.2| + 1)) =
        |det u v| * (|u.1| + |u.2| + |v.1| + |v.2| + 1) := by ring
    rw [this]
    nlinarith
  set ε := |det u v| / (3 * (|u.1| + |u.2| + |v.1| + |v.2| + 1)) with hε
  have hεpos : 0 < ε := by positivity
  refine ⟨ε, hεpos, ?_⟩
  intro z hz
  obtain ⟨h, rfl⟩ : ∃ h, z = a + (1/3 : ℝ) • u + (1/3 : ℝ) • v + h :=
    ⟨z - (a + (1/3 : ℝ) • u + (1/3 : ℝ) • v), by abel⟩
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Prod.norm_def, Real.norm_eq_abs,
    Real.norm_eq_abs, max_lt_iff] at hz
  obtain ⟨h1, h2⟩ := hz
  have hx : |det h v| ≤ ε * |v.2| + ε * |v.1| := by
    calc |det h v| = |h.1 * v.2 - h.2 * v.1| := rfl
      _ ≤ |h.1 * v.2| + |h.2 * v.1| := abs_sub _ _
      _ = |h.1| * |v.2| + |h.2| * |v.1| := by rw [abs_mul, abs_mul]
      _ ≤ ε * |v.2| + ε * |v.1| :=
        add_le_add (mul_le_mul_of_nonneg_right h1.le (abs_nonneg _))
          (mul_le_mul_of_nonneg_right h2.le (abs_nonneg _))
  have hy : |det u h| ≤ ε * |u.1| + ε * |u.2| := by
    calc |det u h| = |u.1 * h.2 - u.2 * h.1| := rfl
      _ ≤ |u.1 * h.2| + |u.2 * h.1| := abs_sub _ _
      _ = |u.1| * |h.2| + |u.2| * |h.1| := by rw [abs_mul, abs_mul]
      _ ≤ |u.1| * ε + |u.2| * ε :=
        add_le_add (mul_le_mul_of_nonneg_left h2.le (abs_nonneg _))
          (mul_le_mul_of_nonneg_left h1.le (abs_nonneg _))
      _ = ε * |u.1| + ε * |u.2| := by ring
  have hsum : |det h v| + |det u h| < |det u v| / 3 := by linarith
  have hxv : |det h v| < |det u v| / 3 := by linarith [abs_nonneg (det u h)]
  have hyu : |det u h| < |det u v| / 3 := by linarith [abs_nonneg (det h v)]
  rw [gu3_cramer a u v h hD]
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · rw [abs_of_neg hneg] at hxv hyu hsum
    refine gu3_mem_convexHull_three a u v ?_ ?_ ?_
    · exact (div_pos_of_neg_of_neg (by linarith [(abs_lt.mp hxv).2]) hneg).le
    · exact (div_pos_of_neg_of_neg (by linarith [(abs_lt.mp hyu).2]) hneg).le
    · rw [← add_div, div_le_one_of_neg hneg]
      linarith [neg_abs_le (det h v), neg_abs_le (det u h)]
  · rw [abs_of_pos hpos] at hxv hyu hsum
    refine gu3_mem_convexHull_three a u v ?_ ?_ ?_
    · exact (div_pos (by linarith [(abs_lt.mp hxv).1]) hpos).le
    · exact (div_pos (by linarith [(abs_lt.mp hyu).1]) hpos).le
    · rw [← add_div, div_le_one hpos]
      linarith [le_abs_self (det h v), le_abs_self (det u h)]

/-- the centroid lies in the open triangle -/
theorem gu3_centroid_mem_interior (C : G11_Config k) :
    G11_centroid C ∈ interior (G11_triangle C.X C.hmp C.hmq C.hpq) := by
  obtain ⟨ε, hε, hsub⟩ := gu3_centroid_ball_subset (crossingPoint (xPair C.hmp))
    (crossingPoint (xPair C.hmq) - crossingPoint (xPair C.hmp))
    (crossingPoint (xPair C.hpq) - crossingPoint (xPair C.hmp)) (gu3_det_triangle C)
  have hc : G11_centroid C = crossingPoint (xPair C.hmp) +
      (1/3 : ℝ) • (crossingPoint (xPair C.hmq) - crossingPoint (xPair C.hmp)) +
      (1/3 : ℝ) • (crossingPoint (xPair C.hpq) - crossingPoint (xPair C.hmp)) := by
    unfold G11_centroid
    module
  have hΔ : G11_triangle C.X C.hmp C.hmq C.hpq = convexHull ℝ {crossingPoint (xPair C.hmp),
      crossingPoint (xPair C.hmp) + (crossingPoint (xPair C.hmq) - crossingPoint (xPair C.hmp)),
      crossingPoint (xPair C.hmp) + (crossingPoint (xPair C.hpq) - crossingPoint (xPair C.hmp))} := by
    unfold G11_triangle
    rw [add_sub_cancel, add_sub_cancel]
  rw [mem_interior, hΔ]
  refine ⟨Metric.ball (G11_centroid C) ε, ?_, Metric.isOpen_ball, Metric.mem_ball_self hε⟩
  rw [hc]
  exact hsub

theorem gu3_triangle_compact (C : G11_Config k) : IsCompact (G11_triangle C.X C.hmp C.hmq C.hpq) :=
  (((Set.finite_singleton _).insert _).insert _).isCompact_convexHull ℝ

theorem gu3_disc_convex (C : G11_Config k) (r : ℝ) : Convex ℝ (G11_discOf C r) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ s t hs ht hst
  refine ⟨s • x + t • y, convex_convexHull ℝ _ hx hy hs ht hst, ?_⟩
  obtain rfl : t = 1 - s := by linarith
  module

theorem gu3_disc_compact (C : G11_Config k) (r : ℝ) : IsCompact (G11_discOf C r) :=
  (gu3_triangle_compact C).image (by fun_prop)

/-- **the closed triangle lies in the open disc** (for every margin `r > 0`) -/
theorem gu3_triangle_sub_interior_disc (C : G11_Config k) {r : ℝ} (hr : 0 < r) :
    G11_triangle C.X C.hmp C.hmq C.hpq ⊆ interior (G11_discOf C r) := by
  intro y hy
  have hs0 : 0 < 1 / (1 + r) := by positivity
  have hs1 : 1 / (1 + r) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  let g : Plane → Plane := fun z => G11_centroid C + (1 / (1 + r)) • (z - G11_centroid C)
  have hg : Continuous g := by fun_prop
  have hgy : g y ∈ interior (G11_triangle C.X C.hmp C.hmq C.hpq) := by
    have hconv : Convex ℝ (G11_triangle C.X C.hmp C.hmq C.hpq) := convex_convexHull ℝ _
    have := hconv.combo_interior_self_mem_interior
      (gu3_centroid_mem_interior C) hy (sub_pos.mpr hs1) hs0.le
      (sub_add_cancel (1 : ℝ) (1 / (1 + r)))
    have e : g y = (1 - 1 / (1 + r)) • G11_centroid C + (1 / (1 + r)) • y := by
      show G11_centroid C + (1 / (1 + r)) • (y - G11_centroid C) = _
      module
    rw [e]
    exact this
  rw [mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset (hg.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hgy))
  intro z hz
  refine ⟨g z, interior_subset hz, ?_⟩
  show G11_centroid C + (1 + r) • (G11_centroid C + (1 / (1 + r)) • (z - G11_centroid C) -
    G11_centroid C) = z
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

/-! ### U3 helpers (Block F) — the choice of the parameters -/

omit [NeZero k] in
theorem gu3_edgeSegment_isClosed (X : LabelledTuple k) (h : ZMod k) : IsClosed (edgeSegment X h) := by
  have himg : edgeSegment X h = (fun t : ℝ => edgePoint X h t) '' Set.Icc 0 1 := by
    ext x
    constructor
    · rintro ⟨t, h0, h1, rfl⟩
      exact ⟨t, ⟨h0, h1⟩, rfl⟩
    · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
      exact ⟨t, h0, h1, rfl⟩
  rw [himg]
  refine (isCompact_Icc.image ?_).isClosed
  unfold edgePoint
  exact continuous_const.add (continuous_id.smul continuous_const)

/-- the three flat vertices and the apex can be chosen `η`-close to the three double points -/
theorem gu3_exists_small (C : G11_Config k) {η : ℝ} (hη : 0 < η) :
    ∃ t₁ t₂ t₃ lam : ℝ, 0 < t₁ ∧
      t₁ < crossingParameter (xPair C.hmp) C.m (mem_pair_left _ _) ∧
      crossingParameter (xPair C.hmp) C.m (mem_pair_left _ _) < t₂ ∧
      t₂ < crossingParameter (xPair C.hmq) C.m (mem_pair_left _ _) ∧
      crossingParameter (xPair C.hmq) C.m (mem_pair_left _ _) < t₃ ∧ t₃ < 1 ∧ 1 < lam ∧
      dist (edgePoint C.X C.m t₁) (crossingPoint (xPair C.hmp)) < η ∧
      dist (edgePoint C.X C.m t₂ + lam • (crossingPoint (xPair C.hpq) - edgePoint C.X C.m t₂))
        (crossingPoint (xPair C.hpq)) < η ∧
      dist (edgePoint C.X C.m t₃) (crossingPoint (xPair C.hmq)) < η := by
  have h0 := (G11_Params.gu3_param_interior C C.hmp).1
  have h1 := (G11_Params.gu3_param_interior C C.hmq).2
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
    rw [dist_eq_norm, G11_Params.gu3_edgePoint_sub, norm_smul, Real.norm_eq_abs]
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

/-- **Leaf (Units B–D, the choice of parameters).** Parameters exist: the subdivision parameters
between the two crossing parameters on `m`; the apex ratio `λ > 1`; the margin `r` below the clearance
(`Δ` is compact and disjoint from the finitely many other closed edges and vertices: a positive distance
`ρ`; every point of `U` is within `r · diam` of `Δ`), then `t₁, t₃, λ − 1` small enough that `Θ ⊆ interior
U`. -/
theorem G11_exists_params (C : G11_Config k) : Nonempty (G11_Params C) := by
  classical
  -- the closed set of the foreign edges and of the vertices
  let K : Set Plane :=
    (⋃ h ∈ {h : ZMod k | h ≠ C.m ∧ h ≠ C.p ∧ h ≠ C.q}, edgeSegment C.X h) ∪ Set.range C.X
  have hKc : IsClosed K :=
    ((Set.toFinite _).isClosed_biUnion fun h _ => gu3_edgeSegment_isClosed C.X h).union
      (Set.finite_range C.X).isClosed
  have hΔK : G11_triangle C.X C.hmp C.hmq C.hpq ⊆ Kᶜ := by
    intro y hy hyK
    rcases hyK with hyK | ⟨i, rfl⟩
    · rw [Set.mem_iUnion₂] at hyK
      obtain ⟨h, ⟨hm, hp, hq⟩, hyh⟩ := hyK
      exact C.clear_edge h hm hp hq y hyh hy
    · exact C.clear_vertex i hy
  obtain ⟨δ, hδ, hδK⟩ := (G11_Params.gu3_triangle_compact C).exists_thickening_subset_open
    hKc.isOpen_compl hΔK
  -- the radius of the triangle about its centroid
  have hMpos : 0 < dist (crossingPoint (xPair C.hmp)) (G11_centroid C) +
      dist (crossingPoint (xPair C.hmq)) (G11_centroid C) +
      dist (crossingPoint (xPair C.hpq)) (G11_centroid C) + 1 := by positivity
  set M := dist (crossingPoint (xPair C.hmp)) (G11_centroid C) +
    dist (crossingPoint (xPair C.hmq)) (G11_centroid C) +
    dist (crossingPoint (xPair C.hpq)) (G11_centroid C) + 1 with hM
  have hΔM : ∀ y ∈ G11_triangle C.X C.hmp C.hmq C.hpq, dist y (G11_centroid C) ≤ M := by
    intro y hy
    have hsub : G11_triangle C.X C.hmp C.hmq C.hpq ⊆ Metric.closedBall (G11_centroid C) M := by
      apply convexHull_min _ (convex_closedBall _ M)
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rw [Metric.mem_closedBall]
      have d1 := dist_nonneg (x := crossingPoint (xPair C.hmp)) (y := G11_centroid C)
      have d2 := dist_nonneg (x := crossingPoint (xPair C.hmq)) (y := G11_centroid C)
      have d3 := dist_nonneg (x := crossingPoint (xPair C.hpq)) (y := G11_centroid C)
      rcases hz with rfl | rfl | rfl <;> linarith
    exact hsub hy
  have hrpos : 0 < δ / (2 * M) := by positivity
  set r := δ / (2 * M) with hr
  have hU : G11_discOf C r ⊆ Kᶜ := by
    rintro _ ⟨y, hy, rfl⟩
    apply hδK
    rw [Metric.mem_thickening_iff]
    refine ⟨y, hy, ?_⟩
    show dist (G11_centroid C + (1 + r) • (y - G11_centroid C)) y < δ
    have hyz : G11_centroid C + (1 + r) • (y - G11_centroid C) - y = r • (y - G11_centroid C) := by
      module
    rw [dist_eq_norm, hyz, norm_smul, Real.norm_of_nonneg hrpos.le, ← dist_eq_norm]
    calc r * dist y (G11_centroid C) ≤ r * M := mul_le_mul_of_nonneg_left (hΔM y hy) hrpos.le
      _ = δ / 2 := by rw [hr, div_mul_eq_mul_div, mul_div_mul_right _ _ hMpos.ne']
      _ < δ := by linarith
  obtain ⟨η, hη, hηU⟩ := (G11_Params.gu3_triangle_compact C).exists_thickening_subset_open
    isOpen_interior (G11_Params.gu3_triangle_sub_interior_disc C hrpos)
  obtain ⟨t₁, t₂, t₃, lam, ht₁, h₁, h₂, h₃, h₄, ht₃, hlam, hd₁, hd₂, hd₃⟩ := gu3_exists_small C hη
  refine ⟨⟨t₁, t₂, t₃, lam, r, ht₁, h₁, h₂, h₃, h₄, ht₃, hlam, hrpos, ?_, ?_, ?_⟩⟩
  · apply convexHull_min _ (G11_Params.gu3_disc_convex C r).interior
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

include hG in
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
  exact gu2_clear hG hs hef heg hfg hcef hceg hcfg hX

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

/-- **A12 for `{p, q}` with the crossing hypothesis.** The frozen `G11_cfg_hpq` below did not have `hcfg`
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

include hfg hcfg in
theorem G11_cfg_hpq (hX : ExactTriangleVisitOrders P P' e f g hs) :
    IsCrossing (geoCornerPolygon hG.cg T q) {G11_pE hn hG hT q hcef htri, G11_qE hn hG hT q hceg htri} := by
  exact gu2_cfg_hpq hn hG hs hT q hcef hceg htri hfg hcfg hX

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
        (G11_cfg_hmq hn hG hs hT q hcef hceg htri hX) (G11_cfg_hpq hn hG hs hT q hfg hcef hceg hcfg htri hX) := by
  intro i hi
  obtain ⟨-, hcfg⟩ := gu2_hcfg_of_hpq hn hG hT q hcef hceg htri (G11_cfg_hpq hn hG hs hT q hfg hcef hceg hcfg htri hX)
  have hΔ : G11_triangle (geoCornerPolygon hG.cg T q) (G11_cfg_hmp hn hG hT q hcef htri)
      (G11_cfg_hmq hn hG hs hT q hcef hceg htri hX) (G11_cfg_hpq hn hG hs hT q hfg hcef hceg hcfg htri hX) =
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
          (G11_cfg_hmq hn hG hs hT q hcef hceg htri hX) (G11_cfg_hpq hn hG hs hT q hfg hcef hceg hcfg htri hX)) := by
  intro h hhm hhp hhq x hx hxF
  obtain ⟨-, hcfg⟩ := gu2_hcfg_of_hpq hn hG hT q hcef hceg htri (G11_cfg_hpq hn hG hs hT q hfg hcef hceg hcfg htri hX)
  have hΔ : G11_triangle (geoCornerPolygon hG.cg T q) (G11_cfg_hmp hn hG hT q hcef htri)
      (G11_cfg_hmq hn hG hs hT q hcef hceg htri hX) (G11_cfg_hpq hn hG hs hT q hfg hcef hceg hcfg htri hX) =
      convexHull ℝ {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)} := by
    unfold G11_triangle
    rw [gu2_xmp_eq hn hG hT q hcef htri, gu2_xmq_eq hn hG hT q hcef hceg htri,
      gu2_xpq_eq hn hG hT q hcef hceg hcfg htri]
  have hxΔ' : x ∈ G11_triangle (geoCornerPolygon hG.cg T q) (G11_cfg_hmp hn hG hT q hcef htri)
      (G11_cfg_hmq hn hG hs hT q hcef hceg htri hX) (G11_cfg_hpq hn hG hs hT q hfg hcef hceg hcfg htri hX) := by
    have := frontier_subset_closure hxF
    rw [hΔ] at this ⊢
    rwa [(gu2_tri_isClosed _ _ _).closure_eq] at this
  rw [hΔ] at hxF
  have hxΔ : x ∈ convexHull ℝ
      {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)} := by
    rw [← hΔ]; exact hxΔ'
  have hcl := gu2_clear hG hs hef heg hfg hcef hceg hcfg hX
  have hvert := gu2_cfg_clear_vertex hn hG hs hT q hcef hceg hcfg htri hef heg hfg hX
  have hx₀ := gu2_edgeSegment_sub hn hG hT q h hx
  obtain ⟨c₀, hc₀, hedge₀⟩ := geoCornerPolygon_edge_smul hn hG.cg hT q h
  have hxmp := gu2_xmp_eq hn hG hT q hcef htri (G11_cfg_hmp hn hG hT q hcef htri)
  have hxmq := gu2_xmq_eq hn hG hT q hcef hceg htri (G11_cfg_hmq hn hG hs hT q hcef hceg htri hX)
  have hxpq := gu2_xpq_eq hn hG hT q hcef hceg hcfg htri (G11_cfg_hpq hn hG hs hT q hfg hcef hceg hcfg htri hX)
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
        (G11_cfg_hmq hn hG hs hT q hcef hceg htri hX) (G11_cfg_hpq hn hG hs hT q hfg hcef hceg hcfg htri hX) := by
  exact gu2_cfg_clear_vertex hn hG hs hT q hcef hceg hcfg htri hef heg hfg hX

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
  hpq := G11_cfg_hpq hn hG hs hT q hfg hcef hceg _hcfg htri hX
  order := G11_cfg_order hn hG hs hT q hcef hceg htri hX hord
  trans := G11_cfg_trans hn hG hT q hcef hceg htri halt
  clear_frontier := G11_cfg_clear_frontier hn hG hs hT q hcef hceg _hcfg htri hef heg hfg hX
  clear_vertex := G11_cfg_clear_vertex hn hG hs hT q hcef hceg _hcfg htri hef heg hfg hX

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
  refine EXT_homfly_wall hn hG hG' hs hT hT' q q' hcarr ?_ ?_
  · intro v w _ _
    refine AV_key_lt_of_gauss hG.cg hG'.cg hs hef heg hfg hX v w ?_
    rintro ⟨hv, hw, hne, -⟩
    exact hne (Finset.card_le_one.mp hcard _ hv _ hw)
  · intro v _
    exact hdet _ _ (by rw [← visit_crossing_val_eq_pair v]; exact v.1.property)

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

end RProof
