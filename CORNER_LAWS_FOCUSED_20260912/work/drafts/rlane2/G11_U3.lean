import RProof.X1Rows3
import SM.CS3

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
