# PLAN_B — mp:zero-link (sm-3-statesum.tex:1538-1580) by the fan-triangle route with a 1-D core

Tag B. Written 2026-09-13 (UTC) for the fixed statement `work/drafts/ZeroLink_statement.lean`
(`SM.ZeroLinkData`, three fields). Skeleton: `work/drafts/zerolink/Skeleton_B.lean` (783 lines,
52 theorems, typechecks with `lake env lean`, 0 errors, 8 `sorry`, no other warnings).

## 0. Route and why it has the least geometric burden

The printed proof is followed: pick an auxiliary point `o` off finitely many lines, decompose
component 2 (`B`, polygon over `ZMod n`) into the fan of triangles `T_q = (o, b_q, b_{q+1})`, show
that the closed component 1 (`A`, polygon over `ZMod m`) has signed crossing count `0` with the
boundary of each triangle, and cancel the radial edges. The single piece of genuine 2-D content —
"a closed transverse path has as many signed entries as exits into a triangle" — is reduced to an
edge-by-edge statement and then to a **one-dimensional lemma about three affine functions on
`[0,1]`** (`affine_triple_jump`): along the edge `x(t) = a + t·u`, the three side functions
`g_k(t) = det(σ_k, x(t) - c_k)` are affine, "inside the open triangle" is `∀ k, g_k(t) > 0`, and a
transverse crossing of side `k` is `g_k(t) = 0` with the other two positive. Everything else is
algebra of `det` (`ring`/`linear_combination`), `Finset.sum` bookkeeping, and `tail_off`.

Alternatives considered and rejected (see the task's emphasis):

* **Ray-casting winding number of `B` evaluated along `A`.** Equivalent to the fan from a point at
  infinity, but the rays are dictated by the diagram (direction of `f_q` from `b_{q+1}`, or a fixed
  direction from every `b_q`), and genericity (`tail_off`) does **not** exclude a vertex `a_p` lying
  on the *extension* of an edge `f_q`; then the ray from `b_{q+1}` passes through the vertex `a_p`,
  where half-open conventions give the wrong count when `A` merely touches the ray. Repairing this
  needs an extra generic direction and an event analysis with two event types (crossings and
  vertex heights). The finite point `o` avoids all of that: `o ∉ line(a_p, b_q)` for all `p, q`.
* **A closed-form sign identity `χ(e,f) = ¼(s_{b'} − s_b)(1 − σ_a σ_{a'})` whose double sum
  telescopes.** The identity is only valid when all four side signs are nonzero (a vertex of `B` on
  the extended line of `e_p` gives a zero sign, not excluded by genericity) and the telescoping of
  the second factor is not termwise; a brute-force check over sign vectors is impossible because the
  identity holds only on realizable configurations. Rejected.
* **Jordan curve / winding-number theory from Mathlib.** Not available in the needed form; not used.
  Only `intermediate_value_Icc(')`, `Metric.isOpen_iff`, continuity of affine maps, `Finset` sums
  and `Infinite.exists_notMem_finset` are used from Mathlib.

Genericity actually consumed: `Generic.regular` (edges nonzero, so the edge lines are lines),
`Generic.tail_off` (no vertex on a closed edge of another component). `Generic.transverse` and
`Generic.no_triple` are **not** needed: the statement's summand is `sgn det(u₁,u₂)` at every mixed
pair whose closed segments meet, and our indicator `chi` has literally that form (it is `0` for a
collinear overlap, which cannot occur anyway).

## 1. Definitions (all in `SM.ZeroLink`)

```lean
def closedSeg (b v : Plane) : Set Plane := {x | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ x = b + s • v}
  -- edgeSegment P i = closedSeg (P i) (edge P i) is `rfl`
def Meets (a u b v : Plane) : Prop :=
  ∃ t s : ℝ, 0 < t ∧ t < 1 ∧ 0 < s ∧ s < 1 ∧ a + t • u = b + s • v
def chi (a u b v : Plane) : ℤ := if Meets a u b v then ((SignType.sign (det u v) : SignType) : ℤ) else 0
def ind (p : Prop) : ℤ := if p then 1 else 0
def Cross (α β : Fin 3 → ℝ) (k : Fin 3) (t : ℝ) : Prop :=
  0 < t ∧ t < 1 ∧ α k + β k * t = 0 ∧ ∀ j, j ≠ k → 0 < α j + β j * t
def InTri (c₀ c₁ c₂ x : Plane) : Prop :=
  0 < det (c₁ - c₀) (x - c₀) ∧ 0 < det (c₂ - c₁) (x - c₁) ∧ 0 < det (c₀ - c₂) (x - c₂)
def triBoundary (c₀ c₁ c₂ : Plane) : Set Plane :=
  closedSeg c₀ (c₁ - c₀) ∪ closedSeg c₁ (c₂ - c₁) ∪ closedSeg c₂ (c₀ - c₂)
def triChi (a u c₀ c₁ c₂ : Plane) : ℤ :=
  chi a u c₀ (c₁ - c₀) + chi a u c₁ (c₂ - c₁) + chi a u c₂ (c₀ - c₂)
-- diagram layer
def fixedSummand (D) (i j) (s t) : ℤ := if D.Γ.MixedPair i j s t then sgn det(dir s, dir t) else 0
def signSummand (D) (i j) (s t) : ℤ := if h : MixedPair then (D.sign ⟨{s,t},h.2.2⟩ : ℤ) else 0
def corr (D) (i j) (s t) : ℤ := if h : MixedPair then (if overStrand = t then -sgn det(dir s,dir t) else 0) else 0
```
Sign convention: `chi` puts the *moving* edge first (matching the statement's `det (dir s) (dir t)`,
`s` on `i`). Entering a positively oriented triangle through side `σ_k` means `det(σ_k, u) > 0`,
i.e. `det(u, σ_k) < 0`, hence the minus sign in L3.

## 2. The lemma chain (exact statements are in the skeleton; status P = proved, S = sorry)

| # | name | statement (abridged) | proof sketch | st | est. lines |
|---|------|----------------------|--------------|----|-----------|
| L1 | `meets_reverse_iff` | `Meets a u (b+v) (-v) ↔ Meets a u b v` | `s ↦ 1-s`; `sub_smul, smul_neg, abel` | P | 12 |
| L1 | `chi_reverse` | `chi a u (b+v) (-v) = -chi a u b v` | L1 + `det u (-v) = -det u v` + `Left.sign_neg` | P | 10 |
| L1' | `chi_reverse'` | `chi a u c (b-c) = -chi a u b (c-b)` | instance of `chi_reverse` | P | 7 |
| — | `closedSeg_reverse` | `closedSeg c (b-c) = closedSeg b (c-b)` | `s ↦ 1-s` | P | 6 |
| — | `not_mem_closedSeg_of_det_ne_zero` | `det v (x-b) ≠ 0 → x ∉ closedSeg b v` | `det_smul_self` | P | 4 |
| — | `not_mem_closedSeg_radial`, `…'` | `det (b-a) (o-a) ≠ 0 → a ∉ closedSeg o (b-o)`, `a ∉ closedSeg b (o-b)` | substitute, `simp [det]; ring` | P | 2×8 |
| L2a | `cross_pos_exists_inside_after` | `Cross α β k t → 0 < β k → ∀ ε>0, ∃ t' ∈ (t,t+ε), ∀ j, 0 < α j + β j * t'` | `U = {t' ∣ ∀ j ≠ k, 0 < g j t'}` is open (`isOpen_iInter_of_finite`, preimage of `Ioi`), `Metric.isOpen_iff` gives a radius `r`; take `t' = t + min ε r / 2`; `g k t' = β k (t'-t) > 0` | S | 35 |
| L2a' | `cross_neg_exists_inside_before` | mirror (`β k < 0`, `t' ∈ (t-ε,t)`) | same | S | 35 |
| L2b | `cross_same_sign_unique` | `Cross k t → Cross k' t' → β k ≠ 0 → sign β k = sign β k' → k = k' ∧ t = t'` | `k = k'`: one root of a non-constant affine map. `k ≠ k'`, both `β > 0`, `t < t'`: L2a at `t` gives an inside point `t'' < t'`, but `g k' t'' = β k' (t''-t') < 0`; symmetric; `t = t'` contradicts `hvert`. Negative slopes via L2a'. | S | 45 |
| L2c | `cross_pos_lt_cross_neg` | `Cross k t (β k>0) → Cross k' t' (β k'<0) → t < t'` | if `t' ≤ t`: L2a at `t` gives inside `t'' > t ≥ t'`, but `g k' t'' < 0`; `t' = t` contradicts `hvert` | S | 20 |
| L2d | `exists_cross_neg_of_inside_not_inside` | inside at `s`, not inside at `s' ∈ (s,1]` ⇒ `∃ k t, Cross k t ∧ β k < 0 ∧ s < t ≤ s'` | `m t := min (g 0 t) (min (g 1 t) (g 2 t))` continuous; `intermediate_value_Icc'` gives `t ∈ [s,s']` with `m t = 0`; some `g k t = 0`, all `≥ 0`, `hvert` ⇒ others `> 0`; `t ≠ s`; `t = 1` excluded by `hend`; `β k < 0` from `g k s > 0 = g k t` | S | 60 |
| L2d' | `exists_cross_pos_of_not_inside_inside` | mirror (`intermediate_value_Icc`, `hend 0`) | same | S | 60 |
| L2 | `affine_triple_jump` | `ind (∀k, 0 < α k + β k*1) - ind (∀k, 0 < α k + β k*0) = ∑ k, if ∃ t, Cross α β k t then sgn (β k) else 0` under `hend`, `hvert` | Case P⁰ (`∃ Cross k t` with `β k = 0`): then `g k ≡ 0`, inside is impossible, all summands `0`. Otherwise split on P⁺ := `∃ Cross with β>0`, P⁻ := `∃ Cross with β<0`. P⁺∧P⁻: L2c gives `t⁺ < t⁻`, hence `¬inside 0`, `¬inside 1`; by L2b exactly one `+1` and one `−1` summand, third is `0`; sum `0`. P⁺ only: `¬inside 0`; `inside 1` else L2a + L2d produce a `−1` crossing; sum `= 1` by L2b. P⁻ only: mirror. Neither: `inside 0 ↔ inside 1` by L2d/L2d'. Sum over `Fin 3` with two marked indices: rewrite summand pointwise as `(if k = k⁺ then 1 else 0) + (if k = k⁻ then -1 else 0)` and `Finset.sum_ite_eq'`. | S | 120 |
| L3a | `side_line_values` | `det (c₂-c₁) (c₀ + s•(c₁-c₀) - c₁) = (1-s)·D ∧ det (c₀-c₂) (…) = s·D`, `D = det (c₁-c₀) (c₂-c₀)` | `simp [det]; ring` | P | 5 |
| — | `side_ne_zero_of_det`, `det_tri_cyclic` | `det (c-b) (d-b) ≠ 0 → c - b ≠ 0`; `det (c₂-c₁) (c₀-c₁) = det (c₁-c₀) (c₂-c₀)` | `simp [det]`; accepted `area_cyclic` | P | 8 |
| L3c' | `line_meet_vertex` | `det (c-b) (d-b) ≠ 0 → det (c-b) (x-b) = 0 → det (d-c) (x-c) = 0 → x = c` | `scalar_of_det_zero` gives `x-b = r•(c-b)`; then `x-c = (r-1)•(c-b)`, `det (d-c) (c-b) = -D ≠ 0` forces `r = 1` | P | 22 |
| L3c | `vertex_of_two_sides_zero` | three rotated instances | L3c' + `det_tri_cyclic` | P | 5 |
| L3b' | `mem_closedSeg_of_side` | on line of `[b,c]`, other two side functions `≥ 0` ⇒ `x ∈ closedSeg b (c-b)` | `scalar_of_det_zero`, L3a, `nlinarith` for `0 ≤ s ≤ 1` | P | 12 |
| L3b | `mem_triBoundary_of_ge_of_eq` | all `≥ 0`, one `= 0` ⇒ `x ∈ triBoundary` | three rotated L3b' | P | 7 |
| L3d | `meets_side_iff` | `(∃ s∈(0,1), a+t•u = c₀ + s•(c₁-c₀)) ↔ g₀ = 0 ∧ g₁ > 0 ∧ g₂ > 0` at `a + t•u` | L3a both ways, `scalar_of_det_zero`, `nlinarith` | P | 20 |
| L3 | `segment_triangle_jump` | `0 < D`, `a, a+u ∉ triBoundary`, `c_k ∉ closedSeg a u` ⇒ `ind (InTri (a+u)) - ind (InTri a) = -triChi a u c₀ c₁ c₂` | put `α = ![det σ₀ (a-c₀), det σ₁ (a-c₁), det σ₂ (a-c₂)]`, `β = ![det σ₀ u, …]`; `g k t = det σ_k (a + t•u - c_k)` by `det_add_right, det_smul_right`; `InTri (a+t•u) ↔ ∀ k, 0 < α k + β k*t` (`Fin.forall_fin_succ`); `hend` from L3b (contrapositive of `ha, ha'`); `hvert` from L3c and `a + t•u ∈ closedSeg a u`; apply L2; per side, `∃ t, Cross k t ↔ Meets a u c_k σ_k` by L3d (sides 1, 2 by rotating the vertices, `det_tri_cyclic`); `sign (β k) = sign det σ_k u = -sign det u σ_k` (`det_swap`, `Left.sign_neg`); `Fin.sum_univ_three`, `one_smul`, `zero_smul` | S | 150 |
| L4a | `triChi_swap` | `triChi a u c₀ c₂ c₁ = -triChi a u c₀ c₁ c₂` | three `chi_reverse'` + `ring` | P | 4 |
| — | `triBoundary_swap` | `triBoundary c₀ c₂ c₁ = triBoundary c₀ c₁ c₂` | `closedSeg_reverse` ×3, `tauto` | P | 7 |
| L4b | `sum_shift_sub` | `∑ p : ZMod m, (f (p+1) - f p) = 0` | `Equiv.sum_comp (Equiv.addRight 1)` | P | 4 |
| L4 | `closed_polygon_triangle_sum` | `det ≠ 0`, vertices of `P` off `triBoundary`, `c_k` off all edges ⇒ `∑ p, triChi (P p) (edge P p) c₀ c₁ c₂ = 0` | `lt_or_gt_of_ne`; positive: L3 on every edge (`P p + edge P p = P (p+1)`), telescoping L4b; negative: L3 on `(c₀,c₂,c₁)`, `triChi_swap`, `triBoundary_swap` | P | 45 |
| L5 | `exists_point_off_lines` | `[Fintype ι] (c v : ι → Plane) (∀ l, v l ≠ 0) → ∃ o, ∀ l, det (v l) (o - c l) ≠ 0` | abscissa `X ∉ image (c ·).1` (`Infinite.exists_notMem_finset`), ordinate `Y ∉ image (l ↦ (c l).2 + (v l).2 (X-(c l).1)/(v l).1)`; vertical lines (`(v l).1 = 0`) miss `(X,Y)` because `X ≠ (c l).1`, others because `Y` is not their value at `X` (`field_simp; ring`) | P | 30 |
| L5a | `det_fan_of_off_line` | `det (b'-b) (o-b) ≠ 0 → det (b-o) (b'-o) ≠ 0` | `ring` identity | P | 6 |
| L6a | `radial_cancel` | `∑ q ∑ p (chi e_p o (B q - o) + chi e_p (B (q+1)) (o - B (q+1))) = 0` | `chi_reverse'` turns the second term into `-chi e_p o (B (q+1) - o)`; telescoping in `q` (L4b) | P | 25 |
| L6 | `fan_sum_zero` | `A B` closed polygons, nonzero edges, `A p ∉ edgeSegment B q`, `B q ∉ edgeSegment A p` ⇒ `∑ p ∑ q chi (A p) (edge A p) (B q) (edge B q) = 0` | L5 on the family indexed by `(ZMod m × ZMod n) ⊕ (ZMod m ⊕ ZMod n)`: lines `a_p b_q` (direction `b_q - a_p ≠ 0` by `hAB`), edge lines of `A`, edge lines of `B`; for each `q` apply L4 to `(o, B q, B (q+1))` — `hD` by L5a, vertices off the boundary by `not_mem_closedSeg_radial(')` and `hAB`, triangle vertices off edges by `not_mem_closedSeg_of_det_ne_zero` and `hBA`; sum over `q`, split `triChi`, L6a, `Finset.sum_comm` | P | 60 |
| — | `edge_ne_zero`, `vertex_not_mem_other_seg`, `ne_of_mixedPair` | from `Generic.regular` / `Generic.tail_off` (`IncidentTail.fst_eq`) | direct | P | 12 |
| L7 | `mixedPair_iff_meets` | `i ≠ j → (MixedPair i j ⟨i,p⟩ ⟨j,q⟩ ↔ Meets (A p) (edge A p) (B q) (edge B q))` | `crossing_pair_spec` gives a common point with parameters in `[0,1]`; `tail_off` (via `vertex_not_mem_other_seg` at `p, p+1, q, q+1`, `edgePoint_zero/one`) pushes them into `(0,1)`; converse by `isCrossing_pair` (strands on different components are never adjacent) | P | 45 |
| — | `fixedSummand_eq_chi`, `fixedSummand_eq_zero_left/right` | | L7; `MixedPair` forces `s.1 = i`, `t.1 = j` | P | 20 |
| L8 | `sum_fixedSummand_eq` | `∑ s ∑ t fixedSummand = ∑ p ∑ q fixedSummand ⟨i,p⟩ ⟨j,q⟩` | `Fintype.sum_sigma`, `Finset.sum_eq_single` twice | P | 12 |
| — | `fixed_order_sum_zero` | field 1 | L8, L6 with the genericity lemmas, `fixedSummand_eq_chi` | P | 10 |
| — | `over_eq_or`, `sign_of_over_left`, `sign_of_over_right` | `overStrand ∈ {s,t}`; `D.sign = sgn det(dir s,dir t)` resp. its negative (`eq_under_of_mem_of_ne`, `det_swap`, `Left.sign_neg`) | | P | 30 |
| L9 | `signSummand_eq` | `signSummand = fixedSummand + 2 * corr` | case on `MixedPair` and on the over strand | P | 12 |
| — | `mixedSignSum_eq`, `mixedSignSum_eq_two_mul` | field 2 | `Finset.mul_sum`, `Finset.sum_add_distrib`, field 1 | P | 14 |
| — | `corr_eq_zero_of_over_left`, `signSummand_eq_neg_of_over_right`, `mixedSignSum_eq_zero_of_over_constant` | field 3 | termwise, `Finset.sum_eq_zero` / `Finset.sum_neg_distrib`, field 1 | P | 35 |
| — | `zero_link : ZeroLinkData` | | the three lemmas above | P | 4 |

Total: 52 theorems; ~783 lines written, ~525 lines estimated for the 8 remaining `sorry`s;
**total estimate ≈ 1300 lines**.

## 3. Dependency order

1. Segment algebra: `meets_reverse_iff → chi_reverse → chi_reverse'`; `closedSeg_reverse →
   triBoundary_swap`; `not_mem_closedSeg_*`; `sum_shift_sub`.
2. 1-D core: `L2a, L2a' → L2b, L2c`; `L2d, L2d'` (IVT); all → `affine_triple_jump` (L2).
3. Triangle algebra: `side_line_values`, `side_ne_zero_of_det`, `det_tri_cyclic`,
   `line_meet_vertex → vertex_of_two_sides_zero` (L3c), `mem_closedSeg_of_side →
   mem_triBoundary_of_ge_of_eq` (L3b), `meets_side_iff` (L3d).
4. `L2 + L3b + L3c + L3d → segment_triangle_jump` (L3).
5. `L3 + triChi_swap + triBoundary_swap + sum_shift_sub → closed_polygon_triangle_sum` (L4).
6. `exists_point_off_lines` (L5), `det_fan_of_off_line`, `radial_cancel`, `L4 → fan_sum_zero` (L6).
7. Diagram layer: `edge_ne_zero`, `vertex_not_mem_other_seg`, `mixedPair_iff_meets` (L7),
   `sum_fixedSummand_eq` (L8), `L6 → fixed_order_sum_zero`; `sign_of_over_*`, `signSummand_eq`
   (L9) → `mixedSignSum_eq_two_mul`, `mixedSignSum_eq_zero_of_over_constant`; `zero_link`.

## 4. Degenerate configurations

* **Crossing at a vertex** (a vertex of one component on a closed edge of the other): excluded by
  `Generic.tail_off` (strands on different components are never `IncidentTail`, by
  `IncidentTail.fst_eq`). Used in L7 (parameters in `(0,1)`) and as the hypotheses `hAB`, `hBA` of
  L6 (vertices of `A` off the sides `f_q` of every fan triangle; vertices `b_q, b_{q+1}` of every fan
  triangle off the edges of `A`).
* **Transversality**: not needed. At a mixed pair whose closed segments meet, the summand is
  `sgn det(u₁,u₂)` whatever its value; `chi` has the same form. (A collinear overlap of an edge of
  `A` with a side of a fan triangle cannot occur under the L3 hypotheses, and would give `chi = 0`
  consistently anyway.)
* **No triple points**: not needed; the argument counts traversed occurrences.
* **Vertex on the extended line of an edge of the other component** (allowed by genericity): the
  1-D core L2 only looks at roots in `(0,1)` with the other two functions positive; a root outside
  `[0,1]`, or a root where another side function is negative, is not a crossing and does not change
  the indicator. Parallel edge and side (`β k = 0`) is covered by L2 (case P⁰ / vacuous
  constraint).
* **The auxiliary point `o`** must avoid: (i) the `n` lines `b_q b_{q+1}` (fan triangles
  nondegenerate, `det_fan_of_off_line`), (ii) the `m` lines `a_p a_{p+1}` (`o` not on an edge of `A`,
  so the triangle vertex `o` is off every edge), (iii) the `m·n` lines `a_p b_q` (no vertex `a_p` on
  a radial side `[o,b_q]` or `[b_{q+1},o]`, `not_mem_closedSeg_radial(')`). All directions are
  nonzero: edges by `Generic.regular`, `b_q - a_p` because `a_p ∉ edgeSegment B q ∋ b_q`.
  **Finiteness argument (L5, proved):** index the lines by the finite type
  `(ZMod m × ZMod n) ⊕ (ZMod m ⊕ ZMod n)`; the abscissas of all line base points form a
  `Finset`, so some `X` avoids them (`Infinite.exists_notMem_finset`); every non-vertical line
  meets the vertical line `x = X` in exactly one ordinate, these ordinates form a `Finset`, so some
  `Y` avoids them; vertical lines miss `(X, Y)` because `X` differs from their abscissa. No
  polynomial root counting is needed.
* **Endpoints of an edge on the triangle boundary / edge through a triangle vertex**: excluded by
  the above (`tail_off` + choice of `o`); they are exactly the hypotheses `hend`, `hvert` of L2
  after translation by L3b, L3c.
* **Self-intersecting or non-simple components, zero turns**: irrelevant; only closedness
  (`ZMod` telescoping) and the per-edge affine structure are used.

## 5. The three riskiest steps and fallbacks

1. **L2 main case analysis (`affine_triple_jump`, est. 120 lines).** Risk: bookkeeping of the
   P⁰/P⁺/P⁻ cases and evaluating a `Fin 3` sum with two distinguished indices. Fallback A: state L2
   with three explicit pairs `(α₀,β₀), (α₁,β₁), (α₂,β₂)` and `Fin.sum_univ_three`, doing the
   `k`-symmetric arguments once via a permutation lemma. Fallback B (fully mechanical): for
   `β k ≠ 0` write `g k t = β k * (t - r k)` with `r k = -α k / β k`; then `Cross k t ↔ t = r k ∧
   0 < r k < 1 ∧ …` and the lemma becomes an order statement about `{0, 1, r 0, r 1, r 2}` and the
   signs of `β`, provable by `rcases lt_trichotomy` case splits and `linarith` (finite, ≤ 27 sign
   patterns × orderings). Fallback C: the sorted-parameter-list formulation (roots of the `g k` in
   `(0,1)` as a `Finset ℝ`, constancy of the sign vector between consecutive roots).
2. **L2d/L2d' (IVT plumbing, est. 2×60 lines).** Risk: `ContinuousOn` for `min` of three affine
   maps, extraction of the vanishing index from `min = 0`, the endpoint exclusion via `hend`.
   Fallback: replace IVT by the explicit-root description of Fallback B (the first exit after `s` is
   the minimum of the negative-slope roots in `(s, s']`, a finite `min`), or by `sSup`/`IsLUB` on
   `{t ∈ [s,s'] | inside t}` with `le_csSup`/`csSup_le`.
3. **L3 translation (`segment_triangle_jump`, est. 150 lines).** Risk: the `Fin 3`-indexed
   `![…]` vectors versus the explicit conjunction `InTri`, and matching `∃ t, Cross α β k t` with
   `Meets` for sides 1 and 2 (L3d is stated for side 0 and must be instantiated on the rotated
   triangles `(c₁,c₂,c₀)`, `(c₂,c₀,c₁)` with `det_tri_cyclic`). Fallback: state L2 for three
   explicit pairs (as in 1A), so no `Matrix.vecCons` appears, and add rotated copies
   `meets_side_iff₁`, `meets_side_iff₂` proved by the same script.

Secondary risks: the definitional matching of the statement's `if D.Γ.MixedPair … then … else 0`
with `fixedSummand` (already verified: `zero_link` typechecks against the verbatim copy of
`ZeroLinkData`); `SignType` coercion lemmas (`simp` closes them, verified in `sign_of_over_right`).

## 6. What is done and what remains

Proved in the skeleton (sorry-free): every definition; L1, L1', segment membership lemmas; L3a-L3d
with helpers; L4a, L4b, L4; L5, L5a; L6a, L6; the whole diagram layer L7-L9 and the three fields;
`SM.zero_link : ZeroLinkData`. Remaining `sorry` (8): `affine_triple_jump` and its six sub-lemmas
(`cross_pos_exists_inside_after`, `cross_neg_exists_inside_before`, `cross_same_sign_unique`,
`cross_pos_lt_cross_neg`, `exists_cross_neg_of_inside_not_inside`,
`exists_cross_pos_of_not_inside_inside`), and `segment_triangle_jump`.
Check command: `cd work/lean && lake env lean ../drafts/zerolink/Skeleton_B.lean` (0 errors,
8 `sorry` warnings, nothing else).
