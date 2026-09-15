# PLAN_A — mp:zero-link by the printed fan-triangle argument

Target: `SM.zero_link : ZeroLinkData` for the FIXED statement in
`work/drafts/ZeroLink_statement.lean` (mp:zero-link, reference/SM/sm-3-statesum.tex:1538-1580,
frame SM15).  Companion file: `work/drafts/zerolink/Skeleton_A.lean`.

**State (2026-09-13, tag A subagent).** The "skeleton" is a complete proof: every chain lemma is
proved, `cd work/lean && lake env lean ../drafts/zerolink/Skeleton_A.lean` prints nothing (no
errors, no warnings, no `sorry`), and `#print axioms SM.zero_link` gives
`[propext, Classical.choice, Quot.sound]` (checked on a temp copy with `#print axioms` appended).
It has NOT been independently reviewed and has NOT been moved into `work/lean`; both are for the
executor (ACCEPT_CYCLE.md).  Line counts below are the actual counts in the file (declaration
statement + proof), 1342 lines total, 1132 lines of chain + assembly.

---

## 0. Route chosen and why

The printed proof (sm-3:1546-1580) is followed step by step:

1. Model: component 1 is the closed polygon `A = (D.Γ.comp i).P : LabelledTuple m`, component 2 is
   `B = (D.Γ.comp j).P : LabelledTuple n`; the "finite polygonal page model" of the text is the
   Lean `Diagram` itself (nothing to replace).
2. "Choose an auxiliary point `o` off the finitely many lines …": `exists_good_apex`, built on
   `exists_point_off_finite_lines` (a finite union of proper lines does not fill the plane).
3. "Orient the triangle chain `[o, v_j, v_{j+1}]` … its coefficient is its determinant sign":
   `triD o v w = det (v - o) (w - o)`; the triangle interior is the open region where
   `triD * lineFn g x > 0` for the three side-line functions `lineFn g x = det (dir g) (x - tail g)`.
4. "For one positively oriented triangle, a closed transverse path has as many entries into its
   interior as exits, counted with sign … Thus its algebraic intersection sum with that boundary
   is zero. Reversing triangle orientation negates the sum and still gives zero":
   `tri_edge_count` (one edge of `A`), `tri_polygon_sum` (the closed polygon `A`, telescoping over
   `ZMod m`).  The orientation sign is carried as the factor `sgn(triD)`, so both orientations are
   one statement.
5. "Summing over the finitely many fan triangles, each radial edge occurs once in each orientation
   and cancels. Their boundary chain is exactly component 2": `fan_triangle_sides` (side 0 of
   triangle `q` is `+radialSum q`, side 2 is `−radialSum (q+1)`, side 1 is the edge `f_q` of `B`)
   and `fan_sum_zero` (telescoping over `ZMod n`).
6. "At each mixed crossing the decorated sign is either the fixed-order determinant sign or its
   negative … Their total differs from the zero fixed-order sum by twice an integer … If the
   over-component is constant … the total is zero": `sign_mixed_eq`, `mixedSignSum_eq_fixed_add`,
   `mixedSignSum_eq_fixed_of_over_fst`, `mixedSignSum_eq_neg_fixed_of_over_snd`.

**Where the topology went.** The only non-algebraic step is 4 ("as many entries as exits").  It is
reduced to a purely one-dimensional statement, `affine_family_count`: for a finite family of affine
functions `φ g t = c g + t * d g` on `[0,1]` (one per bounding half-plane of a convex region — here
three), with the inside indicator `inside t = [∀ g, 0 < φ g t]` and *events* = transverse zeros of
one `φ g` at a parameter in `(0,1)` where all other `φ g'` are positive (= the path crosses the OPEN
side `g`), one has `inside 1 − inside 0 = Σ_{events} sgn(d g)`.  This is proved without sorting
the events, by: entries are unique (`entry_unique`), exits are unique (`exit_unique`), and a
first-zero / last-zero argument (`exists_exit_event` / `exists_entry_event`) produces the required
event in each of the four (inside 0, inside 1) cases.  No Jordan curve theorem, no connectedness,
no continuity beyond affine arithmetic on ℝ.  (The task suggested "a finite sorted list of crossing
parameters"; the uniqueness-plus-first-zero formulation makes the sorted-list induction unnecessary
for a convex region and was cheaper; the sorted-list version remains the fallback for a non-convex
region, which never arises here.)

**Correspondence of hypotheses.**  The event definition contains exactly the genericity the text
invokes: `d g ≠ 0` = transversality of the edge to the side line; "all other `φ g'` positive at the
zero" = the crossing point is in the open side (barycentric characterisation, `mem_openSide_of_lineFn`
/ `lineFn_of_mem_openSide`); `GenericFamily.no_double_zero` = the edge contains no vertex of the
triangle (two side lines meet only at a vertex, `vertex_of_two_lineFn`); `GenericFamily.start_off /
end_off` = the endpoints of the edge are off the closed boundary.

---

## 1. Dependency order (= file order)

```
Part 1 (1-D)      affEval, zeroAt, IsEvent, GenericFamily
                  affEval_zeroAt → affEval_eq_mul → affEval_pos_iff_of_pos/neg
                  affEval_pos_of_between, affEval_pos_of_between'
                  entry_unique, exit_unique
                  reflC, reflD, affEval_refl, zeroAt_refl, isEvent_refl_iff, genericFamily_refl
                  [Fintype ι] inside, inside_eq_one_iff, inside_eq_zero_iff, inside_eq_zero_or_one
                  not_entry_of_inside_zero, not_exit_of_inside_one
                  exists_exit_event → exists_entry_event (by reflection)
                  exists_exit_of_one_zero, exists_entry_of_zero_one, entry_iff_exit_of_zero_zero
                  sum_ite_unique, sum_event_sign_eq → affine_family_count
Part 2 (plane)    Seg, edgeSegment_eq_Seg (rfl), Seg_symm, eq_of_two_dets, coe_sign_*
                  triTail/triHead/triDir/triSide/triD/lineFn/triInside
                  lineFn_add_smul, tri_reconstruct, lineFn_sum
                  lineFn_openSide_vals, vertex_of_two_lineFn, lineFn_of_mem_openSide,
                  mem_openSide_of_lineFn
                  segC/segD, affEval_seg, inside_seg_zero/one, SegGeneric
                  isEvent_iff_meets, genericFamily_seg → tri_edge_count
                  zmod_telescope → tri_polygon_sum
Part 3 (apex)     exists_point_off_finite_lines → exists_good_apex
Part 4 (fan)      segGeneric_fan, radialSum, fan_triangle_sides → fan_sum_zero
Part 5 (diagram)  isCrossing_pair_iff_of_fst_ne → mixedPair_iff; sum_sigma_fst_eq
                  fixedOrderSum, fixedOrderSum_eq_polygon_sum → fixedOrderSum_eq_zero
                  sign_mixed_eq → corrSum, mixedSignSum_eq_fixed_add,
                  mixedSignSum_eq_fixed_of_over_fst, mixedSignSum_eq_neg_fixed_of_over_snd
Assembly          zero_link (fields from fixedOrderSum_eq_zero + the three Part-5 lemmas)
```

Imports: only `SM.LinkDiagram` (which brings `Polygon`, `Segment`, `Chirotope`, `RegularLocus`,
Mathlib).  Library facts used: `det_swap`, `det_add_right`, `det_smul_right`, `det_smul_self`,
`regular_iff_edges`, `Shadow.isCrossing_pair`, `Adjacent.fst_eq`, `IncidentTail.fst_eq`,
`Adjacent.refl`, `Diagram.eq_under_of_mem_of_ne`, `Diagram.mem_iff`, `Diagram.over_mem`,
`Diagram.over_ne_under`, `Shadow.mem_iff_eq_or_other`; Mathlib: `Finset.exists_min_image`,
`Infinite.exists_notMem_finset`, `Fintype.sum_sigma`, `Fintype.sum_eq_single`,
`Fin.sum_univ_three`, `Equiv.sum_comp`, `Finset.sum_comm`, `sign_mul`, `Left.sign_neg`,
`sign_eq_one_iff`, `sign_eq_neg_one_iff`, `mul_div_mul_left`, `field_simp`, `linear_combination`,
`nlinarith`, `fin_cases`.

---

## 2. Lemmas: exact statements, sketches, actual lines

All in `namespace SM.ZeroLinkA` unless noted; `open SM.Link Classical`.  "lines" = statement +
proof as in the file.

### Part 1 — one-dimensional counting (`section OneDim`, `variable {ι : Type*}`)

```lean
def affEval (c d : ι → ℝ) (g : ι) (t : ℝ) : ℝ := c g + t * d g
noncomputable def zeroAt (c d : ι → ℝ) (g : ι) : ℝ := -c g / d g
def IsEvent (c d : ι → ℝ) (g : ι) : Prop :=
  d g ≠ 0 ∧ 0 < zeroAt c d g ∧ zeroAt c d g < 1 ∧ ∀ g', g' ≠ g → 0 < affEval c d g' (zeroAt c d g)
structure GenericFamily (c d : ι → ℝ) : Prop where
  no_double_zero : ∀ t, 0 ≤ t → t ≤ 1 → ∀ g g', g ≠ g' → affEval c d g t = 0 → affEval c d g' t ≠ 0
  start_off : ∀ g, affEval c d g 0 = 0 → ∃ g', g' ≠ g ∧ affEval c d g' 0 ≤ 0
  end_off : ∀ g, affEval c d g 1 = 0 → ∃ g', g' ≠ g ∧ affEval c d g' 1 ≤ 0
```

| lemma | statement | sketch | lines |
|---|---|---|---|
| `affEval_zeroAt` | `d g ≠ 0 → affEval c d g (zeroAt c d g) = 0` | unfold, `field_simp`, `ring` | 4 |
| `affEval_eq_mul` | `d g ≠ 0 → affEval c d g t = d g * (t - zeroAt c d g)` | same | 5 |
| `affEval_pos_iff_of_pos` | `0 < d g → (0 < affEval c d g t ↔ zeroAt c d g < t)` | rewrite by `affEval_eq_mul`; sign of a product | 11 |
| `affEval_pos_iff_of_neg` | `d g < 0 → (0 < affEval c d g t ↔ t < zeroAt c d g)` | same | 11 |
| `affEval_pos_of_between` | `0 ≤ φ t₀ → 0 < φ t₁ → t₀ < t → t ≤ t₁ → 0 < φ t` | `(t₁−t₀) φ t = (t₁−t) φ t₀ + (t−t₀) φ t₁` (ring), then positivity | 11 |
| `affEval_pos_of_between'` | mirror: `0 < φ t₀ → 0 ≤ φ t₁ → t₀ ≤ t → t < t₁ → 0 < φ t` | same identity | 14 |
| `entry_unique` | `IsEvent g₁ → IsEvent g₂ → 0 < d g₁ → 0 < d g₂ → g₁ = g₂` | wlog `zeroAt g₁ ≤ zeroAt g₂`; at `zeroAt g₁` the event says `φ g₂ > 0`, but `φ g₂` is increasing with zero later, so `≤ 0` | 10 |
| `exit_unique` | same with `d < 0` | mirror | 10 |
| `reflC`, `reflD` | `reflC c d g = c g + d g`, `reflD d g = -d g` (the family of `t ↦ 1 − t`) | defs | 2 |
| `affEval_refl` | `affEval (reflC c d) (reflD d) g t = affEval c d g (1 - t)` | `ring` | 3 |
| `zeroAt_refl` | `d g ≠ 0 → zeroAt (reflC c d) (reflD d) g = 1 - zeroAt c d g` | `field_simp; ring` | 4 |
| `isEvent_refl_iff` | `IsEvent (reflC c d) (reflD d) g ↔ IsEvent c d g` | unfold; transport the four conjuncts through the two lemmas above | 17 |
| `genericFamily_refl` | `GenericFamily c d → GenericFamily (reflC c d) (reflD d)` | `no_double_zero` at `1 − t`; `start_off ↔ end_off` swap | 15 |

`variable [Fintype ι]` from here.

```lean
noncomputable def inside (c d : ι → ℝ) (t : ℝ) : ℤ := if ∀ g, 0 < affEval c d g t then 1 else 0
```

| lemma | statement | sketch | lines |
|---|---|---|---|
| `inside_eq_one_iff` | `inside c d t = 1 ↔ ∀ g, 0 < affEval c d g t` | `split_ifs` | 5 |
| `inside_eq_zero_iff` | `inside c d t = 0 ↔ ∃ g, affEval c d g t ≤ 0` | `split_ifs`, `push Not` | 8 |
| `inside_eq_zero_or_one` | `inside c d t = 0 ∨ inside c d t = 1` | `split_ifs` | 3 |
| `not_entry_of_inside_zero` | `inside c d 0 = 1 → IsEvent c d g → d g < 0` | an entry has `φ g 0 < 0` (`affEval_pos_iff_of_pos` at `t = 0 < zeroAt`) | 7 |
| `not_exit_of_inside_one` | `inside c d 1 = 1 → IsEvent c d g → 0 < d g` | mirror | 13 |
| `exists_exit_event` | `GenericFamily c d → 0 ≤ t₀ → t₀ < 1 → (∀ g, 0 ≤ φ g t₀) → (∀ g, φ g t₀ = 0 → 0 < d g) → (∃ g, φ g 1 ≤ 0) → ∃ g, IsEvent c d g ∧ d g < 0 ∧ t₀ < zeroAt c d g` | `S := {g ∣ φ g 1 ≤ 0}` nonempty; each `g ∈ S` has `φ g t₀ > 0` (else it would be increasing), hence `d g < 0` and `zeroAt g ∈ (t₀, 1]`; take `g₀` minimising `zeroAt` (`Finset.exists_min_image`).  Others at `zeroAt g₀`: members of `S` are `≥ 0` there (decreasing, later zero) and `≠ 0` by `no_double_zero`; non-members are `> 0` by `affEval_pos_of_between`.  `zeroAt g₀ = 1` would make `t = 1` an event point, contradicting `end_off`. | 57 |
| `exists_entry_event` | mirror: `0 < t₁ → t₁ ≤ 1 → (∀ g, 0 ≤ φ g t₁) → (∀ g, φ g t₁ = 0 → d g < 0) → (∃ g, φ g 0 ≤ 0) → ∃ g, IsEvent c d g ∧ 0 < d g ∧ zeroAt c d g < t₁` | apply `exists_exit_event` to the reflected family with `t₀ = 1 − t₁`; transport back with `isEvent_refl_iff`, `zeroAt_refl` | 19 |
| `exists_exit_of_one_zero` | `inside c d 0 = 1 → inside c d 1 = 0 → ∃ g, IsEvent c d g ∧ d g < 0` | `exists_exit_event` at `t₀ = 0` | 6 |
| `exists_entry_of_zero_one` | `inside c d 0 = 0 → inside c d 1 = 1 → ∃ g, IsEvent c d g ∧ 0 < d g` | `exists_entry_event` at `t₁ = 1` | 9 |
| `entry_iff_exit_of_zero_zero` | `inside c d 0 = 0 → inside c d 1 = 0 → ((∃ g, IsEvent c d g ∧ 0 < d g) ↔ (∃ g, IsEvent c d g ∧ d g < 0))` | an entry `g⁺` gives `t₀ = zeroAt g⁺` satisfying the hypotheses of `exists_exit_event` (all `φ ≥ 0` there, only `φ g⁺` vanishes and it is increasing); an exit gives `t₁` for `exists_entry_event` | 28 |
| `sum_ite_unique` | `(∀ g g', P g → P g' → g = g') → (∑ g, if P g then (1:ℤ) else 0) = if ∃ g, P g then 1 else 0` | `Fintype.sum_eq_single` | 11 |
| `sum_event_sign_eq` | `∑ g, [IsEvent g]·sgn(d g) = ∑ g, [IsEvent g ∧ 0 < d g] − ∑ g, [IsEvent g ∧ d g < 0]` | termwise, `d g ≠ 0` at events | 14 |
| `affine_family_count` | `GenericFamily c d → inside c d 1 - inside c d 0 = ∑ g, if IsEvent c d g then (sgn (d g) : ℤ) else 0` | rewrite by the two lemmas above and uniqueness; four cases on `(inside 0, inside 1) ∈ {0,1}²`: (1,1) no events; (1,0) exit exists, no entry; (0,1) entry exists, no exit; (0,0) entry ↔ exit | 30 |

### Part 2 — segments and fan triangles (`section Triangle`)

```lean
def Seg (a b : Plane) : Set Plane := {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = a + t • (b - a)}
theorem edgeSegment_eq_Seg (P : LabelledTuple n) (i : ZMod n) : edgeSegment P i = Seg (P i) (P (i + 1)) := rfl
def triTail (o v w) : Fin 3 → Plane := ![o, v, w]      -- sides [o,v], [v,w], [w,o]
def triHead (o v w) : Fin 3 → Plane := ![v, w, o]
def triDir  (o v w) (g) : Plane := triHead o v w g - triTail o v w g
def triSide (o v w) (g) : Set Plane := Seg (triTail o v w g) (triHead o v w g)
def triD    (o v w) : ℝ := det (v - o) (w - o)
def lineFn  (o v w) (g) (x) : ℝ := det (triDir o v w g) (x - triTail o v w g)
noncomputable def triInside (o v w) (x) : ℤ := if ∀ g, 0 < triD o v w * lineFn o v w g x then 1 else 0
def segC (o v w) (a _b) : Fin 3 → ℝ := fun g => triD o v w * lineFn o v w g a
def segD (o v w) (a b)  : Fin 3 → ℝ := fun g => triD o v w * det (triDir o v w g) (b - a)
structure SegGeneric (o v w a b : Plane) : Prop where
  hD : triD o v w ≠ 0
  transverse : ∀ g, (Seg a b ∩ triSide o v w g).Nonempty → det (b - a) (triDir o v w g) ≠ 0
  no_vertex : ∀ g, triTail o v w g ∉ Seg a b
  start_off : ∀ g, a ∉ triSide o v w g
  end_off : ∀ g, b ∉ triSide o v w g
```

| lemma | statement | sketch | lines |
|---|---|---|---|
| `Seg_symm` | `Seg a b = Seg b a` | `t ↦ 1 − t` both ways | 6 |
| `left_mem_Seg`, `right_mem_Seg` | endpoints in `Seg` (convenience) | `t = 0`, `t = 1` | 2 |
| `not_mem_Seg_of_det` | `det (b - a) (x - a) ≠ 0 → x ∉ Seg a b` (convenience) | `det_smul_self` | 5 |
| `eq_of_two_dets` | `det d₁ d₂ ≠ 0 → det d₁ (x - p) = 0 → det d₂ (x - p) = 0 → x = p` | Cramer via `linear_combination` (kept as a general helper; the triangle uses `tri_reconstruct` instead) | 11 |
| `coe_sign_mul_self` | `x ≠ 0 → (sgn x : ℤ) * (sgn x : ℤ) = 1` | two cases, `decide` | 5 |
| `coe_sign_mul` | `(sgn (x*y) : ℤ) = sgn x * sgn y` | `sign_mul` | 4 |
| `coe_sign_det_swap` | `(sgn (det w u) : ℤ) = -(sgn (det u w))` | `det_swap`, `Left.sign_neg` | 3 |
| `triHead_eq_triTail_succ` | `triHead o v w g = triTail o v w (g + 1)` | `fin_cases; rfl` | 2 |
| `mem_triSide_iff` | `x ∈ triSide g ↔ ∃ s, 0 ≤ s ∧ s ≤ 1 ∧ x = triTail g + s • triDir g` | `Iff.rfl` | 3 |
| `triSide_zero/one/two`, `triDir_zero/one/two` | `triSide o v w 1 = Seg v w`, `triDir o v w 2 = o - w`, … | `rfl` | 6 |
| `lineFn_add_smul` | `lineFn g (a + t • u) = lineFn g a + t * det (triDir g) u` | `det_add_right`, `det_smul_right` | 7 |
| `tri_reconstruct` | `triD ≠ 0 → x = o + (lineFn 2 x / triD) • (v - o) + (lineFn 0 x / triD) • (w - o)` | coordinatewise: `triD * (x − o)ᵢ = lineFn 2 x * (v − o)ᵢ + lineFn 0 x * (w − o)ᵢ` by `ring`, then `field_simp` | 23 |
| `lineFn_sum` | `lineFn 0 x + lineFn 1 x + lineFn 2 x = triD` | coordinates, `ring` | 8 |
| `div_pos_of_mul_pos'` | `D ≠ 0 → 0 < D * L → 0 < L / D` | `L / D = (D L)/(D D)` | 6 |
| `lineFn_openSide_vals` | at `x = triTail g + s • triDir g`: `lineFn g x = 0`, `lineFn (g+1) x = (1 - s) * triD`, `lineFn (g+2) x = s * triD` | `fin_cases g`, coordinates, `ring` | 10 |
| `fin3_ne_cases` | `g' ≠ g → g' = g + 1 ∨ g' = g + 2` | `fin_cases`×2 | 2 |
| `vertex_of_two_lineFn` | `triD ≠ 0 → g ≠ g' → lineFn g x = 0 → lineFn g' x = 0 → ∃ g'', x = triTail g''` | `tri_reconstruct` + `lineFn_sum`: two zero coordinates fix the third as `triD`, so `x ∈ {o, v, w}` | 35 |
| `lineFn_of_mem_openSide` | `triD ≠ 0 → 0 < s → s < 1 → lineFn g (tail g + s•dir g) = 0 ∧ ∀ g' ≠ g, 0 < triD * lineFn g' (…)` | `lineFn_openSide_vals`, `fin3_ne_cases`, `s·triD² > 0` | 14 |
| `mem_openSide_of_lineFn` | `triD ≠ 0 → lineFn g x = 0 → (∀ g' ≠ g, 0 < triD * lineFn g' x) → ∃ s, 0 < s ∧ s < 1 ∧ x = tail g + s•dir g` | `s := lineFn (g+2) x / triD`; positivity from `div_pos_of_mul_pos'`; `1 − s = lineFn (g+1) x / triD` from `lineFn_sum`; the point identity from `tri_reconstruct` per `g` | 44 |
| `affEval_seg` | `affEval (segC a b) (segD a b) g t = triD * lineFn g (a + t • (b - a))` | `lineFn_add_smul`, `ring` | 5 |
| `inside_seg_zero`, `inside_seg_one` | `inside (segC a b) (segD a b) 0 = triInside a`, `… 1 = triInside b` | `simp only [affEval_seg]` | 9 |
| `isEvent_iff_meets` | `SegGeneric o v w a b → (IsEvent (segC a b) (segD a b) g ↔ (Seg a b ∩ triSide g).Nonempty)` | (→) the zero parameter gives a point on line `g` with the other two functions positive; `mem_openSide_of_lineFn`.  (←) a common point `a + t u = tail g + s dir g`; `d g ≠ 0` by `transverse`; `s ∉ {0,1}` by `no_vertex` (with `triHead_eq_triTail_succ`); `lineFn_of_mem_openSide`; `t = zeroAt` by `affEval_eq_mul`; `t ∉ {0,1}` by `start_off`/`end_off` | 67 |
| `genericFamily_seg` | `SegGeneric o v w a b → GenericFamily (segC a b) (segD a b)` | `no_double_zero` from `vertex_of_two_lineFn` + `no_vertex`; `start_off`/`end_off` from `mem_openSide_of_lineFn` + `start_off`/`end_off` | 38 |
| `tri_edge_count` | `SegGeneric o v w a b → ∑ g : Fin 3, [Seg a b ∩ triSide g ≠ ∅]·sgn det (b - a) (triDir g) = sgn(triD) * (triInside a - triInside b)` | `affine_family_count` for the segment family; rewrite events by `isEvent_iff_meets`; `sgn (segD g) = sgn triD · sgn det(dir g, u) = −sgn triD · sgn det(u, dir g)`; finish with `linear_combination σ * hcount - S * hσσ` using `σ² = 1` | 23 |
| `zmod_telescope` | `[NeZero n] → ∑ q : ZMod n, (f q - f (q + 1)) = 0` | `Equiv.sum_comp (Equiv.addRight 1)` | 10 |
| `tri_polygon_sum` | `(∀ p, SegGeneric o v w (A p) (A (p + 1))) → ∑ p, ∑ g, [edgeSegment A p ∩ triSide g ≠ ∅]·sgn det (edge A p) (triDir g) = 0` | each `p`-term is `sgn triD · (χ(A p) − χ(A (p+1)))` by `tri_edge_count`; telescope | 27 |

### Part 3 — the apex (`section Apex`)

| lemma | statement | sketch | lines |
|---|---|---|---|
| `exists_point_off_finite_lines` | `(∀ ℓ ∈ L, ℓ.2 ≠ 0) → ∃ o, ∀ ℓ ∈ L, det ℓ.2 (o - ℓ.1) ≠ 0` for `L : Finset (Plane × Plane)` = (base, direction) | Step 1: slope `μ` outside `L.image (d₂/d₁)`, so `det d (1, μ) ≠ 0` for every line (`d₁ = 0` forces `d₂ ≠ 0`).  Step 2: `s` outside `L.image (det d p / det d (1,μ))`; `o := s • (1, μ)`; `det d (o − p) = s·det d (1,μ) − det d p ≠ 0`.  Uses `Infinite.exists_notMem_finset` twice. | 32 |
| `exists_good_apex` | `(∀ p, edge A p ≠ 0) → (∀ q, edge B q ≠ 0) → (∀ p q, A p ∉ edgeSegment B q) → ∃ o, (∀ q, triD o (B q) (B (q+1)) ≠ 0) ∧ (∀ p q, det (edge A p) (B q - o) ≠ 0) ∧ (∀ p, o ∉ edgeSegment A p) ∧ (∀ p q, A p ∉ Seg o (B q))` | `L = L1 ∪ L2 ∪ L3 ∪ L4` with `L1 = {(B q, edge B q)}`, `L2 = {(B q, edge A p)}`, `L3 = {(A p, edge A p)}`, `L4 = {(A p, B q − A p)}`; nonzero directions from regularity and `A p ≠ B q` (from `A p ∉ edgeSegment B q ∋ B q`).  Then: `triD = det (edge B q) (o − B q)` (ring); `det u (B q − o) = −det u (o − B q)`; a point of `edgeSegment A p` is `A p + t·edge`, killing `det (edge) (o − A p)`; a point `A p = o + t (B q − o)` kills `det (B q − A p) (o − A p)`. | 65 |

### Part 4 — the fan (`section Fan`, `A : LabelledTuple m`, `B : LabelledTuple n`)

```lean
noncomputable def radialSum (o : Plane) (q : ZMod n) : ℤ :=
  ∑ p : ZMod m, if (edgeSegment A p ∩ Seg o (B q)).Nonempty then (sgn (det (edge A p) (B q - o)) : ℤ) else 0
```

| lemma | statement | sketch | lines |
|---|---|---|---|
| `segGeneric_fan` | with `hAB, hBA, htr, ho₁..ho₄` as in `fan_sum_zero`/`exists_good_apex`: `SegGeneric o (B q) (B (q + 1)) (A p) (A (p + 1))` | `fin_cases g` per field: side 0 transversal by `ho₂`, side 1 by `htr`, side 2 by `ho₂ (q+1)` (negated det); vertices `o` (`ho₃`), `B q`, `B (q+1)` (`hBA`); endpoints off side 0/2 (`ho₄`, `Seg_symm`) and side 1 (`hAB`) | 43 |
| `fan_triangle_sides` | `∑ p, ∑ g, [e_p ∩ side_q g ≠ ∅]·sgn det (edge A p) (triDir_q g) = radialSum o q + (∑ p, [e_p ∩ f_q ≠ ∅]·sgn det (edge A p) (edge B q)) − radialSum o (q + 1)` | `Fin.sum_univ_three`; sides 0 and 1 are `rfl`; side 2: `Seg (B (q+1)) o = Seg o (B (q+1))` and `det u (o − B) = −det u (B − o)`, `Left.sign_neg`, `neg_ite` | 34 |
| `fan_sum_zero` | `(∀ p, edge A p ≠ 0) → (∀ q, edge B q ≠ 0) → (∀ p q, A p ∉ edgeSegment B q) → (∀ p q, B q ∉ edgeSegment A p) → (∀ p q, (edgeSegment A p ∩ edgeSegment B q).Nonempty → det (edge A p) (edge B q) ≠ 0) → ∑ p, ∑ q, [e_p ∩ f_q ≠ ∅]·sgn det (edge A p) (edge B q) = 0` | apex from `exists_good_apex`; for each `q`, `tri_polygon_sum` + `fan_triangle_sides` give `∑_p F(p,q) = R(q+1) − R q`; `Finset.sum_comm` and `zmod_telescope` | 29 |

### Part 5 — diagram glue and sign bookkeeping (`section Diagram`)

```lean
noncomputable def fixedOrderSum (D : Diagram) (i j : Fin D.Γ.c) : ℤ :=
  ∑ s, ∑ t, if D.Γ.MixedPair i j s t then (sgn (det (D.Γ.dir s) (D.Γ.dir t)) : ℤ) else 0   -- the field expression verbatim
noncomputable def corrSum (D : Diagram) (i j : Fin D.Γ.c) : ℤ :=
  ∑ s, ∑ t, if h : D.Γ.MixedPair i j s t then
    (if D.overStrand ⟨{s, t}, h.2.2⟩ = s then 0 else -(sgn (det (D.Γ.dir s) (D.Γ.dir t)) : ℤ)) else 0
```

| lemma | statement | sketch | lines |
|---|---|---|---|
| `isCrossing_pair_iff_of_fst_ne` | `s.1 ≠ t.1 → (Γ.IsCrossing {s, t} ↔ (Γ.seg s ∩ Γ.seg t).Nonempty)` | strands on different components are not adjacent (`Adjacent.fst_eq`); unpack `{s,t} = {s',t'}` by membership | 16 |
| `mixedPair_iff` | `i ≠ j → (Γ.MixedPair i j s t ↔ s.1 = i ∧ t.1 = j ∧ (Γ.seg s ∩ Γ.seg t).Nonempty)` | previous lemma | 8 |
| `sum_sigma_fst_eq` | `(∀ s, s.1 ≠ i → F s = 0) → ∑ s : Σ i', ZMod (k i'), F s = ∑ p : ZMod (k i), F ⟨i, p⟩` | `Fintype.sum_sigma`, `Fintype.sum_eq_single` | 7 |
| `fixedOrderSum_eq_polygon_sum` | `i ≠ j → fixedOrderSum D i j = ∑ p : ZMod (comp i).k, ∑ q : ZMod (comp j).k, [edgeSegment (comp i).P p ∩ edgeSegment (comp j).P q ≠ ∅]·sgn det (edge (comp i).P p) (edge (comp j).P q)` | `sum_sigma_fst_eq` twice, `mixedPair_iff`, `true_and`, `rfl` (`seg`/`dir` unfold to `edgeSegment`/`edge`) | 26 |
| `fixedOrderSum_eq_zero` | `i ≠ j → fixedOrderSum D i j = 0` | `fan_sum_zero` with: nonzero edges from `regular_iff_edges` (`D.generic.regular`); `A p ∉ f_q` and `B q ∉ e_p` from `D.generic.tail_off` (not `IncidentTail` across components, `IncidentTail.fst_eq`); transversality from `D.generic.transverse` (not `Adjacent` across components) | 19 |
| `sign_mixed_eq` | `(h : D.Γ.MixedPair i j s t) → (D.sign ⟨{s,t}, h.2.2⟩ : ℤ) = if D.overStrand ⟨{s,t}, h.2.2⟩ = s then sgn det (dir s) (dir t) else −sgn det (dir s) (dir t)` | `s ≠ t` (a crossing's strands are not adjacent, `Adjacent.refl`); over ∈ {s,t}; the under strand is the other one (`eq_under_of_mem_of_ne`); `det_swap`, `Left.sign_neg` | 35 |
| `mixedSignSum_eq_fixed_add` | `mixedSignSum D i j = fixedOrderSum D i j + 2 * corrSum D i j` | termwise by `sign_mixed_eq`; `split_ifs <;> ring` | 15 |
| `mixedSignSum_eq_fixed_of_over_fst` | `(∀ s t h, D.overStrand ⟨{s,t},h.2.2⟩ = s) → mixedSignSum D i j = fixedOrderSum D i j` | termwise | 8 |
| `mixedSignSum_eq_neg_fixed_of_over_snd` | `(∀ s t h, D.overStrand ⟨{s,t},h.2.2⟩ = t) → mixedSignSum D i j = -fixedOrderSum D i j` | termwise; `over = t ≠ s` | 24 |

### Assembly (namespace `SM`, no `sorry`)

```lean
theorem zero_link : ZeroLinkData where
  fixed_order_sum := fun D i j hij => fixedOrderSum_eq_zero D i j hij
  half_sum_integer := fun D i j hij => ⟨corrSum D i j, by rw [mixedSignSum_eq_fixed_add, fixedOrderSum_eq_zero D i j hij, zero_add]⟩
  over_constant := fun D i j hij h => by rcases h with h | h; ...
```
(9 lines; the first field is definitionally `fixedOrderSum D i j = 0` — same `Classical.propDecidable`
instances because both files `open Classical`.)

**Totals.** 73 chain theorems (+ 12 defs/structures) + `zero_link`; 1132 lines of declarations,
1342 lines of file.  Original pre-proof estimate was 1225 lines of proof; actual is close.

---

## 3. Degenerate configurations and where each is excluded

| configuration | excluded / handled by |
|---|---|
| a mixed crossing at a vertex of `A` or `B` | `Generic.tail_off` (`A p ∉ edgeSegment B q`, `B q ∉ edgeSegment A p`, both directions, since `IncidentTail` needs equal components) → `SegGeneric.no_vertex` (sides 1: `B q`, `B (q+1)`) and `start_off`/`end_off` (side 1) |
| non-transverse meeting `e_p ∩ f_q` | `Generic.transverse` (not `Adjacent` across components) → `SegGeneric.transverse` (side 1) |
| `e_p` collinear with `f_q` but disjoint | allowed; then `segD 1 = 0`, no event at side 1 (events need `d ≠ 0` and `isEvent_iff_meets` (→) never applies), `inside ≡ 0` if `a` is on the line — the 1-D lemma tolerates constant `φ g` (only `no_double_zero`, `start_off`, `end_off` are assumed) |
| degenerate fan triangle (`o` on the line of `f_q`) | `exists_good_apex` (o₁): `o ∉ line(B q, edge B q)`; `edge B q ≠ 0` from `Generic.regular` (`regular_iff_edges`) |
| radial side `[o, B q]` parallel to `e_p` | (o₂): `o ∉ line(B q, edge A p)` — makes every radial side transverse to every edge of `A` unconditionally |
| radial side passes through a vertex of `A`; `A p` on a radial side | (o₄): `o ∉ line(A p, B q − A p)` (a genuine line since `A p ≠ B q` by `tail_off`); used for sides 0 and 2 via `Seg_symm` |
| `o` on an edge of `A` (a triangle vertex on the path) | (o₃): `o ∉ line(A p, edge A p)` |
| two side lines crossed at the same parameter (path through a triangle vertex) | `vertex_of_two_lineFn` (needs `triD ≠ 0`) + `no_vertex` → `GenericFamily.no_double_zero` |
| endpoint of an edge exactly on a side line but outside the closed side | allowed: `start_off`/`end_off` of `GenericFamily` only forbid endpoints in the OPEN side (contrapositive of `mem_openSide_of_lineFn`), which `SegGeneric.start_off/end_off` (closed sides) implies |
| self-intersections of `A` or of `B` | irrelevant: the argument counts traversed edges `p` and `q`, never distinct points ("counts traversed occurrences") |
| two mixed crossings on one pair `(e_p, f_q)` | impossible for transverse segments, and not needed: the summand is a 0/1 indicator per ordered pair, exactly as `MixedPair` |
| `k ≥ 3`, `c ≥ 1` | never used beyond `NeZero k` (Fintype of `ZMod k`), supplied by `PolyComp.instNeZeroK` |

**Finiteness argument for `o`** (`exists_point_off_finite_lines`): the forbidden set is a finite
union of lines `{x ∣ det d (x − p) = 0}` with `d ≠ 0`, indexed by the `Finset` `L` (four
`Finset.image`s of `univ` over `ZMod m`, `ZMod n`, `ZMod m × ZMod n`).  A line is parallel to
`(1, μ)` for at most one `μ` (`μ = d₂/d₁`, none if `d₁ = 0`), so some `μ` outside a finite set
works for all lines; along `s ↦ s • (1, μ)` each line is met at exactly one `s`, so some `s`
outside a finite set misses them all.  Both choices use `Infinite.exists_notMem_finset` on ℝ.

---

## 4. The three riskiest steps (as assessed before proving) and what happened

1. **`exists_exit_event` / `affine_family_count` (the 1-D core).**  Risk: inequality bookkeeping
   with `zeroAt = −c/d`, sign cases, and the case split.  Mitigation used: characterise
   `0 < φ g t` as `zeroAt < t` / `t < zeroAt` once (`affEval_pos_iff_of_*`), do the last-zero case
   by reflection `t ↦ 1 − t` instead of a second 60-line proof, and split the count as
   `[∃ entry] − [∃ exit]` via uniqueness rather than sorting.  Fallback (not needed): a
   sorted-list induction over `Finset` of event parameters, or specialising to `ι = Fin 3` and
   enumerating sign patterns.  Outcome: proved; 57 + 30 lines.
2. **`isEvent_iff_meets` and the barycentric lemmas.**  Risk: `fin_cases` coordinate algebra over
   `ℝ × ℝ` with `smul`/`det` blowing up, and the syntactic mismatch between `triDir g` and
   `triHead g − triTail g` in `rw`.  Mitigation used: one reconstruction identity
   (`tri_reconstruct`) and one sum identity (`lineFn_sum`) make all three barycentric facts
   mechanical; `mem_triSide_iff` (an `Iff.rfl`) fixes the syntactic form.  Fallback: per-side
   lemmas with `Prod.ext` + `nlinarith`.  Outcome: proved; 67 + 44 + 35 lines.
3. **`fixedOrderSum_eq_polygon_sum` (Σ-type reindexing, `Decidable` instances).**  Risk: the
   dependent index `Fin D.Γ.c → ZMod (comp i).k` and `if MixedPair` vs `if Nonempty` instance
   mismatch.  Mitigation used: a generic `sum_sigma_fst_eq` and `open Classical` in both files so
   instances coincide; the last step is `rfl`.  Fallback: restate `fan_sum_zero` over strands.
   Outcome: proved on the first attempt (26 lines).

**Remaining risks (for the executor).**
- Acceptance path: the file must be moved under `work/lean` (e.g. `SM/ZeroLink.lean` with the
  three statement definitions taken from the accepted statement module, not re-declared), the row
  transcribed against sm-3:1538-1545, and independently reviewed per ACCEPT_CYCLE.md.  Nothing in
  the proof depends on unaccepted declarations.
- Name churn: this Mathlib pin deprecates `if_pos/if_neg/dif_pos/dif_neg` (now
  `ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right`) and `push_neg` (`push Not`); the file
  uses the new names and compiles warning-free, but a different pin would need the old ones.
- The statement's `over_constant` hypothesis is exactly as printed ("one component is always over
  the other"); the proof does not need `i ≠ j` for the sign bookkeeping, only for
  `fixedOrderSum_eq_zero`.
