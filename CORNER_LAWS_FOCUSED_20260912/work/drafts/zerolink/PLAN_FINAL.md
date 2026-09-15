# PLAN_FINAL — mp:zero-link (sm-3-statesum.tex:1538-1580, frame SM15)

Judge's decision, 2026-09-13 (UTC).  Target: `SM.zero_link : ZeroLinkData` for the FIXED statement
`work/drafts/ZeroLink_statement.lean` (three fields: `fixed_order_sum`, `half_sum_integer`,
`over_constant`).  Final skeleton: `work/drafts/zerolink/Skeleton_FINAL.lean`.

Check command (from `work/lean`): `lake env lean ../drafts/zerolink/Skeleton_FINAL.lean`
— prints nothing (no errors, no warnings, no `sorry`).  With `#print axioms SM.zero_link` appended
on a temp copy: `[propext, Classical.choice, Quot.sound]`.  Both facts re-verified by the judge.

---

## 0. Verdict

**Winner: Plan A** (`PLAN_A.md` / `Skeleton_A.lean`).  `Skeleton_FINAL.lean` IS Plan A's file with
three cosmetic changes and no change to any proof: namespace `SM.ZeroLinkA` → `SM.ZeroLink`, a new
header docstring, and four `UNIT n` banner comments delimiting the prover/review units.

| criterion | A | B | why |
|---|---|---|---|
| (a) mathematical correctness against the fixed statement | **10** | 8 | A: every field is closed by Lean against a byte-identical copy of the statement (diffed: `sed -n 15,47p ZeroLink_statement.lean` vs `sed -n 27,59p Skeleton_A.lean`, no difference); standard axioms only; no `sorry`, `axiom`, `native_decide`, `admit`, `set_option`, or `local instance` anywhere (grepped).  All degenerate configurations are discharged by the compiled proof (table in §4).  B: the plan is mathematically right (same fan route; `hend`/`hvert` are the correct 1-D genericity; `Meets` with open parameters is correctly bridged to `MixedPair` by `tail_off`), and its statement copy is also byte-identical; but the load-bearing 1-D lemma `affine_triple_jump`, its six sub-lemmas, and the 2-D translation `segment_triangle_jump` are `sorry` (8 of 52), so the correctness of the core is asserted, not certified. |
| (b) provability in Lean (existing library + Mathlib) | **10** | 7 | A is proved (1347 lines, ~5 s to elaborate).  B has ~525 estimated lines left in exactly the fiddly parts: `Metric.isOpen_iff`/`isOpen_iInter_of_finite` neighbourhood extraction (L2a/L2a'), `intermediate_value_Icc(')` on `min` of three affine maps with vanishing-index extraction (L2d/L2d', 2×60), the P⁰/P⁺/P⁻ case analysis with a two-marked-index `Fin 3` sum (L2, 120), and the `![…]`-vs-`InTri` translation with rotated `meets_side_iff` (L3, 150).  B's own "Fallback B" (explicit roots `r k = -α k / β k`, an order statement decided by `linarith`) is essentially what A did — evidence that A's formulation is the cheaper one. |
| (c) minimality of geometric burden | **8** | 7 | Both use the printed fan from a finite apex `o` (the right choice; B's §0 correctly explains why ray casting and the closed-form sign identity are worse).  A's 1-D core is pure order/affine arithmetic on ℝ for an arbitrary `Fintype ι` — no open sets, no IVT, no continuity — the minimal possible topology.  Its 2-D layer costs one barycentric reconstruction (`tri_reconstruct`) + one sum identity (`lineFn_sum`), and `fin_cases` coordinate algebra over `![o,v,w]`; that vector indexing is the one place A is heavier than B's three explicit side functions.  B's geometric layer (L3a–L3d, proved) is slightly leaner, but its 1-D core imports metric topology and IVT, which is more than the problem needs. |

Total: A 28/30, B 22/30.

---

## 1. Chosen route (Plan A) and grafts from Plan B

The printed proof is followed step by step (line numbers refer to sm-3:1546-1580):

1. Model.  Component 1 is the closed polygon `A = (D.Γ.comp i).P : LabelledTuple m`, component 2 is
   `B = (D.Γ.comp j).P : LabelledTuple n`; the Lean `Diagram` is already the "finite polygonal page
   model", so nothing is replaced.
2. "Choose an auxiliary point `o` off the finitely many lines …": `exists_point_off_finite_lines`
   (a finite union of proper lines does not fill the plane) → `exists_good_apex` (four finite
   families of forbidden lines, §4).
3. "Orient the triangle chain `[o,v_j,v_(j+1)]` … its coefficient … is its determinant sign":
   `triD o v w = det (v - o) (w - o)`; the open triangle is the set of `x` with
   `∀ g, 0 < triD * lineFn g x`, where `lineFn g x = det (triDir g) (x - triTail g)` for the three
   sides `[o,v],[v,w],[w,o]`.
4. "A closed transverse path has as many entries into its interior as exits, counted with sign":
   `affine_family_count` (1-D) → `tri_edge_count` (one edge) → `tri_polygon_sum` (closed polygon,
   telescoping over `ZMod m`).  The orientation sign is the factor `sgn triD`, so both orientations
   are one statement ("Reversing triangle orientation negates the sum and still gives zero").
5. "Each radial edge occurs once in each orientation and cancels. Their boundary chain is exactly
   component 2": `fan_triangle_sides` + `fan_sum_zero` (telescoping over `ZMod n`).
6. "At each mixed crossing the decorated sign is either the fixed-order determinant sign or its
   negative … twice an integer … if the over-component is constant … zero": `sign_mixed_eq`,
   `mixedSignSum_eq_fixed_add`, `mixedSignSum_eq_fixed_of_over_fst`,
   `mixedSignSum_eq_neg_fixed_of_over_snd`; assembled in `zero_link`.

**Where the topology went.**  Only step 4 is non-algebraic, and it is reduced to a 1-D statement: for
a finite family of affine functions `φ g t = c g + t * d g` on `[0,1]` (one per bounding half-plane of
a convex region — three here), with `inside t = [∀ g, 0 < φ g t]` and *events* = zeros of one `φ g`
at a parameter in `(0,1)` with `d g ≠ 0` and all other `φ g'` positive there, one has
`inside 1 − inside 0 = Σ_events sgn (d g)`.  Proved without sorting: entries are unique
(`entry_unique`), exits are unique (`exit_unique`), and a first-zero argument
(`exists_exit_event`, via `Finset.exists_min_image`) plus its reflection `t ↦ 1 − t`
(`exists_entry_event`) supply the needed event in each of the four `(inside 0, inside 1)` cases.

**Grafts from Plan B — considered, and what was done.**  Nothing in B's proof text is needed: every
B lemma that is proved has a proved counterpart in A, and every B `sorry` is proved in A.  Applying a
graft would mean editing a verified proof for no gain, so none was applied to the Lean file.  For the
record:

| B item | status in FINAL |
|---|---|
| L5 `exists_point_off_lines [Fintype ι] (c v : ι → Plane)` (vertical-line trick, `Sum`-indexed families) | **not grafted.** A's `exists_point_off_finite_lines (L : Finset (Plane × Plane))` (slope trick) is proved and used by `exists_good_apex`.  B's `Fintype ι` interface would shorten the four `Finset.mem_union_*`/`mem_image_of_mem` membership proofs in `exists_good_apex` (~20 lines); recorded as an *optional* simplification for the acceptance port, not required. |
| L7 `mixedPair_iff_meets` via `crossing_pair_spec` and the open-parameter `Meets` | **not grafted.** A's `isCrossing_pair_iff_of_fst_ne` + `mixedPair_iff` work with the closed segments `Γ.seg s ∩ Γ.seg t` directly and match the summand by `rfl`, so no open/closed bridge is needed. |
| "`Generic.transverse` is not needed" (B §0) | **not adopted.** A consumes `D.generic.transverse` legitimately (side 1 of `SegGeneric.transverse`).  B is right that it is derivable from `tail_off` for collinear overlapping segments, but the field is in the accepted `Generic` and using it is simpler. |
| B §0's rejection of alternatives (ray casting from a diagram-dictated direction; the closed-form sign identity `χ = ¼(s_b' − s_b)(1 − σ_a σ_a')`) | **adopted into this plan as rationale** (§5): it explains why the finite apex `o` is the right choice and why no cheaper route exists. |
| B's `hend : (t = 0 ∨ t = 1) → (∀ k, 0 < g k t) ∨ ∃ k, g k t < 0` | equivalent to A's `GenericFamily.start_off/end_off` (contrapositive form); A's form is what `genericFamily_seg` produces from `mem_openSide_of_lineFn`.  No change. |

---

## 2. Ordered lemma list with exact statements

All statements below are copied mechanically from `Skeleton_FINAL.lean` (`-- Lnnn` = line in that
file).  Everything is in `namespace SM`, `open SM.Link Classical`; chain lemmas are in `SM.ZeroLink`;
`zero_link` is in `SM`.  Section variables: Unit 1 has `variable {ι : Type*}`,
`variable (c d : ι → ℝ)` (from L99), `variable [Fintype ι]` (from L237); Unit 2 has
`variable (o v w : Plane)` (from L529); Unit 3's `section Fan` has
`variable {m n : ℕ} [NeZero m] [NeZero n] (A : LabelledTuple m) (B : LabelledTuple n)` (with
`omit [NeZero m] [NeZero n] in` before `segGeneric_fan` and `omit [NeZero n] in` before
`fan_triangle_sides`).

### Statement layer (verbatim copy of work/drafts/ZeroLink_statement.lean:15-47; file lines 29-61)

```lean
-- L37
def MixedPair (Γ : Shadow) (i j : Fin Γ.c) (s t : Γ.Strand) : Prop :=
  s.1 = i ∧ t.1 = j ∧ Γ.IsCrossing {s, t}

-- L43
noncomputable def mixedSignSum (D : Diagram) (i j : Fin D.Γ.c) : ℤ :=
  ∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand,
    if h : D.Γ.MixedPair i j s t then ((D.sign ⟨{s, t}, h.2.2⟩ : SignType) : ℤ) else 0

-- L48
structure ZeroLinkData : Prop where
  /-- "For two distinct components of an actual generic oriented plane diagram, the sum of
  `sgn det(u₁, u₂)` over their transverse intersections, in this fixed component order, is zero." -/
  fixed_order_sum : ∀ (D : Diagram) (i j : Fin D.Γ.c), i ≠ j →
    (∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand,
      if D.Γ.MixedPair i j s t then ((SignType.sign (det (D.Γ.dir s) (D.Γ.dir t)) : SignType) : ℤ)
      else 0) = 0
  /-- "Consequently the half-sum of decorated crossing signs is an integer". -/
  half_sum_integer : ∀ (D : Diagram) (i j : Fin D.Γ.c), i ≠ j → ∃ k : ℤ, mixedSignSum D i j = 2 * k
  /-- "and it is zero if one component is always over the other." -/
  over_constant : ∀ (D : Diagram) (i j : Fin D.Γ.c), i ≠ j →
    ((∀ (s t : D.Γ.Strand) (h : D.Γ.MixedPair i j s t), D.overStrand ⟨{s, t}, h.2.2⟩ = s) ∨
     (∀ (s t : D.Γ.Strand) (h : D.Γ.MixedPair i j s t), D.overStrand ⟨{s, t}, h.2.2⟩ = t)) →
    mixedSignSum D i j = 0

```

### Unit 1 — `OneDim` (section OneDim, L65–L469)

```lean
-- L80
def affEval (c d : ι → ℝ) (g : ι) (t : ℝ) : ℝ := c g + t * d g

-- L83
noncomputable def zeroAt (c d : ι → ℝ) (g : ι) : ℝ := -c g / d g

-- L87
def IsEvent (c d : ι → ℝ) (g : ι) : Prop :=
  d g ≠ 0 ∧ 0 < zeroAt c d g ∧ zeroAt c d g < 1 ∧
    ∀ g', g' ≠ g → 0 < affEval c d g' (zeroAt c d g)

-- L94
structure GenericFamily (c d : ι → ℝ) : Prop where
  no_double_zero : ∀ t, 0 ≤ t → t ≤ 1 → ∀ g g', g ≠ g' →
    affEval c d g t = 0 → affEval c d g' t ≠ 0
  start_off : ∀ g, affEval c d g 0 = 0 → ∃ g', g' ≠ g ∧ affEval c d g' 0 ≤ 0
  end_off : ∀ g, affEval c d g 1 = 0 → ∃ g', g' ≠ g ∧ affEval c d g' 1 ≤ 0

-- L102
theorem affEval_zeroAt {g : ι} (hd : d g ≠ 0) : affEval c d g (zeroAt c d g) = 0

-- L107
theorem affEval_eq_mul {g : ι} (hd : d g ≠ 0) (t : ℝ) :
    affEval c d g t = d g * (t - zeroAt c d g)

-- L113
theorem affEval_pos_iff_of_pos {g : ι} (hd : 0 < d g) (t : ℝ) :
    0 < affEval c d g t ↔ zeroAt c d g < t

-- L125
theorem affEval_pos_iff_of_neg {g : ι} (hd : d g < 0) (t : ℝ) :
    0 < affEval c d g t ↔ t < zeroAt c d g

-- L138
theorem affEval_pos_of_between {g : ι} {t₀ t₁ t : ℝ} (h0 : 0 ≤ affEval c d g t₀)
    (h1 : 0 < affEval c d g t₁) (ht : t₀ < t) (ht' : t ≤ t₁) : 0 < affEval c d g t

-- L151
theorem affEval_pos_of_between' {g : ι} {t₀ t₁ t : ℝ} (h0 : 0 < affEval c d g t₀)
    (h1 : 0 ≤ affEval c d g t₁) (ht : t₀ ≤ t) (ht' : t < t₁) : 0 < affEval c d g t

-- L165
theorem entry_unique {g₁ g₂ : ι} (h₁ : IsEvent c d g₁) (h₂ : IsEvent c d g₂) (hd₁ : 0 < d g₁)
    (hd₂ : 0 < d g₂) : g₁ = g₂

-- L177
theorem exit_unique {g₁ g₂ : ι} (h₁ : IsEvent c d g₁) (h₂ : IsEvent c d g₂) (hd₁ : d g₁ < 0)
    (hd₂ : d g₂ < 0) : g₁ = g₂

-- L189
def reflC : ι → ℝ := fun g => c g + d g

-- L192
def reflD : ι → ℝ := fun g => -d g

-- L194
theorem affEval_refl (g : ι) (t : ℝ) : affEval (reflC c d) (reflD d) g t = affEval c d g (1 - t)

-- L198
theorem zeroAt_refl {g : ι} (hd : d g ≠ 0) : zeroAt (reflC c d) (reflD d) g = 1 - zeroAt c d g

-- L203
theorem isEvent_refl_iff (g : ι) : IsEvent (reflC c d) (reflD d) g ↔ IsEvent c d g

-- L221
theorem genericFamily_refl (H : GenericFamily c d) : GenericFamily (reflC c d) (reflD d) where
  no_double_zero

-- L240
noncomputable def inside (c d : ι → ℝ) (t : ℝ) : ℤ := if ∀ g, 0 < affEval c d g t then 1 else 0

-- L242
theorem inside_eq_one_iff (t : ℝ) : inside c d t = 1 ↔ ∀ g, 0 < affEval c d g t

-- L248
theorem inside_eq_zero_iff (t : ℝ) : inside c d t = 0 ↔ ∃ g, affEval c d g t ≤ 0

-- L257
theorem inside_eq_zero_or_one (t : ℝ) : inside c d t = 0 ∨ inside c d t = 1

-- L262
theorem not_entry_of_inside_zero {g : ι} (h0 : inside c d 0 = 1) (he : IsEvent c d g) : d g < 0

-- L271
theorem not_exit_of_inside_one {g : ι} (h1 : inside c d 1 = 1) (he : IsEvent c d g) : 0 < d g

-- L284
theorem exists_exit_event (H : GenericFamily c d) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (ht₀1 : t₀ < 1)
    (hα : ∀ g, 0 ≤ affEval c d g t₀) (hβ : ∀ g, affEval c d g t₀ = 0 → 0 < d g)
    (hγ : ∃ g, affEval c d g 1 ≤ 0) :
    ∃ g, IsEvent c d g ∧ d g < 0 ∧ t₀ < zeroAt c d g

-- L343
theorem exists_entry_event (H : GenericFamily c d) {t₁ : ℝ} (ht₁ : 0 < t₁) (ht₁1 : t₁ ≤ 1)
    (hα : ∀ g, 0 ≤ affEval c d g t₁) (hβ : ∀ g, affEval c d g t₁ = 0 → d g < 0)
    (hγ : ∃ g, affEval c d g 0 ≤ 0) :
    ∃ g, IsEvent c d g ∧ 0 < d g ∧ zeroAt c d g < t₁

-- L364
theorem exists_exit_of_one_zero (H : GenericFamily c d) (h0 : inside c d 0 = 1)
    (h1 : inside c d 1 = 0) : ∃ g, IsEvent c d g ∧ d g < 0

-- L372
theorem exists_entry_of_zero_one (H : GenericFamily c d) (h0 : inside c d 0 = 0)
    (h1 : inside c d 1 = 1) : ∃ g, IsEvent c d g ∧ 0 < d g

-- L381
theorem entry_iff_exit_of_zero_zero (H : GenericFamily c d) (h0 : inside c d 0 = 0)
    (h1 : inside c d 1 = 0) :
    (∃ g, IsEvent c d g ∧ 0 < d g) ↔ (∃ g, IsEvent c d g ∧ d g < 0)

-- L411
theorem sum_ite_unique (P : ι → Prop) [DecidablePred P] (hP : ∀ g g', P g → P g' → g = g') :
    (∑ g, if P g then (1 : ℤ) else 0) = if ∃ g, P g then 1 else 0

-- L424
theorem sum_event_sign_eq :
    (∑ g, if IsEvent c d g then ((SignType.sign (d g) : SignType) : ℤ) else 0) =
      (∑ g, if IsEvent c d g ∧ 0 < d g then (1 : ℤ) else 0) -
      (∑ g, if IsEvent c d g ∧ d g < 0 then (1 : ℤ) else 0)

-- L438
theorem affine_family_count (H : GenericFamily c d) :
    inside c d 1 - inside c d 0 =
      ∑ g, if IsEvent c d g then ((SignType.sign (d g) : SignType) : ℤ) else 0

```

**Unit 1 dependency order.** `affEval_zeroAt → affEval_eq_mul → affEval_pos_iff_of_pos/neg`;
`affEval_pos_of_between(')`; `entry_unique`, `exit_unique`; reflection `reflC/reflD → affEval_refl →
zeroAt_refl → isEvent_refl_iff, genericFamily_refl`; `inside_*`; `not_entry_of_inside_zero`,
`not_exit_of_inside_one`; `exists_exit_event → exists_entry_event (by reflection) →
exists_exit_of_one_zero, exists_entry_of_zero_one, entry_iff_exit_of_zero_zero`;
`sum_ite_unique`, `sum_event_sign_eq → affine_family_count`.

### Unit 2 — `Triangle` (section Triangle, L471–L910)

```lean
-- L477
def Seg (a b : Plane) : Set Plane := {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = a + t • (b - a)}

-- L479
theorem edgeSegment_eq_Seg {n : ℕ} (P : LabelledTuple n) (i : ZMod n) :
    edgeSegment P i = Seg (P i) (P (i + 1))   -- proof: rfl

-- L482
theorem Seg_symm (a b : Plane) : Seg a b = Seg b a

-- L489
theorem left_mem_Seg (a b : Plane) : a ∈ Seg a b

-- L491
theorem right_mem_Seg (a b : Plane) : b ∈ Seg a b

-- L494
theorem not_mem_Seg_of_det {a b x : Plane} (h : det (b - a) (x - a) ≠ 0) : x ∉ Seg a b

-- L501
theorem eq_of_two_dets {d₁ d₂ p x : Plane} (hd : det d₁ d₂ ≠ 0) (h₁ : det d₁ (x - p) = 0)
    (h₂ : det d₂ (x - p) = 0) : x = p

-- L514
theorem coe_sign_mul_self {x : ℝ} (hx : x ≠ 0) :
    ((SignType.sign x : SignType) : ℤ) * ((SignType.sign x : SignType) : ℤ) = 1

-- L520
theorem coe_sign_mul (x y : ℝ) :
    ((SignType.sign (x * y) : SignType) : ℤ) =
      ((SignType.sign x : SignType) : ℤ) * ((SignType.sign y : SignType) : ℤ)

-- L525
theorem coe_sign_det_swap (u w : Plane) :
    ((SignType.sign (det w u) : SignType) : ℤ) = -((SignType.sign (det u w) : SignType) : ℤ)

-- L532
def triTail : Fin 3 → Plane := ![o, v, w]

-- L535
def triHead : Fin 3 → Plane := ![v, w, o]

-- L538
def triDir (g : Fin 3) : Plane := triHead o v w g - triTail o v w g

-- L541
def triSide (g : Fin 3) : Set Plane := Seg (triTail o v w g) (triHead o v w g)

-- L545
def triD : ℝ := det (v - o) (w - o)

-- L548
def lineFn (g : Fin 3) (x : Plane) : ℝ := det (triDir o v w g) (x - triTail o v w g)

-- L552
noncomputable def triInside (x : Plane) : ℤ :=
  if ∀ g, 0 < triD o v w * lineFn o v w g x then 1 else 0

-- L555
theorem triHead_eq_triTail_succ (g : Fin 3) : triHead o v w g = triTail o v w (g + 1)

-- L558
theorem mem_triSide_iff (g : Fin 3) (x : Plane) :
    x ∈ triSide o v w g ↔ ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ x = triTail o v w g + s • triDir o v w g

-- L562
theorem triSide_zero : triSide o v w 0 = Seg o v   -- proof: rfl

-- L563
theorem triSide_one : triSide o v w 1 = Seg v w   -- proof: rfl

-- L564
theorem triSide_two : triSide o v w 2 = Seg w o   -- proof: rfl

-- L565
theorem triDir_zero : triDir o v w 0 = v - o   -- proof: rfl

-- L566
theorem triDir_one : triDir o v w 1 = w - v   -- proof: rfl

-- L567
theorem triDir_two : triDir o v w 2 = o - w   -- proof: rfl

-- L570
theorem lineFn_add_smul (g : Fin 3) (a u : Plane) (t : ℝ) :
    lineFn o v w g (a + t • u) = lineFn o v w g a + t * det (triDir o v w g) u

-- L577
theorem tri_reconstruct (hD : triD o v w ≠ 0) (x : Plane) :
    x = o + (lineFn o v w 2 x / triD o v w) • (v - o) + (lineFn o v w 0 x / triD o v w) • (w - o)

-- L602
theorem lineFn_sum (x : Plane) :
    lineFn o v w 0 x + lineFn o v w 1 x + lineFn o v w 2 x = triD o v w

-- L611
theorem div_pos_of_mul_pos' {D L : ℝ} (hD : D ≠ 0) (h : 0 < D * L) : 0 < L / D

-- L617
theorem lineFn_openSide_vals (g : Fin 3) (s : ℝ) :
    lineFn o v w g (triTail o v w g + s • triDir o v w g) = 0 ∧
    lineFn o v w (g + 1) (triTail o v w g + s • triDir o v w g) = (1 - s) * triD o v w ∧
    lineFn o v w (g + 2) (triTail o v w g + s • triDir o v w g) = s * triD o v w

-- L628
theorem fin3_ne_cases {g g' : Fin 3} (h : g' ≠ g) : g' = g + 1 ∨ g' = g + 2

-- L632
theorem vertex_of_two_lineFn (hD : triD o v w ≠ 0) {g g' : Fin 3} (hgg' : g ≠ g') {x : Plane}
    (h : lineFn o v w g x = 0) (h' : lineFn o v w g' x = 0) : ∃ g'', x = triTail o v w g''

-- L667
theorem lineFn_of_mem_openSide (hD : triD o v w ≠ 0) (g : Fin 3) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    lineFn o v w g (triTail o v w g + s • triDir o v w g) = 0 ∧
      ∀ g', g' ≠ g → 0 < triD o v w * lineFn o v w g' (triTail o v w g + s • triDir o v w g)

-- L681
theorem mem_openSide_of_lineFn (hD : triD o v w ≠ 0) (g : Fin 3) {x : Plane}
    (h0 : lineFn o v w g x = 0) (hpos : ∀ g', g' ≠ g → 0 < triD o v w * lineFn o v w g' x) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ x = triTail o v w g + s • triDir o v w g

-- L725
def segC (a _b : Plane) : Fin 3 → ℝ := fun g => triD o v w * lineFn o v w g a

-- L728
def segD (a b : Plane) : Fin 3 → ℝ := fun g => triD o v w * det (triDir o v w g) (b - a)

-- L730
theorem affEval_seg (a b : Plane) (g : Fin 3) (t : ℝ) :
    affEval (segC o v w a b) (segD o v w a b) g t = triD o v w * lineFn o v w g (a + t • (b - a))

-- L736
theorem inside_seg_zero (a b : Plane) : inside (segC o v w a b) (segD o v w a b) 0 = triInside o v w a

-- L740
theorem inside_seg_one (a b : Plane) : inside (segC o v w a b) (segD o v w a b) 1 = triInside o v w b

-- L746
structure SegGeneric (a b : Plane) : Prop where
  hD : triD o v w ≠ 0
  transverse : ∀ g, (Seg a b ∩ triSide o v w g).Nonempty → det (b - a) (triDir o v w g) ≠ 0
  no_vertex : ∀ g, triTail o v w g ∉ Seg a b
  start_off : ∀ g, a ∉ triSide o v w g
  end_off : ∀ g, b ∉ triSide o v w g

-- L754
theorem isEvent_iff_meets {a b : Plane} (hg : SegGeneric o v w a b) (g : Fin 3) :
    IsEvent (segC o v w a b) (segD o v w a b) g ↔ (Seg a b ∩ triSide o v w g).Nonempty

-- L823
theorem genericFamily_seg {a b : Plane} (hg : SegGeneric o v w a b) :
    GenericFamily (segC o v w a b) (segD o v w a b) where
  no_double_zero

-- L861
theorem tri_edge_count {a b : Plane} (hg : SegGeneric o v w a b) :
    (∑ g : Fin 3, if (Seg a b ∩ triSide o v w g).Nonempty then
        ((SignType.sign (det (b - a) (triDir o v w g)) : SignType) : ℤ) else 0) =
      ((SignType.sign (triD o v w) : SignType) : ℤ) * (triInside o v w a - triInside o v w b)

-- L886
theorem zmod_telescope {n : ℕ} [NeZero n] (f : ZMod n → ℤ) : ∑ q : ZMod n, (f q - f (q + 1)) = 0

-- L896
theorem tri_polygon_sum {m : ℕ} [NeZero m] (A : LabelledTuple m)
    (hg : ∀ p, SegGeneric o v w (A p) (A (p + 1))) :
    (∑ p : ZMod m, ∑ g : Fin 3, if (edgeSegment A p ∩ triSide o v w g).Nonempty then
        ((SignType.sign (det (edge A p) (triDir o v w g)) : SignType) : ℤ) else 0) = 0

```

**Unit 2 dependency order.** segment helpers (`Seg`, `Seg_symm`, `not_mem_Seg_of_det`,
`eq_of_two_dets`, `coe_sign_*`); triangle defs; `lineFn_add_smul`; `tri_reconstruct`, `lineFn_sum`
(the only coordinate computations); `lineFn_openSide_vals → lineFn_of_mem_openSide`;
`tri_reconstruct + lineFn_sum → vertex_of_two_lineFn, mem_openSide_of_lineFn`; segment family
`segC/segD`, `affEval_seg`, `inside_seg_zero/one`; `SegGeneric`; `isEvent_iff_meets` (uses
`mem_openSide_of_lineFn`, `lineFn_of_mem_openSide`, `affEval_eq_mul`), `genericFamily_seg` (uses
`vertex_of_two_lineFn`, `mem_openSide_of_lineFn`); `affine_family_count → tri_edge_count`;
`zmod_telescope → tri_polygon_sum`.

### Unit 3 — `ApexFan` (sections Apex + Fan, L912–L1139)

```lean
-- L924
theorem exists_point_off_finite_lines (L : Finset (Plane × Plane)) (hL : ∀ ℓ ∈ L, ℓ.2 ≠ 0) :
    ∃ o : Plane, ∀ ℓ ∈ L, det ℓ.2 (o - ℓ.1) ≠ 0

-- L956
theorem exists_good_apex {m n : ℕ} [NeZero m] [NeZero n] (A : LabelledTuple m) (B : LabelledTuple n)
    (hA : ∀ p, edge A p ≠ 0) (hB : ∀ q, edge B q ≠ 0) (hAB : ∀ p q, A p ∉ edgeSegment B q) :
    ∃ o : Plane, (∀ q, triD o (B q) (B (q + 1)) ≠ 0) ∧ (∀ p q, det (edge A p) (B q - o) ≠ 0) ∧
      (∀ p, o ∉ edgeSegment A p) ∧ (∀ p q, A p ∉ Seg o (B q))

-- L1032
theorem segGeneric_fan (o : Plane) (hAB : ∀ p q, A p ∉ edgeSegment B q) (hBA : ∀ p q, B q ∉ edgeSegment A p)
    (htr : ∀ p q, (edgeSegment A p ∩ edgeSegment B q).Nonempty → det (edge A p) (edge B q) ≠ 0)
    (ho₁ : ∀ q, triD o (B q) (B (q + 1)) ≠ 0) (ho₂ : ∀ p q, det (edge A p) (B q - o) ≠ 0)
    (ho₃ : ∀ p, o ∉ edgeSegment A p) (ho₄ : ∀ p q, A p ∉ Seg o (B q)) (p : ZMod m) (q : ZMod n) :
    SegGeneric o (B q) (B (q + 1)) (A p) (A (p + 1)) where
  hD

-- L1077
noncomputable def radialSum (o : Plane) (q : ZMod n) : ℤ :=
  ∑ p : ZMod m, if (edgeSegment A p ∩ Seg o (B q)).Nonempty then
    ((SignType.sign (det (edge A p) (B q - o)) : SignType) : ℤ) else 0

-- L1084
theorem fan_triangle_sides (o : Plane) (q : ZMod n) :
    (∑ p : ZMod m, ∑ g : Fin 3, if (edgeSegment A p ∩ triSide o (B q) (B (q + 1)) g).Nonempty then
        ((SignType.sign (det (edge A p) (triDir o (B q) (B (q + 1)) g)) : SignType) : ℤ) else 0) =
      radialSum A B o q +
        (∑ p : ZMod m, if (edgeSegment A p ∩ edgeSegment B q).Nonempty then
          ((SignType.sign (det (edge A p) (edge B q)) : SignType) : ℤ) else 0) -
        radialSum A B o (q + 1)

-- L1118
theorem fan_sum_zero (hA : ∀ p, edge A p ≠ 0) (hB : ∀ q, edge B q ≠ 0)
    (hAB : ∀ p q, A p ∉ edgeSegment B q) (hBA : ∀ p q, B q ∉ edgeSegment A p)
    (htr : ∀ p q, (edgeSegment A p ∩ edgeSegment B q).Nonempty → det (edge A p) (edge B q) ≠ 0) :
    (∑ p : ZMod m, ∑ q : ZMod n, if (edgeSegment A p ∩ edgeSegment B q).Nonempty then
        ((SignType.sign (det (edge A p) (edge B q)) : SignType) : ℤ) else 0) = 0

```

**Unit 3 dependency order.** `exists_point_off_finite_lines → exists_good_apex`;
`segGeneric_fan` (per-side `fin_cases`, uses `Seg_symm`); `radialSum`; `fan_triangle_sides`
(`Fin.sum_univ_three`; sides 0, 1 are `rfl`, side 2 via `Seg_symm` + `Left.sign_neg`);
`exists_good_apex + tri_polygon_sum + segGeneric_fan + fan_triangle_sides + Finset.sum_comm +
zmod_telescope → fan_sum_zero`.

### Unit 4 — `Diagram` (section Diagram + assembly, L1141–L1347)

```lean
-- L1148
theorem isCrossing_pair_iff_of_fst_ne (Γ : Shadow) {s t : Γ.Strand} (hst : s.1 ≠ t.1) :
    Γ.IsCrossing {s, t} ↔ (Γ.seg s ∩ Γ.seg t).Nonempty

-- L1165
theorem mixedPair_iff (Γ : Shadow) {i j : Fin Γ.c} (hij : i ≠ j) (s t : Γ.Strand) :
    Γ.MixedPair i j s t ↔ s.1 = i ∧ t.1 = j ∧ (Γ.seg s ∩ Γ.seg t).Nonempty

-- L1175
theorem sum_sigma_fst_eq {c : ℕ} {k : Fin c → ℕ} [∀ i, NeZero (k i)] (i : Fin c)
    (F : (Σ i', ZMod (k i')) → ℤ) (hF : ∀ s, s.1 ≠ i → F s = 0) :
    ∑ s, F s = ∑ p : ZMod (k i), F ⟨i, p⟩

-- L1184
noncomputable def fixedOrderSum (D : Diagram) (i j : Fin D.Γ.c) : ℤ :=
  ∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand,
    if D.Γ.MixedPair i j s t then ((SignType.sign (det (D.Γ.dir s) (D.Γ.dir t)) : SignType) : ℤ)
    else 0

-- L1190
theorem fixedOrderSum_eq_polygon_sum (D : Diagram) {i j : Fin D.Γ.c} (hij : i ≠ j) :
    fixedOrderSum D i j =
      ∑ p : ZMod (D.Γ.comp i).k, ∑ q : ZMod (D.Γ.comp j).k,
        if (edgeSegment (D.Γ.comp i).P p ∩ edgeSegment (D.Γ.comp j).P q).Nonempty then
          ((SignType.sign (det (edge (D.Γ.comp i).P p) (edge (D.Γ.comp j).P q)) : SignType) : ℤ)
        else 0

-- L1216
theorem fixedOrderSum_eq_zero (D : Diagram) (i j : Fin D.Γ.c) (hij : i ≠ j) :
    fixedOrderSum D i j = 0

-- L1235
theorem sign_mixed_eq (D : Diagram) {i j : Fin D.Γ.c} {s t : D.Γ.Strand} (h : D.Γ.MixedPair i j s t) :
    ((D.sign ⟨{s, t}, h.2.2⟩ : SignType) : ℤ) =
      if D.overStrand ⟨{s, t}, h.2.2⟩ = s then
        ((SignType.sign (det (D.Γ.dir s) (D.Γ.dir t)) : SignType) : ℤ)
      else -((SignType.sign (det (D.Γ.dir s) (D.Γ.dir t)) : SignType) : ℤ)

-- L1272
noncomputable def corrSum (D : Diagram) (i j : Fin D.Γ.c) : ℤ :=
  ∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand,
    if h : D.Γ.MixedPair i j s t then
      (if D.overStrand ⟨{s, t}, h.2.2⟩ = s then 0
        else -((SignType.sign (det (D.Γ.dir s) (D.Γ.dir t)) : SignType) : ℤ))
    else 0

-- L1280
theorem mixedSignSum_eq_fixed_add (D : Diagram) (i j : Fin D.Γ.c) :
    mixedSignSum D i j = fixedOrderSum D i j + 2 * corrSum D i j

-- L1295
theorem mixedSignSum_eq_fixed_of_over_fst (D : Diagram) (i j : Fin D.Γ.c)
    (h : ∀ (s t : D.Γ.Strand) (h : D.Γ.MixedPair i j s t), D.overStrand ⟨{s, t}, h.2.2⟩ = s) :
    mixedSignSum D i j = fixedOrderSum D i j

-- L1305
theorem mixedSignSum_eq_neg_fixed_of_over_snd (D : Diagram) (i j : Fin D.Γ.c)
    (h : ∀ (s t : D.Γ.Strand) (h : D.Γ.MixedPair i j s t), D.overStrand ⟨{s, t}, h.2.2⟩ = t) :
    mixedSignSum D i j = -fixedOrderSum D i j

-- L1337
theorem zero_link : ZeroLinkData   -- fields: fixed_order_sum, half_sum_integer, over_constant (assembled from Unit 4)

```

**Unit 4 dependency order.** `isCrossing_pair_iff_of_fst_ne → mixedPair_iff`; `sum_sigma_fst_eq`;
`fixedOrderSum_eq_polygon_sum` (two `sum_sigma_fst_eq`, `mixedPair_iff`, `rfl`) →
`fixedOrderSum_eq_zero` (`fan_sum_zero` with `regular_iff_edges`, `Generic.tail_off`,
`Generic.transverse`); `sign_mixed_eq`; `corrSum`; `mixedSignSum_eq_fixed_add`,
`mixedSignSum_eq_fixed_of_over_fst`, `mixedSignSum_eq_neg_fixed_of_over_snd`; `zero_link`.

Library facts consumed (all accepted, all in `SM.LinkDiagram`'s import closure): `det_swap`,
`det_add_right`, `det_smul_right`, `det_smul_self`, `regular_iff_edges`, `Shadow.isCrossing_pair`,
`Shadow.Adjacent.fst_eq`, `Shadow.IncidentTail.fst_eq`, `Shadow.Adjacent.refl`,
`Shadow.mem_iff_eq_or_other`, `Diagram.eq_under_of_mem_of_ne`, `Diagram.mem_iff`,
`Diagram.over_mem`, `Diagram.over_ne_under`, `Diagram.sign` (unfolded),
`Generic.regular/tail_off/transverse`, `PolyComp.instNeZeroK`.  Mathlib: `Finset.exists_min_image`,
`Infinite.exists_notMem_finset`, `Fintype.sum_sigma`, `Fintype.sum_eq_single`, `Fin.sum_univ_three`,
`Equiv.sum_comp`, `Finset.sum_comm`, `sign_mul`, `Left.sign_neg`, `sign_eq_one_iff`,
`sign_eq_neg_one_iff`, `mul_div_mul_left`, `field_simp`, `linear_combination`, `nlinarith`,
`fin_cases`, `push Not`, `ite_eq_left/right`, `dite_eq_left/right`.

---

## 3. Partition into independent units (status: ALL PROVED)

Every unit below is already closed in `Skeleton_FINAL.lean`; there is no proving left.  The
partition is for (i) independent review under ACCEPT_CYCLE.md — each reviewer needs only the
interface of the previous unit — and (ii) re-proving from the interface if a reviewer rejects a
lemma.  "May assume" = the exact declarations a prover of that unit may use as black boxes.
Line counts are actual (`Skeleton_FINAL.lean`).

| unit | file range | lines | declarations | may assume | delivers |
|---|---|---|---|---|---|
| **U1 `OneDim`** | L65–L469 | 405 | 32 (25 thm) | Mathlib only (`ℝ` order/field, `Finset`, `Fintype`) | `affEval`, `zeroAt`, `IsEvent`, `GenericFamily`, `inside`, `affEval_zeroAt`, `affEval_eq_mul`, `affine_family_count` (plus the helpers listed above) |
| **U2 `Triangle`** | L471–L910 | 440 | 45 (34 thm) | U1's interface: `affEval`, `zeroAt`, `IsEvent`, `GenericFamily`, `inside`, `affEval_zeroAt`, `affEval_eq_mul`, `affine_family_count`; library `det_*`, `edgeSegment`/`edge`/`LabelledTuple` | `Seg`, `Seg_symm`, `edgeSegment_eq_Seg`, `triTail/triHead/triDir/triSide/triD/lineFn/triInside`, `triSide_two`, `triDir_two`, `SegGeneric`, `zmod_telescope`, `tri_polygon_sum` |
| **U3 `ApexFan`** | L912–L1139 | 228 | 6 (5 thm) | U2's interface: `Seg`, `Seg_symm`, `edgeSegment_eq_Seg`, `triTail/triDir/triSide/triD`, `triSide_two`, `triDir_two`, `SegGeneric` (constructor), `zmod_telescope`, `tri_polygon_sum`; library `edge`, `edgePoint`, `det_smul_self`, `Infinite.exists_notMem_finset` | `exists_point_off_finite_lines`, `exists_good_apex`, `radialSum`, `fan_sum_zero` |
| **U4 `Diagram`** | L1141–L1347 | 207 | 12 (10 thm + `zero_link`) | U3's `fan_sum_zero` ONLY (plus the statement layer and the accepted `Shadow`/`Diagram`/`Generic` API) | `fixedOrderSum`, `fixedOrderSum_eq_zero`, `sign_mixed_eq`, `corrSum`, the three `mixedSignSum_*` lemmas, `SM.zero_link` |

Dependency graph: U1 → U2 → U3 → U4 (a chain; U3 and U4 do not see U1; U4 does not see U2).
The statement layer (L29–L61, 33 lines) is shared and fixed.

Interfaces are stable in the following sense: `fan_sum_zero`'s statement mentions only
`LabelledTuple`, `edge`, `edgeSegment`, `det`, `SignType.sign`, so U4 can be reviewed without opening
U1–U3; `tri_polygon_sum` mentions only U2's triangle defs and `edgeSegment/edge`, so U3 can be
reviewed against U2's definitions alone.

---

## 4. Degenerate configurations — where each is excluded (all discharged by the compiled proof)

| configuration | excluded / handled by |
|---|---|
| mixed crossing at a vertex of `A` or `B` | `Generic.tail_off` (`IncidentTail` needs equal components) gives `A p ∉ edgeSegment B q` and `B q ∉ edgeSegment A p` → `SegGeneric.no_vertex` (side-1 vertices `B q`, `B (q+1)`) and `start_off`/`end_off` (side 1) |
| non-transverse meeting `e_p ∩ f_q` | `Generic.transverse` (not `Adjacent` across components) → `SegGeneric.transverse` (side 1) |
| `e_p` collinear with `f_q` but disjoint | allowed: `segD 1 = 0`, no event at side 1; `GenericFamily` tolerates constant `φ g` |
| degenerate fan triangle (`o` on the line of `f_q`) | `exists_good_apex` (o₁): `o ∉ line(B q, edge B q)`; `edge B q ≠ 0` from `Generic.regular` via `regular_iff_edges` |
| radial side `[o, B q]` parallel to `e_p` | (o₂): `o ∉ line(B q, edge A p)` — every radial side transverse to every edge of `A` |
| radial side through a vertex of `A` | (o₄): `o ∉ line(A p, B q − A p)` (a genuine line since `A p ≠ B q` by `tail_off`); sides 0 and 2 via `Seg_symm` |
| `o` on an edge of `A` | (o₃): `o ∉ line(A p, edge A p)` |
| path through a triangle vertex (two side lines zero at one parameter) | `vertex_of_two_lineFn` (needs `triD ≠ 0`) + `no_vertex` → `GenericFamily.no_double_zero` |
| edge endpoint on a side LINE but outside the closed side | allowed: `GenericFamily.start_off/end_off` forbid only endpoints in the OPEN side (`mem_openSide_of_lineFn`), implied by `SegGeneric.start_off/end_off` (closed sides) |
| self-intersections of `A` or `B`; triple points | irrelevant — the argument counts traversed edge pairs `(p, q)`, never points ("counts traversed occurrences"); `Generic.no_triple` is never used |
| two meetings on one pair `(e_p, f_q)` | impossible for transverse segments and not needed: the summand is a 0/1 indicator per ordered pair, exactly like `MixedPair` |
| `k ≥ 3`, `c ≥ 1` | only `NeZero k` is used (`PolyComp.instNeZeroK`) |

Finiteness of the forbidden set for `o`: `L = L1 ∪ L2 ∪ L3 ∪ L4 : Finset (Plane × Plane)`, four
`Finset.image`s of `univ` over `ZMod n`, `ZMod m × ZMod n`, `ZMod m`, `ZMod m × ZMod n`; a line is
parallel to `(1, μ)` for at most one `μ`, so `Infinite.exists_notMem_finset` on ℝ gives a good slope,
and along `s ↦ s • (1, μ)` each line is met at one `s`, so a second application gives the point.

---

## 5. Why no cheaper route exists (rationale carried over from B §0 and A §0)

* Ray casting (winding number of `B` along `A`) needs rays dictated by the diagram; genericity does
  not exclude a vertex `a_p` on the *extension* of an edge `f_q`, so half-open conventions miscount
  when `A` touches a ray — repairing that needs an extra generic direction and two event types.  The
  finite apex `o` is chosen off `line(a_p, b_q)` and avoids this entirely.
* A closed-form per-pair sign identity whose double sum telescopes is valid only when all four side
  signs are nonzero (a vertex of `B` on the extended line of `e_p` gives a zero, not excluded), and
  the telescoping is not termwise.
* Jordan curve / Mathlib winding numbers: not available in the needed form; not used.
* A sorted event list (the task's suggestion) is unnecessary for a convex region: uniqueness of
  entries and exits + first/last zero suffices (A).  It remains the fallback for non-convex regions,
  which never arise here.

---

## 6. Notes for the executor (acceptance)

1. **Where to put it.** Move `Skeleton_FINAL.lean` to `work/lean/SM/ZeroLink.lean` (or the name the
   acceptance cycle assigns).  If/when the statement module (`ZeroLink_statement.lean`) is accepted as
   its own module, delete lines 29–61 of the final file (the verbatim copy of `MixedPair`,
   `mixedSignSum`, `ZeroLinkData`) and `import` that module instead; nothing else changes.
2. **`Decidable` alignment.** Field 1 is closed by `fixedOrderSum_eq_zero D i j hij` with
   `fixedOrderSum` unfolding definitionally to the field's expression; this relies on both files
   elaborating `if D.Γ.MixedPair … then … else 0` under `open Classical`.  If the accepted statement
   module elaborates the `if` with a different instance, replace the direct term by
   `Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => if_congr Iff.rfl rfl rfl))`
   followed by `fixedOrderSum_eq_zero`, or by the `ite_eq_left/right` split already used in
   `fixedOrderSum_eq_polygon_sum`.
3. **Pin-specific names.** The file uses this pin's `ite_eq_left/ite_eq_right/dite_eq_left/
   dite_eq_right` (the pin deprecates `if_pos/if_neg/dif_pos/dif_neg`, checked with `#check`) and
   `push Not` (for `push_neg`), plus `Infinite.exists_notMem_finset`.  A different toolchain would
   need the old names; on this pin the file is warning-free.
4. **Review checklist per unit** (what a reviewer must confirm; the compiler already confirms the
   proofs): U1 — `IsEvent` and `GenericFamily` say what §1 says (transverse zero in `(0,1)` on the
   open side; no double zero on `[0,1]`; endpoints not on the open boundary).  U2 — `triInside` is
   the open triangle for either orientation; `SegGeneric` is implied by the diagram's genericity (it
   is, via `segGeneric_fan`).  U3 — `exists_good_apex` lists exactly the four line families of the
   printed proof.  U4 — `fixedOrderSum` is the field-1 expression verbatim; `sign_mixed_eq` matches
   def:positive-lift (`D.sign x = sgn det(u_over, u_under)`).
5. **Transcription row** for the accepted table: sm-3:1538-1545, `SM.zero_link : SM.ZeroLinkData`,
   three fields, no hypotheses beyond `i ≠ j` as printed ("two distinct components").
