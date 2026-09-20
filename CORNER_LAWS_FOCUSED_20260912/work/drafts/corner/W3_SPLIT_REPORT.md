# W3_SPLIT_REPORT — wave 3, unit SPLIT (prefix `s7p_`, serving the leaf `s7_sliding_law_at`), 2026-09-15 21:45 UTC / 5:45pm ET

File: `work/drafts/corner/W3_SPLIT.lean` = `W3_Skeleton.lean` (97 lines, the four open declarations of row 110 on the
ported library) + ONE inserted block (lines 23-1240, 1218 lines, **59 declarations**: 55 theorems, 3 `def`s
(`s7p_cyc`, `s7p_kappa`, `s7p_x`), 1 structure (`s7p_SideData`)), placed inside `section VertexEdge` immediately BEFORE
the docstring of the leaf `s7_sliding_law_at` (now line 1244).  `diff W3_Skeleton.lean W3_SPLIT.lean` = `22a23,1240`: a
pure insertion, **0 deleted lines**; the statements, names and docstrings of `s7_sliding_law_at`, `s7_bigon_law_at`,
`thm_C_S7_of`, `thm_C_S7_of_floor`, `thm_C_S7` are untouched (`python3 tools/stmt_check.py W3_SPLIT.lean`: 4/49 —
identical to the skeleton's own 4/49, the W3 file carries only the four row-110 declarations of the 49 frozen ones); no
import added, no `open` added.  **The leaf's `sorry` body is UNCHANGED** (see §3: the termwise identity `hterm` is another
unit's output and was not supplied as a black box).
Check (official): `cd work/lean && lake env lean ../drafts/corner/W3_SPLIT.lean` — **0 errors**, exit 0, ~15 s warm;
**exactly 2 `declaration uses sorry`** = the two leaves (`s7_sliding_law_at` 1244, `s7_bigon_law_at` 1263); **0 other
warnings** (all unused-instance linter hits silenced with `omit [NeZero n] in`; `push Not` used, not the deprecated
`push_neg`).  `grep -c sorry`: 3 before → 3 after (2 leaf bodies + 1 prose mention in the header comment); **no `sorry`
in the block — nothing stated, everything proved; no black boxes consumed.**
Clash scan: `grep -rln s7p_ work/lean/{SM,CV,Bridge}` empty.
Axioms (`#print axioms` on a scratch copy): `s7p_exists_pivotSplit`, `s7p_pivotSplit`, `s7p_rel_first`, `s7p_x_split`,
`s7p_side_of_r`, `s7p_cross`, `s7p_mem_range_first`, `s7p_kappa_first_bounds` = `[propext, Classical.choice, Quot.sound]`;
`s7p_sliding_law_at_of_hterm` = `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]`
(inherited from `s7e_sliding_law_at_of_contact`, exactly as W2_S7E_REPORT reports for it).  Nothing depends on `sorryAx`.
Uses from the library: U110-B (`s7b_firstCrossingQ/_secondCrossingQ` + `_val`, `_injective`, `_not_affected`,
`s7b_firstCrossingQ_ne_secondCrossingQ`, `s7b_firstVisitQ/_secondVisitQ` + `_fst`, `_edge`, `_injective`,
`s7b_visit_of_firstCrossingQ/_secondCrossingQ`, `s7b_firstHalfVisit/_secondHalfVisit`, `s7b_firstHalfCrossing(_not_affected)`,
`s7b_visitParameter_firstHalfVisit(_cut)`, `s7b_visitParameter_secondHalfVisit(_cut)`, `s7b_edgeSegment_firstHalf/_secondHalf`,
`s7b_mem_edgeSegment_firstHalf_cut/_secondHalf_cut`, `s7b_remote_firstHalfIndex_iff/_secondHalfEdgeIndex_iff`,
`s7b_PivotSplit`, `s7b_SupportSplit`, `s7b_slidingDecompositionEquiv`), U110-E (`s7e_va`, `s7e_vl` + `_edge`, `s7e_visit_of_fst`,
`s7e_vl_ne_va`, `s7e_a_ne_leg`, `s7e_persist_a/_M/_M_sub_one`, `s7e_va_param_near`, `s7e_vl_param_false/_true`, `s7e_hQC`,
`s7e_hw`, `s7e_hL`, `s7e_hxm/_hxp`, `s7e_huniq_m/_p`, `s7e_xm/_xp`, `s7e_leg`, `s7e_contactSector_of_pivotSplit`,
`s7e_sliding_law_at_of_contact`), U110-A2 (`s7a2_exists_intervalLocal`, `s7a2_IntervalLocal`, `s7a2_continuousAt_edgeParameter`,
`s7a2_crossing_iff`, `s7a2_pos_of_ne_zero`), U110-A (`s7a_sideGeneric`); accepted: `traversalBetween_shift`, `traversalShift`,
`traversalKey_injective`, `visitPosition(_injective/_interior)`, `Interlaces`, `interlaces_symm`, `crossingVisitBetween`,
`crossingVisitPosition`, `crossing_support_partner`, `crossing_visits_exist`, `crossing_visits_exhaust`,
`visitParameter_eq_of_support_pair`, `contact_crossingParameter_eq_edgeParameter`, `crossingParameter_spec`,
`crossingPoint_mem`, `cyclicRangeIndex_offset/_range`, `firstHalfIndex_range/_zero/_last/_injective`,
`secondHalfEdgeIndex_zero/_last`, `contactDistance_bounds`, `contactSeparated_size`, `contactHalfSizes_bounds`,
`contactAffected_iff_leg`, `g1_firstHalf/_secondHalf`, `last_index_val_succ`, `ContactOrderAgrees`, `ContactParameterWindows`,
`VertexLocalData.parameter_order/.windows`.

## 0. What this unit provides, in one paragraph

**PLAN §3.3 sliding (2), the interlacement transfer (U_S7B_REPORT §2.2), is PROVED on BOTH sides below a radius**:
`s7p_exists_pivotSplit hn g h h₁ h₂ : ∃ δ > 0, ∀ t < δ, s7b_PivotSplit (Interlaces hn (s7a_sideGeneric g false)) (Interlaces hn₁ h₁)
(Interlaces hn₂ h₂) (s7b_firstCrossingQ …) (s7b_secondCrossingQ …) (s7e_xm hn h t) ∧ s7b_PivotSplit (… true …) (s7e_xp hn h t)` —
the two conjuncts are byte-for-byte the hypotheses `hsplitm`, `hsplitp` of `s7e_contactSector_of_pivotSplit` (the
side/half/map proof arguments are propositions, so they unify by proof irrelevance; the pivot `s7p_x` unfolds to
`s7e_xm`/`s7e_xp`).  All six open fields of U_S7B §2.2 are closed: `rel₁ rel₂` (cyclic order of a half's images is the
half's), `cross cross'` (no interlacing between the two halves' images), `x_free₁/₂`, and `x_split` with the CONVERSE of
`s7b_isCrossing_*_image` (`s7p_mem_range_first/_second`).  The method is a single coordinate: `Interlaces` is
`traversalBetween` of visit positions, invariant under the relabelling `traversalShift M` (library
`traversalBetween_shift`), so every visit of a side polygon `Q` is read through its **rotated key**
`κ(v) = (edge v − M).val + parameter v ∈ [0, n)` (`s7p_kappa`).  In it the λ₁-images are `i.val + p_Q` and lie in
`(3η, D + r − 3η)`, the λ₂-images are `D + j.val + p_Q` and lie in `(D + r + 3η, n − 3η)` (`D = contactDistance`), the
contact `a`-visit of `x` is at `D + (r ± η)` and its leg visit at `n − 1 + (1 − η)` (leg `M − 1`) or `0 + η` (leg `M`):
two arcs cut by the two visits of `x`, and every interlacement fact is linear arithmetic on these bounds.  The same-edge
order of `Q` is the centre's (`ContactOrderAgrees`) and the centre's is the half's (U110-B's parameter laws, monotone on
the cut), so `κ ∘ ι` is an order-isomorphic reparametrisation of the half's key and the cyclic order is preserved
verbatim.  The side-of-`r` agreement between `Q` and the CENTRE (needed on the cut edge) is sign constancy along the germ
interval (`s7p_side_of_r`: the `s7e_sign_const` argument with `u = 0` as the second point, via `s7a2_pos_of_ne_zero`).
As a convenience for the assembler, **the leaf is reduced to the termwise identity alone**:
`s7p_sliding_law_at_of_hterm hn g h h₁ h₂ δc hδc hterm : <the frozen leaf statement>` with `hterm` quantified over ANY
proofs `hsplitm hsplitp` (§3).

## 1. Proved (all `s7p_`; `{n} [NeZero n]` from `section VertexEdge`; no `sorry`)

### 1.A Pure cyclic order on real keys
* `s7p_cyc x y z := (x<y ∧ y<z) ∨ (y<z ∧ z<x) ∨ (z<x ∧ x<y)`; `s7p_traversalBetween_iff` (`Iff.rfl` on `traversalKey`);
  **`s7p_cyc_congr`** (cyclic order depends only on the pairwise order: `(∀ u v, G u < G v ↔ F u < F v) → (cyc (G u) (G v) (G w) ↔ cyc (F u) (F v) (F w))`);
  **`s7p_key_lt_iff_of`** (keys `e + p` with `p ∈ [0,1)`: edge indices decide, then parameters).

### 1.B The rotated key and interlacement in `κ`-coordinates
* **`s7p_kappa hn hQ M v := traversalKey (traversalShift M (visitPosition hn hQ v))`**, `s7p_kappa_eq` (`= (edge − M).val + param`, rfl),
  `s7p_kappa_injective` (generic `Q`), **`s7p_between_iff`** (`traversalBetween` of positions ↔ `cyc` of `κ`'s, by `traversalBetween_shift`),
  **`s7p_interlaces_iff`** (`Interlaces hn hQ x y ↔ x ≠ y ∧ ∃ x₀ x₁ y₀ y₁, x₀ ≠ x₁ ∧ y₀ ≠ y₁ ∧ cyc(κ⟨x,x₀⟩, κ⟨y,y₀⟩, κ⟨x,x₁⟩) ∧ cyc(κ⟨x,x₁⟩, κ⟨y,y₁⟩, κ⟨x,x₀⟩)`).

### 1.C The side data (section `S7PSide`; `hd : s7p_SideData M a P Q r η`)
* **`structure s7p_SideData (M a) (P Q) (r η) : Prop`** — `hsep`, `hz : pointZeroTriples P = {contactSupport M a}`, `hm`,
  `hr : P M = edgePoint P a r`, `hr0 hr1 hη hηr hηr1`, `hQ : Generic Q`, `hQC` (persistent crossings agree with the centre),
  `hw : ContactParameterWindows P Q M a r η`, `hord : ContactOrderAgrees P Q M a`, `hside : ∀ j, IsCrossing P {a,j} → ¬affected →
  (edgeParameter Q a j < r ↔ edgeParameter P a j < r)`.  Exactly the fields of `VertexEdgeAt`, `s7a2_exists_intervalLocal` and
  `VertexLocalData` a side polygon has (§1.H).
* `s7p_D_bounds` (`2 ≤ D ≤ n − 3`), `s7p_n5`, **`s7p_centre_visitParameter`** (at the centre, `visitParameter v = edgeParameter P v.edge j`
  for a persistent visit with support `{v.edge, j}` — `contact_crossingParameter_eq_edgeParameter`; the centre is NOT `G1`).
* Edge offsets: **`s7p_d_first : (firstHalfIndex M a i − M).val = i.val`**, **`s7p_d_second : (secondHalfEdgeIndex M a j − M).val = D + j.val`**;
  index arithmetic `s7p_first_val_le` (`i.val ≤ D`), `s7p_first_val_eq_iff` (`i.val = D ↔ i = −1`), `s7p_first_val_zero_iff`,
  `s7p_second_val_lt` (`j.val < n − D`), `s7p_second_val_eq_iff` (`j.val = n − D − 1 ↔ j = −1`).

### 1.D Parameters of the image visits (same-edge order transfer)
* `s7p_first_pair / s7p_second_pair` (a half visit's crossing is `{i, j}` and its image's is `{ι i, ι j}`);
  **`s7p_first_params / s7p_second_params`** (`p_Q(ι v) = edgeParameter Q (ι i) (ι j)`, `p_P(ι_P v) = edgeParameter P (ι i) (ι j)`,
  the image is a persistent crossing of the centre);
  **`s7p_first_param_lt_iff / s7p_second_param_lt_iff`** (two half visits on ONE edge: `p_Q(ι u) < p_Q(ι w) ↔ p(u) < p(w)` —
  `hord` to the centre, then `s7b_visitParameter_*Visit(_cut)`: equal off the cut, `r·p` resp. `r + (1−r)p` on it).

### 1.E `κ ∘ ι` order-isomorphic to the halves' keys; `rel₁ rel₂`
* `s7p_kappa_first` (`κ(ι₁ v) = i.val + p_Q(ι₁ v)`), `s7p_kappa_second` (`κ(ι₂ v) = (D + j.val) + p_Q(ι₂ v)`), `s7p_kappa_zero`
  (a half's own key is its `κ` with `M := 0`); **`s7p_kappa_first_lt_iff / s7p_kappa_second_lt_iff`** (`κ(ι u) < κ(ι w) ↔ key(u) < key(w)`,
  by `s7p_key_lt_iff_of` + §1.D); `s7p_visit_first_ne / _second_ne` (distinct visits have distinct image visits);
  **`s7p_rel_first : Interlaces hn hQ (ι₁ c) (ι₁ c') ↔ Interlaces hn₁ h₁ c c'`**, **`s7p_rel_second`** (both directions of the
  existential over visits via `s7b_visit_of_*CrossingQ` / `Sigma.ext`, then `s7p_cyc_congr`).

### 1.F The two arcs
* **`s7p_first_paramQ_lt_r`** (a λ₁-image on the cut edge `a` has `Q`-parameter `< r`: centre parameter `r·p < r`, then `hside`),
  **`s7p_second_paramQ_gt_r`** (`> r`; strictness from `s7e_persist_a`);
  **`s7p_kappa_first_bounds`** (`3η < κ u < D + r − 3η` for any visit `u` of a λ₁-image crossing: cases edge `M` (`s7e_persist_M`),
  edge `a` (`s7e_persist_a` + `_lt_r`), interior edges), **`s7p_kappa_second_bounds`** (`D + r + 3η < κ u < n − 3η`: edge `a`,
  edge `M−1` (`s7e_persist_M_sub_one`), interior), **`s7p_kappa_persistent_bounds`** (`3η < κ u < n − 3η` for every persistent visit);
  **`s7p_kappa_va_bounds`** (`D + r − η < κ(v_a) < D + r + η`), **`s7p_kappa_vl_false`** (leg `M−1`: `n − η < κ(v_ℓ)`),
  **`s7p_kappa_vl_true`** (leg `M`: `κ(v_ℓ) < η`).
* `def s7p_x f hc : Crossing Q := ⟨{a, contactLeg f M}, hc⟩` (= `s7e_xm`/`s7e_xp` at the wall, definitionally), `s7p_x_affected`,
  `s7p_x_visits` (the two visits of `x` are `v_a, v_ℓ` in one of two orders), `s7p_xl_eq`.
* **`s7p_cross`** (`¬ Interlaces (ι₁ c₁) (ι₂ c₂)`), **`s7p_cross'`**, **`s7p_x_free_first`**, **`s7p_x_free_second`** — each a
  `rcases` over the 3×3 disjuncts of the two `cyc`'s closed by `linarith` on the bounds (`x_free` also over the two visit
  orders and the two legs).

### 1.G The converse of `s7b_isCrossing_*_image` and `x_split`
* **`s7p_mem_range_first`**: a persistent crossing `y` of `Q` with `∀ e ∈ y.val, (e − M).val < firstHalfSize` and
  `∀ j, y.val = {a, j} → edgeParameter P a j < r` is `s7b_firstCrossingQ c` for some `c : Crossing λ₁` (remoteness by
  `s7b_remote_firstHalfIndex_iff`, the wrap pair `{a, M}` being contact-affected; segments equal off the cut, and on the cut
  the crossing point `edgePoint P a u` has `0 ≤ u = edgeParameter P a j ≤ r`, `s7b_mem_edgeSegment_firstHalf_cut`).
  **`s7p_mem_range_second`** (labels in `a..M−1`, `r ≤ edgeParameter P a j`).
* **`s7p_x_split`**: `y ≠ x`, `¬ Interlaces x y` ⇒ `y ∈ range ι₁ ∪ range ι₂` — the negated interlacement for the two visit
  orders, with `κ(v_ℓ)` extremal, forces both visits of `y` on one side of `κ(v_a)`; `κ w < κ(v_a)` gives `(edge w − M).val ≤ D`
  and, on edge `a`, `p_Q(w) < p(v_a) < r + η` hence (`s7e_persist_a`) `< r`, hence (`hside`) centre parameter `< r`; the other
  side symmetrically with `ZMod.val_sub`.

### 1.H Assembly (`S7PSide`, `S7PWall`, top level)
* **`s7p_pivotSplit hn hd f hc huniq h₁ h₂ : s7b_PivotSplit (Interlaces hn hd.hQ) (Interlaces hn₁ h₁) (Interlaces hn₂ h₂) ι₁ ι₂ (s7p_x f hc)`**
  (`split` from U110-B's `inj₁ inj₂ disjoint` + §1.E/1.F; `x_not` from `_not_affected`; `x_free`, `x_split` from §1.F/1.G).
* **`s7p_side_of_r hn g h hloc t ht hη b`** (side-of-`r` agreement side ↔ centre for persistent `a`-visits: `s7a2_pos_of_ne_zero`
  applied to `±(edgeParameter (g.curve u) a j − r)`, nonvanishing from `VertexLocalData.windows` at every `|u| < δ` incl. `u = 0`).
* **`s7p_sideData hn g h hloc t ht hr0 hr1 hr hη hηr hηr1 b : s7p_SideData M a g.center (g.curve (g.sideTime b t)) r η`**.
* **`s7p_exists_pivotSplit`** (§0) — `δ` = the radius of `s7a2_exists_intervalLocal`.
* **`s7p_sliding_law_at_of_hterm`** (§3).

## 2. Not proved

Nothing in this unit.  No black boxes were consumed; every `s7p_` declaration is proved.  Nothing believed false: every
sentence of U_S7B_REPORT §2.2 rendered here is literally true, and the one hypothesis U_S7B feared ("the side-of-`r`
classification of an unaffected `E_a`-visit on `Q` is NOT derivable from `VertexLocalData` alone … only from
`contact_persistent_parameters_approach`") is NOT needed: sign constancy along the interval (`s7p_side_of_r`, as W2_S7E §2
predicted) replaces the approach clause, because `s7a2_IntervalLocal` holds at `u = 0` too.

## 3. How to consume — what still closes the leaf

The leaf body is now ONE hypothesis away:
```
  exact s7p_sliding_law_at_of_hterm hn g h h₁ h₂ δc hδc hterm
```
with `hterm : ∀ t, t.val < δc → ∀ hsplitm hsplitp, ∀ q, s7e_term hn (s7a_sideGeneric g true) ((s7b_slidingDecompositionEquiv … hsplitp).symm q).1 −
s7e_term hn (s7a_sideGeneric g false) ((s7b_slidingDecompositionEquiv … hsplitm).symm q).1 = (g.contactSign M a : ℤ) * (term₁ q.1.1 * term₂ q.2.1)`
(the full statement is printed at `s7p_sliding_law_at_of_hterm`, lines 1202-1230; `hsplitm hsplitp` are universally
quantified propositions, so the SLIDING (3) unit may take them as given or use `s7p_exists_pivotSplit`'s).  Equivalently
the two conjuncts of `s7p_exists_pivotSplit … |>.2 t ht` are `hsplitm t ht`, `hsplitp t ht` in W2_S7E_REPORT §2's
one-liner.  What `hterm` needs is unchanged from W2_S7E_REPORT §2 item 2 (none of it is in this unit):
`s7b_SlidingTransport.ret` on both sides (est. 600-900 lines; §1.C of W2_S7E is the `nextMark` tool), the coefficient
equality of each carrier with its half carrier via `s7d_cornerCoefficient_eq_of_cut` (the `hmono/hcut` inputs are the
parameter laws also used here; the relocated-carrier rotation equality by principal-angle addition, est. 300-500), the
ordered corner bijection for `s7c_carrierWeight_refine` (est. 400-600), and the selector/product bookkeeping
(600-900).  **Estimated remaining for the leaf: 2,000-3,000 lines**, down from W2_S7E's 2,500-4,000 by this unit's
500-800.

Reusable outside the sliding row: §1.A-1.B are branch-independent (any generic polygon; `s7p_interlaces_iff` with any
rotation `M`); §1.C-1.G apply to the bigon side polygons `P₀`, `P₂` as well once a `s7p_SideData` is supplied (for the
bigon's `s7b_SupportSplit` on `P₀` only `rel₁ rel₂ cross cross'` are needed: `s7p_rel_first/_second`, `s7p_cross/_cross'`
take `hd` alone, no pivot).

## 4. Mathlib / Lean pitfalls hit (v4.34.0-rc2 pin)

* `rw [lemma]` where the lemma's only handle on an implicit `hd : s7p_SideData …` (a Prop) is through projections
  `hd.hQ.1`, `hd.hsep` leaves `?hd ?r ?η` unassigned (proof arguments never determine metavariables): pass `hd` explicitly
  (`rw [s7p_kappa_first hn hd]`).
* `simp only [firstHalfSize] at h` rewrites INSIDE the type `ZMod (firstHalfSize M a)` of `i` in `h : i.val < firstHalfSize M a`,
  producing a `ZMod.val` at a different type that `omega` treats as a fresh atom; keep the size opaque and add
  `have : firstHalfSize M a = contactDistance M a + 1 := rfl` for `omega` instead.
* `rw [hs]` with `hs : v.1.val = {v.2.val, j}` fails (motive) because `v.2`'s type mentions `v.1.val`; rewrite only the side
  that does not contain `v.2` (`conv_lhs => rw [hs]`), or `show` the goal first.
* Anonymous-constructor crossings `⟨{a, ℓ}, hc⟩` elaborate to `Subtype (IsCrossing Q)`, not syntactically `Crossing Q`; `rw`
  with a lemma quantified over `Crossing Q` then fails ("not type-correct under implicit transparency").  Wrap the pivot in a
  `def` (`s7p_x`) or use `(lemma _ _).mp` instead of `rw`; for the final `Subtype.ext` goal `show Finset.image ι {i₁, i₂} = y.val`.
* `congrArg (fun w : Visit Q => w.2) h` is rejected (dependent codomain); use `Sigma.mk.inj_iff` + `eq_of_heq`, and build the
  `Sigma.ext rfl (heq_of_eq he)` proof with the two visits spelled out (`have h' : ι ⟨c, x₀⟩ = ι ⟨c, x₁⟩ := …`).
* `mul_lt_mul_left` resolved to an ordered-monoid version needing `MulRightStrictMono ℝ`; `constructor <;> intro <;> nlinarith`
  is the robust route for `r * p < r * q ↔ p < q`.
* `rw [h]` closes the goal by `rfl` when the rewritten sides coincide, and a following `exact` then fails with "no goals";
  use `subst he; exact …` or `rw [he]; exact hDa` only when the residual goal is not closed by `rfl`.
* `omit [NeZero n] in` is rejected for a `def` that needs the instance (`contactAffected_iff_leg`); the linter tells you
  exactly which declarations to `omit` on — drop the `omit` where it errors.
* Section variables used only in a proof (here `hn` in `s7p_D_bounds`, `hη` in `s7p_side_of_r`) must be `include`d or made
  explicit; the two leaves' surrounding `section VertexEdge` supplies `{n} [NeZero n]` only.

## 5. Left

The leaf `s7_sliding_law_at` (its `sorry` untouched; closed conditionally on `hterm` alone by `s7p_sliding_law_at_of_hterm`,
§3).  Not touched (other units): `s7_bigon_law_at`, the row theorems `thm_C_S7_of`, `thm_C_S7_of_floor`, `thm_C_S7`.
