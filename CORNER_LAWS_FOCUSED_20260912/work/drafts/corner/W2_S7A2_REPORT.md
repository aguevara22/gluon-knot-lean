# W2_S7A2_REPORT — unit S7A2 (helper unit: the ROTATION EQUALITY `hr` of the persistent transport; prefix `s7a2_`), 2026-09-15

File: `work/drafts/corner/W2_S7A2.lean` = `Wave1_Assembled.lean` + ONE inserted block (lines 5544-6257, 714 lines,
50 declarations: 7 `def`, 43 theorems), placed inside `section VertexEdge` immediately BEFORE the docstring of the leaf
`s7_sliding_law_at` (now line 6261), i.e. right after U110-D's `s7d_cornerCoefficient_transport`.
`diff Wave1_Assembled.lean W2_S7A2.lean` = `5543a5544,6257`: a pure insertion, **0 deleted lines**; no definition,
structure, statement, name or docstring of the frozen file touched; no import added; no `open` added.
Check (official): `cd work/lean && lake env lean ../drafts/corner/W2_S7A2.lean` — **0 errors**; the only warning inside or
adjacent to the block is the expected `declaration uses sorry` of `s7_sliding_law_at` (6261); every other warning is
pre-existing in `Wave1_Assembled.lean` (the `sfta_`/`sg_` cosmetics of WAVE1_ASSEMBLY_REPORT §9, shifted by +714 lines).
~20 s warm.  `grep -c sorry`: 11 before → 11 after (this unit owns no leaf).
Axioms (`#print axioms` on a scratch copy): `s7a2_carrierRotation_eq`, `s7a2_cornerFamily_regular`,
`s7a2_cornerFamily_continuousOn`, `s7a2_cornerFamily_rotation`, `s7a2_cornerFamily_side_other`,
`s7a2_exists_intervalLocal`, `s7a2_cramer_symm` = `[propext, Classical.choice, Quot.sound]` — no `lit_homfly`/`lp_lm`.
Clash scan: `grep -rln s7a2_ work/lean/{SM,CV,RProof,Bridge}` empty; no other `U_*.lean`/`W2_*.lean` uses the prefix.
Uses from the file: `s7a_Persistent`, `s7a_visit`, `s7a_visit_twin`, `s7a_markMap(_inr)`, `s7a_isTrueCorner_persistent`,
`s7a_ccpCornerCount_eq`, `s7a_ccpCornerMark_map`, `s7a_componentEquiv`, `s7a_SideLocal`, `s7a_sideGeneric`,
`s7a_side_hs`, `s7a_side_hpar`, `s7a_sideComponentEquiv` (U110-A); nothing of U110-D/I (they come later in the file /
are consumers).

## 0. What this unit provides, in one paragraph

The geometric input U110-A left open (U_S7A_REPORT §2): **`hr`**, the equality of the real rotations `carrierRotation`
(def:uniform `r_Q = rot Q`) of corresponding carriers on the two sides of a simple vertex–edge wall for a PERSISTENT
support (a support avoiding the two contact crossings `{a, M−1}`, `{a, M}`), stated EXACTLY in the form U110-D's
`s7d_cornerCoefficient_eq_of_strictMono` / `_cut` take it (`hr : carrierRotation hn hP S q = carrierRotation hm hQ T q'`
with `hP := s7a_sideGeneric g b`, `hQ := s7a_sideGeneric g b'`, `T := S'`, `q' := s7a_sideComponentEquiv … q`):

```
theorem s7a2_carrierRotation_eq (hn : 3 ≤ n) (g : WallGerm n) {M a} {r η δ : ℝ} (h : g.VertexEdgeAt M a)
    (hloc : s7a2_IntervalLocal hn g M a r η δ) {t : g.SideParameter} (ht : t.val < δ)
    (hL : s7a_SideLocal hn g M a r η t) (b b' : Bool)
    (S : Finset (Crossing (g.curve (g.sideTime b t)))) (S' : Finset (Crossing (g.curve (g.sideTime b' t))))
    (hSS' : ∀ v hv, (s7a_visit (s7a_side_hs hn g hL b b') v hv).1 ∈ S' ↔ v.1 ∈ S)
    (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val) (hSp' : ∀ x ∈ S', ¬ ContactAffected M a x.val)
    (hS : IsDecomposition hn (s7a_sideGeneric g b) S) (q : Component hn (s7a_sideGeneric g b) S) :
    carrierRotation hn (s7a_sideGeneric g b) S q =
      carrierRotation hn (s7a_sideGeneric g b') S' (s7a_sideComponentEquiv hn g hL b b' S S' hSS' hSp hSp' q)
```

proved by lem:rot (ii) (`rotationNumber_family_constant`) along the family **`s7a2_cornerFamily hn g b S q : g.Parameter →
LabelledTuple (ccpCornerCount hn (s7a_sideGeneric g b) S q)`** — the corner polygon of `q` READ ON `g.curve u` (vertex
`i ↦ g.curve u i`; selected visit on edge `e` with twin edge `f` ↦ `edgePoint (g.curve u) e (edgeParameter (g.curve u) e f)`;
CSilent's `silentMarkPoint`/`silentCornerFamily` template) — which is **continuous on `|u| ≤ t`**
(`s7a2_cornerFamily_continuousOn`, `continuousAt_contact_edgeParameter` at the centre / `continuousAt_edgeParameter` off it)
and **regular on `|u| ≤ t` INCLUDING the wall `u = 0`** (`s7a2_cornerFamily_regular`; sm-4:495-500: positive edge pieces +
nonzero contact determinants).  Its side values are the corner polygon of `q` (`s7a2_cornerFamily_side_self`, literally)
and, up to `recastTuple` along the equal corner counts, the corner polygon of `s7a_sideComponentEquiv … q`
(`s7a2_cornerFamily_side_other`, from `s7a_ccpCornerMark_map`).  The family with `s7a2_cornerFamily_continuousOn` /
`s7a2_cornerFamily_regular` is EXACTLY the pair `(hf, hr)` U110-I's `s7i_full_rotation_germ` /
`s7i_full_rotation_germ_centre` / `s7i_carrierRotation_sides_of_family` take (the set is written
`{u : g.Parameter | |u.val| ≤ t.val}` as there), so no repackaging is needed; the centre value `rot(L*)` is supplied too
(`s7a2_cornerFamily_regular_centre`, `s7a2_rotation_centre : rotationNumber (family g.zeroParameter) = carrierRotation … q`).

## 1. The route (why it closes at the wall)

The difficulty is regularity AT the centre, where `g.center` is not generic (the contact triple `{a, a+1, M}` is its zero
triple), so `ccpCornerPolygon_regular` does not apply.  The route avoids any identification of the family with a carrier
polygon off the two sides:

1. **Edge formula** (`s7a2_point_sub`, pure algebra + Cramer symmetry `s7a2_cramer_symm`): for any polygon `Q`, if the
   OUTGOING edge of the mark `m` (`s7a2_outEdge`: the vertex's own edge; the twin's edge for a visit) is the INCOMING edge
   of `m'` (`s7a2_inEdge`: the previous edge at a vertex; the visit's own edge), then
   `point_Q m' − point_Q m = (inParam_Q m' − outParam_Q m) • edge Q (outEdge m)`, where the parameters are `0/1` for a
   vertex and the Cramer `edgeParameter`s for a visit (`s7a2_outParam`, `s7a2_inParam`).  Cramer symmetry (the crossing
   point read on either edge) needs only `det(edge e, edge f) ≠ 0`.
2. **Combinatorics on side `b`** (accepted lem:carriers (ii)): consecutive corners `c_j, c_{j+1}` of the carrier satisfy
   `outEdge c_j = inEdge c_{j+1}` (`s7a2_corner_edges` ← `ccpCornerPolygon_outEdge_eq_inEdge`) and
   `outParam c_j < inParam c_{j+1}` on `P_b` (`s7a2_corner_params_lt` ← the positive coefficient of `ccpCornerPolygon_edge`,
   read through `s7a2_point_eq_evaluation`: the mark point read on its own generic polygon is its traversal point).  The edge
   labels are constant along the family (they are labels of the FIXED corner marks of `q`), so
   `edge (family u) j = ψ_j(u) • edge (g.curve u) ε_j` at every `|u| < δ` (`s7a2_cornerFamily_edge`).
3. **`ψ_j` never vanishes on `|u| < δ`, including the centre** (`s7a2_psi_ne_zero`): vertex–vertex `ψ = 1`; vertex–visit /
   visit–vertex by interiority of the Cramer parameter of a persistent crossing (`s7a2_edgeParameter_interior`:
   `contact_pair_data.parameter_interior` at the centre, `crossingParameter_interior` off it); visit–visit on one edge by
   distinctness of the Cramer parameters of two persistent crossings (`s7a2_edgeParameters_ne`:
   `contact_unaffected_parameters_ne` at the centre — needs `g.concurrences = ∅`, i.e. `h.2.2.1` — and
   `generic_edgeParameters_ne` off it; the two twin edges differ because the parameters are strictly ordered on side `b`).
4. **Sign constancy** (`s7a2_pos_of_ne_zero`): `ψ_j` is continuous on `|u| < δ` (`s7a2_psi_continuousAt`), nonzero there,
   positive at `u = sideTime b t` ⇒ positive on `|u| ≤ t` (`PreconnectedSpace.constant` on `sign ∘ ψ_j` over
   `Set.Icc (−t) t`, as `generic_family_crossingOrder_constant` does).  This is "the edge pieces have positive lengths at the
   centre" — the piece lengths are obtained WITHOUT `VertexLocalData.visit_order` (the persistent visit ORDER is only used
   through U110-A's `s7a_side_hpar` inside `s7a_sideComponentEquiv`).
5. **Corner determinants**: `det(edge (family u) (j−1), edge (family u) j) = ψ_{j−1} ψ_j · det(edge Q (inEdge c_j), edge Q
   (outEdge c_j))` and the last factor is nonzero at every `|u| < δ` (`s7a2_corner_det_ne_zero`): at a vertex it is the turn
   determinant, nonzero because the turn triple is not the contact support (`s7a2_turn_ne_zero` ←
   `ChirotopesOutsideZerosAgree`'s nonzero clause + `contactSupport_ne_turnSupport`); at a selected visit it is the crossing
   determinant of a persistent crossing (`s7a2_det_ne_zero` ← `contact_pair_data.det_ne_zero` at the centre,
   `crossing_edgeParameter_det_ne_zero` off it).  Nonzero edges come from `ψ_j > 0` and `edge (g.curve u) ε ≠ 0`
   (`s7a2_edge_ne_zero`, from the turn determinant).  Hence `Regular` on `|u| ≤ t` via `regular_iff_edges`.
6. **lem:rot (ii)**: `rotationNumber_family_constant` on `Set.Icc (−t) t` (`s7a2_cornerFamily_rotation`), and the two side
   identifications give `hr`.

All local geometric facts are stated for EVERY parameter `|u| < δ` at once (the centre is the case `u.val = 0`, handled by
`Subtype.ext` + `subst`, the generic case by `g.generic_punctured`), fed by the interval form of lem:wall-sides (V):
`s7a2_IntervalLocal hn g M a r η δ := ∀ u, |u.val| < δ → VertexLocalData hn g.center (g.curve u) M a r η`
(`s7a2_exists_intervalLocal` from `vertex_sides`; `s7a2_sideLocal` restricts it to U110-A's `s7a_SideLocal` at any `t < δ`).

## 2. Proved (all `s7a2_`; `{n} [NeZero n]` from `section VertexEdge`)

### 2.1 Marks read on another polygon (section `S7A2Marks`; any `R Q : LabelledTuple n`)
* `s7a2_outEdge`, `s7a2_inEdge : Mark R → ZMod n`; `s7a2_outParam`, `s7a2_inParam (Q) : Mark R → ℝ`;
  `s7a2_point (Q) : Mark R → Plane` (+ 10 `@[simp]` unfolding lemmas `_inl`/`_inr`).
* `s7a2_cramer_vec` (Cramer's rule on abstract vectors, `det u v ≠ 0`), **`s7a2_cramer_symm`**
  (`edgePoint Q e (edgeParameter Q e f) = edgePoint Q f (edgeParameter Q f e)`).
* `s7a2_point_eq_in`, `s7a2_point_eq_out` (needs transversality for a visit), **`s7a2_point_sub`** (the edge formula).
* `s7a2_point_eq_evaluation (hn hP m) : traversalEvaluation P (markPosition hn hP.1 m) = s7a2_point P m` (generic `P`);
  `s7a2_visit_isCrossing`; `s7a2_outSlot_fst` (`(ccpOutSlot hn hP S m).1 = s7a2_outEdge m` for a true corner),
  `s7a2_inEdge_eq` (`ccpInEdge hn hP m = s7a2_inEdge m`); **`s7a2_corner_edges`**, `s7a2_det_ne_zero_generic`,
  **`s7a2_corner_params_lt`** (both need `hS : IsDecomposition`); `s7a2_det_smul_smul`.

### 2.2 The germ on the whole interval (section `S7A2Germ`; `(h : g.VertexEdgeAt M a) (hloc : s7a2_IntervalLocal …) {u} (hu : |u.val| < δ)`)
* `s7a2_IntervalLocal` (def), **`s7a2_exists_intervalLocal (M a h)`** (`∃ r η, 0<r<1 ∧ g.center M = edgePoint g.center a r ∧
  0<η ∧ 4η<r ∧ 4η<1−r ∧ ∃ δ, 0<δ ∧ δ ≤ g.radius ∧ s7a2_IntervalLocal hn g M a r η δ`), `s7a2_sideLocal (hloc ht) : s7a_SideLocal …`.
* `s7a2_crossing_iff` (persistent crossings agree with the centre's), `s7a2_chi_ne_zero`, `s7a2_turn_ne_zero`,
  `s7a2_turn_det_ne_zero`, `s7a2_edge_ne_zero`, **`s7a2_det_ne_zero`**, **`s7a2_edgeParameter_interior`**,
  **`s7a2_edgeParameters_ne`**, **`s7a2_continuousAt_edgeParameter`** (all at every `|u| < δ` including the centre).
* **`s7a2_pos_of_ne_zero`** (sign constancy on `|u| ≤ t`; generic in `ψ : g.Parameter → ℝ`).

### 2.3 The family (section `S7A2Family`; `(ht : t.val < δ) (b) (S) (hS) (hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val) (q)`)
* **`s7a2_cornerFamily hn g b S q : g.Parameter → LabelledTuple (ccpCornerCount hn (s7a_sideGeneric g b) S q)`** (def);
  **`s7a2_cornerFamily_side_self`** (`= ccpCornerPolygon hn (s7a_sideGeneric g b) S q` at `g.sideTime b t`, `funext`+`rfl`-level).
* `s7a2_corner_crossing`, `s7a2_corner_crossing'` (a selected visit's crossing is a persistent crossing of the centre, both
  pair orders), `s7a2_corner_hd`, **`s7a2_cornerFamily_edge`**, **`s7a2_psi_ne_zero`**, `s7a2_psi_continuousAt`,
  **`s7a2_psi_pos`**, `s7a2_corner_det_ne_zero`, **`s7a2_cornerFamily_regular (u) (hu : |u.val| ≤ t.val)`**,
  **`s7a2_cornerFamily_continuousOn : ContinuousOn (s7a2_cornerFamily hn g b S q) {u : g.Parameter | |u.val| ≤ t.val}`**,
  **`s7a2_cornerFamily_rotation (u) (hu) : rotationNumber (family u) = rotationNumber (family (g.sideTime b t))`**.

### 2.4 Assembly (section `S7A2Assembly`; the U110-A transport data `hL b b' S S' hSS' hSp hSp'`)
* `s7a2_point_markMap` (the point of a persistent mark read on `Q'` is unchanged by `s7a_markMap`),
  `s7a2_sideCornerCount_eq` (equal corner counts stated on `s7a_sideComponentEquiv`), **`s7a2_cornerFamily_side_other`**
  (`family (g.sideTime b' t) = recastTuple _ (ccpCornerPolygon hn (s7a_sideGeneric g b') S' (s7a_sideComponentEquiv … q))`),
  **`s7a2_carrierRotation_eq`** (= `hr`), `s7a2_cornerFamily_regular_centre`, `s7a2_rotation_centre`.

## 3. How to consume (U110-E sliding step (1); U110-F/K bigon ineligible `T`)

1. `obtain ⟨r, η, -, -, -, -, -, -, δ, hδ, hδr, hloc⟩ := s7a2_exists_intervalLocal hn g M a h.1` (for `h : g.SlidingAt M a`;
   `h` itself for `VertexEdgeAt`).  For `t.val < δ`: `hL := s7a2_sideLocal hn g hloc ht` (any other proof of
   `s7a_SideLocal hn g M a r η t`, e.g. from `s7a_exists_sideLocal`, is interchangeable — proof irrelevance; but then use the
   radius `δ` of THIS unit for `ht`, or take the minimum of the two radii).
2. With U110-A's `e := s7a_sideComponentEquiv hn g hL b b' S S' hSS' hSp hSp'`, the coefficient equality of a spectator
   carrier is `s7d_cornerCoefficient_eq_of_strictMono hn hn (s7a_sideGeneric g b) (s7a_sideGeneric g b') hS q hS' (e q) φ hmem
   hmono htwin hbit (s7a2_carrierRotation_eq hn g h.1 hloc ht hL b b' S S' hSS' hSp hSp' hS q)` — the `hr` slot exactly.
   `s7a_sideGeneric g b` is definitionally `(g.sideTuple b t).property`, so the statement also type-checks against
   `Component hn (g.sideTuple b t).property S` (the form of `CS7Data` / `s7i_carrierRotation_sides_of_family`).
3. U110-I: `s7i_full_rotation_germ g t (s7a2_cornerFamily_continuousOn hn g h hloc ht b S hSp q)
   (s7a2_cornerFamily_regular hn g h hloc ht b S hS hSp q)` and `s7i_full_rotation_germ_centre …` apply verbatim; for
   `s7i_carrierRotation_sides_of_family` take `f := s7a2_cornerFamily hn g false S q`, `hm := s7a2_cornerFamily_side_self …`
   (with `hkm := rfl`, `recastTuple_rfl`), `hp := (s7a2_cornerFamily_side_other hn g hL false true …).symm`.
   `rot(L*) = rot(L_L) = rot(L_H)` for a persistent carrier is `s7a2_rotation_centre`.

## 4. Not proved / not attempted (and why) — read before U110-B/C/E/F/K

* **Scope: PERSISTENT supports only** (`hSp : ∀ x ∈ S, ¬ ContactAffected M a x.val`, the hypothesis of U110-A's transport).
  This is exactly PLAN §3.3 sliding step (1) ("supports avoiding `x₋`") and the bigon "ineligible `T`" cancellation.  NOT
  covered, and not provable by this family: (i) the sliding RELOCATED carriers (`x₋ ∈ S`, step (2)) — the leg visit moves
  from edge `M−1` to edge `M`, the corner polygons differ combinatorially across the wall, and the printed route is
  principal-angle addition in one open half-plane (eq. s7c:turn-short-a/b, U110-B/C), not lem:rot (ii); (ii) the bigon
  FULL contact carrier `L_H = T ∪ {x, y}` vs `L_L` (eq. s7c:full-rotation as printed for the contact carrier) — `x, y` are not
  persistent and the low side has four marks fewer; the family of the contact carrier through the wall (sm-4:493-503, the
  contact triangle at the centre) is U110-I's/U110-B's construction and must be built from the half/contact geometry, not
  from `s7a_ccpCornerMark_map`; (iii) `hr` between a carrier of `P` and a carrier of a HALF `λᵢ` (the `_cut` consumer):
  different polygon sizes, the rotation ledger `s7i_rotation_ledger_*` is the printed route.
* No `MarkTransport`/`Deform` is built (not needed: the record route of U110-D needs only `hr`).
* Nothing believed false.  No missing hypothesis found in the printed argument; the one hypothesis this unit makes
  explicit beyond U110-A's is the INTERVAL form of lem:wall-sides (V) (`s7a2_IntervalLocal`, i.e. `vertex_sides`'s own
  `∀ t, |t| < δ → VertexLocalData …` kept on the whole interval rather than sampled at `±t`), needed for continuity and
  nonvanishing at every `|u| ≤ t`; and `g.concurrences = ∅` (`h.2.2.1`, part of `VertexEdgeAt`) for the visit–visit case.

## 5. Mathlib / Lean pitfalls hit (v4.34.0-rc2 pin)

* `field_simp` did NOT clear the Cramer denominators once `Prod` projections were unfolded (residual `⁻¹` terms; both
  before and after destructuring the vectors).  What works: destructure `a b u v : Plane` into coordinates, rewrite the
  second denominator as `−D` (`div_neg`), `div_eq_mul_inv`, then `linear_combination (b1 − a1) * (mul_inv_cancel₀ hd)`.
* `ContinuousAt.comp` on a goal `ContinuousAt (fun w => sign (ψ (ι w))) w` unifies the wrong way when nested; give
  `(g := SignType.sign) (f := fun w => ψ (ι w)) (x := w)` explicitly (and likewise `(f := ι)` for the inner one).
* `ContinuousAt.continuousOn` does not exist here; use `intro u hu; apply ContinuousAt.continuousWithinAt`.
* `rw [rotationNumber_recastTuple] at h` fails ("target not type-correct under implicit transparency") when the recast's
  proof term is stated on `s7a_componentEquiv` while the tuple is on `s7a_sideComponentEquiv` (a `def` wrapper): state the
  count equality on the wrapper (`s7a2_sideCornerCount_eq`) and prove `side_other` through an explicit `show` of the
  unfolded form before `rw [s7a_ccpCornerMark_map]`.
* `rw [s7a2_point_eq_evaluation]` with `hP` implicit leaves a `case hP : Generic P` goal (the projection `hP.1` in the
  pattern does not unify); pass `hP` explicitly.
* `VertexLocalData.windows.1 s hs : IsCrossing (g.curve u) s ↔ IsCrossing g.center s` (Q-side first) — no `.symm`.
* The centre case is `rcases eq_or_ne u.val 0 with hu0 | hu0; · have : u = g.zeroParameter := Subtype.ext hu0; subst this`,
  after which `g.curve g.zeroParameter` is `g.center` by `exact` (delta), and `h.2.1 : g.pointZeros = _` /
  `h.2.2.1 : g.concurrences = ∅` are accepted where `pointZeroTriples g.center = _` / `concurrenceTriples g.center = ∅` are
  expected.
* `omit [NeZero n] in` must precede the docstring; `edgePoint_sub_edgePoint` needs `[NeZero n]` (so `s7a2_point_sub` keeps it).

## 6. Left

Nothing of this unit's description.  Not touched (other units): `sg_daughters_products`, `s7_sliding_law_at`,
`s7_bigon_law_at`, `sft_same_sign`, `sft_loop`, the four §6 row theorems.
