# U_S7A_REPORT — unit U110-A (helper unit: the contact-wall partial mark transport on persistent marks; prefix `s7a_`), 2026-09-15

File: `work/drafts/corner/U_S7A.lean` = `Statements_FINAL.lean` + ONE import line + ONE inserted block (lines 455-1766,
1312 lines, 88 declarations: 5 `def`/`abbrev`, 83 theorems), placed inside `section VertexEdge` immediately before the
docstring of `s7_sliding_law_at` (the first leaf that consumes them, U110-E; U110-F/K consume them for the bigon branch).
`diff Statements_FINAL.lean U_S7A.lean` = `16a17` (the import) + `453a455,1766` (the block): pure insertions, 0 deleted
lines; no definition, structure, statement, name or docstring of the frozen file touched.
Check (official): `cd work/lean && lake env lean ../drafts/corner/U_S7A.lean` — **0 errors, 0 non-sorry warnings**, exactly
14 `declaration uses sorry` warnings (the other units' 10 leaves + the 4 §6 row theorems). ~18 s warm.
`grep -c sorry`: 16 before → 16 after (this unit owns no leaf).
Axioms (`#print axioms` on a scratch copy): `s7a_componentEquiv_owner`, `s7a_isDecomposition_iff`, `s7a_carrierUniform_iff`,
`s7a_ccpCornerMark_map`, `s7a_side_sgn`, `s7a_sliding_relocation_sign` = `[propext, Classical.choice, Quot.sound]` — no
`lit_homfly`/`lp_lm` (nothing here touches `homfly`; coefficient transport is U110-D's record route).
Clash scan: `grep -rln s7a_ work/lean/SM` empty; no other `U_*.lean` uses the prefix.

## ASSEMBLER MUST KNOW — one header change

**`import SM.VertexSides` was added** (line 17, after `import SM.GermSides`). PLAN_FINAL §3.3 names lem:wall-sides (V)
(`vertex_sides`, `VertexLocalData.visit_order`, `contactVisitTransport`, SM/VertexSides.lean:16-40) as THE setup of row
110, but `SM.VertexSides` (and `SM.ContactVisitOrder`, `SM.ContactCrossingSides`, …) is NOT in the transitive closure of
`Statements_FINAL.lean`'s imports (checked: `VertexLocalData`, `contactVisitTransport`, `VertexCrossingData` are unknown
identifiers there). The module is accepted (`work/lean/SM/VertexSides.lean`, olean present); the import adds no axiom.
At assembly, union the import lists (all other units add none). Nothing else in the header changed.

## 0. What this unit provides, in one paragraph

Two generic polygons `P, Q` (same `n`) that agree on the "persistent" crossings — every crossing support other than the two
contact pairs `{a, M−1}`, `{a, M}` (`ContactAffected M a`) — with the same-edge parameter ORDER of persistent visits
preserved, are related by a **partial mark transport**: the vertices are fixed, the persistent visits are carried by
`contactVisitTransport` (same support, same edge), the contact visits are not carried at all. For a support `S ⊆ Crossing P`
of persistent crossings and its transport `S'` the carriers correspond (`s7a_componentEquiv : Component hn hP S ≃
Component hn hQ S'`, owner-compatible on persistent marks), decompositions correspond (`s7a_isDecomposition_iff`), the
corner LISTS correspond literally (no rotation: `s7a_ccpCornerList_map`), hence corner counts, corner marks and — given vertex
turns and crossing signs of persistent crossings — the turns of the corner polygons and uniformity correspond
(`s7a_turn_ccpCornerPolygon`, `s7a_carrierUniform_iff`); a persistent crossing is a self-crossing of a carrier iff its
transport is one of the corresponding carrier (`s7a_mem_carrierCrossings`); interlacement of persistent crossings is
carried (`s7a_interlaces_iff`). At a simple vertex–edge wall the hypotheses are DISCHARGED for any two sides `b, b'` at one
side parameter `t` below the radius of lem:wall-sides (V): crossing agreement `s7a_side_hs`, parameter order `s7a_side_hpar`,
vertex turns `s7a_side_turn`, crossing signs `s7a_side_sgn`, and the sliding relocation sign `s7a_sliding_relocation_sign`
(`sgn det(E_a,E_M)` on the `{a,M}` side = `sgn det(E_a,E_{M−1})` on the `{a,M−1}` side — U110-D note 1's over-bit input for
`x₋ ↦ x₊`). This covers PLAN §3.3 sliding step (1) and the bigon "ineligible `T`" cancellation and eligible-`T` carrier
correspondence up to the coefficient equality (U110-D's `s7d_cornerCoefficient_eq_of_strictMono/_cut`), whose remaining
geometric input — the ROTATION equality `hr` — is NOT provided here (see §2).

The route is combinatorial (no lists rotated, no `List.next` of filtered lists): the smoothing successor `f` of a persistent
support is contracted to a permutation of the persistent marks by FIRST RETURN (`s7a_returnTime` = `Nat.find`, `s7a_step`,
`s7a_stepPerm`), its cycles are the `f`-cycles (`s7a_sameCycle_stepPerm_iff`, by strong induction on the power), and the
contracted step is characterized ORDER-theoretically as "the first persistent mark strictly after `selectedMarkPerm S m`
in the cyclic order" (`s7a_step_firstAfter`, from the **sweep lemma** `s7a_sweep`: a `nextMark`-chain sweeps the circle in
order, proved from the accepted `markSuccessor_no_mark_between` + `markSuccessor_sameCycle` + the `CircularOrder`
`traversalCircularOrder`); the characterization is carried by the mark map because cyclic betweenness of persistent marks
is (`s7a_between_map`, from the key-order transfer `s7a_markKey_lt`, the persistent analogue of `Carrier.markKey_lt_transport`),
so the two contracted permutations are conjugate (`s7a_stepPerm_map`) and `Quotient.congr` gives the carrier equivalence.

## 1. Proved (all `s7a_`; `{n} [NeZero n]` from `section VertexEdge`)

### 1.1 Persistent marks and the mark map (section `Transport`)
* `s7a_Persistent M a : Mark P → Prop` (vertices; visits of unaffected crossings); `s7a_persistent_inl/_inr` (simp).
* `s7a_visit hs v hv : Visit Q` (transported persistent visit; `hs : ∀ s, ¬ContactAffected M a s → (IsCrossing Q s ↔
  IsCrossing P s)` — the direction of `contactVisitTransport`, P → Q); `_support`, `_edge`, `_eq_contactVisitTransport` (rfl),
  `_not_affected`, `_injective`, `_surjective`, `s7a_visit_ext` (Sigma-ext by crossing and edge), **`s7a_visit_twin`**
  (`s7a_visit hs (visitTwin v) hv = visitTwin (s7a_visit hs v hv)`).
* `s7a_markMap hs : Mark P → Mark Q` (total: vertices fixed, persistent visits transported, contact visits ↦ `inl 0` — junk,
  never reached); `_inl` (simp), `_inr (hv)`, `_persistent`, `_injOn`, `_surjOn`, **`s7a_markMap_selectedMarkPerm`**
  (commutes with the selected exchange when `(s7a_visit hs v hv).1 ∈ S' ↔ v.1 ∈ S`).
* **`s7a_markKey_lt`** (key order of persistent marks carried, given `hpar`: same-edge parameter order of persistent visits);
  **`s7a_markList_filter`**: `(markList hn hQ).filter pers = ((markList hn hP).filter pers).map (s7a_markMap hs)` — literal,
  no rotation (`List.Perm.eq_of_pairwise`).

### 1.2 Cyclic order helpers (section `Cyclic`)
* `s7a_cyc_or` (ℝ trichotomy of three distinct keys), `s7a_between_or` (three distinct marks are `traversalBetween` one way or
  the other), `s7a_between_trans` (`sbtw_trans_left`), `s7a_between_asymm`, `s7a_between_ne`.

### 1.3 The contracted successor (section `Contract`)
* `s7a_PMark M a P := {m : Mark P // s7a_Persistent M a m}`; `s7a_exists_return` (witness `orderOf f`), `s7a_returnTime` (`Nat.find`),
  `_pos`, `_persistent`, `_min`; `s7a_step`, `s7a_step_val`, `s7a_step_inj_aux`, `s7a_step_injective`, `s7a_stepPerm : Equiv.Perm
  (s7a_PMark M a P)` (`Equiv.ofBijective`, `Finite.injective_iff_bijective`), `s7a_stepPerm_apply`; `s7a_sameCycle_step`,
  `s7a_sameCycle_of_stepPerm`, `s7a_stepPerm_of_sameCycle` (strong induction on the power), **`s7a_sameCycle_stepPerm_iff`**;
  `s7a_component_has_persistent` (every carrier of a persistent support has a persistent mark — `component_has_trueCorner`);
  **`s7a_componentEquivQuot : Component hn hP S ≃ Quotient (SameCycle.setoid (s7a_stepPerm …))`**, `s7a_componentEquivQuot_owner`.

### 1.4 The order characterization (section `FirstAfter`)
* `s7a_pow_apply_mod` (power reduction at a periodic point), `s7a_pow_period`; **`s7a_sweep`** (the sweep lemma);
  `s7a_pow_eq_markSuccessor_pow` (`f^i x = nextMark^i (selectedMarkPerm S x)` up to the return time: intermediate marks are
  unselected contact visits); `s7a_exists_vertex_ne` (a vertex avoiding two marks, `n ≥ 3`); **`s7a_step_firstAfter`**
  (`step x ≠ p ∧ ∀ z pers, z ≠ p → z ≠ step x → between p (step x) z`, `p := selectedMarkPerm S x`); `s7a_firstAfter_unique`.

### 1.5 Conjugation and the carrier equivalence (section `Conjugation`)
* `s7a_sameCycle_of_equiv_conj` (generic; re-proved, FlatCarriers' is not imported); `s7a_pmarkEquiv hs : s7a_PMark M a P ≃
  s7a_PMark M a Q`, `_val`; **`s7a_between_map`** (cyclic betweenness of persistent marks carried); **`s7a_step_map`**,
  `s7a_stepPerm_map` (conjugation); **`s7a_componentEquiv hn hP hQ hs hpar S S' hSS' hSp hSp' : Component hn hP S ≃ Component hn hQ S'`**
  with **`s7a_componentEquiv_owner : e (owner hn hP S m) = owner hn hQ S' (s7a_markMap hs m)`** for persistent `m`.
  Hypotheses: `hSS' : ∀ v hv, (s7a_visit hs v hv).1 ∈ S' ↔ v.1 ∈ S` (S' is the transport of S), `hSp : ∀ x ∈ S, ¬affected`,
  `hSp' : ∀ x ∈ S', ¬affected`.

### 1.6 Consequences on carriers (section `Carriers`)
* `s7a_cross hs x hx : Crossing Q` (transported persistent crossing), `_val`, `s7a_visit_fst`, `s7a_cross_surj`, `s7a_cross_mem`
  (`s7a_cross hs x hx ∈ S' ↔ x ∈ S`); **`s7a_mem_carrierCrossings`** (`s7a_cross hs x hx ∈ carrierCrossings … (e q) ↔ x ∈
  carrierCrossings … q`, persistent `x`); `s7a_isTrueCorner_persistent`, `s7a_isTrueCorner_map`; **`s7a_ccpCornerList_map`**
  (`ccpCornerList hn hQ S' (e q) = (ccpCornerList hn hP S q).map (s7a_markMap hs)`), `s7a_ccpCornerCount_eq`,
  **`s7a_ccpCornerMark_map`** (`ccpCornerMark … (e q) (Equiv.cast _ j) = s7a_markMap hs (ccpCornerMark … q j)`);
  `s7a_markTurn_map` (given `hturn : ∀ i, turn Q i = turn P i` and `hsgn` = crossing signs of persistent crossings carried),
  **`s7a_turn_ccpCornerPolygon`** (turns index by index, needs `IsDecomposition` on both sides), **`s7a_carrierUniform_iff`**;
  **`s7a_interlaces_iff`** (persistent crossings), **`s7a_isDecomposition_iff`**.

### 1.7 At a simple vertex–edge wall (section `Germ`)
* `s7a_SideLocal hn g M a r η t := ∀ b, VertexLocalData hn g.center (g.curve (g.sideTime b t)) M a r η`;
  **`s7a_exists_sideLocal (h : g.VertexEdgeAt M a)`** (`∃ r η, 0<r<1 ∧ g.center M = edgePoint g.center a r ∧ 0<η ∧ 4η<r ∧ 4η<1−r
  ∧ ∃ δ, 0<δ ∧ δ ≤ radius ∧ ∀ t, t.val < δ → s7a_SideLocal …`) from the accepted `vertex_sides`; `s7a_sideGeneric g b`.
* For `hL : s7a_SideLocal …` and any two sides `b b'` (transport from side `b` to side `b'`): **`s7a_side_hs`** (the `hs`),
  **`s7a_side_hpar`** (the `hpar`, from `visit_order` on both sides composed through the centre), **`s7a_side_turn (h)`** (vertex turns
  agree, `ChirotopesOutsideZerosAgree` + `contactSupport_ne_turnSupport`), `s7a_crossingSign_eq_chi` (`crossingSign P i j =
  chi P i (i+1) (j+1)` for a crossing of a `G1` polygon — from `crossing_test`), **`s7a_side_sgn (h)`** (crossing signs of
  persistent crossings agree: the triple `{e, e+1, f+1}` of an unaffected pair is never the contact support, via
  `contactSupport_successive`), `s7a_signType_mul_eq_neg_one`, **`s7a_sliding_relocation_sign (h : g.SlidingAt M a)`**.
* Convenience instantiations: `s7a_sideComponentEquiv`, `_owner`, `s7a_side_isDecomposition_iff`, `s7a_side_carrierUniform_iff (h)`,
  `s7a_side_mem_carrierCrossings`.

## 2. Not proved / not attempted (and why) — read this before U110-E/F/K

* **The rotation equality `hr`** (`carrierRotation` of corresponding carriers, lem:rot (ii) along the regular family of
  corner polygons through the wall, eq. s7c:full-rotation) is NOT here. It is the only geometric input U110-D's coefficient
  transport still needs (`s7d_cornerCoefficient_eq_of_strictMono/_cut` take `hr`), and U110-I's `s7i_full_rotation_germ`
  expects the FAMILY `f : g.Parameter → LabelledTuple k` of corner polygons continuous and regular on `|u| ≤ t` (regularity
  at the centre `u = 0` via positive edge pieces + nonzero contact determinants, sm-4:495-500). What this unit gives towards it:
  the corner polygon of `e q` is the corner polygon of `q` "read at `Q`" — `s7a_ccpCornerMark_map` identifies the corner marks
  index by index, so the family is `u ↦ (j ↦ point of the corner mark `ccpCornerMark hn hP S q j` read on `g.curve u`)`
  (vertex `i ↦ g.curve u i`; persistent selected visit on edge `e` with twin edge `f` ↦ `edgePoint (g.curve u) e (edgeParameter
  (g.curve u) e f)`, continuous by `continuousAt_contact_edgeParameter` at the centre / `generic_family_edgeParameter_continuous`
  off it; CSilent's `silentMarkPoint`/`silentCornerFamily` is the template). Estimated 600-900 further lines; recommend a
  dedicated lane (U110-A2) — it is on the critical path of U110-E.
* `carrierCrossingCount`/`cornerSlot` equality is NOT claimed (false in general: a contact crossing can be a self-crossing of a
  carrier on one side only — sliding: `x₋ ∈ cc(q)` iff `x₊ ∈ cc(e q)` is TRUE but needs the relocation of the contact visits,
  not provided here; bigon: `x, y ∈ cc(L_H)` with no counterpart on `P_L`). `s7a_mem_carrierCrossings` covers exactly the
  persistent crossings; the contact crossings are the consumers' case analysis (sliding: the leg visit `x₋` on `M−1` is the
  mark before `μ_M`, the a-visit's neighbours are persistent — both facts follow from the window clause `visit_windows` and
  `s7a_step_firstAfter`; U110-E should prove `owner (inr x₋-visit) = owner (inl M)`-type facts with the sweep lemma).
* The over-bit hypothesis `hbit` of U110-D for the RELOCATED visit is `s7a_sliding_relocation_sign` +
  `s7d_positiveOverBit_eq_of_crossingSign`; for persistent visits it is `s7a_side_sgn` + the same `s7d_` lemma.
* No `MarkTransport` (CChamber) is built: the full mark lists are NOT rotations of each other at a contact wall (the leg visit
  and `μ_M` swap; the bigon side has 4 extra marks), so `cornerStateSum_transport` does not apply — U110-E must reindex
  `uniformDecompositions` by hand (device of `cornerStateSum_transport`: `Finset.sum_nbij` on the underlying sets), with
  `s7a_isDecomposition_iff`, `s7a_carrierUniform_iff` (for `mem_uniformDecompositions`) and `s7d_cornerProduct_eq_of_equiv`
  on `s7a_componentEquiv`.
* Nothing believed false. No missing hypothesis found in the accepted inputs; the only hypothesis the printed text leaves
  implicit that these statements make explicit is `hSp'` (the transported support is persistent — automatic for the image).
* U110-G GO/NO-GO: not this unit's content; see U_S7G_REPORT.md (NO-GO on the RI/RII witnesses within budget).

## 3. How to consume (U110-E sliding step (1), U110-F ineligible/eligible `T`)

1. `obtain ⟨r, η, -, -, -, -, -, -, δ, hδ, hδr, hloc⟩ := s7a_exists_sideLocal hn g M a h.1` (for `h : g.SlidingAt M a`, or
   `h` itself for `VertexEdgeAt`); for `t.val < δ`, `hL := hloc t ht`. Sides: `P₋ = g.curve (g.sideTime false t)`,
   `P₊ = g.curve (g.sideTime true t)`; genericity `s7a_sideGeneric g b` (definitionally `(g.sideTuple b t).property`).
2. For a support `S` of `P₋` avoiding the contact crossings, `S' := S.map ⟨fun x => s7a_cross hs x _, …⟩` (or any `S'` with
   `hSS'`); `hs := s7a_side_hs hn g hL false true`, `hpar := s7a_side_hpar hn g hL false true`.
3. `e := s7a_sideComponentEquiv hn g hL false true S S' hSS' hSp hSp'`; `s7a_side_isDecomposition_iff`,
   `s7a_side_carrierUniform_iff hn g h.1 hL …` give the index-set bijection; `s7a_side_mem_carrierCrossings` +
   `s7a_ccpCornerMark_map`/`s7a_ccpCornerCount_eq` feed U110-D's `hmem`/`hmono` (via `s7d_strictMono_of_edgewise` with
   `hedge := s7a_visit_edge`, `hpar`), `htwin := s7a_visit_twin`, `hbit` via `s7d_positiveOverBit_eq_of_crossingSign` +
   `s7a_side_sgn`; `hr` = the missing rotation input (§2).
4. Sliding relocation: `htest` from `g.vertexEdge_contact_tests hn h.1` at `g.sideTime b t` (`g.sideTime_val_abs`,
   `g.sideTime_ne_zero`); then `s7a_sliding_relocation_sign hn g h hL b b' hb hb' htest`.

## 4. Mathlib / Lean pitfalls hit (v4.34.0-rc2 pin)

* `match`-defined functions (`s7a_markMap`) do not reduce under `rw [dif_neg]`; use `show (if hv' : … then … else …) = _`
  then `rw [dite_eq_right hv]` (`dif_neg` is deprecated → `dite_eq_right`).
* Proof-term coercions: `hm : s7a_Persistent M a (Sum.inr v)` is NOT accepted where `¬ContactAffected M a v.1.val` is expected
  inside `rw` (implicit transparency); restate with `have hv0 : ¬ContactAffected M a v.1.val := hm` first.
* `Subtype.ext (congrArg Subtype.val h')` fails when `h' : s7a_cross … = s7a_cross …` and the expected type is `x = y`
  (unifier picks the wrong subtype); use `have hv := congrArg Subtype.val h'; exact Subtype.ext hv`.
* `rw [he]` with `he : x = y` on a goal containing `s7a_cross hs x hx` fails (motive not type correct: `hx` depends on `x`);
  use `subst he; rfl`.
* `CircularOrder (TraversalPoint n)` is the DEF `traversalCircularOrder`, not an instance: `let _inst : CircularOrder
  (TraversalPoint n) := traversalCircularOrder` inside the proof (`have` makes it opaque → "synthesized instance not defeq";
  `letI` triggers the `haveILetI` linter); then `sbtw_trans_left`, `sbtw_asymm`, `sbtw_cyclic_left` via `traversalBetween_eq_circular`.
* Section variables used only in a PROOF are not included: `include hpar hSS' hSp hSp' in` before the docstring (an `omit … in`
  must also precede the docstring).
* `Nat.lt_succ_iff.mp` on `k % (j+1) < j + 1` fails to unify `j + 1` with `Nat.succ j`; use `by omega`.
* `ZMod.nontrivial_iff.mpr (by omega)` needs `hn` in scope; `prev_ne_self`/`next_ne_self` need `[Nontrivial (ZMod n)]`.
* `Ne.lt_or_lt` is not a valid field on `x ≠ y` (it unfolds to a function type); use `lt_trichotomy` with an `absurd` case.
* `pow_succ' : a^(n+1) = a * a^n` (NOT `a^n * a`, which is `pow_succ`) — matters for `Equiv.Perm.mul_apply` directions.

## 5. Left

Nothing of this unit's PLAN description except the rotation family (§2, recommended as its own lane). Not touched (other
units): `sg_isolated_undominated`, `sg_daughters_products`, `sg_daughters_rotation`, `s7_sliding_law_at`, `s7_bigon_law_at`,
`s7_universal_extraction`, `s7_corner_product` 2nd conjunct, `sft_same_sign`/`sft_mixed`/`sft_loop`, the §6 row theorems.
