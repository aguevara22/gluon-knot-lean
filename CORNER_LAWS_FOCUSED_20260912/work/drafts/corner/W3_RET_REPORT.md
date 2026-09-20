# W3_RET_REPORT — unit RET (prefix `s7r_`; serving `s7_sliding_law_at`), 2026-09-15 22:10 UTC / 6:10pm ET (wave 3, bounded test A-110-1)

File: `work/drafts/corner/W3_RET.lean` (2,278 lines) = `W3_Skeleton.lean` with ONE `s7r_` block (2,181 lines) inserted inside
`section VertexEdge` immediately before the docstring of `s7_sliding_law_at`; the skeleton text before and after the block is
byte-identical (checked).  Frozen statements/names/docstrings untouched; both leaf `sorry`s untouched.
**Compile** (`cd work/lean && lake env lean ../drafts/corner/W3_RET.lean`, ~100 s): **0 errors, 0 warnings other than the two
`declaration uses 'sorry'` of the leaves** (`s7_sliding_law_at` 2207, `s7_bigon_law_at` 2226).  `grep -c sorry` = 3 (line 4 of the
frozen header comment + the two leaf bodies 2215, 2235).  No `sorry` in the `s7r_` block; no black box remains.

## 0. In one paragraph

`s7b_SlidingTransport.ret` (U_S7B_REPORT §2.1, the one geometric field of U110-B's transport structure) is **PROVED on the side of the
wall whose contact crossing is `{a, M−1}`** (leg `false`), for every sliding row `S ∋ x` whose other crossings are carried from the halves,
below the interval radius of lem:wall-sides (V): `s7r_slidingTransport_side` (germ) / `s7r_slidingTransport_of_leg_false` (side polygon).
On the OTHER side (contact crossing `{a, M}`, leg `true`) the statement is **FALSE as written** (rule 4, §2): `s7b_slidingMark` fixes
`inl (inl 0) ↦ μ_M`, but there `nextMark μ_M = v_ℓ = s7b_slidingMark (inr (inl 0))`, so the first `f`-step from an image mark of `λ₁` lands
on an image mark of `λ₂`.  The corrected mark map (`λ₁`'s vertex `0 ↦ v_a`, `λ₂`'s vertex `0 ↦ μ_M`; the leg visit is the skipped extra
corner) is `s7r_slidingMark'`, the corrected structure `s7r_SlidingTransport'`, and **its first-return law is PROVED too**:
`s7r_slidingTransport_side'` / `s7r_slidingTransport_of_leg_true`; its consequences (`componentEquiv`, owners, carrier crossings, `m_Q`)
are ported in `namespace s7r_SlidingTransport'`.  Both proofs run on one generic first-return engine (§1.A).  Estimated size in the
brief: 600-900 lines; actual: 2,181 lines for both sides + engine + consequences + germ wiring.

## 1. Proved (all `s7r_`; `{n} [NeZero n]` from `section VertexEdge`)

### 1.A Generic first-return engine (section `S7RReturn`, lines 38-244; any generic polygon `P`)
* `s7r_Transit hn hP S ι w` := `w ∉ range ι ∧ smoothingSuccessor S w = nextMark w`.
* `s7r_not_between_self`, `s7r_between_nextMark` (`nextMark u` is cyclically between `u` and any third mark: `s7a_between_or` +
  `nextMark_no_mark_between`), `s7r_card_lt` (the finset of marks between shrinks along `nextMark`: `s7a_between_trans`).
* **`s7r_reach_of_transit`**: if every mark cyclically between `u` and `m'` is transit, the iterates of `f` from `nextMark u` reach `m'`
  staying off the image (strong induction on the number of marks between; wrap-agnostic).
* **`s7r_hit_of_transit`**: with one image mark as beacon, every mark reaches the image provided each off-image mark either reaches
  the image by some iterate or steps as the plain successor.
* `s7r_step_of_reach` (a reach from `selectedMarkPerm S (ι b)` is a `s7b_ReturnTransport.step`), `s7r_reach_trans` (composition
  through one off-image mark whose `f`-step is a jump: the contact visit).
* Key decoders `s7r_between_next_vertex` (between `u` on edge `e` and the vertex `e+1` ⇒ on edge `e` beyond `u`; wrap `e = −1`
  included) and `s7r_between_same_edge_of` (between two marks of one edge ⇒ on that edge, parameter strictly between).

### 1.B The side polygon with leg `M − 1` (section `S7RSide`, lines 246-1040)
Hypotheses (all supplied at the germ, §1.E): `hz hm hr hr0 hr1 hη hQC`, `hw : ContactParameterWindows P Q M a r η`,
`hord` (= `VertexLocalData.visit_order`: same-edge parameter order of persistent visits agrees between `Q` and the centre),
`hside` (side-of-`r` law on edge `a`: `visitParameter (s7a_visit hQC u hu) < r ↔ visitParameter u < r`),
`hc : IsCrossing Q {a, contactLeg false M}`, `huniq`, `S`, `hxS : (s7e_va hc).1 ∈ S`,
`hSimg : ∀ y ∈ S, y ≠ x → y ∈ range firstCrossingQ ∪ range secondCrossingQ`.
* `s7r_firstVisitQ_eq / s7r_secondVisitQ_eq` (`s7b_firstVisitQ v = s7a_visit hQC (s7b_firstHalfVisit v) _`, `rfl`).
* **`s7r_first_order` / `s7r_second_order`**: same-edge Q-order of carried visits = the half's order (`s7b_visitParameter_*`: equality
  off the cut, `r·t` / `r + (1−r)t` on it, then `hord`).
* **`s7r_first_cut_lt`** (`Qparam (firstVisitQ v) < r − 3η` on the cut), **`s7r_second_cut_gt`** (`r + 3η < Qparam (secondVisitQ v)`):
  `hside` + the window `s7e_persist_a`.
* `s7r_inr_mem_range_iff` (a visit is an image mark iff it is `vm` or carried from a half), `s7r_va_not_mem_range`,
  `s7r_vl_affected`, `s7r_va_affected`, `s7r_leg_false`.
* `s7r_transit_of` (not `v_ℓ`, not carried, not `v_a` ⇒ transit, via `hSimg`), **`s7r_transit_window`** (all marks between `u` and a
  same-edge/next-vertex target are transit once every visit in the parameter window is excluded).
* `s7r_nextMark_vl` (`nextMark v_ℓ = μ_M`), `s7r_succ_va` (`f v_a = μ_M` in a sliding row).
* `s7r_nextMark_shape`, `s7r_no_half_between` (generic on a half: no visit of the half on the edge of `m₁` strictly between `m₁` and
  `nextMark m₁`), `s7r_edge_first`, `s7r_param_first` (parameter transfer).
* **`s7r_reach_first`** (all `λ₁` marks: vertex target off/on the cut — the cut chain runs through `v_a` then `f v_a = μ_M` — and visit
  target), **`s7r_step_first`**; `s7r_qmark₂` (`λ₂`'s vertex `0` starts its chain at `v_a`), `s7r_edge_second`, `s7r_qmark₂_param_zero`,
  `s7r_param_second`, **`s7r_reach_second`** (`j = −1` ends at `v_ℓ`; `j = 0` starts at `v_a`), **`s7r_step_second`**, **`s7r_hit`**.
* **`s7r_slidingTransport_of_leg_false : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S (s7b_pre … S) (s7b_pre … S) (s7e_vl hc)`** —
  all five fields, `ret` included.
* `s7r_img_of_decomposition` (`hSimg` from `s7b_PivotSplit.x_split` + `IsDecomposition`).
* `s7r_slidingMark'` (corrected map), `s7r_SlidingTransport'` (corrected structure; same five fields with `ret` for the corrected map).

### 1.C The side polygon with leg `M` (section `S7RLegTrue`, lines 1042-1760; `hc : IsCrossing Q {a, contactLeg true M}`)
* `s7r_leg_true`, `s7r_secondHalfIndex_succ` (`secondHalfIndex (j+1) = secondHalfEdgeIndex j + 1` for EVERY `j`), `s7r_va_affected'`,
  the five computation rules of `s7r_slidingMark'`.
* **`s7r_slidingMark'_eq`**: `s7r_slidingMark' va = Equiv.swap (inl M) (inr va) ∘ s7b_slidingMark … va` — hence
  `s7r_slidingMark'_injective`, `s7r_inr_mem_range_iff'`, `s7r_vl_not_mem_range'`, `s7r_va_mem_range'` for free.
* `s7r_transit_of'`, `s7r_transit_window'`; `s7r_nextMark_M` (`nextMark μ_M = v_ℓ`), `s7r_succ_va'` (`f v_a = nextMark v_ℓ`),
  `s7r_succ_vl'` (`f v_ℓ = nextMark v_a`).
* `s7r_qmark₁'` (`λ₁`'s vertex `0` starts its chain at `v_ℓ`), `s7r_edge_first'`, `s7r_qmark₁'_param_zero`, `s7r_param_first'`,
  **`s7r_reach_first'`** (the cut chain ends at `v_a` directly), **`s7r_step_first'`**; `s7r_edge_second'`, `s7r_param_second'`,
  **`s7r_reach_from_va'`** (the exit of `λ₂`'s vertex `0` through `v_a`), **`s7r_reach_second'`** (`inl 0 ↦ μ_M`: `nextMark μ_M = v_ℓ`
  transit-skipped by `s7r_reach_trans`, `f v_ℓ = nextMark v_a`, then the chain out of `v_a`; the vertex targets are uniform via
  `s7r_secondHalfIndex_succ`), **`s7r_step_second'`**, **`s7r_hit'`** (the leg visit exits through `v_a`'s chain).
* **`s7r_slidingTransport_of_leg_true : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S (s7b_pre … S) (s7b_pre … S) (s7e_va hc)`**.

### 1.D Consequences of the corrected structure (section `S7RTransportConsequences`, lines 1762-2038, `namespace s7r_SlidingTransport'`)
The port of the `s7b_SlidingTransport` namespace (SM/CornerChainUnits.lean 3958-4210) by textual substitution — part I is generic in
`ι`: `owner_inl_iff`, `owner_inr_iff`, `owner_inl_ne_inr`, **`componentEquiv : Component hn hQ S ≃ Component … h₁ S₁ ⊕ Component … h₂ S₂`**,
`componentEquiv_owner_inl/_inr/_firstVisit/_secondVisit`, `firstCrossingQ_mem_carrierCrossings_iff`, `secondCrossingQ_mem_carrierCrossings_iff`,
`secondCrossingQ_notMem_carrierCrossings`, `firstCrossingQ_notMem_carrierCrossings`, `carrierCrossings_mem_range`,
**`carrierCrossings_eq_img_first/_second`**, **`carrierCrossingCount_eq_first/_second`** (with `hsplit` at `x = va.1` and `hS`).  The two
contact-carrier lemmas EXCHANGE their halves with respect to the leg-`M−1` side: **`componentEquiv_owner_vertexM`**: `Q`'s carrier through
`μ_M` ↔ `λ₂`'s carrier through its vertex `0`; **`componentEquiv_owner_pivot`**: `Q`'s carrier through `v_a` ↔ `λ₁`'s carrier through its
vertex `0`.

### 1.E Germ level (section `S7RGerm`, lines 2040-2201)
* **`s7r_sign_const_center`**: `edgeParameter (side b) a j < r ↔ edgeParameter g.center a j < r` for persistent `{a, j}` — the `u = 0`
  case of `s7a2_pos_of_ne_zero` (W2_S7E §2's "sign constancy replaces the approach clause", now literally at the centre; U_S7B §2.1(iii)'s
  feared `contact_persistent_parameters_approach` is NOT needed).
* `s7r_hside`, `s7r_hord` (from `VertexLocalData.visit_order`), `s7r_huniq` / `s7r_huniq'` (from `s7e_pattern`).
* **`s7r_slidingTransport_side (h : g.SlidingAt M a) h₁ h₂ : ∃ δ > 0, ∀ t < δ, ∀ b (hc : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg false M}) S,
  (s7e_va hc).1 ∈ S → hSimg → s7b_SlidingTransport hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b) (s7a_sideGeneric g b) h₁ h₂ S (s7b_pre … S) (s7b_pre … S) (s7e_vl hc)`**.
* **`s7r_slidingTransport_side'`**: the same with `contactLeg true M` and `s7r_SlidingTransport' … (s7e_va hc)`.

## 2. Defect found (rule 4): `s7b_SlidingTransport.ret` is FALSE on the leg-`M` side

Let `Q` carry `x = {a, M}` (`f = true`), `S ∋ x`, `ι := s7b_slidingMark hn hsep hm hQC vm` (any `vm`).  `ι (inl (inl 0)) = inl (firstHalfIndex 0)
= μ_M`.  `smoothingSuccessor S (inl M) = nextMark (inl M) = inr v_ℓ` (`s7e_owner_vl_eq_vertex`, `true` branch — reproved as `s7r_nextMark_M`:
`v_ℓ` is the first mark on edge `M`, parameter `< η < 3η <` every persistent `E_M`-visit).  With `vm = v_ℓ` (the intended instance),
`inr v_ℓ = ι (inr (inl 0))`, so `f (ι (inl (inl 0))) = ι (inr (inl 0))`: `step (inl (inl 0))` needs `k = 1` and `ι (inr (inl 0)) = ι (inl (g₁ (inl 0)))`
(impossible: injectivity, `inr ≠ inl`) or `k ≥ 2` with `f¹ (ι b) ∉ range ι` (false).  With any other `vm`, `inr v_ℓ` is off the image and
`f v_ℓ = nextMark v_a` jumps into `λ₂`'s cut — the chain from `ι (inl (inl 0))` then reaches an image mark of `λ₂`, never `ι (inl (g₁ (inl 0)))`.
Geometrically, on that side the carrier through `μ_M` is `μ_M, v_ℓ, [E_a > r], μ_{a+1}, …, μ_{M−1}, [E_{M−1}]` = the closed SECOND half with
`v_ℓ` as the extra corner (W2_S7E §2: "the leg visit on P₊"), and the closed FIRST half is `[E_M], μ_{M+1}, …, μ_a, [E_a < r], v_a` with `v_a`
in the place of `λ₁`'s vertex `0`.  **Corrected form**: `s7r_slidingMark'` (`inl (inl 0) ↦ inr v_a`, `inr (inl 0) ↦ inl M`, all else as
`s7b_slidingMark`) = `swap (μ_M, v_a) ∘ s7b_slidingMark … v_a` (`s7r_slidingMark'_eq`), and `s7r_SlidingTransport'`; PROVED (§1.C).
Nothing in the frozen statement `s7_sliding_law_at` is affected (the halves' state sums are symmetric in which side carries which
extra corner); what changes for the consumer is §3.

## 3. How to consume (the `hterm` unit / wave-3 assembler)

* Legs: `s7e_leg g M a = false` ⇒ `P₋(t)` carries `{a, M−1}` and `P₊(t)` carries `{a, M}`; `= true` ⇒ the reverse (`s7e_pattern`).  So
  exactly ONE side is a `s7b_SlidingTransport` (at the leg visit `s7e_vl hc`) and the OTHER is a `s7r_SlidingTransport'` (at the
  `a`-visit `s7e_va hc`).  Take `hl : s7e_leg g M a = false` (resp. `true`) by cases; then `hc₋ : IsCrossing P₋ {a, contactLeg false M} :=
  hl ▸ s7e_hxm hn g h t` and `hc₊ : IsCrossing P₊ {a, contactLeg true M} := (by simpa [hl] using s7e_hxp hn g h t)`, with
  `(s7e_va hc₋).1 = s7e_xm hn h t` (`Subtype.ext`, `s7e_xm_val`, `hl`) and likewise for `x₊`.
* `hSimg` for a decomposition `S ∋ x`: `s7r_img_of_decomposition hn hQ hsep hm hQC h₁ h₂ S x hsplit hS hx` (the `hsplit` of
  `s7e_contactSector_of_pivotSplit`; `S := (s7b_slidingDecompositionEquiv … hsplit).symm q` is a decomposition containing `x`).
* Radius: intersect the `δ` of `s7r_slidingTransport_side`/`_side'` with those of A2 / E (`s7e_exists_spectatorSector`) and the contact
  sector's own.  Both `δ`s here are the interval radius of `s7a2_exists_intervalLocal`, so one `obtain` serves both.
* From the two instances: `componentEquiv`, `carrierCrossings_eq_img_first/_second`, `carrierCrossingCount_eq_first/_second` on both sides
  (`s7b_SlidingTransport.*` on one, `s7r_SlidingTransport'.*` on the other), and the contact-carrier identifications
  `componentEquiv_owner_vertexM` / `componentEquiv_owner_pivot` — with the halves EXCHANGED between the two sides (§1.D).  For the corner
  correspondence (U_S7B §2.3) and the rotation equality (W2_S7E §2), the extra corner is `v_a` on the leg-`M−1` side and `v_ℓ` on the
  leg-`M` side, as PLAN §3.3 eq. s7c:short-direction-lists prints.

## 4. Not proved / left (nothing of the RET brief)
* Nothing of §2.1 of U_S7B_REPORT is open: `ret` holds on both sides in the corrected form.  The `s7b_SlidingTransport` STRUCTURE itself
  stays as the library states it (usable on the leg-`M−1` side only); U110-B's docstring "`vm` = the visit of `x₋` on the leg edge `M−1 / M`"
  is wrong for the leg `M` — flag for the author notes (FR: the leg-`M` side needs `s7r_SlidingTransport'`).
* Not in scope (other wave-3 units): `s7b_PivotSplit` on both sides (U_S7B §2.2), the ordered corner bijection (§2.3), the coefficient /
  selector `hterm` and the rotation equality (W2_S7E §2).

## 5. Pitfalls met (v4.34.0-rc2 pin)
* `omit [NeZero n] in` is refused on anything mentioning `s7b_*` / `s7e_vl` (the instance is referenced through them).
* `rw [hord _ _ _ _ (by …)]`: the visit placeholders are not inferable before the edge proof elaborates — pass the visits and the
  non-affectedness proofs explicitly; same for `s7b_firstHalfVisit_edge` (explicit `hn hsep hm`).
* `mul_lt_mul_iff_left₀` is the RIGHT-multiplication form (`?a * r < ?b * r`); `nlinarith` + `lt_of_not_ge` is simpler.
* A local `intro w hw` silently shadows the section variable `hw : ContactParameterWindows …`.
* `nextMark hn₁ h₁ m₁` with `hn₁` a `have` is not syntactically `nextMark (contactHalfSizes_bounds hn hsep).1.1 h₁ m₁` (`rw` fails):
  take `hn₁` as an explicit parameter, instantiate at the end (proof irrelevance closes the gap in `exact`).
* `(-1 : ZMod k) ≠ 0` via `neg_ne_zero.mpr one_ne_zero` needs `Fact (1 < k)` in scope (`⟨by omega⟩` from `3 ≤ k`).
* `rw [s7b_secondVisitQ_edge]` does not see through `s7e_mEdge (Sum.inr _)`: `show (…).2.val = _` first.
* `Finset.ssubset_iff_of_subset hsub |>.mpr ⟨x, hx, hx'⟩` for the descent measure; `induction c using Nat.strong_induction_on with | _ c ih`.
* `include … in` lists: everything used only in a proof (here `hη`, `h₂`, `hn`) must be named, or the theorem silently loses the argument
  and every call site breaks with "argument has type … but is expected to have type …".

## 6. Reproduce
`cd work/lean && lake env lean ../drafts/corner/W3_RET.lean` (~100 s; run it in the background if a 120 s tool limit applies) — expected
output: exactly two lines `declaration uses 'sorry'` (2207, 2226).  `grep -c sorry ../drafts/corner/W3_RET.lean` → 3.
