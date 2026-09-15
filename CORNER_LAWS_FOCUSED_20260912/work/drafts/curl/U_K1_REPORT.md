# U_K1 report — Unit K1 (kink location + RI helpers), cf:lem-curl

Prover: Claude (Fable 5.1 subagent), 2026-09-14. File: `work/drafts/curl/U_K1.lean` (copy of
`Skeleton_FINAL.lean`, byte-identical statements; 1460 lines).
Check: `cd work/lean && lake env lean ../drafts/curl/U_K1.lean` — **0 errors**, exit 0, 9.6 s.
`grep -c sorry`: **56 before → 52 after** (the 4 leaves of K1). The only non-`sorry` warning is
the inherited `<;>` linter note at line 567. `#print axioms SM.cf_lem_curl` still lists `sorryAx`
(other units' leaves), `SM.CurlData` = [propext, Classical.choice, Quot.sound, SM.lp_lm] as before.
`diff Skeleton_FINAL.lean U_K1.lean`: exactly four `  sorry` lines removed, 334 lines added
(helper blocks + proof bodies); no definition, structure, statement, name or docstring changed.

## Leaves proved (4 / 4)

| leaf | line | proof |
|---|---|---|
| `Curl.exists_kinkLocation` | 1137 | see §"Construction" |
| `SM.Link.RIData.crossingPoint_ψ` | 1185 | `eval_eq` at the over occurrence, `over_eq`, `outerOverPt_val`, `eval_visitPt` (both sides) |
| `SM.Link.RIData.sign_ψ` | 1195 | crossing point ∉ `U` (`x.2` : ∉ interior, `Clean.crossingPoint_not_mem_frontier`, and `U ⊆ interior ∪ frontier` via `⟨subset_closure hU, x.2⟩ : _ ∈ frontier U`); `dir_pos` at `outerOverPt`/`outerUnderPt` gives `dir' = l • dir`, `m • dir` with `l, m > 0`; `strandOf (visitPt (overVisit x)) = overStrand x` is `rfl`; `det (l•a) (m•b) = (l*m) det a b` by `simp [det]; ring`; `sign_mul`, `sign_pos` |
| `SM.Link.RIData.writhe_eq` | 1242 | `Fintype.sum_subtype_add_sum_subtype (· ≠ kink)`; the `≠ kink` sum transported to `D.Γ.Crossing` by the equivalence `k1_old_equiv` (`Fintype.sum_equiv`, signs by `k1_old_equiv_sign`); the `¬ ≠ kink` sum is the single term (`Fintype.sum_eq_single` with `f` given explicitly) |

Leaves left: none in this unit.

## Helpers added (all `k1_`-prefixed, namespace `SM.Curl`, placed immediately before the leaf that uses them)

Before `exists_kinkLocation` (lines 894-1134):
- `k1_cyc_rot` : `cycBetween a b c ↔ cycBetween b c a` (tauto).
- `k1_cyc_total` : distinct `a b c` → `cycBetween a b c ∨ cycBetween c b a`.
- `k1_cyc_trans` : `cycBetween a b c → cycBetween b d c → cycBetween a d c`.
- `k1_cyc_succ` : **the successor characterisation** — if no set point lies strictly between `x`
  and `q` (`¬ cycBetween x a q`, `¬ cycBetween x c q`, `x ∉ {a, c, q}`, `a ≠ c`) then
  `cycBetween a x c ↔ (q = c ∨ cycBetween a q c)`. This is what makes `gap` an iff without a
  case analysis over the position of `v, w`.
- `k1_exists_succ` : for `f : V → ℝ` on a finite nonempty type and any `x`, some `q` has no `f s`
  strictly cyclically between `x` and `f q` (min of `{v | x < f v}` if nonempty, else the global min).
- `k1_adjacent_cases` : `Γ.Adjacent e s → s = e ∨ s = ⟨e.1, e.2+1⟩ ∨ s = ⟨e.1, e.2-1⟩`.
- `k1_not_mem_seg_succ` / `k1_not_mem_seg_pred` : a point of `e` with parameter in `[0,1)`
  (resp. `(0,1]`) is not on the successor (resp. predecessor) edge — from the accepted
  `Generic.seg_inter_succ` (Smoothing.lean:116, visible through `SM.PolynomialBlock → SM.Smoothing`)
  and `Generic.edgePt_injective`.
- `k1_param_unique` : two parameters of `e` in `(0,1)` landing on one other strand `s ≠ e`
  coincide (adjacent `s`: impossible; else `Generic.transverse` + `intersection_parameters_unique`).
- `k1_bad_finite` : `{u ∈ (0,1) | ∃ s ≠ e, edgePt e u ∈ seg s}` is finite (finite union of
  subsingletons over `Strand`).
- `k1_exists_param` : for `0 ≤ a < b ≤ 1` there is `t ∈ (a, b)` such that **every** `u ∈ [t, b)`
  gives `edgePt e u` off every other strand (take `t` past the largest bad parameter below `b`).
- `k1_key_eq` : `e.val + t = j.val + u` with `t, u ∈ [0,1)` → `j = e ∧ u = t`.
- `k1_visit_data` : on a one-component diagram every occurrence `s` has `visitCoord s = j.val + u`
  with `u ∈ [0,1)` and `edgePt ⟨i, j⟩ u` on the *other* strand of its crossing.
- `k1_key_ne_visitcoord` : the key of a free point (off other strands) is no occurrence coordinate.
- `k1_no_visitcoord_between` : no occurrence coordinate lies strictly between the keys `e.val + t`
  and `e.val + t'` when `[t, t')` is free of other strands.
- `k1_fract_ne` : `Int.fract S.t₀ ≠ S.carried.τ s` (from `no_double` with `n = ⌊t₀⌋`).

Before `RIData.writhe_eq` (lines 1216-1237):
- `def k1_old_equiv (h : RIData U D D') : D.Γ.Crossing ≃ {y : D'.Γ.Crossing // y ≠ h.kink}` —
  `subtypeUnivEquiv h.no_inner`, then `h.out.ψ`, then `subtypeEquivRight (not_congr ∘ inner_iff')`.
  **This has exactly the type of `KinkInsertion.old`** (U6 can set `old := k1_old_equiv ri`).
- `k1_old_equiv_val` (rfl), `k1_old_equiv_point` (= `KinkInsertion.old_point` for that choice),
  `k1_old_equiv_sign` (= `KinkInsertion.old_sign`).

## Construction of the kink location (for the executor / AUTHOR_NOTES)

With `hc : S.D.Γ.c = 1`. If `D` has no occurrence, `r` is any free interior point of edge
`⟨0, 0⟩` (`k1_exists_param` on `(0, 1)`); `gap` is vacuous. Otherwise let `q` be the cyclic
successor of `x := Int.fract t₀` among the parameters `τ` (`k1_exists_succ`; `x ∉ τ(V)` by
`k1_fract_ne`), let `⟨i, e⟩` be the strand of `visitPt q` and `t_q ∈ (0,1)` its crossing
parameter. `k1_exists_param` on `(0, t_q)` gives `t` with `[t, t_q)` free of other strands;
`r := ⟨i, (e, t)⟩`. Then `interior` is `0 < t`, `off_edges` is the freeness at `t`, and `gap`
follows by applying `k1_cyc_succ` on both sides (successor `q` on the `τ` side by construction,
successor `q` on the `visitCoord` side by `k1_no_visitcoord_between`, non-membership by
`k1_key_ne_visitcoord`/`k1_fract_ne`, distinctness by `τ_inj`/`visitCoord_injOn` with all
occurrences on the one component) and closing with `carried.order`. So the kink sits on the edge
carrying the *next* occurrence after `t₀`, just before it; nothing of this is exported by the
statement (`KinkLocation` only records `r`, `interior`, `off_edges`, `gap`).

No leaf was false or needed a stronger hypothesis. The `gap` clause compares with `Int.fract t₀`
and holds as stated (FR-C9).

## Mathlib / library pitfalls met

- `Ne.lt_or_lt` does not exist in this pin; use `lt_or_gt_of_ne`.
- `Set.Infinite.diff` is deprecated (→ `Set.Infinite.sdiff`); not needed in the end (the finite
  bad set is bounded by its maximum via `Set.exists_max_image`).
- `Fintype.sum_eq_single` with `f` left implicit against a goal `… = ↑(D'.sign kink)` hits a
  `whnf` heartbeat timeout (higher-order unification unfolds `SignType.sign` on `ℝ`). Pass
  `(f := fun y => (D'.sign y.1 : ℤ))` explicitly and use `rw`.
- `Fintype.sum_equiv` needs the cast `SignType → ℤ` inside the congruence: use
  `fun x => by rw [k1_old_equiv_sign]`, not `(k1_old_equiv_sign h x).symm`.
- `Finset.sum_subtype` has an *implicit* `{F : Fintype (Subtype p)}`; rewriting left-to-right
  leaves it as a metavariable — avoided by `Fintype.sum_subtype_add_sum_subtype`.
- `x ∈ U → x ∉ interior U → x ∈ frontier U` is `⟨subset_closure h, h'⟩` (frontier is
  `closure \ interior` definitionally).
- `subst` with two free variables (`hji : j = i`): use `subst i` to control which one disappears.
- The Smoothing.lean §0' generic-shadow lemmas (`Shadow.edgePt`, `Generic.seg_inter_succ`,
  `Generic.edgePt_injective`, `mk_sub_one_add_one`, `head_eq_tail_succ`) are visible from the draft
  because `SM.PolynomialBlock` imports `SM.Smoothing`; `eval_eq_edgePt` there is in another
  namespace but is `rfl` anyway.
- `(exfalso; linarith)` fallbacks after `exact Or.inl ⟨by linarith, by linarith⟩`-style
  alternatives are never reached (linarith proves the conjuncts from contradictory hypotheses) and
  trigger the unreachable-tactic linter; removed.

## Notes for the assembler and other units

- Helpers live in `namespace SM.Curl` (section with `variable (S : CurlSite)`); only
  `k1_fract_ne` uses `S`. All others are general (`Shadow`/`Diagram`/`ℝ`).
- U6 (`exists_kinkInsertion`) can use `k1_old_equiv ri`, `k1_old_equiv_point`, `k1_old_equiv_sign`
  for `old`, `old_point`, `old_sign`, and `RIData.writhe_eq` + `kink_neg` for `writhe`
  (`D'.writhe = D.writhe + (-1 : SignType)` → `- 1`). `k1_exists_param`/`k1_bad_finite` give a
  free parameter window around `L.r` on its edge; `k1_not_mem_seg_succ/pred`, `k1_param_unique`
  give the geometry of one edge against the others.
- U7 (`cycBetween_ext_of_insert_pair`, `cycBetween_fract_*`) may reuse `k1_cyc_rot`,
  `k1_cyc_total`, `k1_cyc_trans`, `k1_cyc_succ`.
- Nothing was written under `work/lean`; no imports were changed.
