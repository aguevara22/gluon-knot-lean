# U_KL2_REPORT — unit KL2 (record interlacement on `gaussRecord` = `Interlaces`), 2026-09-14

File: `work/drafts/cb/U_KL2.lean` (782 lines; skeleton was 609). Compile:
`cd work/lean && lake env lean ../drafts/cb/U_KL2.lean` → **0 errors**, exit 0 (7 min wall under a load
average of ~10 from other provers; ~14 s when the machine is idle). `grep -c sorry`: **18 before → 17 after**;
the 17 = the header comment (line 10) + the sorried leaves of the other units (KL0 ×9 incl. the four record laws,
KL1 ×2, KL3, T1, GL, AS ×2), untouched. Lines 1–338 (definitions, bundles, KL0, KL1) and the region from the
KL3 header to EOF are byte-identical to Skeleton_FINAL.lean (checked by `diff`). The leaf statement is verbatim;
only `:= sorry` became `:= by …`.

Axioms: on a scratch copy = U_KL0.lean's proved KL0 block + this KL2 block, `#print axioms SM.CB.gaussRecord_adj_iff`
gives `propext, Classical.choice, Quot.sound` only — i.e. the KL2 proof itself introduces no `sorry`; inside
U_KL2.lean it inherits `sorryAx` only through KL0's black boxes `gaussSucc_val`, `gaussPair_val` and the
`gaussRecord` laws (as intended). Nothing in the proof depends on KL0's *definitions* of `gaussSucc`/`gaussPair`
(only on the two spec lemmas), so it is robust to whatever KL0's merged bodies are.

## Leaf proved (all of KL2)

| leaf | proof |
|---|---|
| `gaussRecord_adj_iff` | `rw [← geometricInterlaces_iff_generic]`; if `p = p'` both sides are false (`SimpleGraph.irrefl`, `geometricInterlaces_irrefl`); otherwise labels differ (`kl2_label_injective`), `Record.adj_iff_alternates` at the representatives `p.rep`, `p'.rep` (`Crossing.rep_mem`), then `kl2_alternates_iff`. |

Leaves left: none in KL2.

## Helpers added (all `kl2_`-prefixed, namespace `SM.CB`, right before the leaf, general `hc : CrossingGeometry P`)

* `kl2_gaussList_nodup hc T : (gaussList hc T).Nodup` and `kl2_mem_gaussList hc T v : v ∈ gaussList hc T ↔ v.1 ∈ T`
  (same content as KL0's `kl0_gaussList_nodup` / `kl0_mem_gaussList`; duplicated here because units may not share
  helpers — the assembler may dedupe by pointing one at the other).
* `kl2_gaussList_pairwise_lt hc T` : `L_T` is strictly sorted by `traversalKey (geometricVisitPosition hc ·)`
  (`geometricGaussList_sorted` ∧ `geometricGaussList_nodup` ⇒ `<` via `geometricVisitKey_injective`, then `.sublist List.filter_sublist`).
* `kl2_key_lt_iff hc T hi hj : key L_T[i] < key L_T[j] ↔ i < j` (`List.pairwise_iff_getElem`, trichotomy).
* `kl2_card_M hc T : Fintype.card (gaussRecord hc T).M = (gaussList hc T).length`
  (`Fintype.card_of_subtype L_T.toFinset` — works for the record's own `mFin` instance — + `List.toFinset_card_of_nodup`).
* `kl2_base hc T h0 : (gaussRecord hc T).M` — the first visit of `L_T` (`h0 : 0 < L_T.length`).
* `kl2_succ_pow_val hc T h0 k hk : ((succ ^ k) base).1 = L_T[k]` for `k < |L_T|` (induction; `gaussSucc_val` + `List.next_getElem`).
* `kl2_steps_base hc T h0 v hi hiv : steps base v = i` when `L_T[i] = v.1` (`Record.steps_eq_iff`, `kl2_card_M`).
* `kl2_steps_lt_iff hc T h0 v w : steps base v < steps base w ↔ key v.1 < key w.1`.
* `kl2_arcBetween_iff hc T v w u : ArcBetween v w u ↔ traversalBetween (pos v.1) (pos w.1) (pos u.1)`
  (`Record.arcBetween_iff_posBetween` at `kl2_base`, then `unfold PosBetween traversalBetween; simp only [kl2_steps_lt_iff]`).
  This is the record-level "`steps` = index difference, cyclic index order = `cycBetween` = `traversalBetween`" of PLAN_FINAL §4.
* `kl2_existsUnique_iff_xor c Q i j hij : (∃! k, Q k) ↔ Xor (Q i) (Q j)` on the two-visit fibre of a crossing
  (`crossing_unique_visit_iff`, `crossing_visits_exhaust`; `omit [NeZero n]`).
* `kl2_alternates_iff hc T v w (hne : v.1.1 ≠ w.1.1) : Alternates v w ↔ GeometricInterlaces hc v.1.1 w.1.1`
  (`gaussPair_val` for `pair = visitTwin`, `kl2_arcBetween_iff` ×2, `CV.geometricInterlaces_iff_unique` at
  `x₀ = v.1.2`, `x₁ = (visitTwin v.1).2` (`visitTwin_snd_ne`), `kl2_existsUnique_iff_xor` at `w.1.2`, `(visitTwin w.1).2`;
  the final step is definitional: `⟨v.1.1, v.1.2⟩ ≡ v.1` (Sigma eta) and `⟨v.1.1, (visitTwin v.1).2⟩ ≡ visitTwin v.1`).
* `kl2_label_injective hc T : label hc T p = label hc T p' → p = p'` (`visit_eq_or_twin` on the reps; the twin case
  is `pair p.rep` by `gaussPair_val`, so `crossingOf_pair` + `crossingOf_rep`).

Useful for GL: `kl2_alternates_iff`/`kl2_arcBetween_iff` are stated for every `hc`, and `kl2_label_injective` +
`label_crossingOf` (KL0) give `label` as a bijection `(gaussRecord hc T).Crossing ≃ T` if needed.

## Mathlib / library pitfalls met

1. `geometricGaussList_pairwise_lt` and `pairwise_lt_of_pairwise_le_nodup` (PLAN's suggested tools) live in
   `SM/GeoMarkTransport.lean`, which is NOT in the import closure of the skeleton (`CV.X1`, `CV.PieceCurve`,
   `SM.MarkedProducts`, `SM.CornerStateSum`). Re-proved inline in `kl2_gaussList_pairwise_lt` rather than adding an import.
2. `geometricInterlaces_iff_unique` / `geometric_alternating_visits_iff_unique` are in namespace **`CV`** (CV/Events.lean),
   although they speak about `SM.GeometricInterlaces`; write `CV.geometricInterlaces_iff_unique`.
3. `List.filter_sublist` takes only implicit arguments in this Mathlib (`(List.filter p l).Sublist l`); `List.filter_sublist _` fails.
4. `rcases … with rfl | rfl` on `a = i` with both sides local variables eliminated `i` (the RHS), breaking later references
   to `i`; use named equations and `ha' ▸ ha` instead.
5. `Subtype.property _` on an occurrence of `(gaussRecord hc T).M` does not elaborate (the type is not syntactically a
   `Subtype`); ascribe `(x : {v : Visit P // v.1 ∈ T}).2`. Likewise anonymous constructors into `(gaussRecord hc T).M`
   need `show {v : Visit P // v.1 ∈ T} from ⟨_, _⟩` (used in `kl2_base`).
6. Dependent index rewriting after `List.next_getElem` (`L[(k+1) % |L|] = L[k+1]`): `exact getElem_congr_idx (Nat.mod_eq_of_lt hk)`
   (core lemma, proof-irrelevant RHS) — no `simp`/`congr` needed. Matching `L.next L[k] hy` against `List.next_getElem`'s
   `L.next L[k] (get_mem ..)` works by proof irrelevance after `rintro y hy rfl`.
7. `Xor` here is Mathlib's `Xor (a b : Prop) := (a ∧ ¬b) ∨ (b ∧ ¬a)` (Mathlib/Logic/Basic.lean:297), not `Xor'`; `unfold Xor` then `Or.inl/inr`.

## Warnings the assembler will see (harmless; from FROZEN statements or other units)

Only the skeleton's own: `hT` unused at the `exists_visit_of_mem_carrierCrossings`-area leaf (line 563), deprecated
`Set.mem_setOf_eq` in the glue (line 635). No warning originates in the KL2 block.

## Nothing false / no missing hypotheses

The leaf is true as stated at every `T` (including `T = ∅`, where `(gaussRecord hc ∅).Crossing` is empty and the statement
is vacuous, and `p = p'`, where both sides are false). No strengthening needed.
