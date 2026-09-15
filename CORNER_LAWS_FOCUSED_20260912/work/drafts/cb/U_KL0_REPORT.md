# U_KL0_REPORT — unit KL0 (abstract restricted Gauss record), 2026-09-14

File: `work/drafts/cb/U_KL0.lean` (687 lines; skeleton was 609). Compile:
`cd work/lean && lake env lean ../drafts/cb/U_KL0.lean` → **0 errors**, exit 0.
`grep -c sorry`: **18 before → 9 after**; the 9 = the header comment (line 10) + the 8 leaves of the
other units (KL1 ×2, KL2, KL3, T1, GL, AS ×2), untouched. The region from the KL1 header to EOF is
byte-identical to Skeleton_FINAL.lean (`diff` empty); lines 1–257 (definitions + bundles) identical too.
Every non-`sorry` line of the skeleton's KL0 block appears verbatim in U_KL0 (statements FROZEN, checked
by script). Axioms of `gaussSucc`, `gaussSucc_val`, `gaussPair`, `gaussPair_val`, `gaussRecord`,
`label_crossingOf`: `propext, Classical.choice, Quot.sound` only (checked on a scratch copy with
`#print axioms`, not in the file).

## Leaves proved (all of KL0)

| leaf | proof |
|---|---|
| `gaussSucc` | `(gaussList hc T).formPerm.subtypePerm (kl0_formPerm_mem_iff hc T)` — Mathlib `List.formPerm` of `L_T`, restricted to `{v // v.1 ∈ T}` (which is exactly the member set of `L_T`). |
| `gaussSucc_val` | `change`, then `List.formPerm_apply_mem_eq_next (kl0_gaussList_nodup hc T) v.1 hv`. |
| `gaussPair` | `visitTwinPerm.subtypePerm (kl0_visitTwinPerm_mem_iff T)`. |
| `gaussPair_val` | `rfl`. |
| `gaussRecord.succ_cycle` | `kl0_gaussSucc_sameCycle` (one cycle via `List.formPerm_pow_apply_getElem`, lifted by `Equiv.Perm.SameCycle.subtypePerm`). |
| `gaussRecord.pair_ne` | `visitTwin_ne v.1 (congrArg Subtype.val h)`. |
| `gaussRecord.pair_invol` | `Subtype.ext (visitTwin_involutive v.1)`. |
| `gaussRecord.bit_pair` | `kl0_positiveOverBit_twin hc v.1` (port of PLAN_B `positiveOverBit_twin`, at arbitrary `hc`). |
| `label_crossingOf` | `Record.Crossing.rep_mem` gives `rep ∈ {x, pair x}`; both cases are `rfl` after `rw` (`(gaussPair x).1.1 = (visitTwin x.1).1 = x.1.1` definitionally). |

Leaves left: none in KL0.

## Helpers added (all `kl0_`-prefixed, namespace `SM.CB`, placed immediately before the leaf using them)

* `kl0_gaussList_nodup hc T : (gaussList hc T).Nodup` — `(geometricGaussList_nodup hc).filter _`.
* `kl0_mem_gaussList hc T v : v ∈ gaussList hc T ↔ v.1 ∈ T` — `List.mem_filter` + `mem_geometricGaussList`.
  (Useful for KL2/KL3: membership in `L_T` is just the label test.)
* `kl0_formPerm_mem_iff hc T v : ((gaussList hc T).formPerm v).1 ∈ T ↔ v.1 ∈ T` — `List.formPerm_mem_iff_mem`.
* `kl0_visitTwinPerm_mem_iff T v : (visitTwinPerm v).1 ∈ T ↔ v.1 ∈ T` (`omit [NeZero n]`).
* `kl0_gaussSucc_sameCycle hc T v w : (gaussSucc hc T).SameCycle v w`.
* `kl0_positiveOverBit_twin hc v : positiveOverBit (visitTwin v) = !positiveOverBit v` (`omit [NeZero n]`);
  needs only `hc : CrossingGeometry P` (for `crossing_det_ne_zero_of_geometry`), not `Generic`.

## Facts other units can rely on (definitional)

* `(gaussSucc hc T v).1 = (gaussList hc T).formPerm v.1` — by `rfl`/`change` (`Equiv.Perm.subtypePerm_apply`).
  So `(gaussRecord hc T).succ v = gaussSucc hc T v` and `((gaussRecord hc T).succ v).1 = L_T.next v.1 _`
  (`gaussSucc_val`). Powers: `Equiv.Perm.subtypePerm_pow` / `subtypePerm_zpow` (Mathlib/Algebra/Group/End.lean:416/432)
  give `((gaussSucc hc T)^k v).1 = (L_T.formPerm^k) v.1`, and `List.formPerm_pow_apply_getElem` indexes it
  (KL2's `steps` = index difference mod `|L_T|` should go through these).
* `(gaussRecord hc T).pair v = gaussPair hc T v`, `(gaussPair hc T v).1 = visitTwin v.1` (`rfl`), and
  `(gaussPair hc T v).1.1 = v.1.1` is `rfl` too (`visitTwin_crossing` is `rfl`).
* `(gaussRecord hc T).isOver v = positiveOverBit v.1`, `.sgn v = 1`, `.comp v = ()` — all `rfl`.
* `(gaussRecord hc T).M = {v : Visit P // v.1 ∈ T}` (`gaussRecord_M`, rfl) — the `mDec`/`mFin` instances are
  whatever instance resolution picked under the local `Classical.propDecidable`; use `Finset.mem_insert` /
  `Finset.mem_singleton` via `rw` on an explicitly typed membership (see pitfall 1) rather than `simp`.

## Mathlib pitfalls met

1. `simpa [Record.crossingOf] using h` did NOT rewrite `rep ∈ {x, pair x}` to the disjunction (membership on
   `Finset (gaussRecord hc T).M`); an explicit `have h : … ∈ ({x, pair x} : Finset (gaussRecord hc T).M) := rep_mem _`
   (defeq) followed by `rw [Finset.mem_insert, Finset.mem_singleton] at h` works.
2. `List.formPerm_apply_of_notMem` (not `_not_mem`) is the current name; `List.formPerm_mem_iff_mem` is `@[simp]`.
3. `Equiv.Perm.SameCycle.subtypePerm` is an alias of `sameCycle_subtypePerm` (Mathlib/GroupTheory/Perm/Cycle/Basic.lean:171);
   `apply` it first, then prove `SameCycle` of the underlying `formPerm` on the coerced values.
4. Dependent `getElem` index rewriting after `List.formPerm_pow_apply_getElem`: used a local
   `key : ∀ k hk, k = j → L[k]'hk = L[j]'hj` (`rintro k hk rfl; rfl`) plus `Nat.add_mod_right`, `Nat.mod_eq_of_lt`.
5. `Set.mem_setOf_eq` is deprecated in this Mathlib (warning at line 540, in the skeleton's glue — not mine).

## Warnings the assembler will see (harmless, from FROZEN statements — not changed)

* `gaussPair`: "Variable name `hc` is not explicitly referenced" (the def's `hc` is unused; the skeleton statement
  names it `hc`, so I kept it rather than renaming to `_hc`).
* `gaussPair_val`: "automatically included section variable(s) unused: [NeZero n]" — `omit [NeZero n] in` would change
  the frozen signature, so left as is. The assembler may add `omit [NeZero n] in` to both if desired.
* Other warnings are the skeleton's own (`hT` unused in `IsBlockCarrierDiagram`-related leaf at 468, `Set.mem_setOf_eq`).

## Nothing false / no missing hypotheses

All KL0 leaves are true as stated; no counterexample, no strengthened hypothesis needed. `bit_pair` needs only
`hc : CrossingGeometry P` (nonzero determinant at a crossing), which `gaussRecord` already carries.
