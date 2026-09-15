# STACK_ASSEMBLY_REPORT — mp:stack row assembled (2026-09-14)

Assembler: Claude subagent; toolchain Lean v4.34.0-rc2 + Mathlib pin of work/lean; checks with `cd work/lean && lake env lean <file>` only.

## Deliverables

| file | lines | `lake env lean` | `sorry` tokens | `#print axioms SM.stack` |
|---|---|---|---|---|
| work/drafts/polyblock/Stack_Assembled_full.lean | 2499 | no output (no errors, no warnings), 14 s | 0 | propext, Classical.choice, Quot.sound, SM.lp_lm |
| work/drafts/polyblock/Stack_Module.lean | 1358 | no output (no errors, no warnings), 13 s | 0 | propext, Classical.choice, Quot.sound, SM.lp_lm |

Axioms were printed on /tmp copies with `#print axioms SM.stack` (and `SM.stack_formula`) appended; both give exactly `[propext, Classical.choice, Quot.sound, SM.lp_lm]` — no sorryAx, no SM.lit_homfly, no SM.lp_lm_uniqueness. Compile times are wall-clock on the 8-vCPU home pod with all imports already built (`SM.PolynomialBlock` olean of 2026-09-14 00:53 UTC / 2026-09-13 8:53pm ET).

## Step 1 — unit diffs and merge

Each `diff -u Skeleton_FINAL.lean U<k>.lean` was checked to only ADD lines and REMOVE `sorry` lines. Result: true for U1, U3, U4, U5. U2 additionally turned two proof delimiters `:= by` into `:=` (term-mode proofs) on the statement-closing lines of `restrictSmoothIso` (skeleton l.1273-1274) and `restrictSmoothDisjointIso` (l.1287-1288); the statement text before `:=` is unchanged (verified: the removed line re-appears with only the trailing ` by` dropped). No unit changed a statement or a definition. No two units touched the same skeleton line.

Merge method: per-unit `difflib` opcodes against the skeleton (exact skeleton-line ranges, not context-based `patch`, because U1's third hunk and U2's third hunk share context lines 1248-1259); all 17 change ranges were checked pairwise disjoint and applied in skeleton order to one copy. Total: +979 −15 lines → 1533 + 964 = 2497 lines (the header docstring was afterwards updated, +2 lines, see Deviations).

Hunks applied (skeleton 1-based line range → unit, removed, added):

| skeleton lines | unit | removed | added | removed text |
|---|---|---|---|---|
| after 1196 | U2 | 0 | 23 | (pure insertion) |
| 1205 | U2 | 1 | 2 | sorry |
| after 1232 | U1 | 0 | 104 | (pure insertion) |
| 1241 | U1 | 1 | 23 | sorry |
| 1251 | U1 | 1 | 27 | sorry |
| after 1252 | U2 | 0 | 21 | (pure insertion) |
| after 1255 | U2 | 0 | 502 | (pure insertion) |
| 1273-1274 | U2 | 2 | 2 | ((ρ.restrict B).smooth (⟨v, hv⟩ : {u : ρ.M // ρ.RestrictKeep B u}))) := by; sorry |
| 1287-1288 | U2 | 2 | 2 | Nonempty (RecordIso ((ρ.smooth v).restrict B') (ρ.restrict B)) := by; sorry |
| 1306 | U4 | 1 | 7 | sorry |
| 1320 | U3 | 1 | 69 | sorry |
| 1330 | U4 | 1 | 13 | sorry |
| 1338 | U4 | 1 | 3 | sorry |
| 1345 | U4 | 1 | 2 | sorry |
| 1362 | U4 | 1 | 50 | sorry |
| 1374 | U3 | 1 | 29 | sorry |
| 1400 | U5 | 1 | 100 | sorry |

Per unit:

- **U1** (+154 −2, net +152 lines): new declarations `firstReturn_val_eq_of_pow`, `firstReturn_congr_pred`, `mul_swap_pow_apply_of_forall_ne`, `firstReturn_pow_val_spec`, `firstReturn_mul_swap_apply_left`.
- **U2** (+552 −5, net +547 lines): new declarations `beta_comp_reconnect_eq`, `beta_comp_reconnect_pow_eq`, `firstReturn_val_congr`, `reconnect_pow_eq_succ_pow`, `reconnect_sameCycle_iff_of_comp_ne`, `reconnect_sameCycle_self_or_pair`, `reconnect_sameCycle_out`, `smooth_restrictKeep_iff`, `mem_of_inl_mem`, `comp_ne_of_mem_disjoint`, `smoothKeep_of_comp_mem_disjoint`, `reconnect_sameCycle_iff_disjoint`, `comp_out_eq_disjoint`, `rdFwd`, `rdBwd`, `rdBwd_pos`, `rdBwd_neg`, `rdBwd_rdFwd`, `rdFwd_rdBwd`, `rdCompsEquiv`, `rdOccEquiv`, `restrictSmoothDisjointIso'`, `restrictKeep_pair_of_keep`, `restrict_reconnect_eq`, `restrict_reconnect_sameCycle_iff`, `restrict_reconnect_sameCycle_out`, `restrict_smoothKeep_iff`, `comp_ne_of_not_hasKept`, `sameCycle_iff_of_not_hasKept`, `comp_ne_of_free`, `sameCycle_iff_of_free`, `not_hasKept_of_free`, `comp_out_eq_of_free`, `rsFreeOfNotKept`, `rsFreeOfFree`, `rsFwd`, `rsBwd`, `rsFwd_inl_pos`, `rsFwd_inl_neg`, `rsBwd_inr_pos`, `rsBwd_inr_neg`, `rsBwd_rsFwd`, `rsFwd_rsBwd`, `rsCompsEquiv`, `rsOccEquiv`, `restrictSmoothIso'`.
- **U3** (+98 −2, net +96 lines): new declarations none (proofs filled in place only).
- **U4** (+75 −5, net +70 lines): new declarations none (proofs filled in place only).
- **U5** (+100 −1, net +99 lines): new declarations none (proofs filled in place only).

De-duplications / renames: **none needed** — the 51 helper names added by the units are pairwise distinct across units and none re-declares a skeleton name (checked by script over the diffs; also confirmed by the compile, which would report a duplicate declaration).

## Step 2 — Stack_Module.lean

Composition: `import SM.PolynomialBlock` + module docstring + `namespace SM` + `open SM.Link` + EXACTLY §6 of Stack_Assembled_full.lean (assembled lines 1090-2388 → byte-identical, 1299 lines, verified with `cmp`) + the `/-- mp:stack as printed. -/ structure StackData` block and the `theorem stack : StackData where …` block of §7 (assembled lines 2476-2496) + `end SM`.

Scaffolding check: in Skeleton_FINAL.lean the only scaffolding in force at §6 is `namespace SM` (l.43) and `open SM.Link` (l.45); there is no `noncomputable section`, no top-level `variable`, no `local instance`/`attribute [local …]` (grep), and every `variable` of §0-§5 lives inside a namespace closed before §6. §6 opens and closes its own namespaces (`Link.Record`, `Link`/`Record`, `Link.Diagram`) and uses `open scoped Classical in` / `open SM.Link in` per declaration; all of these are inside §6 and are reproduced verbatim. `blockRestrict` is declared `noncomputable def` explicitly (as in the statement file). Nothing from §0-§5 or §7 (other than the stack bundle) is re-declared: SM/PolynomialBlock.lean (1182 lines) holds §0-§5 and the four other bundles, and the module compiles against its olean.

Statement fidelity vs work/drafts/Stack_statement.lean: the 12-line block `/-- mp:stack as printed. -/ structure StackData : Prop where … P (blockRestrict D blk hblk 1)` is byte-identical (`cmp` on the extracted blocks). The theorem line is `theorem stack : StackData where` (skeleton form) vs `theorem stack : StackData := by` in the statement file — identical up to the proof delimiter, exactly like the four rows already ported into SM/PolynomialBlock.lean (`record_polynomial`, `lp_core`, `split_circle` use `where` against `:= by` statement files). The `blockRestrict` / `BlockOrdered` definitions are code-identical to the statement file (the `BlockOrdered` docstring carries the skeleton's extra "(copied verbatim)." note).

Name-clash check: all 80 declaration names of Stack_Module.lean were grepped as declarations across the 584 `.lean` files under work/lean/SM and work/lean/CV — no match, not even by last name component in another namespace. No work/lean/SM/Stack*.lean exists yet (SM/PolynomialBlock.lean's §7 docstring already points to `SM/Stack.lean` as the intended home).

## Exact `lake env lean` output for Stack_Module.lean

```
$ cd work/lean && lake env lean ../drafts/polyblock/Stack_Module.lean
(no output)
EXIT 0 ELAPSED 13s
$ lake env lean /tmp/stackasm/Stack_Module_ax.lean     # same file + `#print axioms SM.stack` / `SM.stack_formula`
'SM.stack' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lp_lm]
'SM.stack_formula' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lp_lm]
EXIT 0 ELAPSED 13s
```

## Deviations / notes

1. Stack_Assembled_full.lean is the pure merge except for its header docstring: the skeleton's `Status` paragraph (which listed the 13 `sorry` leaves) was rewritten to describe the assembled state, so that the file contains no `sorry` token at all (prose included). No code line differs from skeleton + hunks. Recompiled after the edit: no output, 14 s.
2. U2's `:= by` → `:=` delimiter change on two statements (see Step 1) is the only non-`sorry` line removal; statements unchanged.
3. Nothing was written under work/lean; the module is delivered as work/drafts/polyblock/Stack_Module.lean and needs only to be copied to work/lean/SM/Stack.lean (its docstring-declared home) and added to the build to become a library module.
4. Blank-line difference: the module has one blank line between `theorem stack` and `end SM` where the assembled file has two.
