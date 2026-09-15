# U_KL3_REPORT — unit KL3 (restriction of the abstract record)

Prover subagent, 2026-09-14. File: `work/drafts/cb/U_KL3.lean` (copy of Skeleton_FINAL.lean with unit KL3 filled in).
Compile: `cd work/lean && lake env lean ../drafts/cb/U_KL3.lean` → **0 errors**; 13 `declaration uses sorry` warnings, all
other units' leaves (KL0 ×6, KL1 ×2, KL2, T1, GL, AS ×2). `grep -c sorry`: 18 before → 17 after. Two pre-existing warnings
untouched (unused `hT` in `exists_blockCarrier`, deprecated `Set.mem_setOf_eq` in the glue).

## Leaves

| leaf | status |
|---|---|
| `SM.CB.gaussRecord_restrict_iso (hc) {T' T} (h : T' ⊆ T) : Nonempty (RecordIso ((gaussRecord hc T).restrictCrossings {p ∣ label hc T p ∈ T'}) (gaussRecord hc T'))` | **PROVED** (statement/docstring byte-identical) |

No other leaf belongs to KL3 in the skeleton (`blockPoly_eq_of_labels_eq` of PLAN §6 is not a skeleton leaf; see §"For the executor").

`#print axioms SM.CB.gaussRecord_restrict_iso`: `[propext, sorryAx, Classical.choice, Quot.sound]` — `sorryAx` enters ONLY through the
KL0 black boxes it consumes: `gaussSucc`/`gaussSucc_val`, `gaussPair`/`gaussPair_val`, `gaussRecord` (its sorried laws are part of the
term), `label_crossingOf`. Once KL0 lands, the leaf is on standard axioms. The general theorem `kl3_firstReturn_next_filter` is
sorry-free: `[propext, Classical.choice, Quot.sound]`.

## Helpers added (all `SM.CB.kl3_*`, immediately before the leaf, in `namespace CB`)

Generic list/permutation lemmas (section `kl3_helpers`, `{α β : Type*} [DecidableEq α]`, `omit [NeZero n]`):
* `kl3_next_congr (l) (hx : x ∈ l) (hy : y ∈ l) (hxy : x = y) : l.next x hx = l.next y hy` — `List.next` congruence in the element
  (needed because `rw` cannot rewrite under the dependent membership proof).
* `kl3_next_congr_list (hll : l = l') (x) (hx) : l.next x hx = l'.next x (hll ▸ hx)` — same, in the list.
* `kl3_pow_val (f : Perm β) (g : β → α) (l) (hl : l.Nodup) (hmem : ∀ b, g b ∈ l) (hf : ∀ b, g (f b) = l.next (g b) (hmem b))
  (b) (i) (hi : i < l.length) (hb : l[i] = g b) (j) : g ((f ^ j) b) = l[(i + j) % l.length]` — iterating a `List.next`-permutation
  walks the list cyclically (`List.next_getElem`, `Nat.mod_add_mod`).
* `kl3_filter_rotate_isRotated (l) (q) (k) : l.filter q ~r (l.rotate k).filter q` — via `rotate_eq_drop_append_take`,
  `filter_append`, `isRotated_append`. (Mathlib has no `IsRotated.filter`.)
* **`kl3_firstReturn_next_filter [Fintype β] (f) (g) (l) (hl) (hmem) (hf) (p : β → Prop) [DecidablePred p] (q : α → Bool)
  (hpq : ∀ b, p b ↔ q (g b) = true) (b : {b // p b}) : g (firstReturn f p b).1 = (l.filter q).next (g b.1) _`** — the heart:
  the first return of a `List.next`-permutation to the `q`-entries is `List.next` on the filtered list. Proof: rotate `l` so that
  `g b` is the LAST entry (`m := l.rotate (i+1)`, `m[j] = g (f^(j+1) b)`), decompose `m.filter q = y :: rest` as `m = a ++ y :: c`
  with `¬q` on `a` (`List.filter_eq_cons_iff`); then `returnTime = a.length + 1` (`returnTime_eq_iff`) so the first return is `y`;
  on the other side `l.filter q ~r m.filter q` (`List.isRotated_next_eq`), `m.filter q = (m.dropLast).filter q ++ [g b]`
  (`dropLast_append_getLast`), and `List.next_getElem` at the last index gives entry `0` = `y`. Rotating to the tail (not the head)
  avoids the case split "no other `q`-entry" vs "some `q`-entry".

Unit-specific:
* `kl3_mem_gaussList (hc) (T) (v) : v ∈ gaussList hc T ↔ v.1 ∈ T` (`mem_geometricGaussList`).
* `kl3_gaussList_filter (hc) (h : T' ⊆ T) : (gaussList hc T).filter (fun v => decide (v.1 ∈ T')) = gaussList hc T'`
  (`List.filter_filter`, `List.filter_congr`).
* `kl3_crossKeep_iff (hc) (T T') (v) : (gaussRecord hc T).CrossKeep {p | label hc T p ∈ T'} v ↔ (occVisit hc T v).1 ∈ T'`
  (KL0's `label_crossingOf`).

The leaf's `RecordIso`: `e := Equiv.refl Unit`; `Φ v := ⟨occVisit hc T v.1, _⟩`, inverse `w ↦ ⟨⟨w.1, h w.2⟩, _⟩`; `comp_eq`, `bit_eq`
(`positiveOverBit` of the same visit), `sgn_eq` (`1 = 1`) are `rfl`; `pair_eq` by `gaussPair_val` twice (both sides `visitTwin`);
`succ_eq` = `kl3_firstReturn_next_filter` at `f := gaussSucc hc T`, `g := occVisit hc T`, `l := gaussList hc T`,
`p := CrossKeep …`, `q := decide (·.1 ∈ T')`, then `kl3_gaussList_filter` + `gaussSucc_val hc T'`.

## Mathlib / Lean pitfalls met (v4.34.0-rc2)

1. **Tactic blocks in a theorem STATEMENT include every section variable.** `l[(i+j) % l.length]'(Nat.mod_lt _ (by omega))` in
   `kl3_pow_val`'s statement pulled in the shadowed `[NeZero n✝]` (the file has two `variable {n} [NeZero n]` layers in
   `namespace CB`), and every application then failed with "typeclass instance problem is stuck NeZero ?m". Use term proofs in
   statements (`Nat.zero_lt_of_lt hi`).
2. `getElem_congr_idx` is in the ROOT namespace (Init/GetElem.lean), not `List.`. Use it (or `List.getElem_of_eq` for the list)
   to rewrite under `l[i]'h` — `rw` fails with "motive is not type correct" on the dependent proof.
3. **TC cannot unfold `gaussRecord`**: applying a lemma with `β := ρ.M` implicit, `f := gaussSucc hc T : Perm {v // v.1 ∈ T}` fixes
   `β` to the subtype and then `DecidablePred ((gaussRecord hc T).CrossKeep X)` / `Fintype β` fail to synthesize (the instances are
   stated at `(gaussRecord hc T).M`). Pass `(β := (gaussRecord hc T).M)` explicitly; defeq of the explicit arguments is checked at
   default transparency and succeeds.
4. `show (gaussPair hc T v.1).1 = …` with `v.1 : (gaussRecord hc T).M` type-checks but leaves a target that is "not type-correct
   under implicit transparency", so the following `rw [gaussPair_val]` fails. Prove the equation as a `have` on the bare subtype
   `{v : Visit P // v.1 ∈ T}` and `exact` it.
5. `omega` does not identify `(l.rotate k).length` with `m.length` for `set m := l.rotate k`; rewrite `List.length_rotate` first.
6. Names: `List.filter_filter : filter p (filter q l) = filter (fun a => p a && q a) l` (outer predicate first);
   `List.filter_eq_cons_iff`; `List.getElem_concat_length (h : i = l.length) w : (l ++ [a])[i]'w = a`; `List.isRotated_next_eq`;
   `List.getElem_rotate : (l.rotate n)[k] = l[(k + n) % l.length]`; `Nat.mod_add_mod`, `Nat.add_mod_right`.
7. `Set.mem_setOf_eq` is deprecated in this Mathlib (→ `Set.mem_ofPred_eq`); the glue uses it (warning only).

## For the assembler / executor

* Nothing in the leaf depends on `hn`, `hP`, `NeZero`-free geometry or the CV layer: the proof is pure list combinatorics on top of
  KL0's spec lemmas. It will port verbatim to `SM/CBRecordRestriction.lean` after `SM/CBGaussRecord.lean` (KL0) — the generic
  section `kl3_helpers` could equally live in `SM/LinkRecordExtras.lean` (next to `firstReturn_map_val`) as a general
  `firstReturn`/`List.next` bridge; it does not mention records.
* The KL0 lemmas actually consumed (KL0 must deliver exactly these statements): `gaussSucc_val`, `gaussPair_val`, `label_crossingOf`,
  plus `mem_geometricGaussList`, `geometricGaussList_nodup` (accepted). No use of `succ_cycle`/`bit_pair` etc. beyond the record term.
* Intended instantiation in `record_iso_blockRecord`: `T := carrierCrossings hn hP S A_H`, `T' := pieceLabels (cg hn hP) S H`
  (`⊆` by `carrierCrossings_eq_biUnion`/`mem_piecesOn`), composed with KL1 (`positiveLiftRecordIso` at `A_H`, transported by T1
  to the restricted records with `X := blockRecordCrossings … A_H H`, `X' := {p | label hc T p ∈ T'}` — the occurrence condition is
  `mem_blockRecordCrossings_crossingOf` + `positiveLiftRecordIso_val` + `label_crossingOf`) and KL1 at the block carrier `q`
  (`carrierCrossings T q = pieceLabels H`).
* `blockPoly_eq_of_labels_eq` (PLAN §6, for cb:singleton / CV:prop:chamberinv(ii)): not a skeleton leaf, so not added here (frozen
  file). In the module state it as: for two carriers `q`, `q'` of independent `T`, `T'` with `carrierCrossings T q = carrierCrossings
  T' q'`, `SM.P (positiveLift … q) = SM.P (positiveLift … q')` — this needs only KL1 twice + `RecordIso.trans/symm` + `P_eq_of_recordIso`
  (lc:presentations); KL3 enters only when one side is a RESTRICTED record (`blockRecord`), exactly as in `record_iso_blockRecord`.
* Sanity: the assembled `SM.cb_products` still compiles against the filled leaf (0 errors in the whole file).
