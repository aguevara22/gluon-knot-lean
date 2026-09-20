# U_READING_REPORT — unit READING (U4, PLAN_FINAL §6 U4 / §7 R1), prover report

Prover, 2026-09-15.  File: `work/drafts/contact/U_READING.lean` (copy of `Skeleton_FINAL.lean`; helper
prefix `urd_`).  Check: `cd work/lean && lake env lean ../drafts/contact/U_READING.lean` — **0 errors**,
10 warnings (`declaration uses sorry`, one per remaining unit leaf of the OTHER units), ~10 s.
`grep -c sorry`: 12 before → 11 after (the surviving hit at line 19 is the module docstring; the 10 leaf
`sorry`s are `u_circle`, `u_sl_radius`, `u_sl_family`, `u_sl_reparam`, `u_sl_isotopy`, `u_legendrianFront`,
`u_spatialOf`, `u_transport`, `u_regular`, `u_family`).  Diff against `Skeleton_FINAL.lean`: exactly one
line removed (the `sorry` body of `u_reading`), 247 lines added (the helper block + the proof); no
definition, structure, axiom, statement, name or docstring touched.

Axiom check (on a scratch copy with `#print axioms` appended): `SM.u_reading` and
`SM.urd_markingOfRecordIso` depend on `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`, no
literature axiom.  THE RISK ITEM R1 IS CLOSED: row 94 is no longer blocked by FR-1.

## 1. Leaves

| leaf | status |
|---|---|
| `u_reading : U_reading` (`∀ F : SmoothFront, ∃ S : Diagram, Nonempty (F.Marking S)`) | **PROVED** |

Proof route = PLAN_FINAL §6 U4 verbatim: `S := (realize (FrontRows.U8R.oword F)).diagram`;
`ι : RecordIso (frontRecord F) S.record := (FrontRows.U8R.recordIso F).trans
(FrontRows.U2.realizeRecordIso (oword F) (word_ne_nil F)).symm` (types unify: `(oword F).closed` reduces to
`word_closed F`); `m := urd_markingOfRecordIso ι`.  The fallback (extracting a `Marking` from the sweep
block's own `occEquiv` / `circleEquiv` / `ΦFun_cycNext`) was NOT needed.

## 2. Helpers added (all inside `section urd_helpers … end urd_helpers`, placed in §5.4 immediately before
`theorem u_reading`; `open FrontRows FrontRows.U8R` local to the section)

Generic cyclic-enumeration layer (`Diagram.ent` / `visitBetween_ent_iff` / `visitBetween_iff_of_nextVisit_comm`
of SM/LinkDiagramRecord.lean made generic over ANY list):
* `urd_ent l hl n := l[n % l.length]` — definitionally `Diagram.ent i hi n` for `l = D.compList i`.
* `urd_ent_of_lt`, `urd_ent_congr` (index congruence mod length; NO `Nodup` needed), `urd_exists_ent`,
  `urd_ent_add_sub` (the `(b + len − a) % len` step), `urd_iterate_ent` (`s^[j] (ent n) = ent (n + j)`),
  `urd_iterate_comm` (a map commuting with `s` commutes with `s^[j]`).
* `urd_cycBetween_ent_iff` — `cycBetween (k (ent a)) (k (ent (a+j))) (k (ent (a+j'))) ↔ j < j'` for
  `0 < j, j' < len`, from the accepted `cycIdx_iff` + `add_mod_cases` (SM/LinkDiagramRecord.lean:860-873),
  under the hypothesis `hk : k (ent a) < k (ent b) ↔ a % len < b % len` (strict key-sortedness).
* `urd_cycBetween_iff_of_succ_comm` — THE STRUCTURAL LEMMA: two key-sorted cycles `l`, `l'` of equal length
  with successors `s`, `s'` (`s (ent n) = ent (n+1)`), and any `Φ` with `Φ ∘ s = s' ∘ Φ` mapping `l` into `l'`,
  preserve `cycBetween` of the keys (`x, y, z ∈ l`).  Proof mirrors `Diagram.visitBetween_iff_of_nextVisit_comm`:
  the three degenerate cases by `not_cycBetween_self_*`, then indices `j = (b + len − a) % len`, transport by
  `s^[j]`.  Injectivity of `Φ` is not needed (both sides reduce to `j < j'` with the SAME `j, j'`).

Front side (U8R's `fibList` / `cycNext`, SM/FrontRowsW2.lean:13361-13560):
* `urd_fibList_length` (`Finset.length_sort` under `keyOrder`), `urd_fibList_key_ent_lt_iff` (keys along the
  sorted fibre compare as indices: `Finset.sortedLT_sort` + `List.SortedLT.getElem_lt_getElem_iff` +
  `keyOrder_lt_iff`), `urd_cycNext_ent` (from the accepted `cycNext_getElem`).

The record isomorphism read on the front's data:
* `urd_Φ ι : F.Occ ≃ S.Γ.Visit := ι.Φ`, `urd_e ι : Fin F.c ≃ Fin S.Γ.c := ι.e` — retyped copies (see pitfall 1).
* `urd_compOf_Φ`, `urd_Φ_cycNext`, `urd_Φ_partner`, `urd_overBit_Φ`, `urd_sign_Φ` — the five record clauses
  `comp_eq`/`succ_eq`/`pair_eq`/`bit_eq`/`sgn_eq`, each a one-token `rfl`-retyping of the `RecordIso` field
  (`frontRecord_*` and `Diagram.record_*` are all `rfl`).
* `urd_fib_map_eq` (`(fib (occComp F) i).map Φ = S.compVisits (e i)`), `urd_compList_length_eq` (equal fibre
  lengths, via `Finset.card_map`).
* `urd_between_iff` — the `between_iff` clause of `Marking` from `succ_eq`, instantiating the structural lemma
  with `l = fibList (occComp F) (occKey F) (occKey_inj F) p.1.1`, `k = occKey F`, `s = cycNext …` and
  `l' = S.compList (e p.1.1)`, `k' = S.visitCoord`, `s' = S.nextVisit` (diagram-side hypotheses are the accepted
  `Diagram.visitCoord_ent_lt_iff` and `Diagram.nextVisit_ent`, accepted by `exact` since `Diagram.ent` unfolds
  to `urd_ent`).
* `urd_markingOfRecordIso ι : F.Marking S` — THE CONVERSE OF `markingRecordIso`: `e`, `Φ`, `comp_eq` direct;
  `between_iff := urd_between_iff ι`; `pair_eq`/`over_iff`/`sgn_eq` by `eq_partner_of` (uniqueness of the
  partner, `no_triple`) then the record clause (`frontOver = decide (slope < slope partner)`,
  `frontSgn` unfolds under `hs` to `sign (det …)` = `crossSign_eq_sign`).

Total ≈ 240 lines (plan estimate 900; the enumeration argument already existed for diagrams and only had to
be made generic).

## 3. Mathlib / Lean pitfalls met

1. **Retype the `RecordIso` bijections before `rw`.**  `ι.Φ : (frontRecord F).M ≃ S.record.M`; the types are
   `rfl`-equal to `F.Occ ≃ S.Γ.Visit` but only after δ-unfolding `frontRecord`, which `rw` does not do
   (motive "not type-correct under implicit transparency"; `Finset.map ι.Φ.toEmbedding (fib …)` and
   `S.overBit (ι.Φ p)`, `S.sign (ι.Φ p).1` all failed).  `def urd_Φ ι : F.Occ ≃ S.Γ.Visit := ι.Φ` fixes every
   such rewrite; `exact ι.succ_eq p` etc. are accepted by defeq for the retyped statements.
2. `urd_ent` must be `unfold`ed before rewriting with `mem_fibList … (List.getElem_mem _)` (the `l[i]` pattern is
   hidden behind the definition); everywhere else `exact` handles the defeq.
3. `if_pos` is deprecated in this Mathlib (warning); use `simp only [hs, ↓reduceIte]` (as `markingRecordIso` does).
4. Instances agree: `frontRecord F`'s `DecidableEq F.Occ` / `Fintype F.Occ` (FrontRowsW2 has no global
   `open Classical`) coincide with those elaborated under the skeleton's `open Classical`
   (`(frontRecord F).succ p = cycNext (occComp F) (occKey F) (occKey_inj F) p` is `rfl` in the file's context).
5. `omega` is not needed for `0 < (b + len − a) % len`; `Nat.pos_of_ne_zero` + `rw [h0, Nat.add_zero]` on the
   `urd_ent` equation avoids the `% variable` question.
6. Fully-qualified names (namespace `SM`): `FrontRows.U8R.{recordIso, frontRecord, oword, word_ne_nil, fibList,
   cycNext, cycNext_getElem, keyOrder_lt_iff, mem_fibList, fib, mem_fib, occComp, occKey, occKey_inj, partner,
   eq_partner_of, isDouble_partner, frontOver, frontSgn}`, `FrontRows.U2.realizeRecordIso`, `SM.realize`,
   `Link.cycBetween` (opened), `Link.Diagram.*` (via `S.` dot notation).

## 4. For the assembler / executor

* Nothing to graft: `fd_contact_of_units … (U_package_of u_legendrianFront u_spatialOf u_reading u_transport) …`
  in §6 now consumes a proved `u_reading`; the remaining `sorry`s of the file are the other units' leaves.
* `urd_markingOfRecordIso` is a reusable converse of `markingRecordIso` (FrontRowsW2.lean:13748); with it,
  `Nonempty (F.Marking S) ↔ Nonempty (RecordIso (frontRecord F) S.record)` for every `S`.  The generic
  `urd_cycBetween_iff_of_succ_comm` is the "successor determines cyclic order" lemma for ANY pair of
  key-sorted finite cycles (the diagram-only `Diagram.visitBetween_iff_of_nextVisit_comm` is its special case).
* No leaf of this unit is false or needs a stronger hypothesis.
* Module placement suggestion when porting to `SM/FdContactUnits*.lean`: the generic layer (`urd_ent` … 
  `urd_cycBetween_iff_of_succ_comm`) belongs next to `cycIdx_iff` in SM/LinkDiagramRecord.lean's §G; the
  `fibList` lemmas next to `cycNext_getElem` in FrontRowsW2 §A; `urd_markingOfRecordIso` next to
  `markingRecordIso` (FrontRowsW2 §C).
