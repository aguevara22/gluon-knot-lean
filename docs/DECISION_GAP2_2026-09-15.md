# Decision on GAP-2 — 2026-09-15

**Owner:** Seif (author of the source, frame SM15). **Decision:** restate the HOMFLY literature input so that it carries
its printed descent clause, in the *additive* form below. **Status:** decided, not yet executed (execution runs on Mark's pod).

## The gap in one paragraph

Row 91 `cp:finite-contact-path` (sm-3-statesum.tex:3210) needs "an ambient isotopy of links gives equal HOMFLY values of
their diagrams". The printed literature input lit:homfly (sm-3:916-923) ends with exactly that sentence: "Its value depends
only on the oriented link presented by D". The executor's design decision D2 rendered the sentence as
`HomflyClauses.descent : LinkEquiv D D' → H D = H D'`, i.e. invariance under planar isotopy and the three Reidemeister
moves between *polygonal diagrams* only, and declared Reidemeister's theorem (smooth isotopy ⇒ move sequence) out of
scope with "no sixth axiom". So the accepted axiom `SM.lit_homfly` is weaker than the printed one. Row 91 was proved
modulo the single proposition `SM.AmbientIsotopyDescent` (`work/lean/SM/ContactPathOfDescent.lean:176`, statement
independently reviewed clean), and 22 claim rows behind it stayed open, including thm:C-S7, thm:C-soft,
thm:comparison, cor:C-inherits, Hypothesis R, the bridge, and `SM.corner_laws_and_soft`.

## The chosen form (additive, nothing accepted is rewritten)

1. `SM.lit_homfly` and `HomflyClauses` stay byte-identical. The printed descent sentence is declared as its own axiom
   about the already fixed function `SM.homfly`:

   ```lean
   axiom lit_homfly_descent : AmbientIsotopyDescent
   ```

   in a module imported after `SM.CeSmoothingRecord` (which owns `SpatialLink`, `SpatialFamily`, `HeightMarking`), using
   the proposition already stated in `SM/ContactPathOfDescent.lean`.
2. `work/lean/axiom-policy.json` gains the name under `literature` as a second declaration of lit:homfly. This is the
   same registry item (`blueprint/AXIOM_REGISTRY.md` "lit:homfly", sm-3:920-921), not a sixth literature interface; the
   author authorizes this reading. The declaration gets the same interface review as the other four.
3. Row 91 closes with one line, `cp_finite_contact_path := cp_finite_contact_path_of_descent lit_homfly_descent`,
   is mapped and reviewed, and the chain resumes: 94, 99, 100, 103, 105, 110, 112, 122, 127, 128; CV 155, 161, 162, 165;
   R 174-178; Bridge:theorem; the final theorem.

Because `homfly`'s definition does not change, the 28 accepted rows that depend on `SM.lit_homfly` keep their reviewed
statement hashes and need no re-review. This is the executor's route (α) without the type change, or equivalently
route (α′) with the isotopy-extension step absorbed into the literature clause (the clause is stated on a jointly smooth
family of embeddings; for compact links such a family extends to an ambient isotopy, so the two ends present the same
oriented link).

## Also requested in the same batch

- Declare `src:contact` (`SM.src_contact`, the fifth interface, sm-3:3341-3365): rows 94 and 161 consume it.
- Refresh the `FINAL_REVIEW.md` line of the root `MANIFEST.sha256` (`verify_bundle.py` failed on it, which made
  `setup.sh` stop before the checker). Done in this repository on 2026-09-15, together with dropping the `work/` line
  from the package's `.gitignore`; Mark's copy has both until the next pull.
- Row 57 `lem:gauss-two-discs` stays deferred (no pending consumer). The reassessment rule keeps applying per branch.

## Note as sent to Mark

```text
Decision on GAP-2 (2026-09-15): restate, in the additive form.

1. Do not modify SM.lit_homfly or HomflyClauses (accepted). Instead declare the printed
   descent sentence of lit:homfly ("Its value depends only on the oriented link presented
   by D", sm-3:920-921) as its own axiom about the existing SM.homfly:
       axiom SM.lit_homfly_descent : SM.AmbientIsotopyDescent
   using the Prop already stated and reviewed in SM/ContactPathOfDescent.lean. Put it in a
   module after SM.CeSmoothingRecord so the spatial vocabulary is in scope.
2. Register the name in work/lean/axiom-policy.json under literature as a second
   declaration of lit:homfly (not a sixth interface; I authorize this reading as the author).
   Interface-review it against the registry text like the other four.
3. Close row 91: cp_finite_contact_path := cp_finite_contact_path_of_descent lit_homfly_descent,
   map it, review it, then continue down the chain (94, 99, 100, 103, 105, 110, 112, 122, 127,
   128, the CV rows 155/161/162/165, R rows 174-178, Bridge:theorem, the final theorem).
4. Also declare src:contact now (rows 94 and 161 need it), refresh the FINAL_REVIEW.md line in
   the root MANIFEST.sha256 (verify_bundle.py currently fails on it), and delete the stray
   file "=3" at the package root.
5. Row 57 stays deferred. Apply the reassessment rule per branch as before.
```
