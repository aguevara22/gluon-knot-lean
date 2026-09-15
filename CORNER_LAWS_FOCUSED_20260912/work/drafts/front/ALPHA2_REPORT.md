# Lane α, unit α2 — row 74 ng:smoothing-record — report, 2026-09-14 (rebased on the ported row 73)

**Deliverable:** `work/drafts/front/FrontRecordBridge.lean` (intended home `work/lean/SM/FrontRecordBridge.lean`),
479 lines, 41 declarations, **sorry-free** (`grep -c "sorry\|admit\|native_decide"` → 0).
Check: `cd work/lean && lake env lean ../drafts/front/FrontRecordBridge.lean` → no errors, no warnings, exit 0
(Lean v4.34.0-rc2, project Mathlib pin; ~6 s), against the ported `work/lean/SM/FrontSmooth.lean` (v2, 03:47 UTC).
Main declaration: `SM.ng_smoothing_record : SM.SmoothingRecordData` (PROVED).
`#print axioms SM.ng_smoothing_record` → `[propext, Classical.choice, Quot.sound, SM.lp_lm]` (`SM.lp_lm` only through `P`);
`Marking.recordIso`, `GeomRounding.occSetOf_eq`, `IsRounding.recordIso_nonempty` → the standard three.
Imports: `SM.FrontSmooth` only.  Scratch files (α1-basis unit incl. the defect proof `GeomRounding.false_of_cusp`,
the v2 mock test, the rebase file) moved to `/tmp/front_scratch/` as instructed.

## 1. Structure of the file (printed proof, sentence by sentence)

| § | content | reuse |
|---|---|---|
| doc | printed statement and proof verbatim; basis note (α1 defects → v2 repair); notion → Lean table; FR-1, FR-4 | |
| 1 | `signType_intCast_injective` | |
| 2 | `IsDoubleOf G p q`, `occSetOf G`, `slopeOf G p`, `crossSignOf G p q` for a loop family `G : Fin c → SmoothLoop` (the rounded curves are not a `SmoothFront`); on `F.comp` they are `F`'s notions by `rfl` | |
| 3 | `GeomRounding.isDoubleOf_iff` ("creates no crossing"; = module `isDouble_iff`), `eventuallyEq_of_isDouble` (germ of `G` at a double point = germ of `F`), `occSetOf_eq : occSetOf G = F.occSet` ("changes no successor …": same parameters on the same oriented circles), `slopeOf_eq`, `crossSignOf_eq` ("determined by germs outside the cusp discs, which are unchanged") | module: `isDouble_iff`, `closedArcFree_of_isDouble`, `eventuallyEq_of_closedArcFree`, `deriv_eq_of_isDouble` |
| 4 | `Marking.exists_partner`, `partner_of_Φ_eq_twin`, `compOf_eq_e`, `compOf_eq_iff`, `visitBetween_iff`; **`Marking.recordIso (m : F.Marking S) (m' : F.Marking S') : RecordIso S.record S'.record`** ("Thus any two such diagrams have a named decorated-record isomorphism"): `e := m.e.symm.trans m'.e`, `Φ := m.Φ.symm.trans m'.Φ`; `succ_eq` via the accepted `Diagram.nextVisit_comm_of_visitBetween_iff` with `between_iff` on both sides; `pair_eq` via the partner; `bit_eq` via `over_iff` both sides; `sgn_eq` via `sgn_eq` both sides in either slope order (`slope_ne_of_isDouble`, `twin_fst`) | accepted LinkDiagramRecord |
| 5 | `RecordIso.{compOf_eq, nextVisit_eq, twin_eq, overBit_eq, sign_eq}` (diagram vocabulary; `compOf_iff`, `visitBetween_iff` are the accepted ones) | |
| 6 | `recordIso_nonempty_of_markings`, `P_eq_of_markings`, `defect_eq_of_markings` | `presentations` |
| 7 | `Rounding.iso ρ ρ' := ρ.marking.recordIso ρ'.marking`; `IsRounding.{marking_nonempty, recordIso_nonempty, P_eq, defect_eq}`; bundle `SmoothingRecordData` (14 fields) and `theorem ng_smoothing_record` | module `Rounding.componentCount_eq`, `Marking.card_visit_eq`, `comp_eq`, `GeomRounding.agree` |

## 2. The bundle (pasted from the file)

```lean
structure SmoothingRecordData : Prop where
  /-- "Any two ordinary diagrams S(F) obtained by the cusp replacement of that definition have the same full named record" -/
  full_named_record : ∀ (F : SmoothFront) (S S' : Diagram), F.IsRounding S → F.IsRounding S' →
    Nonempty (RecordIso S.record S'.record)
  /-- "the same component circles, including crossing-free ones" -/
  component_circles : ∀ (F : SmoothFront) (S S' : Diagram) (ρ : F.Rounding S) (ρ' : F.Rounding S'),
    S.componentCount = F.c ∧ S'.componentCount = F.c ∧
    ∀ v, S'.compOf ((ρ.iso ρ').Φ v) = (ρ.iso ρ').e (S.compOf v)
  /-- "and the same crossing occurrences" -/
  crossing_occurrences : ∀ (F : SmoothFront) (S S' : Diagram) (ρ : F.Rounding S) (ρ' : F.Rounding S'),
    Fintype.card S.Γ.Visit = Fintype.card F.Occ ∧ Fintype.card S'.Γ.Visit = Fintype.card F.Occ ∧
    ∀ v, (ρ.iso ρ').Φ (S.twin v) = S'.twin ((ρ.iso ρ').Φ v)
  /-- "cyclic orders" -/
  cyclic_orders : ∀ (F : SmoothFront) (S S' : Diagram) (ρ : F.Rounding S) (ρ' : F.Rounding S'),
    (∀ v, (ρ.iso ρ').Φ (S.nextVisit v) = S'.nextVisit ((ρ.iso ρ').Φ v)) ∧
    ∀ v w u, S.compOf w = S.compOf v → S.compOf u = S.compOf v →
      (S'.VisitBetween ((ρ.iso ρ').Φ v) ((ρ.iso ρ').Φ w) ((ρ.iso ρ').Φ u) ↔ S.VisitBetween v w u)
  /-- "over/under bits" -/
  over_under_bits : ∀ (F : SmoothFront) (S S' : Diagram) (ρ : F.Rounding S) (ρ' : F.Rounding S'),
    ∀ v, S'.overBit ((ρ.iso ρ').Φ v) = S.overBit v
  /-- "and signs." -/
  signs : ∀ (F : SmoothFront) (S S' : Diagram) (ρ : F.Rounding S) (ρ' : F.Rounding S'),
    ∀ v, S'.sign ((ρ.iso ρ').Φ v).1 = S.sign v.1
  /-- "Consequently P_{S(F)} does not depend on the choice of rounding." -/
  polynomial : ∀ (F : SmoothFront) (S S' : Diagram), F.IsRounding S → F.IsRounding S' → P S = P S'
  /-- (proof) "A cusp replacement inside a clean cusp disc creates no crossing" -/
  no_new_crossing : ∀ (F : SmoothFront) (S : Diagram) (ρ : F.Rounding S) (p q : Param F.c),
    IsDoubleOf ρ.G p q ↔ F.IsDouble p q
  /-- (proof) "and changes no successor of an old crossing visit along the oriented parameter circle" -/
  successor_unchanged : ∀ (F : SmoothFront) (S : Diagram) (ρ : F.Rounding S),
    occSetOf ρ.G = F.occSet
  /-- (proof) "the replacing arc has the same oriented attachments as the cusp it replaces" -/
  same_attachments : ∀ (F : SmoothFront) (S : Diagram) (ρ : F.Rounding S) (i : Fin F.c) (t : ℝ),
    (∀ c : F.Cusp, c.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (ρ.geom.a c) (ρ.geom.b c)) →
    (ρ.G i).γ t = (F.comp i).γ t
  /-- (proof) "Every crossing pairing, sign and over/under bit is determined by germs outside the cusp discs, which are unchanged" -/
  germs_unchanged : ∀ (F : SmoothFront) (S : Diagram) (ρ : F.Rounding S) (p q : Param F.c),
    F.IsDouble p q → ((ρ.G p.1).γ =ᶠ[𝓝 p.2] (F.comp p.1).γ) ∧
      slopeOf ρ.G p = F.slope p ∧ crossSignOf ρ.G p q = F.crossSign p q
  /-- (proof) "and the component correspondence is the identity on the parameter circles, including those without crossings" -/
  component_identity : ∀ (F : SmoothFront) (S : Diagram) (ρ : F.Rounding S),
    S.componentCount = F.c ∧ ∀ p : F.Occ, S.compOf (ρ.marking.Φ p) = ρ.marking.e p.1.1
  /-- (proof) "Thus any two such diagrams have a named decorated-record isomorphism": an S(F) carries the named record of F itself -/
  front_record : ∀ (F : SmoothFront) (S : Diagram), F.IsRounding S → Nonempty (F.Marking S)
  /-- (proof) "and Lemma rp:record-polynomial identifies their polynomial values" (the accepted `presentations`) -/
  record_polynomial : ∀ D D' : Diagram, Nonempty (RecordIso D.record D'.record) → P D = P D'

theorem ng_smoothing_record : SmoothingRecordData  -- all 14 fields discharged
```
"This does not use an ambient identification with a spatial cusp-shaped link" is witnessed by `#print axioms`
(standard + `SM.lp_lm` only); recorded in the theorem's docstring.

## 3. Readings recorded

* FR-1: `S(F)` is a polygonal `Diagram` carrying the front's own named record (`Rounding.marking : F.Marking S`,
  ported module); the justification that this is the record of the rounded curves is the module's
  `GeomRounding.isDouble_iff` / `deriv_eq_of_isDouble` plus §3 here (occurrence set, slopes, signs, germs).
* FR-4: "same oriented attachments" = `GeomRounding.agree` on the shared parameter circles (field `same_attachments`).
* "the same component circles, including crossing-free ones" is read as: both `componentCount`s equal `F.c` and the
  record isomorphism's `e : Fin S.Γ.c ≃ Fin S'.Γ.c` is compatible with the occurrence bijection (`compOf_eq`).
* "cyclic orders" is rendered both as successor commutation (`RecordIso.succ_eq`) and as the equivalence of the
  oriented betweenness relations (accepted `RecordIso.visitBetween_iff`), the two being equivalent by the accepted
  `nextVisit_comm_iff_visitBetween_iff`.

## 4. History of this unit (for the reviewer)

The unit was first written against the α1 row 73 and found (independently of the coordinator's review) that its
`GeomRounding` is uninhabited for cusped fronts (`GeomRounding.false_of_cusp`, kernel-checked; open-interval `clean`
vs. compact disc + continuity of the replacing arc).  That version (804 lines, its bundle proved, the F-side clause
derivable only through the defect) and a v2 mock test are in `/tmp/front_scratch/` (`FrontRecordBridge_alpha1.lean`,
`FrontRecordBridge_mocktest.lean`, `FrontRecordBridge_row_v2.lean`).  After the port, the duplicated helpers
(`eventually_add_int_notMem_Icc`, arc bookkeeping, `CleanReplacement` mirror, the `castParam` transfer no longer
needed since `G` lives on `Fin F.c`) were dropped in favour of the module's `GeomRounding` lemmas.

## 5. Not proved / not needed

* Nothing of the printed statement or proof is left unrendered.  Regularity of the rounded curves is the module's
  `GeomRounding.regular_everywhere` (not used by this row).
