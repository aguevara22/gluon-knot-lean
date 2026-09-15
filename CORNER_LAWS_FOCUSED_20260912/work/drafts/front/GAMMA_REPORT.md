# Lane α, unit γ ("front lane γ", decision D-F6) — the geometric model of S(F) — report, 2026-09-14

**Deliverable:** `work/drafts/front/FrontGeomModel.lean` (intended home `work/lean/SM/FrontGeomModel.lean`),
358 lines, 33 declarations, no placeholders, no admits, no new axioms (`grep -c` for the placeholder words → 0;
no `axiom` line).
Check: `cd work/lean && lake env lean ../drafts/front/FrontGeomModel.lean` → no errors, no warnings, exit 0
(Lean v4.34.0-rc2, project Mathlib pin; ~5 s), against the ported `work/lean/SM/FrontSmooth.lean` (v2) and
`work/lean/SM/FrontRecordBridge.lean` (accepted row ng:smoothing-record). Imports: `SM.FrontRecordBridge` only.
`#print axioms` (run on a copy in `/tmp/front_gamma/`, not in the deliverable):
`Marking.ofGeom`, `GeomMarking.ofMarking`, `isRounding_of_geomModel`, `isRounding_iff_geomModel`,
`GeomRounding.marking_nonempty_iff`, `GeomMarking.ofGeom_ofMarking`, `ofMarking_ofGeom`,
`recordIso_nonempty_of_geomModels` → `[propext, Classical.choice, Quot.sound]`;
`P_eq_of_geomModels` → `[propext, Classical.choice, Quot.sound, SM.lp_lm]` (`SM.lp_lm` only through `P`, exactly as
the accepted row's `IsRounding.P_eq`).
Accepted declarations changed: **none** (rule 2; D-F6). Nothing written under `work/lean`.

## 1. What the unit is for (D-F6)

Reviewers of ng:smoothing-record observed that `SmoothFront.Rounding S = ⟨G, geom, marking : F.Marking S⟩` has no
field tying the polygonal `S` to the rounded curves `G`: "S(F) has F's record" sits in the definition, and the
printed proof's content (sm-3:1851-1862) is kernel-checked only as lemmas about `G` versus `F`
(`GeomRounding.isDoubleOf_iff`, `occSetOf_eq`, `slopeOf_eq`, `crossSignOf_eq`). D-F6: extend the library by a
reading `GeomMarking G S` of `S` on the **rounded curves alone**, and prove that it is an `F.Marking S`. Done here.

## 2. Declarations (all in `namespace SM.SmoothFront`, inside `noncomputable section` / `open Classical`)

| § | declaration | content |
|---|---|---|
| 1 | `abbrev OccOf (G : Fin c → SmoothLoop) : Type := occSetOf G` | the occurrence type of a loop family (the subtype of `occSetOf G`), the analogue of `F.Occ := F.occSet` |
| 1 | `occOf_comp (F) : OccOf F.comp = F.Occ` | `rfl` |
| 1 | `OccOf.mem_Ico`, `OccOf.not_sameParam_of_ne`, `OccOf.isDoubleOf_of_ne` | analogues of `Occ.mem_Ico`, `Occ.isDouble_of_ne` |
| 1 | `Occ.not_sameParam_of_ne` | the front-side helper (two distinct occurrences are not the same parameter) |
| 2 | **`structure GeomMarking (G : Fin c → SmoothLoop) (S : Diagram)`** | fields `e`, `Φ`, `comp_eq`, `between_iff`, `pair_eq`, `over_iff`, `sgn_eq` — see §3 |
| 2 | `GeomMarking.c_eq`, `componentCount_eq`, `finite_occ`, `card_visit_eq`, `under_bit` | analogues of the accepted `Marking.c_eq`, `componentCount_eq`, `card_visit_eq`, `under_bit`; `finite_occ : (occSetOf G).Finite` |
| 2 | `GeomMarking.toMarkingComp (m : GeomMarking F.comp S) : F.Marking S`, `GeomMarking.ofComp (m : F.Marking S) : GeomMarking F.comp S` | **sanity**: on `G = F.comp` the two structures are the same field for field (each is the seven-tuple of the other's fields, accepted by the elaborator without any rewriting) |
| 3 | `GeomRounding.occEquiv (r : F.GeomRounding G) : OccOf G ≃ F.Occ := Equiv.setCongr r.occSetOf_eq` | the occurrences of the rounded curves are the occurrences of the front as the same parameters; `occEquiv_apply_val`, `occEquiv_symm_apply_val` (`(r.occEquiv p).1 = p.1`, `rfl`) |
| 3 | `GeomRounding.eval_eq_iff (r) (h : ¬ SameParam p q) : (G p.1).γ p.2 = (G q.1).γ q.2 ↔ F.eval p = F.eval q` | "creates no crossing" for parameters (from `isDoubleOf_iff`) |
| 3 | `GeomRounding.isDouble_of_occOf_ne (r) (hne : p ≠ q) (he) : F.IsDouble p.1 q.1` | a double point of `G` at two occurrences is a double point of `F` |
| 4 | **`Marking.ofGeom (r : F.GeomRounding G) (m : GeomMarking G S) : F.Marking S`** | **the D-F6 theorem** (a `def`: `Marking` is data) |
| 4 | `Marking.ofGeom_e`, `ofGeom_Φ` | `(ofGeom r m).e = m.e`, `(ofGeom r m).Φ p = m.Φ (r.occEquiv.symm p)`, `rfl` |
| 4 | **`GeomMarking.ofMarking (r : F.GeomRounding G) (m : F.Marking S) : GeomMarking G S`** | the converse |
| 4 | `GeomMarking.ofMarking_e`, `ofMarking_Φ`; `ofGeom_ofMarking : Marking.ofGeom r (ofMarking r m) = m`; `ofMarking_ofGeom : ofMarking r (Marking.ofGeom r m) = m` | the two transports are mutually inverse |
| 5 | `GeomRounding.marking_nonempty_iff (r) (S) : Nonempty (F.Marking S) ↔ Nonempty (GeomMarking G S)` | |
| 5 | `Rounding.geomMarking (ρ : F.Rounding S) : GeomMarking ρ.G S` | a rounding carries the record of its own rounded curves |
| 5 | **`isRounding_of_geomModel`**, **`isRounding_iff_geomModel`** | see §4 |
| 5 | `recordIso_nonempty_of_geomModels`, `P_eq_of_geomModels` | ng:smoothing-record in the geometric model |

## 3. `GeomMarking`, pasted, next to the accepted `Marking`

```lean
structure GeomMarking (G : Fin c → SmoothLoop) (S : Diagram) where
  e : Fin c ≃ Fin S.Γ.c
  Φ : OccOf G ≃ S.Γ.Visit
  comp_eq : ∀ p : OccOf G, S.compOf (Φ p) = e p.1.1
  between_iff : ∀ p q r : OccOf G, p.1.1 = q.1.1 → q.1.1 = r.1.1 →
    (cycBetween p.1.2 q.1.2 r.1.2 ↔
      cycBetween (S.visitCoord (Φ p)) (S.visitCoord (Φ q)) (S.visitCoord (Φ r)))
  pair_eq : ∀ p q : OccOf G, p ≠ q → (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2 → Φ q = S.twin (Φ p)
  over_iff : ∀ p q : OccOf G, p ≠ q → (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2 →
    (S.overBit (Φ p) = true ↔ slopeOf G p.1 < slopeOf G q.1)
  sgn_eq : ∀ p q : OccOf G, p ≠ q → (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2 →
    slopeOf G p.1 < slopeOf G q.1 → ((S.sign (Φ p).1 : ℤ)) = crossSignOf G p.1 q.1
```

Accepted `Marking (S : Diagram)` for `F : SmoothFront` (SM/FrontSmooth.lean ~1001), for comparison:
`e : Fin F.c ≃ Fin S.Γ.c`; `Φ : F.Occ ≃ S.Γ.Visit`; `comp_eq : ∀ p : F.Occ, S.compOf (Φ p) = e p.1.1`;
`between_iff` identical with `F.Occ`; `pair_eq : ∀ p q : F.Occ, p ≠ q → F.eval p = F.eval q → Φ q = S.twin (Φ p)`;
`over_iff : … → (S.overBit (Φ p) = true ↔ F.slope p.1 < F.slope q.1)`;
`sgn_eq : … → F.slope p.1 < F.slope q.1 → ((S.sign (Φ p).1 : ℤ)) = F.crossSign p.1 q.1`.

Substitutions, one per notion: `F.Occ` → `OccOf G` (= `↥(occSetOf G)`); `F.eval p = F.eval q` →
`(G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2`; `F.slope` → `slopeOf G`; `F.crossSign` → `crossSignOf G`. `F` does not
occur in the structure. On `G = F.comp` each right-hand side is the left one by `rfl` (`occSetOf_comp`,
`slopeOf_comp`, `crossSignOf_comp` of the accepted bridge; `F.eval p = (F.comp p.1).γ p.2` by definition), which is
what `toMarkingComp` / `ofComp` check.

## 4. The main statements, pasted

```lean
def Marking.ofGeom (r : F.GeomRounding G) (m : GeomMarking G S) : F.Marking S
  -- e := m.e ; Φ := r.occEquiv.symm.trans m.Φ

def GeomMarking.ofMarking (r : F.GeomRounding G) (m : F.Marking S) : GeomMarking G S
  -- e := m.e ; Φ := r.occEquiv.trans m.Φ

theorem isRounding_of_geomModel {F : SmoothFront} {G : Fin F.c → SmoothLoop}
    (geom : F.GeomRounding G) {S : Diagram} (h : Nonempty (GeomMarking G S)) : F.IsRounding S

theorem isRounding_iff_geomModel (F : SmoothFront) (S : Diagram) :
    F.IsRounding S ↔
      ∃ G : Fin F.c → SmoothLoop, Nonempty (F.GeomRounding G) ∧ Nonempty (GeomMarking G S)

theorem recordIso_nonempty_of_geomModels {F : SmoothFront} {G G' : Fin F.c → SmoothLoop}
    (geom : F.GeomRounding G) (geom' : F.GeomRounding G') {S S' : Diagram}
    (h : Nonempty (GeomMarking G S)) (h' : Nonempty (GeomMarking G' S')) :
    Nonempty (RecordIso S.record S'.record)

theorem P_eq_of_geomModels … : P S = P S'
```

Proof of `ofGeom`, field by field (this is the printed proof sm-3:1851-1862 made kernel-checked):
* `e := m.e` — "the component correspondence is the identity on the parameter circles" (the circles are shared, FR-4).
* `Φ := r.occEquiv.symm.trans m.Φ` where `occEquiv := Equiv.setCongr r.occSetOf_eq` — "changes no successor of an
  old crossing visit along the oriented parameter circle": the occurrence sets are equal *as sets of parameters*.
* `comp_eq`, `between_iff` — transported with **no rewriting**: `(r.occEquiv.symm p).1 = p.1` is `rfl`, so the
  accepted `m.comp_eq`, `m.between_iff` applied to the transported occurrences already have the required type
  (the cyclic order is `cycBetween` on the same parameters).
* `pair_eq` — "creates no crossing": `F.eval p = F.eval q` ↔ `(G p.1).γ p.2 = (G q.1).γ q.2` for distinct
  occurrences (`eval_eq_iff`, from the accepted `isDoubleOf_iff`; `¬ SameParam` from both lying in `[0,1)`).
* `over_iff`, `sgn_eq` — "determined by germs outside the cusp discs, which are unchanged": rewrite with the
  accepted `r.slopeOf_eq hd`, `r.slopeOf_eq hd.symm`, `r.crossSignOf_eq hd`, where `hd : F.IsDouble p.1 q.1` comes from
  the accepted `Occ.isDouble_of_ne`.
`ofMarking` is the mirror image (rewrites in the other direction; `hd` from `isDoubleOf_iff` + `OccOf.isDoubleOf_of_ne`).

## 5. Where the brief's shapes were adjusted, and why

1. **`ofGeom` / `ofMarking` are `def`s, not `theorem`s.** `Marking` and `GeomMarking` are `Type`-valued structures
   (they carry two `Equiv`s), so a term of `F.Marking S` is data. The Prop-level content is `isRounding_of_geomModel`
   / `isRounding_iff_geomModel` / `marking_nonempty_iff` (theorems). The two transports are proved mutually inverse
   (`ofGeom_ofMarking`, `ofMarking_ofGeom`), so no information is lost either way.
2. **Meeting is written as `(G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2`**, not through a new `evalOf`. The accepted bridge
   has no `evalOf`; `IsDoubleOf` and `occSetOf` use exactly this relation, and on `F.comp` it is `F.eval p = F.eval q`
   by `rfl`. Introducing a new name would only have added an unfolding step to every use.
3. **`Fintype` handling.** No finiteness is needed for the structure to typecheck: `Φ : OccOf G ≃ S.Γ.Visit` is a
   plain `Equiv` between types. Finiteness of `occSetOf G` is a *consequence* (`GeomMarking.finite_occ`, from the
   `Fintype S.Γ.Visit` instance through `Φ.symm`). Because `OccOf G` has no `Fintype` instance in general, the
   cardinality statement is `card_visit_eq : Nat.card S.Γ.Visit = Nat.card (OccOf G)` (`Nat.card` rather than the
   accepted `Marking.card_visit_eq`'s `Fintype.card`).
4. **Namespace.** `GeomMarking`, `OccOf` and the transports live in `SM.SmoothFront`, where the accepted G-side
   notions `IsDoubleOf`, `occSetOf`, `slopeOf`, `crossSignOf` already live (they were placed there by the accepted
   bridge although they do not mention a front). Full names: `SM.SmoothFront.GeomMarking`,
   `SM.SmoothFront.Marking.ofGeom`, `SM.SmoothFront.GeomMarking.ofMarking`, `SM.SmoothFront.isRounding_of_geomModel`,
   `SM.SmoothFront.isRounding_iff_geomModel`.
5. **Transport of `Φ`.** `Equiv.setCongr r.occSetOf_eq` (Mathlib, `subtypeEquivProp` under the hood); its forward and
   inverse maps are definitionally the identity on the underlying parameter, which is what lets `comp_eq` and
   `between_iff` transport by mere application. The bridge lemmas `slopeOf_eq` / `crossSignOf_eq` require
   `F.IsDouble p q` (not just membership in the occurrence sets); the hypotheses `p ≠ q` and the meeting relation of
   the `Marking` fields supply it via the accepted `Occ.isDouble_of_ne` (or `isDoubleOf_iff` on the `G` side).
6. **Extra corollaries beyond the brief:** `recordIso_nonempty_of_geomModels` (standard axioms) and
   `P_eq_of_geomModels` (carries `SM.lp_lm` through `P`, like the accepted row's `IsRounding.P_eq`) restate
   ng:smoothing-record for diagrams carrying the records of two roundings `G`, `G'`; `Rounding.geomMarking` gives
   every accepted rounding its geometric reading; `toMarkingComp` / `ofComp` witness "exactly as `Marking`".

## 6. Scratch

`/tmp/front_gamma/FrontGeomModel_axioms.lean`: the deliverable plus the `#print axioms` lines (output in the header
above). Nothing else created; nothing under `work/lean` touched.
