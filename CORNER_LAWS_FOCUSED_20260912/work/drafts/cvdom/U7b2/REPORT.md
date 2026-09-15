# U7b2 — REPORT (CV:lem:carrierword, row 137; CV:selector_A, row 164; on the accepted geo layer)

Written 2026-09-14 (≈03:51 UTC / 11:51pm ET) by the U7b2 prover subagent (claude-fable-5-1) of the pod executor, for
the CV-DOM decision work/drafts/cvdom/DECISION_FINAL.md (§0 option (C), §2 fidelity + the three documented
readings — reading (i) is this unit's brief —, §3 rulings R1–R5, §4 review-note template, §5 units U7b/U7b2,
§6 order of rows steps 2–3). Paths relative to the package root
/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912. Nothing under
work/lean was written; both drafts were checked with `cd work/lean && lake env lean <file>` only.

## 0. Deliverables and status

| item | row 137 CV:lem:carrierword | row 164 CV:selector_A |
|---|---|---|
| file | `work/drafts/cvdom/U7b2/CVCarrierWord.lean` — **349 lines** (≈105 module docstring; the 4 trailing `#print axioms` lines are removed at porting); intended home `work/lean/CV/CarrierWord.lean` | `work/drafts/cvdom/U7b2/CVSelectorA.lean` — **182 lines** (≈75 module docstring; 4 trailing `#print axioms` lines removed at porting); intended home `work/lean/CV/SelectorA.lean` |
| imports | `CV.CarriersLemma` (U7b, landed; through it `CV.Carriers`, `CV.CarrierBridges`, `SM.FlatCarriers`, `SM.GeoCarrierOrder` (U1b), `SM.GeoCarrierCount` (U1a), `SM.GeoCarrierCrossings`/`Noncrossing` (U2a)). Used from U7b: `CV.geoIndependent_of_mem_Ind` only | `CV.Carriers` (U7a, landed: `CarrierGeometry.ofCV`/`ofDiagrammatic` via `CV.CarrierBridges`), `SM.GeoCornerPolygon` (U2b, landed: `three_le_geoCornerCount`) |
| check | `cd work/lean && lake env lean ../drafts/cvdom/U7b2/CVCarrierWord.lean` → **exit 0**, no errors, no warnings (5.7 s) | `cd work/lean && lake env lean ../drafts/cvdom/U7b2/CVSelectorA.lean` → **exit 0**, no errors, no warnings (5.8 s) |
| sorries | **none** (`grep -c sorry` = 0) | **none** (`grep -c sorry` = 0) |
| bundle | `structure CV.CarrierWordData (hD : Diagrammatic P) (S) (_hS : S ∈ Ind hD.crossingGeometry) : Prop` — 3 fields (one per printed sentence + the refinement clause of reading (i)) | `structure CV.SelectorAData (hG : Generic P) : Prop` — 1 field (clause (A) is one sentence) |
| row theorem PROVED | `CV.carrierword hD S hS : CarrierWordData hD S hS` | `CV.selector_A hG : SelectorAData hG` |
| axioms | `[propext, Classical.choice, Quot.sound]` for `CV.carrierword`, `CV.carrierword_generic`, `CV.carrierGaussList_eq_filter`, `CV.visits_geoMarkList_eq_gaussList` | `[propext, Classical.choice, Quot.sound]` for `CV.selector_A`, `CV.selector_A_three_le`, `CV.three_le_cornerCount_of_diagrammatic`, `CV.three_corner_marks` |
| binder | `hD : CV.Diagrammatic P`, `hS : S ∈ CV.Ind hD.crossingGeometry` (DECISION_FINAL §2 fidelity list); **no `hn`** on any declaration of the row (ruling R5: every geo lemma consumed is `hn`-free) | `hG : CV.Generic P` ("under the guards of def:generic(A)"); `S`, `hS`, `q` quantified inside the field ("every carrier of every support"); `hn : 3 ≤ n` quantified locally in the field (`∀ (_hn : 3 ≤ n), …`, U7a's / `CV.InterlaceData.vertices`' pattern) because `three_le_geoCornerCount` consumes it |
| tier | tier 0 throughout (`hD.crossingGeometry` only) | tier 1 through `CarrierGeometry.ofCV hG` (the lane proves (A) at `SM.CarrierGeometry`, ruling R4); the two `CrossingGeometry P` proofs are identified by proof irrelevance (no `recast`) |
| accepted declarations modified / `geo*` names re-declared | none (ruling R3; the two helper names that started with `geo` were renamed `visits_geoMarkList_eq_gaussList`, `markList_eq_filter_geoMarkList`; every new name checked against work/lean: 0 prior declarations) | none |
| new names (namespace `CV`) | `carrierGaussList` (def), `mem_carrierGaussList`, `carrierGaussList_nodup`, `visits_geoMarkList_eq_gaussList`, `carrierGaussList_eq_filter`, `markList_eq_filter_geoMarkList`; `carrierword_inherits_order`, `carrierword_next`, `carrierword_traced`, `carrierword_refines`, `carrierword_markList_of_subset`, `carrierword_refinement`, `carrierword_insert`; `CarrierWordData`, `carrierword` (row), `carrierword_generic` | `selector_A_three_le`, `three_le_cornerCount_of_diagrammatic`, `cornerCount_eq_length_filter`, `three_corner_marks`; `SelectorAData`, `selector_A` (row) |

Neither row is in the checker's fixed-name list (`axiom-policy.json` targets); the names `CV.carrierword` /
`CV.selector_A` are the ones the unit brief fixes. lean-declarations.json rows: `CV:lem:carrierword` (source
d1_setup.tex:450) and `CV:selector_A` (labels `lem:selectorid(A)`, source d6_vertexedge.tex:1017), both `pending`.

## 1. Row 137 — CV:lem:carrierword

### 1.1 The printed statement and reading (i)

d1_setup.tex:450–456: "Let C be a closed curve with a traversal circle Γ_C and finitely many transverse double
points, and let S be a set of them no two of which interlace. Then each closed curve produced by smoothing C
along S traverses the marked points of Γ_C lying on it in the cyclic order they have on Γ_C. / In particular,
taking C = P generic and S ∈ Ind(G_P), each carrier of S traverses the marked points lying on it in the order
induced from Γ."

Reading (i), quoted verbatim in the module docstring from DECISION_FINAL §2: "(i) lem:carrierword's printed
generality over "a closed curve C with finitely many transverse double points" is realised on the carriers of a
diagrammatic polygon P and its refinement clause (S ⊆ S′ both independent ⇒ every carrier of S′ lies in one
carrier of S with the induced order) — the only instances the CV text consumes (lem:piececurve Step 5 applies it
to daughter carriers)". The proof text (457–486, induction on |S| through curves "which are not polygons") is
read for conventions only and not rendered; its closing paragraph explains why the statement is printed at that
generality, which reading (i) resolves.

### 1.2 Clause → field map and proof sources (write `hP := hD.crossingGeometry`, `ρ_S := geoSmoothingSuccessor hP S`)

| printed sentence | field of `CarrierWordData` | rendering | proved from |
|---|---|---|---|
| 1 (450–454) "each closed curve produced by smoothing C along S traverses the marked points of Γ_C lying on it in the cyclic order they have on Γ_C", realised on the carriers of P | `smoothing_preserves_order` | (a) the marked points of Γ lying on the carrier L, in the cyclic order of Γ: `geoComponentCycle hP S L = (geoMarkCycle hP).filter (owner = L)`; (b) L traverses them in that order: `GeoInheritsMarkOrder hP S` = ∀ L, ∀ a ∈ that cycle, `cycle.next a = ρ_S a` | (a) `rfl` (definition of U1a's `geoComponentCycle`, the port of the accepted `componentCycle`; the same field shape as the accepted SM `CarriersLemmaData.component_cycle`); (b) `SM.GeoCarrier.geoInheritsMarkOrder_of_independent` (U1a, `hn`-free; the same shape as the accepted SM `CarriersLemmaData.inherited_order`) via `CV.geoIndependent_of_mem_Ind` (ruling R2) — wrapped as `CV.carrierword_inherits_order` / `carrierword_next` |
| 2 (455–456) "In particular, taking C = P generic and S ∈ Ind(G_P), each carrier of S traverses the marked points lying on it in the order induced from Γ" | `carrier_word` | for every carrier L: (a) its traversal word `geoComponentMarkList hP S L` (its marks in the order induced from Γ = `(geoMarkList hP).filter (owner = L)`, accepted def:flat-carriers) is traced by ρ_S entry by entry, cyclically (`TracedSuccessor hP S L`, SM/FlatCarriers.lean:3147); (b) its **Gauss word** `carrierGaussList hP S L` (the visits it traverses in traversal order = the visit part of the traversal word) is **P's Gauss word restricted to the visits on L**: `= (geometricGaussList hP).filter (fun v => owner (inr v) = L)` | (a) `SM.GeoCarrier.geoComponentMarkList_getElem_successor` (U1b, the `hn`-free body of the §5 target `geoTracedSuccessor_of_independent`) — `CV.carrierword_traced`; (b) NEW `CV.carrierGaussList_eq_filter` (§1.3) |
| reading (i), refinement clause "S ⊆ S′ both independent ⇒ every carrier of S′ lies in one carrier of S with the induced order" (the instance of sentence 1 that lem:piececurve Step 5, d1:650–652, applies to the single smoothed chord) | `refinement` | ∀ S′ ∈ Ind(G_P), S ⊆ S′, ∀ carrier L′ of S′, ∃ carrier L of S: (a) every mark of L′ is a mark of L (`owner_{S′} m = L′ → owner_S m = L`); (b) the induced order: the traversal word of L′ is that of L restricted to L′'s marks (`geoComponentMarkList hP S′ L′ = (geoComponentMarkList hP S L).filter (owner_{S′} = L′)`); (c) L′ traverses it (`TracedSuccessor hP S′ L′`) | (a) `SM.GeoCarrier.geoOwner_refines` (U1a, "lem:carrierword clause 3 on the geometric carrier layer", from `geoOwner_eq_of_subset`) — `CV.carrierword_refines`; (b) NEW `CV.carrierword_markList_of_subset`: both words are filters of `geoMarkList`, `List.filter_filter` + `List.filter_congr` with (a); (c) sentence 2 (a) at S′ — assembled in `CV.carrierword_refinement`; the single-chord instance is `CV.carrierword_insert (d) (hd : insert d S ∈ Ind hP)` |

The row theorem `CV.carrierword hD S hS` fills the three fields with `⟨fun _ => rfl, carrierword_inherits_order⟩`,
`⟨carrierword_traced, carrierGaussList_eq_filter⟩`, `carrierword_refinement`. The printed instance "C = P generic"
is the companion `CV.carrierword_generic (hn) (hG : Generic P) (S) (hS) : CarrierWordData (hG.diagrammatic hn) S hS`
(`hn` only to pass from `Generic` to `Diagrammatic` through the accepted `CV.Generic.diagrammatic`; `hS : S ∈ Ind
hG.crossingGeometry` is accepted at the type `Ind (hG.diagrammatic hn).crossingGeometry` by proof irrelevance).

### 1.3 The new Gauss-word lemma (≈ 60 lines)

* `CV.carrierGaussList hP S L := (geoComponentMarkList hP S L).filterMap Sum.getRight?` — the crossing visits of
  the carrier's traversal word, vertices dropped (a list = the word cut at P's vertex 0; its rotation class is
  the cyclic word). `mem_carrierGaussList`: `v ∈ … ↔ owner (inr v) = L`; `carrierGaussList_nodup`.
* `CV.visits_geoMarkList_eq_gaussList : (geoMarkList hP).filterMap Sum.getRight? = geometricGaussList hP` — P's
  Gauss word (the accepted `geometricGaussList`, SM/GeometricVisits.lean:51, = the accepted `gaussList` on
  SM-generic P) is the visit part of the marked traversal circle. Proof: `List.Perm.eq_of_pairwise` with
  `le := geometricVisitKey ≤` (antisymmetric by `geometricVisitKey_injective`), exactly the argument of the
  accepted `geoMarkList_eq_generic` (FlatCarriersDefs.lean:644): the left side is sorted by
  `List.Pairwise.filterMap` from `geoMarkList_sorted` (`geoMarkKey hP (inr v) = geometricVisitKey hP v` is
  `rfl`), the right side by `Finset.pairwise_sort` under `geometricVisitLinearOrder`; both are nodup
  (`List.Nodup.filterMap` with `Sum.getRight?_eq_some_iff`) with the same members (`List.perm_ext_iff_of_nodup`).
* `CV.carrierGaussList_eq_filter`: `carrierGaussList hP S L = (geometricGaussList hP).filter (owner (inr ·) = L)`
  — rewrite the right side through `visits_geoMarkList_eq_gaussList`, then `List.filterMap_filter` and
  `List.filter_filterMap` turn both sides into a `filterMap` over `geoMarkList` with pointwise-equal functions
  (case split on the mark: a vertex contributes nothing either way; a visit is kept iff its owner is L).

### 1.4 Readings the reviewer should confirm (none is a scope change)

1. **"marked points of Γ_C"** are, in CV, the 2m double-point preimages (the visits). The finite model's marks
   also include the original vertices (`Mark P = ZMod n ⊕ Visit P`); sentence 1 is rendered on ALL marks
   (`GeoInheritsMarkOrder`, stronger), and sentence 2's Gauss-word conjunct restates it on the visits alone.
2. **"in the cyclic order they have on Γ_C"** = the restriction of the marked traversal circle `geoMarkCycle hP`
   (marks sorted along Γ by `geoMarkKey`, a rotation class) to the marks of the carrier; "traverses … in that
   order" = `ρ_S` at a mark of L is the cycle's `next` (`Cycle.next`), equivalently the `formPerm` of the
   restricted cycle agrees with `ρ_S` on L's marks (`geoInheritsMarkOrder_iff_formPerm`).
3. **"the order induced from Γ"** as a word: `geoMarkList hP` is Γ cut at the vertex 0 of P; a carrier's traversal
   word is its filter. `TracedSuccessor` says the closed traversal of L visits the entries of that word in order
   and returns to the first — so the word read along L IS the restriction of P's word.
4. **"In particular, taking C = P generic"**: the row is stated at `hD : Diagrammatic P` (the CV-DOM binder,
   DECISION_FINAL §2 fidelity list — the general sentence holds on any closed curve with transverse double
   points, which every diagrammatic polygon is); the generic instance is `carrierword_generic`. No clause of
   the row uses the (G1) guard.
5. **Refinement clause**: "lies in one carrier of S" = ownership implication (a); "with the induced order" =
   the word of the daughter is the word of the mother restricted (b), traversed by the daughter (c). The
   induction step of the printed proof (one crossing at a time) is the instance `carrierword_insert`.
6. **Ownership convention** at a selected visit (which of the two visits of `c ∈ S` lies on which carrier) is
   SM conv:selected-visits (`selectedMarkPerm`, a mark keeps its own cycle) — cited in the docstrings; the CV
   text leaves it implicit. It affects sentence 1 only through which marks are "on" L.

### 1.5 Not rendered (deliberately)

The proof (457–486): the induction on |S| through non-polygonal curves, the arcs Γ₁, Γ₂ of the first smoothed
chord. Its content on P's carriers is exactly the refinement clause at `S′ = insert c S`, which IS rendered.
The paragraph on why the statement is printed at curve generality (483–486) is what reading (i) resolves.

## 2. Row 164 — CV:selector_A (lem:selectorid (A))

### 2.1 The printed clause

d6_vertexedge.tex:1017–1020: "(A) Under the guards of Definition def:generic(A), every carrier of every support
has at least three corners." Clause (B) (1021–1040: the selector identities `W_T = −s_low W₁W₂` at ε = 1 and
`W_T W₁ W₂ = 0` at ε = 0 for an eligible T, and the uniformity transfer) is a different row and is not
rendered here. The unit brief's paraphrase "wind(S) = (−1)^{ℓ(P)+|S|} when every carrier is uniform" is NOT a
sentence of clause (A) either (it is SM lem:C-X1's proof content, the accepted `SM.wind_eq_of_uniform` /
`SM.C_X1`, and on the CV side belongs to R:generic_selector, row 172, which consumes def:wind + selector_A);
per the brief's "read the exact printed clause (A) and render exactly it", the bundle renders (A) alone.

### 2.2 Clause → field map and proof source (`hP := hG.crossingGeometry`)

| printed clause | field of `SelectorAData` | rendering | proved from |
|---|---|---|---|
| (A) "Under the guards of Definition def:generic(A), every carrier of every support has at least three corners" | `three_corners` | binder `hG : Generic P` (def:generic (A) = the accepted `CV.Generic`: every relevant member of 𝓖 nonzero); `∀ (_hn : 3 ≤ n) (S) (hS : S ∈ Ind hP) (q : GeoComponent hP S), 3 ≤ geoCornerCount hP S q` — "corners" and `c(L) = geoCornerCount` are def:wind's (row 138, `WindDefinitionData.corner_iff`/`corner_count`: the marks of L that are original vertices or smoothing sites of S) | `SM.GeoCarrier.three_le_geoCornerCount hn (CarrierGeometry.ofCV hG) hS' q` (U2b, SM/GeoCornerPolygon.lean §5: one segment cannot close, two nonzero segments closing are antiparallel — `geoCornerPolygon_edge_ne_zero_of_independent`, `geoCornerPolygon_not_antiparallel`), `hS'` by ruling R2 — wrapped as `CV.selector_A_three_le (hn) (hG) (hS) (q)`, the §5-printed shape |

Companions outside the bundle: `CV.three_le_cornerCount_of_diagrammatic (hn) (hD : Diagrammatic P) (hS) (q)`
(the lane's strengthening: (A) needs only tier 1, not the (G1) guard — offered for the reviewer's information,
NOT the row); `CV.cornerCount_eq_length_filter` (what `c(L)` counts, `rfl`); `CV.three_corner_marks` ("at
least three corners" as three pairwise distinct corner marks `geoCornerMark L 0, 1, 2` of L, each an owned
original vertex or selected visit — via `geoCornerMark_injective`, `geoCornerMark_mem`, `ZMod.val_cast_of_lt`).

### 2.3 Readings the reviewer should confirm (none is a scope change)

1. **"the guards of Definition def:generic(A)"** = `CV.Generic P` (d1:222–229), the accepted CV:def:generic.
2. **"every support"** = every `S ∈ Ind(G_P)` (the supports of def:X1's state sum, d1:908–930); **"every
   carrier"** = every cycle of ρ_S (CV:def:smoothing, row 135).
3. **"corners"** = def:wind's corners (d1:489–492): original vertices and smoothing sites of S traversed by
   the carrier; their number is `geoCornerCount` = the number of vertices of the corner polygon
   `geoCornerPolygon` whose turns are the carrier's turns (U7a's `WindDefinitionData`).
4. **`n ≥ 3`** is quantified locally in the field (CV def:polygon's standing "Let n ≥ 3", d1:9), as in U7a's
   `WindDefinitionData` and the accepted `CV.InterlaceData.vertices`; the row theorem itself takes only `hG`.
   The geo lemma genuinely consumes it (`geoMarkSuccessor_position_cases hn` inside the edge lemmas).
5. The proof goes through tier 1 (`CarrierGeometry.ofCV hG`, U0), so the (G1) guard is unused; the printed
   binder is nevertheless kept (fidelity: same domain as printed; the strengthening is a companion theorem).

## 3. The bundles (from the compiled files)

### 3.1 `CVCarrierWord.lean` lines 287–337

```lean
structure CarrierWordData (_hS : S ∈ Ind hD.crossingGeometry) : Prop where
  /-- "Let `C` be a closed curve with a traversal circle `Γ_C` and finitely many transverse double
  points, and let `S` be a set of them no two of which interlace. Then each closed curve produced by
  smoothing `C` along `S` traverses the marked points of `Γ_C` lying on it in the cyclic order they
  have on `Γ_C`" — realised on the carriers of `P` (reading (i)): the marked points of `Γ` lying on a
  carrier `L`, in the cyclic order they have on `Γ`, form the cycle `(geoMarkCycle hP).filter
  (owner = L)` (= `geoComponentCycle hP S L`), and `L` traverses them in that order: at every mark `a`
  of `L`, the next mark along `L` (`ρ_S a`) is the next mark of `L` in that cycle
  (`GeoInheritsMarkOrder`) -/
  smoothing_preserves_order :
    (∀ q : GeoComponent hD.crossingGeometry S,
      geoComponentCycle hD.crossingGeometry S q =
        (geoMarkCycle hD.crossingGeometry).filter
          (fun m => decide (geoOwner hD.crossingGeometry S m = q))) ∧
    GeoInheritsMarkOrder hD.crossingGeometry S
  /-- "In particular, taking `C = P` generic and `S ∈ Ind(G_P)`, each carrier of `S` traverses the
  marked points lying on it in the order induced from `Γ`": the traversal word of a carrier `L` —
  its marks in the order induced from `Γ`, `geoComponentMarkList hP S L = (geoMarkList hP).filter
  (owner = L)` — is traced by `ρ_S` entry by entry (`TracedSuccessor`), and its Gauss word (the
  visits it traverses, in traversal order) is `P`'s Gauss word `geometricGaussList hP` restricted to
  the visits lying on `L` -/
  carrier_word : ∀ q : GeoComponent hD.crossingGeometry S,
    TracedSuccessor hD.crossingGeometry S q ∧
    carrierGaussList hD.crossingGeometry S q =
      (geometricGaussList hD.crossingGeometry).filter
        (fun v => decide (geoOwner hD.crossingGeometry S (Sum.inr v) = q))
  /-- Reading (i), the refinement clause: "`S ⊆ S'` both independent ⇒ every carrier of `S'` lies in
  one carrier of `S` with the induced order" — for `S ⊆ S'`, `S' ∈ Ind(G_P)`, every carrier `L'` of
  `S'` has a carrier `L` of `S` containing all its marks; the traversal word of `L'` is that of `L`
  restricted to the marks of `L'` (the induced order), and `L'` traverses it (`TracedSuccessor` at
  `S'`) — the instance lem:piececurve Step 5 applies to the single smoothed chord -/
  refinement : ∀ S' : Finset (Crossing P), S' ∈ Ind hD.crossingGeometry → S ⊆ S' →
    ∀ q' : GeoComponent hD.crossingGeometry S', ∃ q : GeoComponent hD.crossingGeometry S,
      (∀ m : Mark P, geoOwner hD.crossingGeometry S' m = q' → geoOwner hD.crossingGeometry S m = q) ∧
      geoComponentMarkList hD.crossingGeometry S' q' =
        (geoComponentMarkList hD.crossingGeometry S q).filter
          (fun m => decide (geoOwner hD.crossingGeometry S' m = q')) ∧
      TracedSuccessor hD.crossingGeometry S' q'

/-- **Row 137, CV:lem:carrierword**, on the printed binder `hD : Diagrammatic P`, `S ∈ Ind(G_P)`. -/
theorem carrierword (hS : S ∈ Ind hD.crossingGeometry) : CarrierWordData hD S hS where
  smoothing_preserves_order :=
    ⟨fun _ => rfl, carrierword_inherits_order hD.crossingGeometry hS⟩
  carrier_word q :=
    ⟨carrierword_traced hD.crossingGeometry hS q, carrierGaussList_eq_filter hD.crossingGeometry S q⟩
  refinement _ hS' hSS' q' := carrierword_refinement hD.crossingGeometry hS' hSS' q'
```

(`variable (hD : Diagrammatic P) (S : Finset (Crossing P))` in scope.)

### 3.2 `CVSelectorA.lean` lines 164–172

```lean
structure SelectorAData : Prop where
  /-- "(A) Under the guards of Definition def:generic(A), every carrier of every support has at least
  three corners": for every support `S ∈ Ind(G_P)` and every carrier `L` of `S`, `3 ≤ c(L)` -/
  three_corners : ∀ (_hn : 3 ≤ n) (S : Finset (Crossing P)), S ∈ Ind hG.crossingGeometry →
    ∀ q : GeoComponent hG.crossingGeometry S, 3 ≤ geoCornerCount hG.crossingGeometry S q

/-- **Row 164, CV:selector_A** (lem:selectorid (A)), on the printed binder `hG : Generic P`. -/
theorem selector_A : SelectorAData hG where
  three_corners hn _ hS q := selector_A_three_le hn hG hS q
```

(`variable (hG : Generic P)` in scope.)

## 4. Axioms (from `lake env lean`)

```
'CV.carrierword' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.carrierword_generic' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.carrierGaussList_eq_filter' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.visits_geoMarkList_eq_gaussList' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.selector_A' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.selector_A_three_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.three_le_cornerCount_of_diagrammatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.three_corner_marks' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 5. Porting notes for the assembler

* Add only the standard "Ported 2026-09-14 from work/drafts/cvdom/U7b2/…" header and drop the four
  `#print axioms` lines at the end of each file; no other edit. Both files import only landed modules.
* Row 137 depends on rows 135/136/139 modules (`CV.Carriers`, `CV.CarriersLemma`) and the lane modules
  U1a/U1b; row 164 on `CV.Carriers` and U2b. lean-declarations.json: `CV:lem:carrierword` → declaration
  `CV.carrierword`, module `CV.CarrierWord`; `CV:selector_A` → `CV.selector_A`, module `CV.SelectorA`.
* Downstream consumers: lem:piececurve (row 143, U7c) Steps 3 and 5 use `carrierGaussList_eq_filter` and
  `carrierword_insert`/`carrierword_refinement`; def:X1 (146) / U4's `geoCarrierPolyComp` use
  `selector_A_three_le` (or the lane's `three_le_geoCornerCount` directly); R:generic_table (171) and
  R:generic_selector (172) consume the two rows on CV events.
