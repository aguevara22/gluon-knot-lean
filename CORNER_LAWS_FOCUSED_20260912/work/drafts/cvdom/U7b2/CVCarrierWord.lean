import CV.CarriersLemma

/-! # CV/CarrierWord.lean — CV:lem:carrierword (137) on the accepted geometric carrier layer
(CV-DOM unit U7b2)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor, for the CV-DOM decision
(work/drafts/cvdom/DECISION_FINAL.md §0 option (C), §2 fidelity + the three documented readings,
§3 rulings R1–R5, §4 review-note template, §5 units U7b/U7b2, §6 order of rows step 2). Draft home
work/drafts/cvdom/U7b2/CVCarrierWord.lean; intended home work/lean/CV/CarrierWord.lean (after
CV/CarriersLemma.lean, row 136, whose `geoIndependent_of_mem_Ind` this module reuses). Source:
reference/R/CV/d1_setup.tex (frozen) 450–456 (the statement) and 457–486 (its proof, read for the
conventions only); the consumer lem:piececurve Steps 3 and 5 (d1:627–633, 640–662).

Row declaration: `CV.carrierword hD S hS : CV.CarrierWordData hD S hS` (137, a PROVE row). Each field
of `CarrierWordData` renders one printed sentence and quotes it.

## Printed statement (d1_setup.tex:450–456)

"Let `C` be a closed curve with a traversal circle `Γ_C` and finitely many transverse double points,
and let `S` be a set of them no two of which interlace. Then each closed curve produced by
smoothing `C` along `S` traverses the marked points of `Γ_C` lying on it in the cyclic order they
have on `Γ_C`.

In particular, taking `C = P` generic and `S ∈ Ind(G_P)`, each carrier of `S` traverses the marked
points lying on it in the order induced from `Γ`."

## Reading (i) of DECISION_FINAL §2 (quoted verbatim; this module realises it)

"(i) lem:carrierword's printed generality over "a closed curve C with finitely many transverse
double points" is realised on the carriers of a diagrammatic polygon P and its refinement clause
(S ⊆ S′ both independent ⇒ every carrier of S′ lies in one carrier of S with the induced order) —
the only instances the CV text consumes (lem:piececurve Step 5 applies it to daughter carriers)".

So the three clauses rendered are: (1) the general sentence, on the carriers of `P`; (2) the
"In particular" sentence — the Gauss word of a carrier is the restriction of `P`'s traversal word
to the carrier's marks in the inherited cyclic order; (3) the refinement clause — for
`S ⊆ S'` both in `Ind(G_P)` every carrier of `S'` lies in one carrier of `S` with the induced order
(lem:piececurve Step 5: "the retained visits keep their cyclic order by Lemma lem:carrierword applied
to the single smoothed chord", `S' = insert d S`).

## Binder (as printed; DECISION_FINAL §2 "Fidelity", no domain change)

`hD : CV.Diagrammatic P` — the CV-DOM binder of lem:carrierword (d1:450–456; the printed
generality over any closed curve with transverse double points covers every diagrammatic polygon,
and "in particular P generic" is its instance `CV.carrierword_generic` below) — and
`hS : S ∈ CV.Ind hD.crossingGeometry` (the accepted CV:def:interlace; ruling R2:
`CV.mem_Ind_iff_geoIndependent`). No `hn : 3 ≤ n` anywhere (ruling R5): none of the geo lemmas
consumed here takes it (`geoInheritsMarkOrder_of_independent`, `geoComponentMarkList_getElem_successor`,
`geoOwner_refines`, `geoOwner_eq_of_subset` are `hn`-free; the §5 target
`geoTracedSuccessor_of_independent hn` carries an unused `hn`, and its `hn`-free body is used).

## Review note (DECISION_FINAL §4, filled in)

Stated on the printed binder (`hD : CV.Diagrammatic P`, `S ∈ Ind(G_P)`); no domain change (CV-DOM
decision, AUTHOR_NOTES 2026-09-14). The carriers and their marks are the accepted `SM.GeoCarrier`
objects (def:flat-carriers, SM/FlatCarriersDefs.lean) read through `hD.crossingGeometry`;
`Ind(G_P)` is the accepted `CV.Ind` (CV:def:interlace). On SM-generic polygons these are the
accepted def:smoothing / lem:carriers objects by `geoSmoothingSuccessor_eq_generic`,
`geoComponentEquivGeneric`, `geoComponentCornerList_eq_generic` (FlatCarriersDefs.lean:638–724).
The ownership of the two visits of a selected crossing follows SM conv:selected-visits (the same
`selectedMarkPerm`), a disambiguation the CV text leaves implicit. The printed generality over an
arbitrary closed curve `C` is realised on the carriers of `P` (clauses 1–2) and on daughter
carriers via the refinement clause (clause 3); these are the only instances the CV text consumes
(lem:piececurve Step 5). The reviewer checks: same binder as printed, same quantifiers, each
printed sentence = one bundle field, and that the `geo*` object named in each field is the one the
sentence describes.

## Printed notions → Lean (write `hP := hD.crossingGeometry`)

* the traversal circle `Γ` (= `Γ_C` at `C = P`) with its marked points: the marked traversal circle
  `geoMarkCycle hP : Cycle (Mark P)` — the marks `Mark P = ZMod n ⊕ Visit P` (original vertices and
  crossing visits) in the cyclic order of their positions `geoMarkPosition hP` on `Γ`
  (`geoMarkList hP` is this order cut at the vertex `0`, sorted by `geoMarkKey`); CV's "marked
  points" proper — the `2m` double-point preimages — are the visits, listed in that order by
  `geometricGaussList hP` (P's Gauss word, CV:ax:gausscode's datum), the visit part of `geoMarkList`
  (`visits_geoMarkList_eq_gaussList` below).
* "smoothing `C` along `S`", "each closed curve produced" = "each carrier of `S`": CV:def:smoothing
  (row 135) — the cycles `GeoComponent hP S` of `ρ_S = geoSmoothingSuccessor hP S`; "the marked points
  lying on it": the marks `m` with `geoOwner hP S m = L`.
* "traverses … in the cyclic order they have on `Γ_C`": walking the carrier is iterating `ρ_S`; the
  cyclic order its marks have on `Γ` is the restriction `geoComponentCycle hP S L =
  (geoMarkCycle hP).filter (owner = L)`; the sentence says that `ρ_S` at a mark of `L` is the *next*
  mark of `L` in that restricted cycle — the accepted-lane invariant `GeoInheritsMarkOrder hP S`
  (U1a, SM/GeoCarrierCount.lean, the port of SM lem:carriers' `InheritsMarkOrder`).
* "the order induced from `Γ`" as a word: the traversal word of a carrier is its mark list
  `geoComponentMarkList hP S L = (geoMarkList hP).filter (owner = L)` (accepted, def:flat-carriers);
  "traverses … in that order" is `TracedSuccessor hP S L` (SM/FlatCarriers.lean:3147): `ρ_S` of the
  `i`-th entry is the `(i+1)`-th, cyclically. Its Gauss word (visits only) is `carrierGaussList hP S L`
  (defined here), and clause 2 says it is `P`'s Gauss word restricted to the visits on `L`.
* "no two of which interlace": `S ∈ Ind hP` (accepted CV:def:interlace, = `GeoIndependent hP S`).

## Proof sources (all tier 0, `hP : CrossingGeometry P`)

(1) `SM.GeoCarrier.geoInheritsMarkOrder_of_independent` (U1a) and the definition
`geoComponentCycle` (rfl); (2) `geoComponentMarkList_getElem_successor` (U1b, SM/GeoCarrierOrder.lean)
and NEW here `carrierGaussList_eq_filter` (the visit part of a filtered sorted list is the filtered
visit part: `List.filterMap_filter`, `List.filter_filterMap`, and `visits_geoMarkList_eq_gaussList`,
proved by `List.Perm.eq_of_pairwise` as `geoMarkList_eq_generic` is); (3)
`geoOwner_refines` / `geoOwner_eq_of_subset` (U1a) for the containment, `List.filter_filter` for the
induced order, and (1)–(2) at `S'` for its traversal.

Checked with `cd work/lean && lake env lean ../drafts/cvdom/U7b2/CVCarrierWord.lean`. -/

namespace CV

open SM SM.Carrier SM.GeoCarrier

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-! ## 1. The traversal word and the Gauss word of a carrier -/

section Word

variable (hP : CrossingGeometry P) (S : Finset (Crossing P))

/-- The **Gauss word of a carrier** `L`: the crossing visits it traverses, in the order of its
traversal — the visit part of its traversal word `geoComponentMarkList hP S L` (the carrier's marks
in the cyclic order inherited from `Γ`, cut at the vertex `0` of `P`), the original vertices dropped.
(A list, i.e. the word cut at one point; its rotation class is the cyclic word.) -/
noncomputable def carrierGaussList (q : GeoComponent hP S) : List (Visit P) :=
  (geoComponentMarkList hP S q).filterMap Sum.getRight?

theorem mem_carrierGaussList (q : GeoComponent hP S) (v : Visit P) :
    v ∈ carrierGaussList hP S q ↔ geoOwner hP S (Sum.inr v) = q := by
  simp only [carrierGaussList, List.mem_filterMap, Sum.getRight?_eq_some_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_geoComponentMarkList hP S q _).mp ha
  · intro h
    exact ⟨Sum.inr v, (mem_geoComponentMarkList hP S q _).mpr h, rfl⟩

theorem carrierGaussList_nodup (q : GeoComponent hP S) : (carrierGaussList hP S q).Nodup := by
  refine List.Nodup.filterMap ?_ (geoComponentMarkList_nodup hP S q)
  intro a a' b hb hb'
  rw [Option.mem_def, Sum.getRight?_eq_some_iff] at hb hb'
  rw [hb, hb']

/-- `P`'s Gauss word (the accepted `geometricGaussList hP`: all visits sorted along `Γ`) is the visit
part of the marked traversal circle `geoMarkList hP` (all marks sorted along `Γ`): both are sorted by
the traversal coordinate, both list every visit once (`List.Perm.eq_of_pairwise`, the argument of the
accepted `geoMarkList_eq_generic`). -/
theorem visits_geoMarkList_eq_gaussList :
    (geoMarkList hP).filterMap Sum.getRight? = geometricGaussList hP := by
  apply List.Perm.eq_of_pairwise
    (le := fun v w : Visit P => geometricVisitKey hP v ≤ geometricVisitKey hP w)
  · intro a b _ _ hab hba
    exact geometricVisitKey_injective hP (le_antisymm hab hba)
  · refine List.Pairwise.filterMap Sum.getRight? ?_ (geoMarkList_sorted hP)
    intro a a' h b hb b' hb'
    rw [Sum.getRight?_eq_some_iff] at hb hb'
    subst hb
    subst hb'
    exact h
  · classical
    let _ := geometricVisitLinearOrder hP
    exact Finset.pairwise_sort _ _
  · refine (List.perm_ext_iff_of_nodup ?_ (geometricGaussList_nodup hP)).mpr ?_
    · refine List.Nodup.filterMap ?_ (geoMarkList_nodup hP)
      intro a a' b hb hb'
      rw [Option.mem_def, Sum.getRight?_eq_some_iff] at hb hb'
      rw [hb, hb']
    · intro v
      simp only [List.mem_filterMap, Sum.getRight?_eq_some_iff]
      exact ⟨fun _ => mem_geometricGaussList hP v, fun _ => ⟨Sum.inr v, mem_geoMarkList hP _, rfl⟩⟩

/-- **The Gauss word of a carrier is `P`'s Gauss word restricted to the visits lying on it** (reading
(i): "the Gauss word of a carrier is the restriction of `P`'s traversal word to the carrier's marks
in the inherited cyclic order"; lem:piececurve Step 3: "the carrier's word is the parent word
restricted to those crossings"). -/
theorem carrierGaussList_eq_filter (q : GeoComponent hP S) :
    carrierGaussList hP S q =
      (geometricGaussList hP).filter (fun v => decide (geoOwner hP S (Sum.inr v) = q)) := by
  rw [← visits_geoMarkList_eq_gaussList hP, carrierGaussList, geoComponentMarkList,
    List.filterMap_filter, List.filter_filterMap]
  congr 1
  funext a
  cases a with
  | inl i => simp
  | inr v => by_cases h : geoOwner hP S (Sum.inr v) = q <;> simp [h, Option.filter_some]

/-- The traversal word of a carrier is the marked traversal circle restricted to its marks
(definitional: the accepted `geoComponentMarkList`). -/
theorem markList_eq_filter_geoMarkList (q : GeoComponent hP S) :
    geoComponentMarkList hP S q = (geoMarkList hP).filter (fun m => decide (geoOwner hP S m = q)) :=
  rfl

end Word

/-! ## 2. The clauses on the CV binder `S ∈ Ind(G_P)` (tier 0) -/

section Clauses

variable (hP : CrossingGeometry P) {S : Finset (Crossing P)}

/-- **Clause 1** (the general sentence, on the carriers of `P`): "each closed curve produced by
smoothing `C` along `S` traverses the marked points of `Γ_C` lying on it in the cyclic order they
have on `Γ_C`" — at every mark `a` of a carrier `L`, `ρ_S a` is the next mark of `L` in the cyclic
order that `L`'s marks inherit from `Γ` (`GeoInheritsMarkOrder`, U1a's port of the accepted
`InheritsMarkOrder` of SM lem:carriers (i)). -/
theorem carrierword_inherits_order (hS : S ∈ Ind hP) : GeoInheritsMarkOrder hP S :=
  geoInheritsMarkOrder_of_independent hP (geoIndependent_of_mem_Ind hP hS)

/-- The same, unfolded: for `a` on `L`, `ρ_S a = next_L a` in the cycle `(geoMarkCycle hP).filter
(owner = L)`. -/
theorem carrierword_next (hS : S ∈ Ind hP) (q : GeoComponent hP S) (a : Mark P)
    (ha : a ∈ geoComponentCycle hP S q) :
    (geoComponentCycle hP S q).next (geoComponentCycle_nodup hP S q) a ha =
      geoSmoothingSuccessor hP S a :=
  carrierword_inherits_order hP hS q a ha

/-- **Clause 2** ("In particular … each carrier of `S` traverses the marked points lying on it in the
order induced from `Γ`"), word form: the traversal word `geoComponentMarkList hP S L` (the marks of
`L` in the order induced from `Γ`) is traced by `ρ_S` — consecutive entries are successors, the last
returning to the first (`TracedSuccessor`; `hn`-free body of U1b's `geoTracedSuccessor_of_independent`). -/
theorem carrierword_traced (hS : S ∈ Ind hP) (q : GeoComponent hP S) : TracedSuccessor hP S q :=
  fun i => geoComponentMarkList_getElem_successor hP (geoIndependent_of_mem_Ind hP hS) q i

/-- **Clause 3** (the refinement clause of reading (i)): for `S ⊆ S'` both in `Ind(G_P)`, every
carrier of `S'` lies in one carrier of `S` — U1a's `geoOwner_refines`. -/
theorem carrierword_refines {S' : Finset (Crossing P)} (hS' : S' ∈ Ind hP) (hSS' : S ⊆ S')
    (q' : GeoComponent hP S') :
    ∃ q : GeoComponent hP S, ∀ m : Mark P, geoOwner hP S' m = q' → geoOwner hP S m = q :=
  geoOwner_refines hP (geoIndependent_of_mem_Ind hP hS') hSS' q'

/-- Clause 3, "with the induced order": if the carrier `q'` of `S'` lies in the carrier `q` of `S`,
its traversal word is the traversal word of `q` restricted to the marks of `q'` — the daughter
carrier's marks keep the cyclic order they have on the mother carrier (both being restrictions of
the order on `Γ`). -/
theorem carrierword_markList_of_subset {S' : Finset (Crossing P)} (q' : GeoComponent hP S')
    (q : GeoComponent hP S) (h : ∀ m : Mark P, geoOwner hP S' m = q' → geoOwner hP S m = q) :
    geoComponentMarkList hP S' q' =
      (geoComponentMarkList hP S q).filter (fun m => decide (geoOwner hP S' m = q')) := by
  rw [markList_eq_filter_geoMarkList, markList_eq_filter_geoMarkList, List.filter_filter]
  apply List.filter_congr
  intro m _
  by_cases hm : geoOwner hP S' m = q'
  · simp [hm, h m hm]
  · simp [hm]

/-- Clause 3 assembled: the mother carrier `q`, the containment, the induced order (the daughter's
word is the mother's word restricted), and the daughter's traversal of it (`TracedSuccessor` at
`S'`). -/
theorem carrierword_refinement {S' : Finset (Crossing P)} (hS' : S' ∈ Ind hP) (hSS' : S ⊆ S')
    (q' : GeoComponent hP S') :
    ∃ q : GeoComponent hP S,
      (∀ m : Mark P, geoOwner hP S' m = q' → geoOwner hP S m = q) ∧
      geoComponentMarkList hP S' q' =
        (geoComponentMarkList hP S q).filter (fun m => decide (geoOwner hP S' m = q')) ∧
      TracedSuccessor hP S' q' := by
  obtain ⟨q, hq⟩ := carrierword_refines hP hS' hSS' q'
  exact ⟨q, hq, carrierword_markList_of_subset hP q' q hq, carrierword_traced hP hS' q'⟩

/-- The single-chord instance consumed by lem:piececurve Step 5 ("the retained visits keep their
cyclic order by Lemma lem:carrierword applied to the single smoothed chord"): smoothing one more
crossing `d ∉ S` with `insert d S ∈ Ind(G_P)`, each daughter carrier lies in one carrier of `S` with
the induced order. -/
theorem carrierword_insert (d : Crossing P) (hd : insert d S ∈ Ind hP) (q' : GeoComponent hP (insert d S)) :
    ∃ q : GeoComponent hP S,
      (∀ m : Mark P, geoOwner hP (insert d S) m = q' → geoOwner hP S m = q) ∧
      geoComponentMarkList hP (insert d S) q' =
        (geoComponentMarkList hP S q).filter (fun m => decide (geoOwner hP (insert d S) m = q')) ∧
      TracedSuccessor hP (insert d S) q' :=
  carrierword_refinement hP hd (Finset.subset_insert d S) q'

end Clauses

/-! ## 3. Row 137 — CV:lem:carrierword (d1_setup.tex:450–456)

Printed text: "Let `C` be a closed curve with a traversal circle `Γ_C` and finitely many transverse
double points, and let `S` be a set of them no two of which interlace. Then each closed curve
produced by smoothing `C` along `S` traverses the marked points of `Γ_C` lying on it in the cyclic
order they have on `Γ_C`. In particular, taking `C = P` generic and `S ∈ Ind(G_P)`, each carrier of
`S` traverses the marked points lying on it in the order induced from `Γ`." Reading (i) of
DECISION_FINAL §2 adds the refinement clause (`S ⊆ S'` both independent ⇒ every carrier of `S'`
lies in one carrier of `S` with the induced order). -/

section CarrierWordRow

variable (hD : Diagrammatic P) (S : Finset (Crossing P))

/-- CV:lem:carrierword, one field per printed sentence (plus the refinement clause of reading (i)),
on the printed binder `hD : Diagrammatic P`, `hS : S ∈ Ind(G_P)`; `hP = hD.crossingGeometry`,
`ρ_S = geoSmoothingSuccessor hP S`. "The marked points of `Γ` lying on the carrier `L`" are the marks
`m` with `geoOwner hP S m = L` (SM conv:selected-visits at the selected visits). -/
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

end CarrierWordRow

/-- The printed instance "taking `C = P` generic and `S ∈ Ind(G_P)`" (d1:455–456): the row at a
generic `P` (`n ≥ 3`, CV def:polygon's standing hypothesis, needed only to pass from `Generic` to
`Diagrammatic`, `CV.Generic.diagrammatic`). -/
theorem carrierword_generic (hn : 3 ≤ n) (hG : Generic P) (S : Finset (Crossing P))
    (hS : S ∈ Ind hG.crossingGeometry) : CarrierWordData (hG.diagrammatic hn) S hS :=
  carrierword (hG.diagrammatic hn) S hS

end CV

/-! ## Axiom check (removed at porting, as in the accepted CV modules) -/
#print axioms CV.carrierword
#print axioms CV.carrierword_generic
#print axioms CV.carrierGaussList_eq_filter
#print axioms CV.visits_geoMarkList_eq_gaussList
