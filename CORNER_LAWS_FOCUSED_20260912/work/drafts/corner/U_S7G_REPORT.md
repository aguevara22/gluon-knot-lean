# U_S7G_REPORT — unit U110-G (skein extraction; prefix `s7g_`), 2026-09-15

File: `work/drafts/corner/U_S7G.lean` (copy of `Statements_FINAL.lean` + 138 lines).
Check: `cd work/lean && lake env lean ../drafts/corner/U_S7G.lean` — **0 errors**, 13 `declaration uses sorry`
warnings (the 9 leaves of the other units + the 4 row theorems of §6), 14 s warm.  `grep -c sorry`: 16 before →
15 after (the one removed is this unit's leaf; the counted 15 = 13 declarations + the two prose mentions at lines
24 and §6's header).  `diff Statements_FINAL.lean U_S7G.lean`: the only removed text is the leaf's `:= by\n  sorry`
(replaced by a one-line body); everything else is added helper text placed immediately before the leaf inside
`section VertexEdge`.  No definition, structure, statement, name or docstring changed; no import added.

## 0. GO / NO-GO verdict on the RI / RII witnesses (the plan's question, PLAN_FINAL §4 / §6.1 / FR-CC-14)

**Split verdict.**

* **GO — the skein triple at `q` and the identification of the oriented smoothing with `D_A`, at the RECORD level.**
  The accepted `exists_smoothing_record_visit (D) (x) (v) (hv : v.1 = x) : ∃ D₀, IsOrientedSmoothing D x D₀ ∧
  Nonempty (RecordIso D₀.record (D.record.smooth v))` (SM/Smoothing.lean:8185, GENERIC in `D`) together with
  `P_recursion_pos` (SM/PolynomialBlock.lean:693) gives, for every diagram and every positive crossing, the skein
  triple `(D, D.switch x, D₀)` and eq. s7c:universal-skein with the smoothing's record equal to the record-level
  smoothing.  No geometry is needed.  PROVED here as `s7g_skein_at_positive`, and on the actual positive lift with
  `F_H = cornerHomfly` as `s7g_cornerHomfly_skein` (every crossing of `positiveLift` is positive,
  `positiveLift_isPositive`).  What remains for `D_A` is pure record bookkeeping (U110-B/H: the two components of
  `(positiveLift …).record.smooth v` are the records of the half contact carriers' lifts, via the CB record bridge
  `positiveLiftRecordIso`, CBProducts.lean:946) — not geometry.

* **NO-GO (within this lane's budget) — the `RIIData` witness for the bigon `{x, y}` and the `RIData` witness for
  the curl `y` on actual polygonal lifts.**  Facts established by inspection:
  1. `RIIData U D D'` (SM/LinkMoves.lean:599-627) requires: a disc `U` (compact convex, nonempty interior), `Clean U`
     for BOTH diagrams (frontier of `U` traversed injectively; every component exits `U`), an `ArcCover U {a, b}` /
     `{a', b'}` (the traversal points evaluating INTO `U` are exactly the points of the two arcs — a GLOBAL statement
     about the whole polygon), the two `IsArc`s (ends on `frontier U`, inner points in `interior U`), a `MoveMatch`
     (a bijection of ALL outside traversal points with equal `eval`, positive rescaling of the forward AND arriving
     directions, a bijection of outer crossings with over↔over / under↔under, and a component bijection), the
     inner-crossing characterisations, `Separates`, and `same_over`.  `RIData` (:569-588) is the same frame with one
     arc and one kink.
  2. The reduced diagram `D_red` (the side without the bigon) must AGREE POINTWISE with `D_H.switch x` outside `U`.
     The vertex `M` of the bigon triangle `x M y` is a vertex of the corner polygon whose two incident edges change
     along their whole length when `M` moves; so `D_red` cannot be "the other side of the wall" (`D_L`, whose edges
     `(M−1, M_L)`, `(M_L, M+1)` differ from `(M−1, M)`, `(M, M+1)` outside `U`) nor the polygon with `M` replaced
     (same objection).  `D_red` must be a NEW polygon with two extra vertices: the entry/exit points `p ∈ (M−1, M)`,
     `q ∈ (M, M+1)` of the arc on `∂U` made into FLAT vertices, and `M ↦ M'` on the far side of the remote strand
     inside `U`: `…, M−1, p, M', q, M+1, …` (`k+2` vertices).  Flat vertices ARE admitted by `Shadow.Generic`
     (`Regular`, SM/RegularLocus.lean:12: "Positive collinear consecutive edges are retained in the regular domain";
     `transverse` exempts adjacent strands), so `D_red` is a legal `Diagram` — the route is not blocked in principle.
     Then `P D_red = P D_L` needs a record isomorphism `D_red.record ≅ D_L.record` (the crossings outside `U` agree
     with `D_H`'s, and `D_H` ↔ `D_L` differ exactly by `{x, y}` with the persistent visit order — the contact-wall
     transport of U110-A, `VertexLocalData.visit_order`).  Alternatively (CS3 §A) `D_red → D_L` by a flat
     `Reparam` (`reparam_positiveDiagram_single_appendVertex`, CS3.lean:1166, is the precedent, for `positiveDiagram`
     of a single polygon — which IS the type of `positiveLift`, LinkPositiveLift.lean:596) plus a `Deform` inside
     the chamber (constant crossing set).
  3. **There is NO generic constructor of `RIIData` or `RIData` in the accepted library.**  Every construction site:
     `SM/FrontRowsW3.lean:8279 riiData_of` (+ `RISpec`/`RIISpec`, :2228/:8079) builds the witness ONLY for the
     slot diagrams `U2.mkDiagram` of standard front-word realizations (`rlDiagram`, `mvDiagram`, discs `polygon L`
     with the chain ends on the lattice boundary) — the U6 block is ≈ 14,000 lines (W3_U6.lean L11103-25423);
     `SM/Curl.lean:7196 k2_ri : RIData (k2_U S L) S.D (k2_D' S L)` builds a kink INSERTION at a `KinkLocation` of a
     smooth-carried diagram (unit K, ≈ 4,300 lines) — the wrong direction and the wrong shape for deleting `y`;
     `SM/Smoothing.lean` (8,200 lines) is the only GENERIC local-replacement constructor and it is for the oriented
     smoothing (splice model: cut two strands at parameter distance `ε`, rejoin crosswise).  An RII deletion is a
     harder local replacement than the smoothing (a vertex is removed, two flat vertices created, the polygon's
     vertex count changes, the arcs are two-edge paths, and the `mem_iff` clause needs a quantitative separation of
     the bigon disc from every other edge of the corner polygon at the wall).  Honest estimate for a generic
     "empty bigon with a common over strand ⇒ `RIIData` to a reduced polygon with the four visits deleted from the
     record" lemma, following the Smoothing architecture: **6,000-10,000 lines / 80-120 h**, i.e. 3-4× the whole
     U110-G budget (2,500 lines / 35 h).  The RI curl deletion on `D_A` (a two-component diagram produced by the
     smoothing constructor, whose geometry is only known through `OrientedSmoothingData`) is comparable and worse
     to specify.
  4. **The escape routes checked and closed.**  (a) Record-level RII for `P`: `P_reidemeister_II` is
     `P_congr (lmF_reidemeister_II h)` with `lmF_reidemeister_II` a field of the literature interface `SM.lp_lm`;
     there is no record-level bigon lemma anywhere, and proving one would be proving RII invariance of HOMFLY from
     the skein relation (the (N,b) induction of PolynomialBlock does not contain it) — against the
     literature-interface policy.  (b) Front-word calculus: `SM.FrontRows.P_typeII` proves RII for type-II word
     pairs at the word level, but `IsTypeII` (SM/FrontWords.lean:433) is only the cusp-adjacent pattern
     `l_{m±1} σ σ ↦ l_m` / `σ σ r_{m±1} ↦ r_m`, and `represent` (FrontRowsW2.lean:8553) takes a `SmoothFront`'s
     roundings, not an arbitrary `Diagram`; an arbitrary bigon in a polygon's record is out of scope.  (c) Skein
     tricks (smoothing one bigon crossing yields a kink) need RI invariance — the same kind of witness.
  5. Consequence for the row.  `lp_core.reidemeister_II` / `reidemeister_I` are consumed in the corner lane ONLY at
     these two steps (sm-4:600-606 and 491-503).  Everything else in the bigon branch (`B = (1−ε)J`, the
     two-component row, the rotation ledger, the floor branches, cb:singleton) is record/state-sum bookkeeping.

**Recommendation to the executor.**  Keep the leaf statements; schedule the two witnesses as a separate lane
("RIIDeletion": a generic polygonal bigon-deletion constructor in the style of SM/Smoothing.lean, with the
record clause `D_red.record ≅ D.record` minus the four visits; and the curl deletion, or better: avoid the RI step
by reading `D_A^{post}`'s component 1 directly as the positive lift of the half contact carrier of the enlarged
support `T ∪ {x, y}` with the triangle discarded — the printed discharge sm-4:857-866 — so that only the
two-component ROW needs `y` accounted as a self crossing of writhe `+1`, which `homflyrows.two_component_row`
handles without deleting it: check `MarkedProducts.lean:323/381` before building any RI witness).  FINAL_REVIEW
should carry the honest sentence "110 sliding proved, bigon stated; the bigon route waits on a generic R-II
deletion constructor (Smoothing-scale)".  Until then the bigon branch is consumable through the two hypothesis-form
glue lemmas below: whoever produces `RII D_red (D_H.switch x)` and `D_red.record ≅ D_L.record` gets
`P (D_H.switch x) = P D_L` and the extraction for free.

## 1. Proved (all inside `section VertexEdge`, immediately before the leaf; axioms below)

Leaf:
* `s7_universal_extraction` — body `s7g_extraction_of_skein FH FL FA k hsk`.  Axioms `[propext, Classical.choice,
  Quot.sound]`.

Helpers (prefix `s7g_`):
* `s7g_coeffAt_single_mul (p q d k) (f) : coeffAt d k (single (p,q) 1 * f) = coeffAt (d-p) (k-q) f` — the missing
  shift lemma (PLAN §3.3 "no shift lemmas in LinkLaurentRing yet").
* `s7g_coeffAt_a_mul`, `s7g_coeffAt_aInv_mul`, `s7g_coeffAt_z_mul`, `s7g_coeffAt_zInv_mul` — the four unit shifts.
* `s7g_extraction_of_skein` — the leaf's identity as a ring lemma.
* `s7g_skein_at_positive (D) (x) (hx : D.IsPositive x) (v) (hv : v.1 = x) : ∃ D₀, IsSkeinTriple D (D.switch x) D₀ ∧
  IsOrientedSmoothing D x D₀ ∧ Nonempty (RecordIso D₀.record (D.record.smooth v)) ∧
  P D = aInv*aInv*P (D.switch x) + aInv*z*P D₀` — "IsSkeinTriple at q" + the record identification of the
  smoothing.  Axioms `+ lp_lm`.
* `s7g_switch_record_iso` — `(D.switch x).record ≅ ρ` from `D.record.switch v ≅ ρ` (`Diagram.switchRecordIso`).
* `s7g_switch_value_of_rii (D Dred DL) (x) (hR : RII Dred (D.switch x)) (hrec : Nonempty (RecordIso Dred.record
  DL.record)) : P (D.switch x) = P DL` — the printed sentence sm-4:600-606 with the R-II witness as a HYPOTHESIS.
* `s7g_value_of_ri (D Dred DL) (hR : RI Dred D) (hrec) : P D = P DL` — the curl deletion, witness as hypothesis.
* `s7g_extraction_at_positive` — eq. s7c:universal-extraction on an actual diagram given `P (D.switch x) = FL`.
* `s7g_cornerHomfly_skein` — the skein triple on `positiveLift hn hP S q hS` at ANY crossing `x`, with
  `cornerHomfly = aInv² P (lift.switch x) + aInv z P D₀`.  Axioms `+ lit_homfly, lp_lm, lp_lm_uniqueness`
  (through `P_eq_homfly`, as for `cornerHomfly_ne_zero`).
* `s7g_cornerCoefficient_extraction` — `[a^{k−2} z⁰] H⁺_Q = [a^k z⁰] F_L + [a^{k−1} z⁻¹] P D₀` on the lift.

## 2. Not proved (this unit's remaining content, PLAN §4 row U110-G)

* The `RIIData` witness for the bigon `{x, y}` on `D_H.switch x` (→ verdict §0; needs its own lane).
* The `RIData` witness for the curl `y` on component 1 of `D_A` at `ε = 0` (→ §0, and the suggested avoidance).
* The record identification of the R-II-reduced diagram with `D_L` (depends on U110-A's persistent-visit-order
  transport; stated here only as the hypothesis `hrec`).
* The identification of the two components of `(positiveLift …).record.smooth v` with the half contact carriers'
  lifts (U110-B/H bookkeeping through `positiveLiftRecordIso`; not attempted).
No sorried declaration was added; the open inputs are hypotheses of the glue lemmas.

## 3. Mathlib / library pitfalls met

* `AddMonoidAlgebra.single_mul_apply_aux` is DEPRECATED (2026-06-18) → `coeff_single_mul_eq_mul_coeff`; the group
  form `AddMonoidAlgebra.coeff_single_mul_apply (x) (r) (g h) : (single g r * x).coeff (g + h) = r * x.coeff h`
  is `@[simp]` and the convenient one: rewrite `(d,k) = (p,q) + (d-p,k-q)` first; the rewrite leaves
  `-(p,q) + ((p,q) + …)`, closed by `neg_add_cancel_left`.
* In any lemma with the polygon binder `P : LabelledTuple n`, the polynomial `P : Diagram → R`
  (SM/LocalPolynomial.lean:22, namespace `SM`) is SHADOWED: write `SM.P` (not `Link.P`, which does not exist).
* `Record`, `RecordIso`, `Record.smooth`, `Record.switch`, `Diagram.record`, `Diagram.switchRecordIso`,
  `exists_smoothing_record_visit`, `P_recursion_pos`, `presentations`, `P_reidemeister_I/II`, `knotRestrict`,
  `twoLinking` are all reachable under the statements file's 16 imports (probe by `#check`); no import needed.
* `congr 1 <;> ring` after the shift rewrite triggers the `unnecessarySeqFocus` linter; use `congr 1; ring`.

## 4. Notes for the assembler

* Insert position: the block sits between the comment `/-! Two pure-algebra leaves … -/` and the docstring of
  `s7_universal_extraction`; all names are `s7g_`-prefixed (no clash: `grep -rn "s7g_" work/lean/SM` empty).
* `#print axioms` (scratch): the leaf and the ring helpers standard-only; the diagram helpers `+ lp_lm`; the
  `cornerHomfly` helpers `+ lit_homfly, lp_lm, lp_lm_uniqueness` — the policy set of the plan.
* Diff summary: `-` 2 lines (the leaf's `:= by` / `sorry`), `+` 138 lines.
