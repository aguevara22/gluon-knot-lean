# PRE-REVIEW — comparison lane: rows 122 prop:anchor-values, 127 thm:comparison, 128 cor:C-inherits

Independent auditor (pod subagent), 2026-09-15T17:39Z / 1:39pm ET.  This is the PRE-review requested before the formal
fidelity review, not the fidelity review itself.  Inputs: work/drafts/comparison/Statements_FINAL.lean (the frozen
statements, 896 lines), PLAN_FINAL.md §1, §3.4, §5 (FR-CM-1..17), §6, §7; the printed rows reference/SM/sm-5-transport.tex
461-476 (proof 477-505), sm-6-comparison.tex 299-303 (proof 304-311), 313-319 (proof 320-372); the printed inputs
cor:A-lawful (sm-6:105-116), thm:uniqueness (sm-6:201-218), def:walls (K) (sm-1:745-755), def:anchors (sm-5:373-397),
thm:A-S4 (sm-2:460-468), lem:children (sm-1:1269-1277); the accepted siblings `SM.A_lawful : ALawfulData`
(module SM.ALawful, lean-declarations.json row cor:A-lawful, accepted) and `SM.uniqueness` / `UniquenessHypotheses`
(module SM.Uniqueness, row thm:uniqueness, accepted); `SM.hyp_R` (SM/HypR.lean:83, row hyp:R accepted, axiom-policy
mode `explicit_parameter`); the accepted vocabulary SM/Anchors.lean, SM/CuspDefinition.lean, SM/CuspBetweenness.lean,
SM/CuspLawTree.lean, SM/CuspSideCrossings.lean, SM/Generic.lean, SM/DeletedTuple.lean, SM/DeletionIndices.lean,
SM/InsertionIndices.lean, SM/DeletionGeneric.lean, SM/DeletionG1.lean, SM/DeletionInteriors.lean, SM/FlatAdjacent.lean,
SM/ZeroTriples.lean, SM/GenericTopology.lean, SM/GermDefinition.lean, SM/WallGerm.lean, SM/NamedWallPredicates.lean,
SM/SoftParentEdges.lean, SM/SoftTheoremTree.lean, SM/SoftAmplitudeSectors.lean, SM/StarGenericLaw.lean; the CV/R tail's
copies work/drafts/cvtail/Statements_FINAL.lean:870-1000 and the corner lane's work/drafts/corner/Statements_FINAL.lean
(§0 sources); tools/check_lean.py (what the checker enforces about fixed names / hyp:R).

Commands run (from work/lean; nothing written there; two compiles only, the machine is loaded):
- `lake env lean <scratch copy of Statements_FINAL.lean>`: 0 errors; exactly 4 `sorry` warnings (lines 778
  `cusp_deletion_generic`, 848 `prop_anchor_values`, 853 `thm_comparison`, 860 `cor_C_inherits`) and 3 unused-variable
  warnings (`hn` at 177, 195, 198 — the `soft` binders, harmless).  17 s.  The header's claim "every sorry is the leaf or a
  §5 row theorem" is CONFIRMED.
- `lake env lean <copy + probe section>` (probes P1-P7 reproduced in §1/§4 below): 0 errors.  `#print axioms`:
  `anchor_values_of` = [propext, Classical.choice, Quot.sound, lit_homfly]; `thm_comparison_of`, `trianglesC`,
  `uniquenessHypotheses_C_of` = standard + lit_homfly, lp_lm, lp_lm_uniqueness; `cor_C_inherits_of` = the same +
  sorryAx (through the leaf ONLY); `cusp_deletion_generic` = standard + sorryAx.  All literature axioms are the ones the
  policy allows (through def:C / lem:corner-values (i)); no `SM.hyp_R` axiom anywhere, no `Bridge.*` import.
- Byte comparison (python): §0's `CS7Data`, `CSoftData`, `cvl_embedded_of_no_crossings`, `corner_values_i` are IDENTICAL to
  work/drafts/corner/Statements_FINAL.lean; `CuspLawC`, `ReversalLawC`, `TrianglesC` are identical to the CV/R tail's
  (cvtail:874-905) by inspection.

Verdicts in one line each: **(1) SATISFIABLE** (no contradictory hypothesis combination found; every bundle is either
proved from accepted rows or reduces to the three pending rows 110/112/hyp:R plus the leaf); **(2) no blocking fidelity
red flag** (every printed clause has a field; every unprinted field is disclosed in FR-CM-1..17; the fixed-name rows
honour `explicit_parameter` and have exactly the shape of the accepted siblings); **(3) nothing makes a row trivially
true**; **(4) leaf `cusp_deletion_generic`: TRUE** (printed argument complete; every step has accepted vocabulary; one
bonus: its (G1) premise is automatic).

---

## 1. Non-vacuity / joint satisfiability

### 1.1 Row 122: `AnchorValuesHypotheses F`, `AnchorValuesData`

- `AnchorValuesHypotheses F` is the accepted `UniquenessHypotheses.chamber` and `.soft` verbatim (compared with
  SM/Uniqueness.lean:37-38, 72-76: same binders, same `∃ δ > 0, ∀ ε ∈ (0, δ), ∀ hQ`, same ℚ cast).  It is SATISFIABLE:
  the zero function satisfies it (probe P2, kernel-checked:
  `example : AnchorValuesHypotheses (fun _ _ _ => (0 : ℤ)) := ⟨fun _ _ _ _ _ _ => rfl, fun … => ⟨1, one_pos, by simp⟩⟩`),
  `cornerPolygon` satisfies it given `CSoftData` (`cornerPolygon_anchorValuesHypotheses_of`, PROVED), and any
  `UniquenessHypotheses F` restricts to it (`UniquenessHypotheses.toAnchorValuesHypotheses`, PROVED).  So the fields
  `zero`, `loop`, `loopZero` (which quantify `∀ F, AnchorValuesHypotheses F → …`) are not vacuous.
- The anchor types are inhabited: accepted `anchors_exist` (SM/Anchors.lean:533) gives `Nonempty (ZeroAnchor m r)` when
  `Admissible m r`, `Nonempty (LoopAnchor m r)` when `(m+1, r)` is minimal with `|r| ≥ 2`, `Nonempty (LoopAnchorZero m)`
  when `m = 3`.  So `zero`, `loop`, `loopZero`, `loop_turn`, `loopZero_turn`, `A_zero`, `A_loop`, `A_loopZero` quantify
  over non-empty domains.
- **The ∃! parent-root clause** (`A_loop`, `A_loopZero`: `a ≠ A.softEdge → ∃! g, a = softParentEdge A.vertex g ∧ …`).
  Not contradictory and not vacuous: `softParentEdge j : ZMod m → ZMod (m+1)` is injective (accepted
  `softParentEdge_injective`) and misses `softOldIndex j j = A.softEdge` (accepted `softParentEdge_ne_soft`), so by
  cardinality it is a BIJECTION onto the complement of the soft edge — probe P5 (kernel-checked, ≈ 20 lines, Finset
  cardinality): `∀ a ≠ softOldIndex j j, ∃ g, a = softParentEdge j g`.  Hence for every non-soft root `a` there is exactly
  one candidate `g`, and the clause asserts exactly the identity `A_a(Y) = τ_j · A_g(P)` at it.  It is moreover PROVED
  (`av_treeCoefficient_anchor`, from the accepted `soft_theorem_treeCoefficient`, whose own conclusion has the same `∃!`
  shape), so it cannot be contradictory.
- Joint satisfiability of the whole bundle: `anchor_values_of (hs : CSoftData) : AnchorValuesData` is PROVED, axioms
  standard + lit_homfly.  Every field except `C_hypotheses.soft` is unconditional; the only hypothesis is the printed
  thm:C-soft (row 112).  A contradiction inside `AnchorValuesData` would therefore be a contradiction in the accepted
  library or a refutation of thm:C-soft — none is visible.  VERDICT: SATISFIABLE (modulo row 112, exactly as intended).

### 1.2 Row 127: `UniquenessHypotheses cornerPolygon` and `thm_comparison`

- `uniquenessHypotheses_C_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData) : UniquenessHypotheses cornerPolygon` is
  PROVED (sorry-free): (a) `cornerPolygon_chamber` (accepted prop:C-chamber) + `prop_C_silent`; (b) `cs3_flat_bridge
  thm_C_S3` (accepted thm:C-S3; the bridge moves side parameters below the CS3 radius by accepted `cornerStateSum_side_eq`
  / `side_turn_constant` — same proposition, checked); (c) `h7`; (d) `hR`; (e) `hs`; (f) `trianglesC` (UNCONDITIONAL,
  standard + literature axioms).  So the assembly is consistent whenever hyp:R, thm:C-S7, thm:C-soft are.
- `thm_comparison_of hR h7 hs` is the accepted `SM.uniqueness` at `cornerPolygon` — PROVED.  Satisfiability of the row
  reduces to the three pending rows.  Nothing in this lane could make `hyp_R ∧ CS7Data ∧ CSoftData` inconsistent (the
  lane only CONSUMES them).

### 1.3 Row 128: `CInheritsData` (12 fields), `CuspLawC`, `ReversalLawC`, `TrianglesC`

- `cor_C_inherits_of hR h7 hs : CInheritsData` is PROVED modulo the leaf (axioms: standard + literature + sorryAx via
  `cusp_deletion_generic` only).  Field by field the witnesses are accepted rows (`cornerStateSum_genericShift`,
  `prop_C_chamber`, `prop_C_silent`, `thm_C_S3` + `generic_deleteVertex`, `vertex_halves_children`, `soft_family_generic`,
  `generic_reversal`, `star_generic_law`) or `A_lawful.<field>` with `C = A` substituted through `thm_comparison_of`.
  Since `A_lawful : ALawfulData` is ACCEPTED (sorry-free), every `C`-identity obtained by substitution is consistent.
- **`CuspLawC` at a simple cusp wall with (G1)**: the only place where satisfiability depends on something not yet
  proved — the `∃ hQ : Generic (deleteVertex w.center j)` conjunct is exactly the leaf.  If the leaf were FALSE at some
  simple cusp wall, `CuspLawC` would be FALSE (not vacuous), hence `CInheritsData` unsatisfiable and row 128 unprovable.
  §4 finds the leaf TRUE.  Two facts sharpen the picture (both kernel-checked, probes P1/P4):
  * (P1) `G1 (deleteVertex w.center j)` follows from `hf : w.CuspAt j` alone: `g1_deleteVertex hf.2.1` (accepted,
    SM/DeletionG1.lean:11 — it needs only `pointZeros = {turnSupport j}`, which def:walls (K) requires as much as (F)).
    So the printed hypothesis "when the deletion satisfies (G1)" of thm:A-S4 / cor:A-lawful / cor:C-inherits is
    automatically satisfied at every Lean simple cusp wall; the cusp law's domain is ALL simple cusp walls.  Keeping the
    redundant premise is faithful to the print (and to the accepted `ALawfulData.cusp_law`), and harmless.
  * (P4) Consequently `CuspLawC → ∀ w j, w.CuspAt j → Generic (deleteVertex w.center j)`: the row asserts the genericity
    of EVERY cusp deletion.  This is what the printed proof (sm-6:335-359) proves, and §4 confirms it is true.
- The remaining sub-clauses of `CuspLawC` (`∃ b, CuspCase ∧ unique`, `κ = ±1`, the rotation jump at every pair of side
  parameters) are `A_lawful.cusp_law`'s, accepted.  `TrianglesC` is PROVED (`trianglesC`), consistent with
  `A_lawful.triangles` (`A(K₁) = −1`, `A(K₋₁) = +1`) as it must be under `C = A`.  `ReversalLawC` is
  `A_lawful.reversal_law` transported.
- Domain non-emptiness of the wall predicates (`CuspAt`, `FlatAt`, `VertexEdgeAt`, `TripleAt`, …) is NOT established in
  the accepted library as far as I can see (no `∃ w, w.CuspAt j` lemma); if some predicate were unsatisfiable, the
  corresponding law would be vacuous.  This is a property of the accepted definitions shared with the accepted
  `ALawfulData`, `UniquenessHypotheses`, `CS3Data`, `CS7Data`, `hyp_R` — not of this lane.  Recorded as NON-BLOCKING
  context, not as a finding against the statements.

**Overall (1): SATISFIABLE.**  No contradictory combination: the bundles are proved (rows 122/127/128 modulo rows 110,
112, hyp:R and, for 128, the leaf), and the two named suspects — the ∃! parent-root clause and the cusp deletion at a
(G1) cusp wall — are respectively a bijection fact (P5) and a true genericity statement whose (G1) premise is even
automatic (P1, §4).

## 2. Fidelity red flags

### 2.1 Printed clause → field (completeness)

Row 122 (sm-5:461-476), seven printed sentences, nine fields:

| printed | field | note |
|---|---|---|
| "Let F be a function on generic polygons of all arities, constant on chambers and satisfying the soft theorem in the form of thm:C-soft at every admissible soft insertion into a generic polygon" | `AnchorValuesHypotheses F` (`chamber`, `soft`) | verbatim `UniquenessHypotheses` (a, first half) + (e); FR-CM-1/2 |
| "F(Z) = 0 for every zero anchor" | `zero` | `ZeroAnchor m r`, polygon `polygonProjection ⟨A.polygon, A.polygon_generic⟩`; FR-CM-3 |
| "F(Y) = τ_j(P) F(P) for every loop anchor" | `loop` (L), `loopZero` (L₀) | one sentence, two Lean types; FR-CM-3 |
| "In case (L), τ_j(P) = −sgn(r)" | `loop_turn` | = `LoopAnchor.parent_turn` (by definition in BOTH source and Lean: def:anchors (L) requires it); trivially true, see §3 |
| "in case (L₀), it is the orientation sign of the parent triangle" | `loopZero_turn` | both readings asserted (common turn sign; rotation number); FR-CM-3 |
| "The function C satisfies these hypotheses" | `C_hypotheses : AnchorValuesHypotheses cornerPolygon` | `C` descended to the polygon space; FR-CM-5 |
| "The same identities hold for A_g at every anchor root other than the soft edge, with the corresponding parent root used on the right-hand side" | `A_zero`, `A_loop`, `A_loopZero` | `a ≠ A.softEdge`, `∃! g, a = softParentEdge A.vertex g ∧ …`; FR-CM-4 |

No printed clause is without a field.  Row 127 (one sentence) = `thm_comparison`.  Row 128: "every identity of
cor:A-lawful on the domains stated there" = one field per `ALawfulData` field (checked field by field against
SM/ALawful.lean:37-131: `shift_invariant`, `descends`, `chamber_constant`, `silent`, `flat_law`, `cusp_law`,
`vertex_edge_law`, `triple_law`, `soft_theorem`, `reversal_law`, `triangles` — same binders, same sides
(`sideTuple true t` minus `sideTuple false s`; flat sides by `turn … j = ∓1`; cusp sides `cuspLoopSide b j` / `!`),
same signs (`contactSign`, `−κ`, `(−1)^n`), same multipliers (`softAmplitudeMultiplier` in ℚ)); "in particular the
cusp law C(P_loop) − C(P_no) = −κ C(P(0)∖j)" = `cusp_law : CuspLawC`.  Genericity of every substituted argument is
ASSERTED (`∃ hQ` / `∧ Generic`), exactly as the printed proof requires (sm-6:322-333) and as `ALawfulData` does.

### 2.2 Field → printed clause (no undisclosed additions)

Fields with no literal printed counterpart, all disclosed in PLAN_FINAL §5:
- `CInheritsData.root_values` (`C(P) = A_g(P)` for every root `g`) — FR-CM-13.  This is a STRENGTHENING beyond the
  printed corollary: cor:A-lawful's "A(P) := A_g(P) (any g) is well defined" has no `C`-identity as content, and
  `root_values` is thm:comparison itself (plus thm:root-indep-proof).  True and PROVED, and row 128 already assumes
  hyp:R, so nothing is lost; but the formal reviewer may ask why the corollary's bundle contains its own theorem.  The
  alternative (drop it; `thm_comparison_root_of` stays as companion) is a one-line change.  NON-BLOCKING; my
  recommendation is to keep it (harmless, disclosed) unless the formal reviewer objects.
- `CInheritsData.descends`, `shift_invariant` — the `C`-reading of "well defined on generic polygons" — FR-CM-13.  Fine.
- `AnchorValuesData.loopZero_turn`'s third conjunct (rotation number) — FR-CM-3, both readings.  Fine (stronger).
- `cornerPolygon` returning `0` below arity 3 — FR-CM-5; every clause quantifies `3 ≤ n`.  Fine.
- The `zero`/`loop`/`loopZero` fields quantify over the raw structures `ZeroAnchor m r`, `LoopAnchor m r`,
  `LoopAnchorZero m` WITHOUT def:anchors' case conditions (`Admissible m r`; `MinimalAdmissible (m+1) r ∧ 2 ≤ |r|`;
  `(m+1, r) = (4, 0)`).  A generalisation (the printed proof never uses the admissibility conditions), PROVED, hence
  harmless — but it is NOT listed in FR-CM-1..17.  I recommend one sentence in AUTHOR_NOTES (FR-CM-3′): "the anchor
  identities are stated for every anchor datum of the three kinds, whether or not `(n, r)` is in the case where
  def:anchors uses it; the printed proposition is the special case."  NON-BLOCKING (a stronger statement with the same
  proof).
- `CuspLawC` retains the redundant `G1 (deleteVertex w.center j) →` premise (automatic by P1).  Faithful to the print
  and to `ALawfulData.cusp_law`; NON-BLOCKING; worth one sentence in AUTHOR_NOTES since the formal reviewer will ask
  whether the (G1) domain is narrower than "every simple cusp wall" — it is not.

### 2.3 The fixed-name theorems and hyp:R's `explicit_parameter` mode

- axiom-policy.json: `targets` = {`thm:comparison` ↦ `SM.thm_comparison`, `cor:C-inherits` ↦ `SM.cor_C_inherits`, …};
  `hypothesis` = {declaration `SM.hyp_R`, mode `explicit_parameter`}.  tools/check_lean.py:104 enforces only the fixed
  NAMES (`fixed = literature | targets | {'hyp:R': 'SM.hyp_R'}`) and the axiom allow-list (`standard` + `literature`);
  `explicit_parameter` is therefore a policy honoured by construction: `SM.hyp_R : Prop` is a definition (SM/HypR.lean:83)
  and must never be an axiom, and every consumer takes `(hR : hyp_R)`.
- Kernel-printed types (probe P6):
  `thm_comparison : hyp_R → ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P), cornerStateSum hn hP = amplitude P ⋯ hn`
  `cor_C_inherits : hyp_R → CInheritsData`
  `uniqueness : ∀ F, UniquenessHypotheses F → ∀ n [NeZero n] (hn) (P) (hP), F n (polygonProjection ⟨P, hP⟩) = amplitude P ⋯ hn`.
  `thm_comparison` is `uniqueness` at `F := cornerPolygon` with the projection unfolded by `cornerPolygon_projection`
  (`rfl`-level) — the accepted sibling's exact conclusion shape, `C = cornerStateSum hn hP` (def:C on generic labelled
  tuples, every accepted C row's convention), `A = amplitude P hP.1 hn` (cor:A-lawful's `A(P) := A_g(P)` at root 0,
  SM/ALawful.lean:37).  "Assume Hypothesis R" = the leading explicit `hyp_R →`.  ✓
- `cor_C_inherits (hR : hyp_R) : CInheritsData` consumes `hR` through `thm_comparison_of hR …` and as `triple_law`
  (FR-CM-17) — exactly as `A_lawful` is consumed by `uniqueness`.  ✓
- No `Bridge.sm_R`, no `RProof.*` inside the rows (imports: SM.* only).  ✓  Row 122 does not mention R (FR-CM-7).  ✓
- The `_of` library forms additionally take `(h7 : CS7Data) (hs : CSoftData)` — the D-F11/D-F14 pattern; the fixed-name
  rows take ONLY `hR` and are `sorry` until rows 110/112 land (declared and mapped only then, per the header).  This is
  the honest intermediate state; the formal review should be of the STATEMENTS now and of the one-line bodies then.

### 2.4 Checks against the accepted siblings

- `AnchorValuesHypotheses.chamber/.soft` ≡ `UniquenessHypotheses.chamber/.soft` (byte-level modulo doc strings).  ✓
- `CInheritsData.<field>` ≡ `ALawfulData.<field>` with `cornerStateSum hn hP` for `amplitude P hP.1 hn` and `∃ hQ`/`∧
  Generic` witnesses (proof-irrelevant, so `∃ hQ, φ hQ` ≡ `Generic ∧ ∀ hQ, φ hQ`).  The A-specific per-induced-root
  sub-clause `∀ g, … = −κ treeCoefficient (deletion) hQ (deletionRoot j g)` is dropped (no `C` analogue; under the proved
  genericity it is the generic clause by root independence) — FR-CM-9, disclosed.  ✓
- `vertex_edge_law` names the accepted witnesses `(vertex_halves_children hn w hc).1/.2.1` inside the statement (as
  `ALawfulData` names `g1_firstHalf …`); the leading `Generic λ₁ ∧ Generic λ₂ ∧` is then redundant but printed
  ("both halves are generic", lem:children (ii)).  Style only.
- `TrianglesC`'s witnesses `(star_generic_law le_rfl).1.2.2.2.1 : Generic (star 1)` and `.1.2.2.2.2.1 : Generic (starNeg 1)`
  — verified against SM/StarGenericLaw.lean:21-34 (the `(Generic (star r) ∧ Generic (starNeg r) ∧ …)` block).  ✓
- The §6 `example`s prove `CInheritsData → hyp_R`, `→ CS7Data`, `→ CSoftData` and the consumer shape
  `CInheritsData → CuspLawC ∧ ReversalLawC ∧ TrianglesC` (the CV/R tail's `corner_laws_and_soft_of` reads exactly these
  three fields at these types — confirmed against cvtail:973-985).  ✓

**Overall (2): no blocking red flag.**  Two non-blocking disclosures to add to AUTHOR_NOTES (anchor case conditions
dropped = generalisation; (G1) premise of the cusp law automatic), one non-blocking design point (`root_values`).

## 3. Triviality

- `loop_turn` is true by definition (`LoopAnchor.parent_turn`) — but so is the printed sentence: def:anchors (L) DEFINES a
  loop anchor's vertex by `τ_j(P) = −sgn(r)`, and prop:anchor-values merely restates it.  Faithful; not a defect.
- `descends` is discharged by `⟨cornerPolygonSum hn, fun P => rfl⟩`; its content is the compatibility proof inside the
  `Quotient.lift` (accepted `cornerStateSum_genericShift`) — not trivial.
- `C_hypotheses.chamber` is prop:C-chamber (accepted, non-trivial); `.soft` is thm:C-soft.
- `thm_comparison` is not trivially true: `hyp_R` is a definition expected to be PROVED (Bridge lane), so the
  implication is not vacuous; the conclusion is a genuine identity between two independently defined integers.
- `CuspLawC`, `flat_law`, `vertex_edge_law`, `triple_law`, `silent` could only be vacuous if the wall predicates were
  unsatisfiable — shared with every accepted law row (§1.3, last bullet); not this lane's statement.
- `cornerPolygon = 0` below arity 3 makes no clause trivially true (all quantify `3 ≤ n`; the `(n+1)`-gon of the soft
  hypothesis has arity ≥ 4).
- No hypothesis in any field implies its conclusion syntactically; no field has a `False`-implying premise.

**Overall (3): nothing makes a row trivially true.**

## 4. Truth probe of the leaf `cusp_deletion_generic` — VERDICT: TRUE

Statement (frozen): `(w : WallGerm (n+1)) (j : ZMod (n+1)) (hf : w.CuspAt j) (hQ1 : G1 (deleteVertex w.center j)) :
Generic (deleteVertex w.center j)`.  `Generic = G1 ∧ G2` (SM/Generic.lean:11-19); `hQ1` is G1 (and is in fact derivable:
`g1_deleteVertex hf.2.1`, probe P1).  So the leaf is exactly (G2) for the deletion — the printed argument sm-6:335-359.

**Geometry of a simple cusp wall deletion satisfying (G1).**  Write `P = w.center : LabelledTuple (n+1)` (`n+1 ≥ 4`),
`A = P (j−1)`, `M = P j`, `B = P (j+1)`.  `CuspAt` (SM/CuspDefinition.lean:41-45) = def:walls (K): `pointZeros = {turnSupport
j}` (the ONLY zero triple is `{j−1, j, j+1}`, so `A, M, B` are collinear — `singlePointTriple_turn_zero` — and every other
triple of vertices has `chi ≠ 0`), `concurrences = ∅` (no three pairwise remote edges of `P` share a relative-interior
point), `M ∉ [A, B]` (closed segment), and a sign change of `τ_j`.  `A ≠ B` (`singlePointTriple_vertices_injective` +
`prev_ne_next`).  `cusp_cases hf` gives exactly one of: (true) `StrictBetween A B M` — `B = A + t₀ (M − A)`, `0 < t₀ < 1`,
so `[A, B] ⊂ [A, M] = E_{j−1}(0)` (the cusp points "beyond B"); (false) `StrictBetween M A B` — `A = M + t₀ (B − M)`, so
`[A, B] ⊂ [M, B] = E_j(0)`.  In either case `E_{j−1}(0) = [A, M]` and `E_j(0) = [M, B]` OVERLAP along a segment (they are
collinear with `M` outside `[A, B]`), i.e. the adjacent pair `(j−1, j)` of `P` shares interior points — the one place
where "adjacent edges meet only at their vertex" FAILS in `P`; the printed argument never lifts to both of them.
`Q = deleteVertex P j` (SM/DeletedTuple.lean:13: `Q i = P (deletionIndex j i)`, `deletionIndex j i = insertIndex i + (j+1)`,
`insertIndex i = (i.val : ZMod (n+1))`): `Q 0 = B`, `Q (−1) = A`; for `i ≠ −1`, `edge Q i = edge P (deletionIndex j i)` and
`edgeInterior Q i = edgeInterior P (deletionIndex j i)` (accepted `edgeInterior_deleteVertex`); `edge Q (−1) = B − A`, the
fused edge `[A, B]` (`edge_deleteVertex_last`).  A concrete instance: `n+1 = 5`, `A = (0,0)`, `B = (1,0)`, `M = (2,0)`
(case true), `P (j+2) = (1,1)`, `P (j−2) = (0,1)` — no other collinear triple, no triple concurrence; `Q` is the unit
square, generic; the wall `t ↦ M(t) = (2, t)` changes `τ_j`'s sign.  A THREADED instance: add vertices so that another
edge of `P` crosses `[A, M]` between `B` and `M` on the loop side — allowed by (K) (only triple concurrences are excluded),
and the argument below is unaffected (it uses only `Z_c = ∅` and `Z_pt`).

**(G2) for `Q`, clause by clause** (every step names an accepted lemma; none needs a new definition):
1. Suppose `a, b, c : ZMod n` distinct and `x ∈ edgeInterior Q a ∩ edgeInterior Q b ∩ edgeInterior Q c`.  By `hQ1` and
   `g1_common_interiors_remote (3 ≤ n) hQ1` (SM/GenericTopology.lean:47; needs `[Nontrivial (ZMod n)]`, from `3 ≤ n`),
   the three are PAIRWISE REMOTE in `Q` (in a (G1) polygon two distinct edges sharing an interior point are non-adjacent).
   ✓ (Also disposes of `n = 3` automatically: in `ZMod 3` no two indices are remote.)
2. Lift each edge to an edge of `P` whose interior contains `x`.  Unchanged edge `i ≠ −1` ↦ `deletionIndex j i`, interior
   equal (accepted).  Fused edge `−1` ↦ `j−1` (case true) or `j` (case false), with `x = A + q (B − A)`, `0 < q < 1`:
   case true `x = A + (q t₀)(M − A)`, `0 < q t₀ < 1` ⇒ `x ∈ edgeInterior P (j−1)`; case false `x = M + (t₀ + q(1−t₀))(B − M)`,
   `t₀ < t₀ + q(1−t₀) < 1` ⇒ `x ∈ edgeInterior P j`.  ✓  (This is the "no `x = M` case" variant of the accepted flat-case
   `fused_interior_lift`, SM/DeletionInteriors.lean:22, which uses `affine_interior_subdivision`; here a product of
   parameters — PLAN §3.4 step 2, ≈ 60 lines, elementary.)
3. The lift is injective on `{a, b, c}`: `deletionIndex_injective`; the image of `deletionIndex j` avoids `j`
   (`deletionIndex_ne_deleted`) and, for `i ≠ −1`, avoids `j−1` (`deletionIndex_ne_prev`); so the fused edge's image
   (`j−1` or `j`) collides with no unchanged image ("neither `E_{j−1}(0)` nor `E_j(0)` is an edge of `Q`").  ✓
4. The three lifted edges are PAIRWISE REMOTE in `P` (needed because `concurrences` counts only pairwise-remote triples):
   (i) two unchanged edges `a, b ≠ −1`: `a.val, b.val ∈ [0, n−2]`; `deletionIndex j a − deletionIndex j b = a.val − b.val`
   as an integer of absolute value ≤ n−2 < n, so adjacency in `P` (`∈ {−1, 0, 1}` mod `n+1`) forces `|a.val − b.val| ≤ 1`,
   i.e. adjacency in `Q` (the wrap `±n` would need `{a.val, b.val} = {0, n−1}`, excluded by `a, b ≠ −1`) — contrapositive
   of remoteness in `Q`.  ✓  (ii) fused vs unchanged `i` remote in `Q`: `i ∉ {−2, −1, 0}`, so `i.val ∈ [1, n−3]`;
   `deletionIndex j i − (j−1) = i.val + 2 ∈ [3, n−1]` and `deletionIndex j i − j = i.val + 1 ∈ [2, n−2]`, neither in
   `{n, 0, 1}` mod `n+1`.  ✓  (This is the printed "the parent neighbours of the longer cusp edge are the other cusp edge,
   which is not an edge of `Q`, and one of the two edges of `Q` adjacent to the fused edge".)  Pure `ZMod`/`Fin.val`
   bookkeeping — PLAN §3.4 step 4, the bulk of the unit; no geometry.
5. `ConcurrenceTriple P {ka, kb, kc}` (`concurrenceTriple_iff` with the three remoteness facts and `x`), hence
   `{ka, kb, kc} ∈ concurrenceTriples P = w.concurrences` (`mem_concurrenceTriples`, `WallGerm.concurrences`), contradicting
   `hf.2.2.1 : w.concurrences = ∅` — the last three lines of the accepted `flat_center_g2` (SM/FlatAdjacent.lean:79).  ✓

Every printed sentence of sm-6:335-359 is one of these steps; the argument uses `Z_pt` only through the case split and
`Z_c = ∅` only at the end; emptiness of the cusp is never used ("the argument does not require the cusp to be empty").
Refutation attempts: (a) a threaded cusp — irrelevant, only TRIPLE concurrences of `P` are excluded and the lifted triple
is one; (b) `x = M` — impossible, `M ∉ [A, B] ⊇ interior of the fused edge`, and for an unchanged edge `x = M` would put
`M` in the interior of a `P`-edge not incident to `j`, a zero triple outside `turnSupport j` (this is the accepted
`deleted_middle_not_on_unchanged`'s argument), but step 2 does not even need it; (c) the overlap of `E_{j−1}` and `E_j`
— never lifted to together (step 3).  **TRUE**, one line: at a (K) centre the fused edge `[A, B]` lies inside the longer
cusp edge with interior in interior, so a triple concurrence of `Q` lifts injectively to a pairwise-remote triple
concurrence of `P`, contradicting `Z_c = ∅`; (G1) of `Q` is automatic from `Z_pt = {{j−1, j, j+1}}`.

Estimate check against PLAN §3.4 (300-450 lines, 6-10 h): plausible; step 4 is the only sizeable part.  Keep `hQ1` as
a parameter (fidelity to the printed domain); it is used only in step 1.  P1 shows the prover could also derive it from
`hf`, so a companion `cusp_deletion_generic' (hf) : Generic (deleteVertex w.center j) := cusp_deletion_generic w j hf
(g1_deleteVertex hf.2.1)` is a free one-liner once the leaf closes.

## 5. Summary for the executor

| question | verdict |
|---|---|
| (1) joint satisfiability | SATISFIABLE — every bundle PROVED from accepted rows modulo rows 110/112, hyp:R (consumed only) and the leaf; ∃! clause = bijection (P5); cusp (G1) automatic (P1); leaf TRUE (§4) |
| (2) fidelity red flags | none blocking; add to AUTHOR_NOTES: (a) anchor fields drop def:anchors' case conditions (generalisation), (b) `CuspLawC`'s (G1) premise is automatic; design point (c) `root_values` strengthens row 128 by thm:comparison itself (disclosed FR-CM-13; keep or drop) |
| (3) triviality | none; `loop_turn` is by-definition in source and Lean alike |
| (4) leaf | TRUE — printed argument complete, vocabulary accepted, `n = 3` and threaded cusps covered |

Blocking issues: none.

Non-blocking:
1. AUTHOR_NOTES FR-CM-3′: `zero`/`loop`/`loopZero`/`A_*` are stated for every `ZeroAnchor m r` / `LoopAnchor m r` /
   `LoopAnchorZero m`, without `Admissible m r` / `MinimalAdmissible (m+1) r ∧ 2 ≤ |r|` / `m = 3 ∧ r = 0` — a proved
   generalisation of the printed proposition.
2. AUTHOR_NOTES FR-CM-9′: the `G1 (deleteVertex w.center j) →` premise of `CuspLawC` is implied by `w.CuspAt j`
   (`g1_deleteVertex hf.2.1`); the printed domain "when the deletion satisfies (G1)" is all simple cusp walls.  Keep the
   premise (faithful to print and to `ALawfulData.cusp_law`).
3. `CInheritsData.root_values` is thm:comparison (every root) inside the row-128 bundle — a strengthening the formal
   reviewer may query; one-line removable (`thm_comparison_root_of` remains as the companion).
4. Unused-variable warnings on the `soft` binders `hn` (lines 177, 195, 198): rename to `_hn` at port (cosmetic; the
   accepted `UniquenessHypotheses` disables the linter file-wide instead).
5. `import SM.CS5` appears unused by this file (the CV/R tail needs it, this lane does not); drop at port.
6. Wall-predicate satisfiability (`∃ w, w.CuspAt j` etc.) is not in the accepted library — shared context with every
   accepted law row, no action for this lane.
7. Probe P5 (the bijection `softParentEdge j : ZMod n ≃ {a // a ≠ softOldIndex j j}`) is a 20-line kernel-checked fact
   worth adding to SM/SoftParentEdges.lean as `softParentEdge_surjective_ne_soft` if any consumer wants the `∀ g, a =
   softParentEdge j g → …` reading instead of `∃!`.

Disclosure: this pre-review was produced by a Claude Code subagent (Fable 5.1) that did not write the statements; it read
the printed rows, the accepted siblings and the frozen file, and ran two `lake env lean` compiles on scratch copies.
