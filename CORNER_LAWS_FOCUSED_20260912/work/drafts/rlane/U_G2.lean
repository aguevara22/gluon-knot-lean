import Bridge.B3
import SM.TripleWallSides
import SM.GaussAdjacencyTransport
import SM.GeometricRecords
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! # R lane — FINAL statements of the four X₁-free obligation rows

Judge's merge (2026-09-14) of the two statement-design drafts `Statements_A.lean` (spec-first) and
`Statements_B.lean` (text-first); companion notes: `NOTES_FINAL.md` (adopted readings, rejected
alternatives, fidelity risks, proof-lane sketch).

Rows (blueprint/ORDER.md 164, 167, 171, 172; fixed names, work/lean/axiom-policy.json `targets`):
`R:localization → RProof.localization`, `R:parity → RProof.parity`,
`R:fibre_partition → RProof.fibre_partition`, `R:generic_table → RProof.generic_table`.

Sources (frozen): R_ASSEMBLY_SPEC.md (the fibre-sum assembly (1)–(4)); OPEN_WORK.md items 1 and 3;
reference/R/RA/R_ATTACHMENT_WARRANTS.md ("R-LOC-2 — localization": statement and proof;
"R-PAR-v6 — parity and availability": statement and proof); reference/R/RA/
R_GENERIC_ORBIT_ACTUAL_TABLE.md (whole file); R_GENERIC_NONSELECTED_SELECTOR_PROOF.md ("Oriented
line-order calculation" (1)–(3), "Which pair is selected" (4) and its six-case table — the sign
classification the TABLE cites in "Earliest remaining interface"); R_GENERIC_COMMON_TRANSPORT_PROOF.md
("Statement and canonical branch" (1), the labels `a=(u1,u2)`, `b=(u1,u3)`, `c=(u2,u3)`).
The R rows have no printed theorem statement; each bundle below renders the clauses of these texts,
one field per printed/specified clause, the clause quoted in the field's docstring. Checked with
`lake env lean` (the four row theorems and the auxiliary `indep_partition`
are `sorry`; the abstract tables and `isSimpleRIII_eventOfTriple` are proved).

## Domain (decision F2(A), work/AUTHOR_NOTES.md 2026-09-13: no narrowing)

Every row is stated on CV's own locus: a CV event `E : CV.Event n` (CV:def:event, CV/Events.lean)
that is a simple transversal Reidemeister-III event of CV ax:R, `E.IsSimpleRIII e f g h3 h4e h4f h4g`
(CV/Events.lean: zero set exactly the forced bundle `{G3_{e,f,g}, G4_{e;f,g}, G4_{f;e,g}, G4_{g;e,f}}`
with `e < f < g` in the one-based representatives `CV.rep`, pairwise remote, concurrent at `t = 0` at
a point interior to all three edges, transversal). The sides are the CV-generic polygons `E.curve t`,
`t ≠ 0` (`E.generic_punctured`), hence in the accepted geometric class `SM.CrossingGeometry`
(`CV.Generic.crossingGeometry`), on which CV:def:interlace (row 134) is stated:
`SM.geometricVisitPosition`, `SM.geometricGaussList`, `SM.GeometricInterlaces`,
`SM.geometricInterlacementGraph`, `CV.Ind`, `CV.N`, `CV.U`. No SM (all-triple) genericity is assumed
anywhere; no clause is restricted to the SM triple germ.

The SM triple germ. The RA texts are stated for the CV event; the SM triple germ
`SM.WallGerm.TripleAt e f k` (SM/NamedWallPredicates.lean) reaches them through `Bridge.eventOfTriple`
(Bridge:B1), whose event is a simple RIII event of ax:R by Bridge:B2 (zero set) and Bridge:B3
(transversality): `isSimpleRIII_eventOfTriple` below is PROVED, and `localization_of_tripleAt` is the
row instantiated on the germ's event. The accepted lem:triple-sides lane (`SM.triple_wall_sides`,
SM/TripleWallSides.lean: `TripleWallSidesData` = crossing equivalence, `ExactTriangleParameterOrders`,
`ExactTriangleVisitOrders`, `TripleSides`) proves clauses (1)–(3) of R-LOC-2 on SM-generic sides; under
F2(A) the proof lane re-derives them on `CrossingGeometry` + `CV.Generic` (NOTES_FINAL.md §5).

## Notation map (RA text → Lean)

| RA text | Lean |
|---|---|
| simple transversal RIII event `t ↦ P(t)` with zero set the forced bundle | `E : CV.Event n`, `E.IsSimpleRIII e f g h3 h4e h4f h4g` |
| "on a punctured neighbourhood of `t = 0`", "near the wall" | `∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ … Punctured E δ t` (`t ≠ 0 ∧ |t| < δ`) |
| "the two sides", `P₊`/`P₋`, `G⁺`/`G⁻` | `OppositeSides E t t'` (`t·t' < 0`); one side: `SameSide E t t'` |
| the crossing set "indexed by carrying edge pairs" | `IsCrossing (E.curve t) s`, `s : Finset (ZMod n)`; `SM.Crossing P = {s // IsCrossing P s}`; across the wall `crossingTransport hs` (support-preserving, `rfl`) |
| `T = {x_ef, x_eg, x_fg}`; `a = x_ef`, `b = x_eg`, `c = x_fg` | `triangleSupports e f g`, `triangleCrossings P e f g`; `xPair hef`, `xPair heg`, `xPair hfg` |
| a crossing-visit; "the visit of `x` on edge `h`" | `Visit P`; `visitOn x h hh`; position `geometricVisitPosition hP v` on the traversal circle `Γ` |
| "adjacent crossing-visits of the traversal circle" | `AdjacentVisits hP v w` (no crossing visit strictly inside one of the two arcs cut by `v, w`) |
| "order along the edge `e`", `t_f`, `t_ij` | `CV.crossParam P e f` (= `SM.edgeParameter`, `CV.crossParam_eq_edgeParameter`) |
| "the two Gauss words differ by exactly the three transpositions" | `SM.ExactTriangleVisitOrders` (accepted) |
| interlacement `c ∼ c'`, the graph `G_P`, `Ind`, `N`, `U(S)` | `GeometricInterlaces hP`, `geometricInterlacementGraph hP`, `CV.Ind hP`, `CV.N hP`, `CV.U hP` |
| `G⁺ = G⁻ △ binom(T,2)` | `Xor (x ∼ y on side t) (x ≠ y ∧ x ∈ T ∧ y ∈ T)` on side `t'` |
| clumps `C_e, C_f, C_g`; the 2-colouring by the arcs of `u, v` | `clump P e f g h`; `InArc hP u v C`; `two_colouring_bichromatic_pairs` (proved) |
| the interlaced pair `I(y)`, the "mask" of `y` | `interlacedTriangle hP e f g y` |
| `avail(S')`, `𝓐(Q)` | `avail hP e f g S'` |
| `Ind(G[W])`, `Ind(G_±[𝓐(Q)])` | `outsideSupports hP e f g`, `localFibre hP e f g Q` |
| `F_±(S)` (complete summand of CV def:X1), `Φ_±(Q)` | an arbitrary `F : Finset (Crossing P) → M` (X₁ not in Lean, see below); `fibreSum hP e f g F Q` |
| `D_ef = det(u_e,u_f)`, `s_a`; `Δ = G3`, `δ`; `q_e = sgn(t_ef − t_eg)` | `CV.G5 P e f`, `strandSign P e f`; `CV.G3 P e f g`, `concurrenceSign P e f g`; `orderSign P e f g` |
| alternating triple `s_a = s_c = −s_b`; selected-conditions (4) | `IsAlternating sa sb sc`; `SelectedAB`, `SelectedAC`, `SelectedBC` |
| the local edges `ab, ac, bc`; the extreme orbit `K₃ ↔ ∅` | `EdgeAB`, `EdgeAC`, `EdgeBC`; `ExtremeLocal` (its negation is the generic orbit) |
| the local words `P = a b A a c B b c C`, `E = b a A c a B c b C` | on the event: `triangleVisits ~r blockWord`, `wordPVisits`, `wordEVisits`; abstractly: `LocalTable.wordP`, `LocalTable.wordE` |
| successor cycles, residual words, undominated table (on the words) | `LocalTable.SuccessorTable`, `LocalTable.ResidualWordTable`, `LocalTable.SkeletonTable` (all proved by `decide`) |

## What cannot be stated without X₁ / the carrier definitions (flagged)

* `F_±(S)`, "the **complete** summand of CV def:X1 at `S` on that side", and `X₁(P_±)` are not in Lean
  (CV:def:X1, row 146, blocked by the diagram/record layer). The partition (3) is stated for every
  summand `F` into an `AddCommMonoid`; the specialisation `F := F_±` is a one-line corollary once
  def:X1 lands (NOTES_FINAL.md §3).
* The identification of the abstract successor cycles on the six local marks (with `A, B, C` opaque
  gaps) with the actual carriers of `Q ∪ J` on `E.curve t` (CV:def:smoothing / lem:carriers, the
  "arbitrary-Q successor lift" of R_GENERIC_COMMON_TRANSPORT_PROOF.md; Carrier lane, deferred under
  F2(A)) is NOT asserted. The tables are proved on the skeleton; the event-level fields assert the
  block structure of the six triangle visits, the local supports and the local undominated sets.
-/

namespace RProof

open SM

/-! ## Part 0 — abstract combinatorics (no geometry)

### The fibre partition of a state sum over independent sets (R_ASSEMBLY_SPEC.md (1)–(3), abstract) -/

section AbstractGraph

variable {V : Type*} [DecidableEq V]

/-- R_ASSEMBLY_SPEC.md (1): "For each independent outside support `Q` in `W`, define its availability
set by `𝓐(Q) = {t ∈ T : no element of Q is adjacent to t}`" — for an arbitrary graph. -/
def graphAvail (G : SimpleGraph V) [DecidableRel G.Adj] (T Q : Finset V) : Finset V :=
  T.filter fun x => ∀ q ∈ Q, ¬ G.Adj q x

open scoped Classical in
/-- The abstract engine of R:fibre_partition (proof-lane lemma, not a row): "Every independent
support `S` on either side decomposes uniquely into `Q = S ∩ W` and `J = S ∩ T` … This proves a
bijection of supports … The finite bijection just established partitions the exact state sum"
(R_ASSEMBLY_SPEC.md (2)–(3)), for an arbitrary finite graph `G`, local set `T` and summand `F`. -/
theorem indep_partition [Fintype V] (G : SimpleGraph V) (T : Finset V)
    {M : Type*} [AddCommMonoid M] (F : Finset V → M) :
    ∑ S ∈ (Finset.univ : Finset (Finset V)).filter (fun S : Finset V => G.IsIndepSet (↑S : Set V)), F S =
      ∑ Q ∈ (Finset.univ : Finset (Finset V)).filter
          (fun Q : Finset V => G.IsIndepSet (↑Q : Set V) ∧ Disjoint Q T),
        ∑ J ∈ (Finset.univ : Finset (Finset V)).filter
            (fun J : Finset V => G.IsIndepSet (↑J : Set V) ∧ J ⊆ graphAvail G T Q),
          F (Q ∪ J) := by
  sorry

end AbstractGraph

/-! ### The 2-colouring count of R-PAR-v6's proof -/

/-- R_ATTACHMENT_WARRANTS.md, proof of (P1): "A 2-colouring of three objects has either 0
bichromatic pairs (monochromatic) or exactly 2 (the odd object pairs bichromatically with each of
the other two, while those two pair monochromatically). Never 1, never 3." (proof-lane lemma). -/
theorem two_colouring_bichromatic_pairs (χ : Fin 3 → Bool) :
    ((Finset.univ : Finset (Fin 3 × Fin 3)).filter fun p => p.1 < p.2 ∧ χ p.1 ≠ χ p.2).card = 0 ∨
    ((Finset.univ : Finset (Fin 3 × Fin 3)).filter fun p => p.1 < p.2 ∧ χ p.1 ≠ χ p.2).card = 2 := by
  revert χ; decide

/-! ### The local skeleton of R_GENERIC_ORBIT_ACTUAL_TABLE.md

"Use the three unchanged exterior gaps `A,B,C` between the RIII strand blocks:
`P = a b A a c B b c C` (edges ab, bc; centre b), `E = b a A c a B c b C` (edge ac; b isolated)."
The nine letters occupy the positions `0..8` of a cyclic word; the table's visit numbering `1..6` is
positions `0,1,3,4,6,7` and the gaps `A,B,C` are positions `2,5,8` (both words). Oriented smoothing
at a selected crossing letter with visits at positions `p, q` gives the successor `p ↦ q+1`,
`q ↦ p+1` ("Regard oriented smoothing as reconnecting the traversal circle at the two visits of each
selected crossing", R-EXTERIOR-1 §1; the Carrier lane's `smoothingSuccessor = selectedMarkPerm ∘
markSuccessor` on the six local marks). A successor cycle is written as the list of positions it
visits in traversal order, so the table's `(126)[C]` is `[0, 1, 7, 8]`. Each gap is a single opaque
position ("fixed boundary-to-boundary successor paths"). The identification of this skeleton with the
actual carriers is NOT part of this file (module docstring). -/

namespace LocalTable

/-- The letters of the local words: the three local crossings and the three exterior gaps. -/
inductive Letter | a | b | c | A | B | C
  deriving DecidableEq, Repr

open Letter

/-- "`P = a b A a c B b c C`". -/
def wordP : Fin 9 → Letter := ![a, b, A, a, c, B, b, c, C]

/-- "`E = b a A c a B c b C`". -/
def wordE : Fin 9 → Letter := ![b, a, A, c, a, B, c, b, C]

/-- Local crossing letters versus gap letters. -/
def Letter.isLocal : Letter → Bool
  | a | b | c => true
  | _ => false

/-- The positions of a letter in a word (two for a local crossing, one for a gap). -/
def positions (w : Fin 9 → Letter) (ℓ : Letter) : List (Fin 9) :=
  (List.finRange 9).filter fun i => decide (w i = ℓ)

/-- The first visit of a local crossing letter. -/
def firstVisit (w : Fin 9 → Letter) (ℓ : Letter) : Fin 9 := (positions w ℓ).headD 0

/-- The second visit of a local crossing letter. -/
def secondVisit (w : Fin 9 → Letter) (ℓ : Letter) : Fin 9 := (positions w ℓ).getD 1 0

/-- CV:def:interlace on the local word: "exactly one of the two occurrences of `c'` lies between the
two occurrences of `c`" (the local graph "edges ab, bc" of `P`, "edge ac" of `E`). -/
abbrev Interlaces (w : Fin 9 → Letter) (ℓ ℓ' : Letter) : Prop :=
  ℓ ≠ ℓ' ∧ ((positions w ℓ').filter fun j =>
    decide (firstVisit w ℓ < j ∧ j < secondVisit w ℓ)).length = 1

/-- A local support is independent in the local graph ("present"); the others are "absent". -/
abbrev Indep (w : Fin 9 → Letter) (J : Finset Letter) : Prop :=
  ∀ ℓ ∈ J, ∀ ℓ' ∈ J, ¬ Interlaces w ℓ ℓ'

/-- "Local undominated table": the local crossings neither selected nor adjacent to a selected one
(CV def:pieces `U(S)` restricted to `T`). -/
def undominated (w : Fin 9 → Letter) (J : Finset Letter) : Finset Letter :=
  ({a, b, c} : Finset Letter).filter fun ℓ => ℓ ∉ J ∧ ∀ j ∈ J, ¬ Interlaces w ℓ j

/-- The other visit of the crossing letter at position `i` (a gap is its own partner). -/
def partner (w : Fin 9 → Letter) (i : Fin 9) : Fin 9 :=
  ((positions w (w i)).filter fun j => decide (j ≠ i)).headD i

/-- The successor of the oriented smoothing of the local word at the selected letters `S`: the
traversal successor after exchanging the two visits of every selected crossing. -/
def succ (w : Fin 9 → Letter) (S : Finset Letter) (i : Fin 9) : Fin 9 :=
  (if w i ∈ S then partner w i else i) + 1

/-- A successor cycle, written as the positions it visits in order. -/
abbrev IsCycle (σ : Fin 9 → Fin 9) (l : List (Fin 9)) : Prop :=
  l ≠ [] ∧ ∀ k, k < l.length → σ (l.getD k 0) = l.getD ((k + 1) % l.length) 0

/-- "Successor cycles": the listed cycles are cycles of `σ` and together visit every position once
(the complete cycle decomposition). -/
abbrev IsCycleDecomposition (σ : Fin 9 → Fin 9) (ls : List (List (Fin 9))) : Prop :=
  (∀ l ∈ ls, IsCycle σ l) ∧ ls.flatten.Perm (List.finRange 9)

/-- The "unsigned residual word" of a successor cycle: its letters with every local crossing that is
selected or dominated erased (only undominated local crossings and gaps remain). -/
def residual (w : Fin 9 → Letter) (S : Finset Letter) (l : List (Fin 9)) : List Letter :=
  (l.map w).filter fun ℓ => !ℓ.isLocal || decide (ℓ ∈ undominated w S)

/-- The graph, present/absent-support and undominated blocks of the TABLE, on the two words. -/
structure SkeletonTable : Prop where
  /-- "`P = a b A a c B b c C` (edges ab, bc; centre b)". -/
  graph_P : Interlaces wordP a b ∧ Interlaces wordP b c ∧ ¬ Interlaces wordP a c
  /-- "`E = b a A c a B c b C` (edge ac; b isolated)". -/
  graph_E : Interlaces wordE a c ∧ ¬ Interlaces wordE a b ∧ ¬ Interlaces wordE b c
  /-- The tabulated rows of `P` are present: `∅, a, b, c, ac`. -/
  present_P : Indep wordP ∅ ∧ Indep wordP {a} ∧ Indep wordP {b} ∧ Indep wordP {c} ∧
    Indep wordP {a, c}
  /-- "The supports `ab, bc, T` are absent on `P`". -/
  absent_P : ¬ Indep wordP {a, b} ∧ ¬ Indep wordP {b, c} ∧ ¬ Indep wordP {a, b, c}
  /-- The tabulated rows of `E` are present: `∅, a, b, c, ab, bc`. -/
  present_E : Indep wordE ∅ ∧ Indep wordE {a} ∧ Indep wordE {b} ∧ Indep wordE {c} ∧
    Indep wordE {a, b} ∧ Indep wordE {b, c}
  /-- "`ac, T` are absent on `E`". -/
  absent_E : ¬ Indep wordE {a, c} ∧ ¬ Indep wordE {a, b, c}
  /-- "Local undominated table. P: empty -> abc; a -> c; b -> empty; c -> a; ac -> empty". -/
  undominated_P : undominated wordP ∅ = {a, b, c} ∧ undominated wordP {a} = {c} ∧
    undominated wordP {b} = ∅ ∧ undominated wordP {c} = {a} ∧ undominated wordP {a, c} = ∅
  /-- "E: empty -> abc; a -> b; b -> ac (connected); c -> b; ab -> empty; bc -> empty". -/
  undominated_E : undominated wordE ∅ = {a, b, c} ∧ undominated wordE {a} = {b} ∧
    (undominated wordE {b} = {a, c} ∧ Interlaces wordE a c) ∧ undominated wordE {c} = {b} ∧
    undominated wordE {a, b} = ∅ ∧ undominated wordE {b, c} = ∅

/-- The printed "Successor cycles" block of the TABLE, row by row, on the skeleton. -/
structure SuccessorTable : Prop where
  /-- "P empty : (123456)[ABC]". -/
  P_empty : IsCycleDecomposition (succ wordP ∅) [[0, 1, 2, 3, 4, 5, 6, 7, 8]]
  /-- "P a : (1456)[BC](23)[A]". -/
  P_a : IsCycleDecomposition (succ wordP {a}) [[0, 4, 5, 6, 7, 8], [1, 2, 3]]
  /-- "P b : (126)[C](345)[AB]". -/
  P_b : IsCycleDecomposition (succ wordP {b}) [[0, 1, 7, 8], [3, 4, 5, 6, 2]]
  /-- "P c : (1234)[AC](56)[B]". -/
  P_c : IsCycleDecomposition (succ wordP {c}) [[0, 1, 2, 3, 4, 8], [5, 6, 7]]
  /-- "P ac : (14)[C](23)[A](56)[B]". -/
  P_ac : IsCycleDecomposition (succ wordP {a, c}) [[0, 4, 8], [1, 2, 3], [5, 6, 7]]
  /-- "E empty : (123456)[ABC]". -/
  E_empty : IsCycleDecomposition (succ wordE ∅) [[0, 1, 2, 3, 4, 5, 6, 7, 8]]
  /-- "E a : (1256)[BC](34)[A]". -/
  E_a : IsCycleDecomposition (succ wordE {a}) [[0, 1, 5, 6, 7, 8], [2, 3, 4]]
  /-- "E b : (1)[C](23456)[AB]". -/
  E_b : IsCycleDecomposition (succ wordE {b}) [[0, 8], [1, 2, 3, 4, 5, 6, 7]]
  /-- "E c : (1236)[AC](45)[B]". -/
  E_c : IsCycleDecomposition (succ wordE {c}) [[0, 1, 2, 3, 7, 8], [4, 5, 6]]
  /-- "E ab : (1)[C](256)[B](34)[A]". -/
  E_ab : IsCycleDecomposition (succ wordE {a, b}) [[0, 8], [1, 5, 6, 7], [2, 3, 4]]
  /-- "E bc : (1)[C](236)[A](45)[B]". -/
  E_bc : IsCycleDecomposition (succ wordE {b, c}) [[0, 8], [1, 2, 3, 7], [4, 5, 6]]

/-- The printed residual words (TABLE, paragraph before "Earliest remaining interface"), as cyclic
words (`List.IsRotated`) of the successor cycles above, on the skeleton. -/
structure ResidualWordTable : Prop where
  /-- "For endpoint `a`, the unsigned residual word is `c B c C` on P …" -/
  endpoint_a_P : List.IsRotated (residual wordP {a} [0, 4, 5, 6, 7, 8]) [c, B, c, C]
  /-- "… versus `b B b C` on E, …" -/
  endpoint_a_E : List.IsRotated (residual wordE {a} [0, 1, 5, 6, 7, 8]) [b, B, b, C]
  /-- "… with the A-carrier unchanged." -/
  endpoint_a_gap : List.IsRotated (residual wordP {a} [1, 2, 3]) [A] ∧
    List.IsRotated (residual wordE {a} [2, 3, 4]) [A]
  /-- "For endpoint `c`, it is `a A a C` …" -/
  endpoint_c_P : List.IsRotated (residual wordP {c} [0, 1, 2, 3, 4, 8]) [a, A, a, C]
  /-- "… versus `b A b C`, …" -/
  endpoint_c_E : List.IsRotated (residual wordE {c} [0, 1, 2, 3, 7, 8]) [b, A, b, C]
  /-- "… with the B-carrier unchanged." -/
  endpoint_c_gap : List.IsRotated (residual wordP {c} [5, 6, 7]) [B] ∧
    List.IsRotated (residual wordE {c} [4, 5, 6]) [B]
  /-- "For the selected row, P-`b` has no local residual on carriers `C|AB`; …" -/
  selected_P_b : List.IsRotated (residual wordP {b} [0, 1, 7, 8]) [C] ∧
    List.IsRotated (residual wordP {b} [3, 4, 5, 6, 2]) [A, B]
  /-- "… E-`b` has residual `a A c a B c` on `AB` …" (and no local residual on `C`). -/
  selected_E_b : List.IsRotated (residual wordE {b} [0, 8]) [C] ∧
    List.IsRotated (residual wordE {b} [1, 2, 3, 4, 5, 6, 7]) [a, A, c, a, B, c]
  /-- "… and P-`ac` has three local-empty carriers `C|A|B`". -/
  selected_P_ac : List.IsRotated (residual wordP {a, c} [0, 4, 8]) [C] ∧
    List.IsRotated (residual wordP {a, c} [1, 2, 3]) [A] ∧
    List.IsRotated (residual wordP {a, c} [5, 6, 7]) [B]

/-- The three tables hold on the skeleton (finite computation). -/
theorem skeletonTable : SkeletonTable := by
  constructor <;> decide

theorem successorTable : SuccessorTable := by
  constructor <;> decide

theorem residualWordTable : ResidualWordTable := by
  constructor <;> decide

end LocalTable

/-! ## Part 1 — the triangle of a simple RIII event on one polygon -/

variable {n : ℕ} [NeZero n]

/-- Crossings are carried by their edge pairs (`Finset (ZMod n)`), so equality of crossings is
decidable; this lets the supports be handled with `∪`, `∩`, `\`, `insert` without classical choice
("identify the crossing sets with one finite set `V`", R_ASSEMBLY_SPEC.md). -/
instance instDecidableEqCrossing {P : LabelledTuple n} : DecidableEq (Crossing P) :=
  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

/-- "`T = {x_ef, x_eg, x_fg}`", "the three crossings identified by their carrying edge pairs": the
three supports of the triangle. -/
def triangleSupports (e f g : ZMod n) : Finset (Finset (ZMod n)) := {{e, f}, {e, g}, {f, g}}

/-- The triangle `T` as a set of actual crossings of `P`. -/
noncomputable def triangleCrossings (P : LabelledTuple n) (e f g : ZMod n) : Finset (Crossing P) :=
  Finset.univ.filter fun x => x.val ∈ triangleSupports e f g

omit [NeZero n] in
theorem mem_pair_left (i j : ZMod n) : i ∈ ({i, j} : Finset (ZMod n)) := Finset.mem_insert_self i {j}

omit [NeZero n] in
theorem mem_pair_right (i j : ZMod n) : j ∈ ({i, j} : Finset (ZMod n)) :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self j)

/-- The crossing `x_{ij}` carried by the edge pair `{i, j}` (`a = x_ef`, `b = x_eg`, `c = x_fg`). -/
def xPair {P : LabelledTuple n} {i j : ZMod n} (h : IsCrossing P {i, j}) : Crossing P := ⟨{i, j}, h⟩

/-- The visit of the crossing `x` on its edge `h` (one of the two "occurrences of `x` in the Gauss
word"). -/
def visitOn {P : LabelledTuple n} (x : Crossing P) (h : ZMod n) (hh : h ∈ x.val) : Visit P := ⟨x, h, hh⟩

/-- "adjacent crossing-visits of the traversal circle" (R-LOC-2 (2)): `v ≠ w` and no crossing visit
lies strictly inside one of the two arcs into which `v, w` cut the traversal circle `Γ`. This is what
R-LOC-2 (2b) proves ("some punctured neighbourhood is free of them … the two visits are adjacent
among crossing visits") and what R-PAR's proof consumes ("no crossing-visit lies between the two
members of a clump"). Positions are the geometric visit positions of the CV-generic polygon, cyclic
order `traversalBetween`; on SM-generic polygons this is the empty-arc form of the accepted
`SM.GaussVisitsAdjacent` (`SM.gauss_adjacent_empty_arc`). -/
def AdjacentVisits {P : LabelledTuple n} (hP : CrossingGeometry P) (v w : Visit P) : Prop :=
  v ≠ w ∧
  ((∀ u : Visit P, ¬ traversalBetween (geometricVisitPosition hP v) (geometricVisitPosition hP u)
      (geometricVisitPosition hP w)) ∨
   (∀ u : Visit P, ¬ traversalBetween (geometricVisitPosition hP w) (geometricVisitPosition hP u)
      (geometricVisitPosition hP v)))

/-- "Clumps" (R-PAR-v6, proof): "Write the three adjacent pairs as clumps `C_e = {visits of x_ef,
x_eg on e}`, `C_f`, `C_g`. Each crossing of `T` has one visit in each of two clumps" — the visits of
triangle crossings on the bundle edge `h`. -/
noncomputable def clump (P : LabelledTuple n) (e f g h : ZMod n) : Finset (Visit P) :=
  Finset.univ.filter fun v => v.1.val ∈ triangleSupports e f g ∧ v.2.val = h

/-- R-PAR-v6, proof: "each clump lies wholly in one of the two arcs that `u, v` cut `Γ` into. This is
a 2-colouring `χ : {C_e, C_f, C_g} → {1, 2}`": the colour of a set of visits `C` relative to the
visits `u, v` — `C` lies in the arc from `u` to `v`. -/
def InArc {P : LabelledTuple n} (hP : CrossingGeometry P) (u v : Visit P) (C : Finset (Visit P)) :
    Prop :=
  ∀ w ∈ C, traversalBetween (geometricVisitPosition hP u) (geometricVisitPosition hP w)
    (geometricVisitPosition hP v)

/-- "the interlaced pair" `I(y)` (R-PAR-v6), the "mask" of an outside crossing (TABLE): the triangle
crossings interlacing `y`. -/
noncomputable def interlacedTriangle {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n)
    (y : Crossing P) : Finset (Crossing P) := by
  classical
  exact (triangleCrossings P e f g).filter fun x => GeometricInterlaces hP y x

/-- R-PAR-v6 (P2): "`avail(S') = {x ∈ T : x interlaces no member of S'}`"; R_ASSEMBLY_SPEC.md (1):
"`𝓐(Q) = {t ∈ T : no element of Q is adjacent to t}`". -/
noncomputable def avail {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n)
    (Q : Finset (Crossing P)) : Finset (Crossing P) := by
  classical
  exact (triangleCrossings P e f g).filter fun x => ∀ q ∈ Q, ¬ GeometricInterlaces hP q x

/-- "`Ind(G[W])`", the independent outside supports: independent (CV:def:interlace, `CV.Ind`) and
disjoint from `T` ("`W` the complement" of `T`). -/
noncomputable def outsideSupports {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n) :
    Finset (Finset (Crossing P)) := by
  classical
  exact (CV.Ind hP).filter fun Q => Disjoint Q (triangleCrossings P e f g)

/-- "`Ind(G_±[𝓐(Q)])`", the local fibre over `Q`: the independent supports contained in `𝓐(Q)`. -/
noncomputable def localFibre {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n)
    (Q : Finset (Crossing P)) : Finset (Finset (Crossing P)) := by
  classical
  exact (CV.Ind hP).filter fun J => J ⊆ avail hP e f g Q

/-- R_ASSEMBLY_SPEC.md (2): "`Φ_±(Q) = Σ_{J ∈ Ind(G_±[𝓐(Q)])} F_±(Q ∪ J)`", for an arbitrary summand
`F` (the complete summand `F_±` of CV:def:X1 is not yet in Lean; module docstring). -/
noncomputable def fibreSum {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n)
    {M : Type} [AddCommMonoid M] (F : Finset (Crossing P) → M) (Q : Finset (Crossing P)) : M :=
  ∑ J ∈ localFibre hP e f g Q, F (Q ∪ J)

/-! ### Sign data of the oriented line-order calculation (R_GENERIC_NONSELECTED_SELECTOR_PROOF.md) -/

/-- "`D_ef = det(u_e,u_f)`, …" with "`s_a = sgn(D_ef)`, `s_b = sgn(D_eg)`, `s_c = sgn(D_fg)`": the sign
of the strand determinant `det(d_i, d_j) = G5_{i,j}` (CV/Setup.lean). -/
noncomputable def strandSign (P : LabelledTuple n) (i j : ZMod n) : SignType :=
  SignType.sign (CV.G5 P i j)

/-- "`Delta = G3(e,f,g)`" with "`delta = sgn(Delta)`". -/
noncomputable def concurrenceSign (P : LabelledTuple n) (e f g : ZMod n) : SignType :=
  SignType.sign (CV.G3 P e f g)

/-- "`q_e = sgn(t_ef − t_eg)`, `q_f = sgn(t_fe − t_fg)`, `q_g = sgn(t_ge − t_gf)`" with `t_ij` "the
parameter on oriented line `i` of its intersection with line `j`" (`CV.crossParam P i j`):
`q_e = orderSign P e f g`, `q_f = orderSign P f e g`, `q_g = orderSign P g e f`. -/
noncomputable def orderSign (P : LabelledTuple n) (h i j : ZMod n) : SignType :=
  SignType.sign (CV.crossParam P h i - CV.crossParam P h j)

/-- "one of the two alternating sign triples", "`s_a = s_c = −s_b`" (the extreme orbit). -/
def IsAlternating (sa sb sc : SignType) : Prop := sa = sc ∧ sb = -sa

instance (sa sb sc : SignType) : Decidable (IsAlternating sa sb sc) :=
  inferInstanceAs (Decidable (sa = sc ∧ sb = -sa))

/-- (4) "pair ab selected-condition: `s_a = −s_b`" (the shared strand `u_1 = e` separates `u_2, u_3`). -/
def SelectedAB (sa sb : SignType) : Prop := sa = -sb

/-- (4) "pair ac selected-condition: `s_a = s_c`" (the shared strand `u_2 = f` separates). -/
def SelectedAC (sa sc : SignType) : Prop := sa = sc

/-- (4) "pair bc selected-condition: `s_b = −s_c`" (the shared strand `u_3 = g` separates). -/
def SelectedBC (sb sc : SignType) : Prop := sb = -sc

instance (sa sb : SignType) : Decidable (SelectedAB sa sb) := inferInstanceAs (Decidable (sa = -sb))
instance (sa sc : SignType) : Decidable (SelectedAC sa sc) := inferInstanceAs (Decidable (sa = sc))
instance (sb sc : SignType) : Decidable (SelectedBC sb sc) := inferInstanceAs (Decidable (sb = -sc))

/-! ### The local graph `G[T]` and its two orbits (R-LOC-2 corollary) -/

/-- The local edge `ab`: "`x_ef ∼ x_eg`". -/
def EdgeAB {P : LabelledTuple n} (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) : Prop :=
  GeometricInterlaces hP (xPair hef) (xPair heg)

/-- The local edge `ac`: "`x_ef ∼ x_fg`". -/
def EdgeAC {P : LabelledTuple n} (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (hfg : IsCrossing P {f, g}) : Prop :=
  GeometricInterlaces hP (xPair hef) (xPair hfg)

/-- The local edge `bc`: "`x_eg ∼ x_fg`". -/
def EdgeBC {P : LabelledTuple n} (hP : CrossingGeometry P) {e f g : ZMod n}
    (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) : Prop :=
  GeometricInterlaces hP (xPair heg) (xPair hfg)

/-- "the extreme orbit (empty ↔ complete)" (R-LOC-2 corollary), "the extreme graph orbit
`K3 <-> empty`": the induced graph `G[T]` is complete or empty. Its negation is "the one-edge ↔
two-edge orbit" = "the generic graph orbit `P3 <-> (one edge plus one isolated vertex)`". -/
def ExtremeLocal {P : LabelledTuple n} (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) : Prop :=
  (EdgeAB hP hef heg ∧ EdgeAC hP hef hfg ∧ EdgeBC hP heg hfg) ∨
    (¬ EdgeAB hP hef heg ∧ ¬ EdgeAC hP hef hfg ∧ ¬ EdgeBC hP heg hfg)

/-! ### The local word of the triangle on the traversal circle -/

/-- The six visits of the triangle in traversal order — the local word "after erasing every outside
visit" (the gaps `A, B, C` are the erased outside strings between the three blocks). -/
noncomputable def triangleVisits {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n) :
    List (Visit P) :=
  (geometricGaussList hP).filter fun v => decide (v.1.val ∈ triangleSupports e f g)

/-- The local word predicted by the order signs: "the traversal encounters the `e`, `f`, and `g`
two-crossing blocks in that order", each block ordered by its `q` (`a` before `b` on `e` iff
`t_ef < t_eg`, i.e. `q_e = −1`; `a` before `c` on `f` iff `q_f = −1`; `b` before `c` on `g` iff
`q_g = −1`). -/
noncomputable def blockWord {P : LabelledTuple n} {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) :
    List (Visit P) :=
  (if orderSign P e f g = -1 then
      [visitOn (xPair hef) e (mem_pair_left e f), visitOn (xPair heg) e (mem_pair_left e g)]
    else [visitOn (xPair heg) e (mem_pair_left e g), visitOn (xPair hef) e (mem_pair_left e f)]) ++
  (if orderSign P f e g = -1 then
      [visitOn (xPair hef) f (mem_pair_right e f), visitOn (xPair hfg) f (mem_pair_left f g)]
    else [visitOn (xPair hfg) f (mem_pair_left f g), visitOn (xPair hef) f (mem_pair_right e f)]) ++
  (if orderSign P g e f = -1 then
      [visitOn (xPair heg) g (mem_pair_right e g), visitOn (xPair hfg) g (mem_pair_right f g)]
    else [visitOn (xPair hfg) g (mem_pair_right f g), visitOn (xPair heg) g (mem_pair_right e g)])

/-- The printed word "`P = a b A a c B b c C`" as the list of the six triangle visits. -/
noncomputable def wordPVisits {P : LabelledTuple n} {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) :
    List (Visit P) :=
  [visitOn (xPair hef) e (mem_pair_left e f), visitOn (xPair heg) e (mem_pair_left e g),
   visitOn (xPair hef) f (mem_pair_right e f), visitOn (xPair hfg) f (mem_pair_left f g),
   visitOn (xPair heg) g (mem_pair_right e g), visitOn (xPair hfg) g (mem_pair_right f g)]

/-- The printed word "`E = b a A c a B c b C`" as the list of the six triangle visits. -/
noncomputable def wordEVisits {P : LabelledTuple n} {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) :
    List (Visit P) :=
  [visitOn (xPair heg) e (mem_pair_left e g), visitOn (xPair hef) e (mem_pair_left e f),
   visitOn (xPair hfg) f (mem_pair_left f g), visitOn (xPair hef) f (mem_pair_right e f),
   visitOn (xPair hfg) g (mem_pair_right f g), visitOn (xPair heg) g (mem_pair_right e g)]

/-! ## Part 2 — sides of an event -/

/-- The CV genericity of the side polygon `P(t)`, `t ≠ 0` (CV:def:event). -/
theorem genericAt (E : CV.Event n) (t : E.Parameter) (ht : t.val ≠ 0) : CV.Generic (E.curve t) :=
  E.generic_punctured t ht

/-- The crossing geometry of the side polygon `P(t)` (the domain of the Gauss word and of
CV:def:interlace). -/
theorem geomAt (E : CV.Event n) (t : E.Parameter) (ht : t.val ≠ 0) : CrossingGeometry (E.curve t) :=
  (genericAt E t ht).crossingGeometry

/-- "on a punctured neighbourhood of `t = 0`" (R-LOC-2), "near the wall" (R-PAR-v6): `0 < |t| < δ`. -/
def Punctured (E : CV.Event n) (δ : ℝ) (t : E.Parameter) : Prop := t.val ≠ 0 ∧ |t.val| < δ

/-- "the two sides" of the wall (`P₊`, `P₋`; `G⁺`, `G⁻`): parameters of opposite signs. -/
def OppositeSides (E : CV.Event n) (t t' : E.Parameter) : Prop := t.val * t'.val < 0

/-- One side of the wall (one CV chamber): parameters of the same sign. -/
def SameSide (E : CV.Event n) (t t' : E.Parameter) : Prop := 0 < t.val * t'.val

/-! ## Row 164 — R:localization (R-LOC-2, R_ATTACHMENT_WARRANTS.md, "R-LOC-2 — localization")

Printed statement: "Let `t ↦ P(t)` be a simple transversal Reidemeister-III event with zero set
exactly the forced bundle `Z = {G3_{e,f,g}, G4_{e;f,g}, G4_{f;e,g}, G4_{g;e,f}}`, `e < f < g` pairwise
remote and concurrent at `t = 0` at a point interior to all three. Let `T = {x_ef, x_eg, x_fg}`. Then on
a punctured neighbourhood of `t = 0`:
1. the crossing set, indexed by carrying edge pairs, is constant;
2. on each of `e, f, g` the two crossings of `T` carried by that edge occupy adjacent crossing-visits
   of the traversal circle, and their order along that edge is opposite on the two sides;
3. every other pair of crossings keeps its order along every edge;
4. hence `G⁺ = G⁻ △ binom(T,2)`: the three internal pairs of `T` toggle and no other pair changes.
Corollary. The induced graph `G[T]` maps to its complement in `T` across the wall. Both orbits of
that map occur — the extreme orbit (empty ↔ complete) and the one-edge ↔ two-edge orbit." -/

/-- **R-LOC-2 — localization**, clause by clause, for the event `E`, the triangle `e, f, g` and the
punctured radius `δ`. Cross-wall clauses identify crossings by their carrying edge pairs through
`crossingTransport hs`, `hs` being clause (1) at the two parameters. -/
structure LocalizationData (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "Let `T = {x_ef, x_eg, x_fg}`": the three crossings of the triangle exist on the whole punctured
  neighbourhood (presupposed by the statement; the three bundle pairs are active there). -/
  triangle_crossings : ∀ t : E.Parameter, Punctured E δ t →
    IsCrossing (E.curve t) {e, f} ∧ IsCrossing (E.curve t) {e, g} ∧ IsCrossing (E.curve t) {f, g}
  /-- (1) "the crossing set, indexed by carrying edge pairs, is constant". -/
  crossing_set_constant : ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' →
    ∀ s : Finset (ZMod n), IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s
  /-- (2), adjacency: "on each of `e, f, g` the two crossings of `T` carried by that edge occupy adjacent
  crossing-visits of the traversal circle" — on `e` the visits of `x_ef, x_eg` on `e`; on `f` those of
  `x_ef, x_fg` on `f`; on `g` those of `x_eg, x_fg` on `g`. -/
  adjacent : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    AdjacentVisits (geomAt E t ht.1) (visitOn (xPair hef) e (mem_pair_left e f))
      (visitOn (xPair heg) e (mem_pair_left e g)) ∧
    AdjacentVisits (geomAt E t ht.1) (visitOn (xPair hef) f (mem_pair_right e f))
      (visitOn (xPair hfg) f (mem_pair_left f g)) ∧
    AdjacentVisits (geomAt E t ht.1) (visitOn (xPair heg) g (mem_pair_right e g))
      (visitOn (xPair hfg) g (mem_pair_right f g))
  /-- (2), reversal: "their order along that edge is opposite on the two sides" — with the printed
  parameters `t_f = crossParam P e f` along `e` (def:guarded), likewise along `f` and `g`; both
  directions per edge, as in the accepted `SM.TriangleOrderExchanges`. -/
  order_reverses : ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' → OppositeSides E t t' →
    ((CV.crossParam (E.curve t) e f < CV.crossParam (E.curve t) e g ↔
        CV.crossParam (E.curve t') e g < CV.crossParam (E.curve t') e f) ∧
      (CV.crossParam (E.curve t) e g < CV.crossParam (E.curve t) e f ↔
        CV.crossParam (E.curve t') e f < CV.crossParam (E.curve t') e g)) ∧
    ((CV.crossParam (E.curve t) f e < CV.crossParam (E.curve t) f g ↔
        CV.crossParam (E.curve t') f g < CV.crossParam (E.curve t') f e) ∧
      (CV.crossParam (E.curve t) f g < CV.crossParam (E.curve t) f e ↔
        CV.crossParam (E.curve t') f e < CV.crossParam (E.curve t') f g)) ∧
    ((CV.crossParam (E.curve t) g e < CV.crossParam (E.curve t) g f ↔
        CV.crossParam (E.curve t') g f < CV.crossParam (E.curve t') g e) ∧
      (CV.crossParam (E.curve t) g f < CV.crossParam (E.curve t) g e ↔
        CV.crossParam (E.curve t') g e < CV.crossParam (E.curve t') g f))
  /-- Implicit in "on the two sides" / "on a punctured neighbourhood": on one side the order of any
  two crossings along a common edge is constant (each side is one chamber; lem:guardconst on the
  active `G4`s), so that "the order on a side" is well defined. -/
  order_same_side : ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' → SameSide E t t' →
    ∀ h i j : ZMod n, IsCrossing (E.curve t) {h, i} → IsCrossing (E.curve t) {h, j} →
      (CV.crossParam (E.curve t) h i < CV.crossParam (E.curve t) h j ↔
        CV.crossParam (E.curve t') h i < CV.crossParam (E.curve t') h j)
  /-- (3) "every other pair of crossings keeps its order along every edge": two crossings on the edge
  `h` that are not both triangle crossings (a bundle pair is two triangle crossings sharing `h`). -/
  other_orders_persist : ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' →
    OppositeSides E t t' →
    ∀ h i j : ZMod n, IsCrossing (E.curve t) {h, i} → IsCrossing (E.curve t) {h, j} →
      ¬ (({h, i} : Finset (ZMod n)) ∈ triangleSupports e f g ∧
          ({h, j} : Finset (ZMod n)) ∈ triangleSupports e f g) →
      (CV.crossParam (E.curve t) h i < CV.crossParam (E.curve t) h j ↔
        CV.crossParam (E.curve t') h i < CV.crossParam (E.curve t') h j)
  /-- (2)–(3) at the level of the Gauss words (proof of (3), last sentence: "the two Gauss words
  differ by exactly the three transpositions of (2a)"): exactly the same-edge visit pairs of a bundle
  pair (`x.val ∪ y.val = {e, f, g}`) reverse, every other same-edge visit pair keeps its order — the
  accepted predicate `SM.ExactTriangleVisitOrders`, transported along (1). -/
  gauss_words : ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' → OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
      ExactTriangleVisitOrders (E.curve t) (E.curve t') e f g hs
  /-- (4) "hence `G⁺ = G⁻ △ binom(T,2)`: the three internal pairs of `T` toggle and no other pair
  changes" — crossings identified across the wall by their carrying edge pairs. -/
  interlace_toggle : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ x y : Crossing (E.curve t),
      (GeometricInterlaces (geomAt E t' ht'.1) (crossingTransport hs x) (crossingTransport hs y) ↔
        Xor (GeometricInterlaces (geomAt E t ht.1) x y)
          (x ≠ y ∧ x.val ∈ triangleSupports e f g ∧ y.val ∈ triangleSupports e f g))
  /-- Implicit in "`G⁺`, `G⁻`": the interlacement graph is the same at any two parameters of one side. -/
  interlace_same_side : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    SameSide E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ x y : Crossing (E.curve t),
      (GeometricInterlaces (geomAt E t' ht'.1) (crossingTransport hs x) (crossingTransport hs y) ↔
        GeometricInterlaces (geomAt E t ht.1) x y)
  /-- **Corollary**, first sentence: "The induced graph `G[T]` maps to its complement in `T` across
  the wall." -/
  complement_on_triangle : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ x y : Crossing (E.curve t), x.val ∈ triangleSupports e f g → y.val ∈ triangleSupports e f g →
      x ≠ y →
      (GeometricInterlaces (geomAt E t' ht'.1) (crossingTransport hs x) (crossingTransport hs y) ↔
        ¬ GeometricInterlaces (geomAt E t ht.1) x y)

/-- **Row 164, R:localization** (R-LOC-2): for every simple transversal RIII event of CV ax:R there is
a punctured neighbourhood of `t = 0` (radius `δ`) on which all clauses of `LocalizationData` hold. -/
theorem localization (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ LocalizationData E e f g δ := by
  sorry

/-- The CV event of an SM type-`T` germ (Bridge:B1) is a simple transversal RIII event of CV ax:R
(Bridge:B2 for the zero set, the concurrency point of `TripleAt`, Bridge:B3 for transversality) —
so every R row applies to the SM triple germ by instantiation. PROVED. -/
theorem isSimpleRIII_eventOfTriple (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) (hef : CV.rep e < CV.rep f) (hfk : CV.rep f < CV.rep k) :
    (Bridge.eventOfTriple hn g h).IsSimpleRIII e f k
      ⟨Bridge.tripleAt_remote_ef h, Bridge.tripleAt_remote_fk h, Bridge.tripleAt_remote_ek h, hef, hfk⟩
      ⟨Bridge.tripleAt_remote_ef h, Bridge.tripleAt_remote_ek h, ne_of_apply_ne CV.rep hfk.ne, hfk⟩
      ⟨remote_symm (Bridge.tripleAt_remote_ef h), Bridge.tripleAt_remote_fk h,
        ne_of_apply_ne CV.rep (hef.trans hfk).ne, hef.trans hfk⟩
      ⟨remote_symm (Bridge.tripleAt_remote_ek h), remote_symm (Bridge.tripleAt_remote_fk h),
        ne_of_apply_ne CV.rep hef.ne, hef⟩ :=
  ⟨Bridge.B2 hn g h hef hfk, (Bridge.tripleAt_remote_and_common_point h).2.2.2,
    Bridge.B3 hn g h hef hfk⟩

/-- R-LOC-2 for the SM triple germ: the row instantiated on the CV event `Bridge.eventOfTriple hn g h`
of a germ `g.TripleAt e f k` named by increasing representatives (the accepted lem:triple-sides lane,
`SM.triple_wall_sides`, supplies clauses (1)–(3) on the SM locus). Proved from `localization`. -/
theorem localization_of_tripleAt (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) (hef : CV.rep e < CV.rep f) (hfk : CV.rep f < CV.rep k) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ LocalizationData (Bridge.eventOfTriple hn g h) e f k δ :=
  localization (Bridge.eventOfTriple hn g h) e f k _ _ _ _ (isSimpleRIII_eventOfTriple hn g h hef hfk)

/-- A simple transversal RIII event with its data (used only to state the existence claim below). -/
structure SimpleRIIIEvent where
  n : ℕ
  [inst : NeZero n]
  E : CV.Event n
  e : ZMod n
  f : ZMod n
  g : ZMod n
  h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g
  h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g
  h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g
  h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f
  simple : E.IsSimpleRIII e f g h3 h4e h4f h4g

attribute [instance] SimpleRIIIEvent.inst

/-! The optional existence remark of R-LOC-2's corollary ("Both orbits of that map occur") is consumed by no
row and is not part of any bundle; the executor excluded it from the fixed statement (AUTHOR_NOTES 2026-09-14). -/

/-! ## Row 167 — R:parity (R-PAR-v6, R_ATTACHMENT_WARRANTS.md, "R-PAR-v6 — parity and availability")

Printed statement: "Let `t ↦ P(t)` be a simple transversal Reidemeister-III event with triangle
`T = {x_ef, x_eg, x_fg}`, and let `P` be either side's polygon, near the wall. Then:
(P1) Parity. Every crossing `y ∉ T` interlaces exactly 0 or exactly 2 of the three crossings of `T` —
never 1, never 3. Moreover the interlaced pair, when nonempty, is one of `{x_ef,x_eg}`, `{x_ef,x_fg}`,
`{x_eg,x_fg}` — the two crossings sharing one of the three bundle edges.
(P2) Trichotomy. For any set `S'` of crossings disjoint from `T`, the set
`avail(S') = {x ∈ T : x interlaces no member of S'}` has size 3, 1, or 0 — never 2. And `avail(S')` is
the same set on the two sides of the wall."
The proof's clumps and 2-colouring are the supporting definitions `clump`, `InArc` and the proved
lemma `two_colouring_bichromatic_pairs` above (not clauses of the statement). -/

/-- **R-PAR-v6 — parity and availability**, clause by clause, for the event `E`, the triangle
`e, f, g`, "near the wall" = `0 < |t| < δ`, "either side's polygon" = every punctured `E.curve t`. -/
structure ParityData (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "the three crossings of `T`": the triangle has exactly three crossings on either side
  (presupposition, as in `LocalizationData.triangle_crossings`). -/
  triangle_card : ∀ t : E.Parameter, Punctured E δ t → (triangleCrossings (E.curve t) e f g).card = 3
  /-- **(P1) Parity.** "Every crossing `y ∉ T` interlaces exactly 0 or exactly 2 of the three crossings
  of `T` — never 1, never 3." -/
  parity : ∀ t : E.Parameter, ∀ ht : Punctured E δ t, ∀ y : Crossing (E.curve t),
    y.val ∉ triangleSupports e f g →
    (interlacedTriangle (geomAt E t ht.1) e f g y).card = 0 ∨
      (interlacedTriangle (geomAt E t ht.1) e f g y).card = 2
  /-- **(P1)** "Moreover the interlaced pair, when nonempty, is one of `{x_ef,x_eg}`, `{x_ef,x_fg}`,
  `{x_eg,x_fg}` — the two crossings sharing one of the three bundle edges" `h ∈ {e, f, g}`. -/
  interlaced_pair : ∀ t : E.Parameter, ∀ ht : Punctured E δ t, ∀ y : Crossing (E.curve t),
    y.val ∉ triangleSupports e f g → (interlacedTriangle (geomAt E t ht.1) e f g y).Nonempty →
    ∃ h ∈ ({e, f, g} : Finset (ZMod n)),
      interlacedTriangle (geomAt E t ht.1) e f g y =
        (triangleCrossings (E.curve t) e f g).filter fun x => h ∈ x.val
  /-- **(P2) Trichotomy.** "For any set `S'` of crossings disjoint from `T`, the set
  `avail(S') = {x ∈ T : x interlaces no member of S'}` has size 3, 1, or 0 — never 2." (`S'` is any
  set of crossings disjoint from `T`; independence is not assumed, as printed.) -/
  trichotomy : ∀ t : E.Parameter, ∀ ht : Punctured E δ t, ∀ S' : Finset (Crossing (E.curve t)),
    Disjoint S' (triangleCrossings (E.curve t) e f g) →
    (avail (geomAt E t ht.1) e f g S').card = 3 ∨ (avail (geomAt E t ht.1) e f g S').card = 1 ∨
      (avail (geomAt E t ht.1) e f g S').card = 0
  /-- **(P2)** "And `avail(S')` is the same set on the two sides of the wall" (crossings identified by
  their carrying edge pairs). -/
  avail_wall_invariant : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ S' : Finset (Crossing (E.curve t)), Disjoint S' (triangleCrossings (E.curve t) e f g) →
      avail (geomAt E t' ht'.1) e f g (S'.map (crossingTransport hs).toEmbedding) =
        (avail (geomAt E t ht.1) e f g S').map (crossingTransport hs).toEmbedding

/-- **Row 167, R:parity** (R-PAR-v6). -/
theorem parity (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ParityData E e f g δ := by
  sorry

/-! ## Row 171 — R:fibre_partition (R_ASSEMBLY_SPEC.md, paragraphs 2–4 and displays (1)–(3);
OPEN_WORK.md item 1)

Specified text: "Fix the two nearby generic sides of a source simple RIII event. First prove R-LOC-2
and use its carrying-edge labels to identify the crossing sets with one finite set `V`. Let `T` be its
three local crossings and `W` the complement. R-LOC-2 says only the three internal pairs of `T`
toggle. Consequently both graphs induce the same graph on `W` and have the same adjacencies between
`W` and `T`. For each independent outside support `Q` in `W`, define its availability set by
`𝓐(Q) = {t ∈ T : no element of Q is adjacent to t}` (1). It is the same on both sides because the
`W`-to-`T` adjacencies are unchanged. Every independent support `S` on either side decomposes
uniquely into `Q = S ∩ W` and `J = S ∩ T`. `Q` is independent in the outside graph. `J` is independent
in the local graph and belongs to the availability set because independence forbids every `Q`-to-`J`
edge. Conversely, these three conditions imply that `Q ∪ J` is independent … This proves a bijection
of supports, not merely an injection or a list of examples. Let `F_±(S)` denote the complete summand
of CV def:X1 at `S` on that side … Define each fibre sum by `Φ_±(Q) = Σ_{J ∈ Ind(G_±[𝓐(Q)])} F_±(Q ∪ J)`
(2). The finite bijection just established partitions the exact state sum, so
`X_1(P_±) = Σ_{Q ∈ Ind(G[W])} Φ_±(Q)` (3). … Thus availability has size three, one or zero."
OPEN_WORK.md item 1: "Partition supports by outside independent support `Q` and available local set.
Prove exhaustion, disjointness and availability sizes 0, 1 or 3 on both sides."

`X_1` and `F_±` are not in Lean (CV:def:X1 is blocked on the diagram/record layer); (3) is stated for
an arbitrary summand `F`, which is exactly what "partitions the exact state sum" asserts once
`X_1(P) = Σ_{S ∈ Ind(G_P)} F(S)` is available (module docstring, NOTES_FINAL.md §3). -/

/-- **The fibre partition**, clause by clause, on each punctured side (`Ind(G_P)` = `CV.Ind`, `T` the
triangle, `W = Tᶜ`) and across the wall. -/
structure FibrePartitionData (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "R-LOC-2 says only the three internal pairs of `T` toggle. Consequently both graphs induce the
  same graph on `W`". -/
  graph_on_W_same : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ x y : Crossing (E.curve t), x.val ∉ triangleSupports e f g → y.val ∉ triangleSupports e f g →
      (GeometricInterlaces (geomAt E t' ht'.1) (crossingTransport hs x) (crossingTransport hs y) ↔
        GeometricInterlaces (geomAt E t ht.1) x y)
  /-- "and have the same adjacencies between `W` and `T`". -/
  W_to_T_same : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ x y : Crossing (E.curve t), x.val ∉ triangleSupports e f g → y.val ∈ triangleSupports e f g →
      (GeometricInterlaces (geomAt E t' ht'.1) (crossingTransport hs x) (crossingTransport hs y) ↔
        GeometricInterlaces (geomAt E t ht.1) x y)
  /-- (1) "For each independent outside support `Q` in `W`, define its availability set by
  `𝓐(Q) = {t ∈ T : no element of Q is adjacent to t}`. It is the same on both sides because the
  `W`-to-`T` adjacencies are unchanged." -/
  avail_same : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      avail (geomAt E t' ht'.1) e f g (Q.map (crossingTransport hs).toEmbedding) =
        (avail (geomAt E t ht.1) e f g Q).map (crossingTransport hs).toEmbedding
  /-- "Every independent support `S` on either side decomposes uniquely into `Q = S ∩ W` and
  `J = S ∩ T`. `Q` is independent in the outside graph. `J` is independent in the local graph and
  belongs to the availability set because independence forbids every `Q`-to-`J` edge." -/
  decompose : ∀ t : E.Parameter, ∀ ht : Punctured E δ t, ∀ S ∈ CV.Ind (geomAt E t ht.1),
    S = (S \ triangleCrossings (E.curve t) e f g) ∪ (S ∩ triangleCrossings (E.curve t) e f g) ∧
    Disjoint (S \ triangleCrossings (E.curve t) e f g) (S ∩ triangleCrossings (E.curve t) e f g) ∧
    (S \ triangleCrossings (E.curve t) e f g) ∈ outsideSupports (geomAt E t ht.1) e f g ∧
    (S ∩ triangleCrossings (E.curve t) e f g) ∈ CV.Ind (geomAt E t ht.1) ∧
    S ∩ triangleCrossings (E.curve t) e f g ⊆
      avail (geomAt E t ht.1) e f g (S \ triangleCrossings (E.curve t) e f g)
  /-- "Conversely, these three conditions imply that `Q ∪ J` is independent: its possible edges are
  outside, inside `T`, or between the two parts, and the respective conditions exclude all three
  kinds." -/
  compose : ∀ t : E.Parameter, ∀ ht : Punctured E δ t, ∀ Q J : Finset (Crossing (E.curve t)),
    Q ∈ outsideSupports (geomAt E t ht.1) e f g → J ∈ CV.Ind (geomAt E t ht.1) →
    J ⊆ avail (geomAt E t ht.1) e f g Q → Q ∪ J ∈ CV.Ind (geomAt E t ht.1)
  /-- "This proves a bijection of supports, not merely an injection or a list of examples":
  `S ↦ (S ∩ W, S ∩ T)` is a bijection from `Ind(G_P)` onto the pairs `(Q, J)` with `Q ∈ Ind(G[W])`
  and `J ∈ Ind(G[𝓐(Q)])`. -/
  bijection : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    Set.BijOn
      (fun S : Finset (Crossing (E.curve t)) =>
        (S \ triangleCrossings (E.curve t) e f g, S ∩ triangleCrossings (E.curve t) e f g))
      (↑(CV.Ind (geomAt E t ht.1)) : Set (Finset (Crossing (E.curve t))))
      {p | p.1 ∈ outsideSupports (geomAt E t ht.1) e f g ∧
        p.2 ∈ localFibre (geomAt E t ht.1) e f g p.1}
  /-- (2)–(3) "Define each fibre sum by `Φ_±(Q) = Σ_{J ∈ Ind(G_±[𝓐(Q)])} F_±(Q ∪ J)`. The finite
  bijection just established partitions the exact state sum, so `X_1(P_±) = Σ_{Q ∈ Ind(G[W])} Φ_±(Q)`":
  for every summand `F` on the supports of either side, `Σ_{S ∈ Ind(G_P)} F(S) = Σ_{Q ∈ Ind(G[W])}
  Σ_{J ∈ Ind(G[𝓐(Q)])} F(Q ∪ J)` (X₁-free form; `F := F_±` once CV:def:X1 exists). -/
  state_sum_partition : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ {M : Type} [AddCommMonoid M] (F : Finset (Crossing (E.curve t)) → M),
      ∑ S ∈ CV.Ind (geomAt E t ht.1), F S =
        ∑ Q ∈ outsideSupports (geomAt E t ht.1) e f g, fibreSum (geomAt E t ht.1) e f g F Q
  /-- "Prove R-PAR-v6(P1) before using availability sizes. … Thus availability has size three, one or
  zero" (the paragraph after (3); OPEN_WORK.md item 1 "availability sizes 0, 1 or 3 on both sides"),
  for every outside independent `Q` — the instance of `ParityData.trichotomy` the assembly reads. -/
  avail_card : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 3 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 ∨
        (avail (geomAt E t ht.1) e f g Q).card = 0

/-- **Row 171, R:fibre_partition** (R_ASSEMBLY_SPEC.md (1)–(3)). -/
theorem fibre_partition (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ FibrePartitionData E e f g δ := by
  sorry

/-! ## Row 172 — R:generic_table (R_GENERIC_ORBIT_ACTUAL_TABLE.md, with the sign classification of
R_GENERIC_NONSELECTED_SELECTOR_PROOF.md (1)–(4) that it cites)

The strands are `u_e, u_f, u_g` (edge directions), the local crossings `a = x_ef = (u_1,u_2)`,
`b = x_eg = (u_1,u_3)`, `c = x_fg = (u_2,u_3)` (R_GENERIC_COMMON_TRANSPORT_PROOF.md); the determinants
`D_ef = det(u_e,u_f)` etc. are the (G5) members, `Delta = G3(e,f,g)`; `t_ij` is the parameter on line
`i` of its intersection with line `j` (`CV.crossParam P i j`). The printed words `P`, `E` and their
tables are stated (i) on the event in the canonical branch `s_a = s_b = s_c` of
R_GENERIC_COMMON_TRANSPORT_PROOF.md (1), where the labels `a, b, c` need no relabelling, and (ii)
abstractly on the skeleton (`LocalTable`), where they are proved. The other four generic branches are
the label/block relabellings the TABLE calls "the same mechanism after permuting labels"; they are
covered uniformly by `sign_vector`, `edges_iff` and `local_word`. -/

/-- **The generic-orbit table and the sign classification**, clause by clause. -/
structure GenericTableData (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "All four quantities are nonzero on either chamber of a simple wall" (`D_ef, D_eg, D_fg, Delta`). -/
  nonzero : ∀ t : E.Parameter, Punctured E δ t →
    CV.G5 (E.curve t) e f ≠ 0 ∧ CV.G5 (E.curve t) e g ≠ 0 ∧ CV.G5 (E.curve t) f g ≠ 0 ∧
      CV.G3 (E.curve t) e f g ≠ 0
  /-- (1) "`t_ef − t_eg = −Delta/(D_ef D_eg)`, `t_fe − t_fg = −Delta/(D_ef D_fg)`,
  `t_ge − t_gf = −Delta/(D_eg D_fg)`" (the Cramer identities; sign convention checked against
  `CV.G4_factorization` with `G4_{e;f,g} = −G3`, `G4_{f;e,g} = G3`, `G4_{g;e,f} = −G3`). -/
  cramer : ∀ t : E.Parameter, Punctured E δ t →
    CV.crossParam (E.curve t) e f - CV.crossParam (E.curve t) e g =
        -CV.G3 (E.curve t) e f g / (CV.G5 (E.curve t) e f * CV.G5 (E.curve t) e g) ∧
    CV.crossParam (E.curve t) f e - CV.crossParam (E.curve t) f g =
        -CV.G3 (E.curve t) e f g / (CV.G5 (E.curve t) e f * CV.G5 (E.curve t) f g) ∧
    CV.crossParam (E.curve t) g e - CV.crossParam (E.curve t) g f =
        -CV.G3 (E.curve t) e f g / (CV.G5 (E.curve t) e g * CV.G5 (E.curve t) f g)
  /-- (2) "`(q_e, q_f, q_g) = −delta (s_a s_b, s_a s_c, s_b s_c)`". -/
  sign_vector : ∀ t : E.Parameter, Punctured E δ t →
    orderSign (E.curve t) e f g =
        -concurrenceSign (E.curve t) e f g * (strandSign (E.curve t) e f * strandSign (E.curve t) e g) ∧
    orderSign (E.curve t) f e g =
        -concurrenceSign (E.curve t) e f g * (strandSign (E.curve t) e f * strandSign (E.curve t) f g) ∧
    orderSign (E.curve t) g e f =
        -concurrenceSign (E.curve t) e f g * (strandSign (E.curve t) e g * strandSign (E.curve t) f g)
  /-- (3) "After erasing every outside visit, the traversal encounters the `e`, `f`, and `g`
  two-crossing blocks in that order. Hence direct reading of the six-letter word gives: edge(a,b) is
  present iff `q_e = −1`, edge(a,c) is present iff `q_f = +1`, edge(b,c) is present iff `q_g = −1`." -/
  edges_iff : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    (EdgeAB (geomAt E t ht.1) hef heg ↔ orderSign (E.curve t) e f g = -1) ∧
    (EdgeAC (geomAt E t ht.1) hef hfg ↔ orderSign (E.curve t) f e g = 1) ∧
    (EdgeBC (geomAt E t ht.1) heg hfg ↔ orderSign (E.curve t) g e f = -1)
  /-- "Changing chamber changes the sign of `Delta`, so (2) negates all three `q`'s; (3) therefore
  toggles exactly the three local graph edges, consistently with R-LOC": across the wall `delta`
  flips, the three strand signs are unchanged (active (G5) members outside `Z`, lem:guardconst), and
  the three `q`'s negate. -/
  chamber_change : ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' → OppositeSides E t t' →
    concurrenceSign (E.curve t') e f g = -concurrenceSign (E.curve t) e f g ∧
    (strandSign (E.curve t') e f = strandSign (E.curve t) e f ∧
      strandSign (E.curve t') e g = strandSign (E.curve t) e g ∧
      strandSign (E.curve t') f g = strandSign (E.curve t) f g) ∧
    (orderSign (E.curve t') e f g = -orderSign (E.curve t) e f g ∧
      orderSign (E.curve t') f e g = -orderSign (E.curve t) f e g ∧
      orderSign (E.curve t') g e f = -orderSign (E.curve t) g e f)
  /-- "The local graph is extreme exactly when all three indicators in (3) agree. That requires
  `(q_e,q_f,q_g)` to be `(−,+,−)` or `(+,−,+)`." -/
  extreme_iff_orders : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ExtremeLocal (geomAt E t ht.1) hef heg hfg ↔
      ((orderSign (E.curve t) e f g = -1 ∧ orderSign (E.curve t) f e g = 1 ∧
          orderSign (E.curve t) g e f = -1) ∨
        (orderSign (E.curve t) e f g = 1 ∧ orderSign (E.curve t) f e g = -1 ∧
          orderSign (E.curve t) g e f = 1))
  /-- "Dividing the first and third entries of (2) by the middle one shows this is equivalent to
  `s_a = s_c = −s_b`, namely one of the two alternating sign triples." -/
  extreme_iff_alternating : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ExtremeLocal (geomAt E t ht.1) hef heg hfg ↔
      IsAlternating (strandSign (E.curve t) e f) (strandSign (E.curve t) e g)
        (strandSign (E.curve t) f g)
  /-- "Therefore the generic orbit is exactly the other six, nonalternating triples." -/
  generic_iff_nonalternating : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg ↔
      ¬ IsAlternating (strandSign (E.curve t) e f) (strandSign (E.curve t) e g)
        (strandSign (E.curve t) f g)
  /-- "The exact line-order calculation instead partitions the wall into six generic nonalternating
  sign branches and two extreme alternating branches" (TABLE, "Earliest remaining interface"): the
  finite count over the nonzero sign triples. -/
  branch_count :
    ((Finset.univ : Finset (SignType × SignType × SignType)).filter fun s =>
      s.1 ≠ 0 ∧ s.2.1 ≠ 0 ∧ s.2.2 ≠ 0 ∧ IsAlternating s.1 s.2.1 s.2.2).card = 2 ∧
    ((Finset.univ : Finset (SignType × SignType × SignType)).filter fun s =>
      s.1 ≠ 0 ∧ s.2.1 ≠ 0 ∧ s.2.2 ≠ 0 ∧ ¬ IsAlternating s.1 s.2.1 s.2.2).card = 6
  /-- (4) "For each nonalternating sign triple exactly one condition in (4) holds", with the printed
  six-case table: `+++`/`−−−` → `ac` selected, `++−`/`−−+` → `bc`, `+−−`/`−++` → `ab`. -/
  selected_unique : ∀ sa sb sc : SignType, sa ≠ 0 → sb ≠ 0 → sc ≠ 0 → ¬ IsAlternating sa sb sc →
    ((SelectedAB sa sb ∧ ¬ SelectedAC sa sc ∧ ¬ SelectedBC sb sc) ∨
     (¬ SelectedAB sa sb ∧ SelectedAC sa sc ∧ ¬ SelectedBC sb sc) ∨
     (¬ SelectedAB sa sb ∧ ¬ SelectedAC sa sc ∧ SelectedBC sb sc)) ∧
    ((sa = sb ∧ sb = sc) → SelectedAC sa sc) ∧
    ((sa = sb ∧ sc = -sb) → SelectedBC sb sc) ∧
    ((sb = sc ∧ sa = -sb) → SelectedAB sa sb)
  /-- (4) "Using (2)–(3), the `P3` graph on either chamber has as its degree-two vertex the crossing
  complementary to that pair. Thus the unique separating-strand pair is precisely the graph-selected
  pair": in the generic orbit, a pair is selected exactly when, on the two-edge side, it is the
  complement of the degree-two vertex and, on the one-edge side, it is the present edge (the TABLE's
  "graph-selected generic complement couple `b/ac`"). -/
  selected_is_graph_selected : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    (SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g) ↔
      ((EdgeAB (geomAt E t ht.1) hef heg ∧ EdgeBC (geomAt E t ht.1) heg hfg) ∨
        (EdgeAC (geomAt E t ht.1) hef hfg ∧ ¬ EdgeAB (geomAt E t ht.1) hef heg ∧
          ¬ EdgeBC (geomAt E t ht.1) heg hfg))) ∧
    (SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) ↔
      ((EdgeAC (geomAt E t ht.1) hef hfg ∧ EdgeBC (geomAt E t ht.1) heg hfg) ∨
        (EdgeAB (geomAt E t ht.1) hef heg ∧ ¬ EdgeAC (geomAt E t ht.1) hef hfg ∧
          ¬ EdgeBC (geomAt E t ht.1) heg hfg))) ∧
    (SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g) ↔
      ((EdgeAB (geomAt E t ht.1) hef heg ∧ EdgeAC (geomAt E t ht.1) hef hfg) ∨
        (EdgeBC (geomAt E t ht.1) heg hfg ∧ ¬ EdgeAB (geomAt E t ht.1) hef heg ∧
          ¬ EdgeAC (geomAt E t ht.1) hef hfg)))
  /-- "After erasing every outside visit, the traversal encounters the `e`, `f`, and `g` two-crossing
  blocks in that order": the six triangle visits, in traversal order, form (up to rotation — the
  traversal cut is at edge `0`) the three blocks, each ordered by its order sign. -/
  local_word : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    List.IsRotated (triangleVisits (geomAt E t ht.1) e f g) (blockWord hef heg hfg)
  /-- "`P = a b A a c B b c C` (edges ab, bc; centre b)", "`E = b a A c a B c b C` (edge ac; b isolated)"
  as the words of the event in the canonical branch `sgn det(u1,u2) = sgn det(u1,u3) = sgn det(u2,u3)
  = sigma` (R_GENERIC_COMMON_TRANSPORT_PROOF.md (1)): by (2)–(3), `P` is the side `delta = +1` and `E`
  the side `delta = −1`. -/
  canonical_words : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    strandSign (E.curve t) e f = strandSign (E.curve t) e g →
    strandSign (E.curve t) e g = strandSign (E.curve t) f g →
    (concurrenceSign (E.curve t) e f g = 1 →
      List.IsRotated (triangleVisits (geomAt E t ht.1) e f g) (wordPVisits hef heg hfg) ∧
      EdgeAB (geomAt E t ht.1) hef heg ∧ EdgeBC (geomAt E t ht.1) heg hfg ∧
      ¬ EdgeAC (geomAt E t ht.1) hef hfg) ∧
    (concurrenceSign (E.curve t) e f g = -1 →
      List.IsRotated (triangleVisits (geomAt E t ht.1) e f g) (wordEVisits hef heg hfg) ∧
      EdgeAC (geomAt E t ht.1) hef hfg ∧ ¬ EdgeAB (geomAt E t ht.1) hef heg ∧
      ¬ EdgeBC (geomAt E t ht.1) heg hfg)
  /-- "The supports `ab, bc, T` are absent on P; `ac, T` are absent on E" — and the rows of the table
  are the present local supports (`∅, a, b, c, ac` on P; `∅, a, b, c, ab, bc` on E), on the event in
  the canonical branch (`Ind(G_P)` = `CV.Ind`). -/
  local_supports : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    strandSign (E.curve t) e f = strandSign (E.curve t) e g →
    strandSign (E.curve t) e g = strandSign (E.curve t) f g →
    (concurrenceSign (E.curve t) e f g = 1 →
      ({xPair hef, xPair heg} : Finset (Crossing (E.curve t))) ∉ CV.Ind (geomAt E t ht.1) ∧
      ({xPair heg, xPair hfg} : Finset (Crossing (E.curve t))) ∉ CV.Ind (geomAt E t ht.1) ∧
      ({xPair hef, xPair heg, xPair hfg} : Finset (Crossing (E.curve t))) ∉ CV.Ind (geomAt E t ht.1) ∧
      (∅ : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair hef} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair heg} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair hfg} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair hef, xPair hfg} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1)) ∧
    (concurrenceSign (E.curve t) e f g = -1 →
      ({xPair hef, xPair hfg} : Finset (Crossing (E.curve t))) ∉ CV.Ind (geomAt E t ht.1) ∧
      ({xPair hef, xPair heg, xPair hfg} : Finset (Crossing (E.curve t))) ∉ CV.Ind (geomAt E t ht.1) ∧
      (∅ : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair hef} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair heg} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair hfg} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair hef, xPair heg} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair heg, xPair hfg} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1))
  /-- "Local undominated table: P: empty → abc; a → c; b → empty; c → a; ac → empty. E: empty → abc;
  a → b; b → ac (connected); c → b; ab → empty; bc → empty" — `U(S) ∩ T` (CV:def:pieces' `U(S)` is
  `CV.U`), on the event in the canonical branch. -/
  local_undominated : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    strandSign (E.curve t) e f = strandSign (E.curve t) e g →
    strandSign (E.curve t) e g = strandSign (E.curve t) f g →
    (concurrenceSign (E.curve t) e f g = 1 →
      CV.U (geomAt E t ht.1) ∅ ∩ triangleCrossings (E.curve t) e f g = {xPair hef, xPair heg, xPair hfg} ∧
      CV.U (geomAt E t ht.1) {xPair hef} ∩ triangleCrossings (E.curve t) e f g = {xPair hfg} ∧
      CV.U (geomAt E t ht.1) {xPair heg} ∩ triangleCrossings (E.curve t) e f g = ∅ ∧
      CV.U (geomAt E t ht.1) {xPair hfg} ∩ triangleCrossings (E.curve t) e f g = {xPair hef} ∧
      CV.U (geomAt E t ht.1) {xPair hef, xPair hfg} ∩ triangleCrossings (E.curve t) e f g = ∅) ∧
    (concurrenceSign (E.curve t) e f g = -1 →
      CV.U (geomAt E t ht.1) ∅ ∩ triangleCrossings (E.curve t) e f g = {xPair hef, xPair heg, xPair hfg} ∧
      CV.U (geomAt E t ht.1) {xPair hef} ∩ triangleCrossings (E.curve t) e f g = {xPair heg} ∧
      (CV.U (geomAt E t ht.1) {xPair heg} ∩ triangleCrossings (E.curve t) e f g = {xPair hef, xPair hfg} ∧
        EdgeAC (geomAt E t ht.1) hef hfg) ∧
      CV.U (geomAt E t ht.1) {xPair hfg} ∩ triangleCrossings (E.curve t) e f g = {xPair heg} ∧
      CV.U (geomAt E t ht.1) {xPair hef, xPair heg} ∩ triangleCrossings (E.curve t) e f g = ∅ ∧
      CV.U (geomAt E t ht.1) {xPair heg, xPair hfg} ∩ triangleCrossings (E.curve t) e f g = ∅)
  /-- "Full availability plus R-PAR sharpens the exterior masks: after `a`, survivors have mask `0` or
  `bc`, so `b,c` are twins; after `c`, mask `0` or `ab`, so `a,b` are twins; after `b`, mask `0` or `ac`,
  so `a,c` are twins; after any present pair only mask-zero outsiders survive." Full availability:
  `𝓐(Q) = T` for the outside independent `Q`; survivors after `x`: the undominated outside crossings
  `U(Q ∪ {x})` of CV def:pieces (`CV.U`); the mask: `interlacedTriangle`. -/
  mask_sharpening : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      avail (geomAt E t ht.1) e f g Q = triangleCrossings (E.curve t) e f g →
      (∀ y ∈ CV.U (geomAt E t ht.1) (insert (xPair hef) Q), y.val ∉ triangleSupports e f g →
        interlacedTriangle (geomAt E t ht.1) e f g y = ∅ ∨
        interlacedTriangle (geomAt E t ht.1) e f g y = {xPair heg, xPair hfg}) ∧
      (∀ y ∈ CV.U (geomAt E t ht.1) (insert (xPair hfg) Q), y.val ∉ triangleSupports e f g →
        interlacedTriangle (geomAt E t ht.1) e f g y = ∅ ∨
        interlacedTriangle (geomAt E t ht.1) e f g y = {xPair hef, xPair heg}) ∧
      (∀ y ∈ CV.U (geomAt E t ht.1) (insert (xPair heg) Q), y.val ∉ triangleSupports e f g →
        interlacedTriangle (geomAt E t ht.1) e f g y = ∅ ∨
        interlacedTriangle (geomAt E t ht.1) e f g y = {xPair hef, xPair hfg}) ∧
      (∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
        Q ∪ J ∈ CV.Ind (geomAt E t ht.1) →
        ∀ y ∈ CV.U (geomAt E t ht.1) (Q ∪ J), y.val ∉ triangleSupports e f g →
          interlacedTriangle (geomAt E t ht.1) e f g y = ∅)
  /-- The graph, present/absent and undominated blocks of the TABLE on the words `P`, `E` (abstract
  skeleton; proved by `decide`: `LocalTable.skeletonTable`). -/
  skeleton_table : LocalTable.SkeletonTable
  /-- The printed "Successor cycles" block (11 rows) on the skeleton (proved:
  `LocalTable.successorTable`; the identification with the actual carriers is Carrier-lane work, see
  the module docstring). -/
  successor_table : LocalTable.SuccessorTable
  /-- The printed residual words (`c B c C` vs `b B b C`, `a A a C` vs `b A b C`, `C|AB`, `a A c a B c`,
  `C|A|B`) on the skeleton (proved: `LocalTable.residualWordTable`). -/
  residual_table : LocalTable.ResidualWordTable

/-! ## Unit G1 — the sign classification of R:generic_table (proof lane, 2026-09-14)

Standalone lemmas `RProof.G1.<field>`, one per sign-classification field of `GenericTableData`, each
stated with exactly the field's type (after the radius data `G1.GoodRadius E e f g δ`, supplied by
`G1.exists_goodRadius hE`), so that the assembler can discharge the field by `exact G1.<field> hδ`
(or `G1.<field> h3` for the fields that need no radius). Nothing in the fixed statements above is
changed. -/

namespace G1

/-! ### Abstract `SignType` facts (finite checks) -/

/-- The finite count of `branch_count`. -/
theorem branch_count :
    ((Finset.univ : Finset (SignType × SignType × SignType)).filter fun s =>
      s.1 ≠ 0 ∧ s.2.1 ≠ 0 ∧ s.2.2 ≠ 0 ∧ IsAlternating s.1 s.2.1 s.2.2).card = 2 ∧
    ((Finset.univ : Finset (SignType × SignType × SignType)).filter fun s =>
      s.1 ≠ 0 ∧ s.2.1 ≠ 0 ∧ s.2.2 ≠ 0 ∧ ¬ IsAlternating s.1 s.2.1 s.2.2).card = 6 := by
  decide

/-- The six-case table of `selected_unique`. -/
theorem selected_unique : ∀ sa sb sc : SignType, sa ≠ 0 → sb ≠ 0 → sc ≠ 0 →
    ¬ IsAlternating sa sb sc →
    ((SelectedAB sa sb ∧ ¬ SelectedAC sa sc ∧ ¬ SelectedBC sb sc) ∨
     (¬ SelectedAB sa sb ∧ SelectedAC sa sc ∧ ¬ SelectedBC sb sc) ∨
     (¬ SelectedAB sa sb ∧ ¬ SelectedAC sa sc ∧ SelectedBC sb sc)) ∧
    ((sa = sb ∧ sb = sc) → SelectedAC sa sc) ∧
    ((sa = sb ∧ sc = -sb) → SelectedBC sb sc) ∧
    ((sb = sc ∧ sa = -sb) → SelectedAB sa sb) := by
  decide

/-- "(q_e,q_f,q_g) ∈ {(−,+,−), (+,−,+)}" with `q = −δ(s_a s_b, s_a s_c, s_b s_c)` is exactly
"`s_a = s_c = −s_b`" (the middle entry divides the other two). -/
theorem orders_iff_alternating_abstract : ∀ d sa sb sc : SignType, d ≠ 0 → sa ≠ 0 → sb ≠ 0 →
    sc ≠ 0 →
    (((-d * (sa * sb) = -1 ∧ -d * (sa * sc) = 1 ∧ -d * (sb * sc) = -1) ∨
      (-d * (sa * sb) = 1 ∧ -d * (sa * sc) = -1 ∧ -d * (sb * sc) = 1)) ↔
      IsAlternating sa sb sc) := by
  decide

/-- "all three indicators agree" for nonzero order signs: all edges or no edges. -/
theorem extreme_iff_orders_abstract : ∀ qe qf qg : SignType, qe ≠ 0 → qf ≠ 0 → qg ≠ 0 →
    (((qe = -1 ∧ qf = 1 ∧ qg = -1) ∨ (¬ qe = -1 ∧ ¬ qf = 1 ∧ ¬ qg = -1)) ↔
      ((qe = -1 ∧ qf = 1 ∧ qg = -1) ∨ (qe = 1 ∧ qf = -1 ∧ qg = 1))) := by
  decide

/-- (4) read on the edges of (3): on a nonalternating triple the selected pair is the
graph-selected pair. -/
theorem selected_abstract : ∀ d sa sb sc : SignType, d ≠ 0 → sa ≠ 0 → sb ≠ 0 → sc ≠ 0 →
    ¬ IsAlternating sa sb sc →
    (SelectedAC sa sc ↔ ((-d * (sa * sb) = -1 ∧ -d * (sb * sc) = -1) ∨
        (-d * (sa * sc) = 1 ∧ ¬ -d * (sa * sb) = -1 ∧ ¬ -d * (sb * sc) = -1))) ∧
    (SelectedAB sa sb ↔ ((-d * (sa * sc) = 1 ∧ -d * (sb * sc) = -1) ∨
        (-d * (sa * sb) = -1 ∧ ¬ -d * (sa * sc) = 1 ∧ ¬ -d * (sb * sc) = -1))) ∧
    (SelectedBC sb sc ↔ ((-d * (sa * sb) = -1 ∧ -d * (sa * sc) = 1) ∨
        (-d * (sb * sc) = -1 ∧ ¬ -d * (sa * sb) = -1 ∧ ¬ -d * (sa * sc) = 1))) := by
  decide

theorem neg_mul_ne_zero_abstract : ∀ c a b : SignType, c ≠ 0 → a ≠ 0 → b ≠ 0 →
    -c * (a * b) ≠ 0 := by
  decide

theorem neg_neg_mul_abstract : ∀ c a b : SignType, -(-c) * (a * b) = -(-c * (a * b)) := by
  decide

theorem eq_neg_of_mul_eq_neg_one_abstract : ∀ x y : SignType, x * y = -1 → y = -x := by
  decide

/-! ### Signs of real quotients -/

theorem sign_inv' (y : ℝ) : SignType.sign y⁻¹ = SignType.sign y := by
  rcases lt_trichotomy y 0 with h | rfl | h
  · rw [sign_neg h, sign_neg (inv_lt_zero.mpr h)]
  · simp
  · rw [sign_pos h, sign_pos (inv_pos.mpr h)]

theorem sign_div' (x y : ℝ) : SignType.sign (x / y) = SignType.sign x * SignType.sign y := by
  rw [div_eq_mul_inv, sign_mul, sign_inv']

/-- `x y < 0` is a sign condition: it persists where the two signs are unchanged. -/
theorem mul_neg_iff_of_sign_eq {a b a' b' : ℝ} (ha : SignType.sign a = SignType.sign a')
    (hb : SignType.sign b = SignType.sign b') : a * b < 0 ↔ a' * b' < 0 := by
  rw [← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, sign_mul, sign_mul, ha, hb]

/-! ### The Cramer identities and the sign vector, on any polygon with nonzero strand determinants -/

omit [NeZero n] in
/-- (1) from `CV.G4_factorization` and `G4_{e;f,g} = −G3`, `G4_{f;e,g} = G3`, `G4_{g;e,f} = −G3`. -/
theorem cramer_of_ne (P : LabelledTuple n) (e f g : ZMod n)
    (hef : CV.G5 P e f ≠ 0) (heg : CV.G5 P e g ≠ 0) (hfg : CV.G5 P f g ≠ 0) :
    CV.crossParam P e f - CV.crossParam P e g =
        -CV.G3 P e f g / (CV.G5 P e f * CV.G5 P e g) ∧
    CV.crossParam P f e - CV.crossParam P f g =
        -CV.G3 P e f g / (CV.G5 P e f * CV.G5 P f g) ∧
    CV.crossParam P g e - CV.crossParam P g f =
        -CV.G3 P e f g / (CV.G5 P e g * CV.G5 P f g) := by
  have hef' : det (edge P e) (edge P f) ≠ 0 := hef
  have heg' : det (edge P e) (edge P g) ≠ 0 := heg
  have hfg' : det (edge P f) (edge P g) ≠ 0 := hfg
  have hfe : det (edge P f) (edge P e) ≠ 0 := by rw [det_swap]; exact neg_ne_zero.mpr hef'
  have hge : det (edge P g) (edge P e) ≠ 0 := by rw [det_swap]; exact neg_ne_zero.mpr heg'
  have hgf : det (edge P g) (edge P f) ≠ 0 := by rw [det_swap]; exact neg_ne_zero.mpr hfg'
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_div_iff (mul_ne_zero hef heg), ← CV.G4_eq_neg_G3, CV.G4_factorization P e f g hfe hge]
    unfold CV.G5
    rw [det_swap (edge P f) (edge P e), det_swap (edge P g) (edge P e)]
    ring
  · rw [eq_div_iff (mul_ne_zero hef hfg), ← CV.G4_swap_first_eq_G3,
      CV.G4_factorization P f e g hef' hgf]
    unfold CV.G5
    rw [det_swap (edge P g) (edge P f)]
    ring
  · rw [eq_div_iff (mul_ne_zero heg hfg), ← CV.G4_last_eq_neg_G3,
      CV.G4_factorization P g e f heg' hfg']
    unfold CV.G5
    ring

omit [NeZero n] in
/-- (2) `(q_e, q_f, q_g) = −δ (s_a s_b, s_a s_c, s_b s_c)`, from (1) by `sign_mul`/`sign_div`. -/
theorem sign_vector_of_ne (P : LabelledTuple n) (e f g : ZMod n)
    (hef : CV.G5 P e f ≠ 0) (heg : CV.G5 P e g ≠ 0) (hfg : CV.G5 P f g ≠ 0) :
    orderSign P e f g = -concurrenceSign P e f g * (strandSign P e f * strandSign P e g) ∧
    orderSign P f e g = -concurrenceSign P e f g * (strandSign P e f * strandSign P f g) ∧
    orderSign P g e f = -concurrenceSign P e f g * (strandSign P e g * strandSign P f g) := by
  obtain ⟨h1, h2, h3⟩ := cramer_of_ne P e f g hef heg hfg
  unfold orderSign concurrenceSign strandSign
  rw [h1, h2, h3]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [sign_div', sign_mul, Left.sign_neg]

/-! ### The event: the three bundle pairs cross near the wall, strand signs are constant -/

variable {E : CV.Event n} {e f g : ZMod n}

theorem g2_not_mem_zeroSet {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (a i : ZMod n) (h : i ≠ a ∧ i ≠ a + 1) : CV.Member.g2 a i h ∉ E.zeroSet := by
  rw [hE.1]; simp

theorem g5_not_mem_zeroSet {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (a b : ZMod n) (h : remote a b ∧ CV.rep a < CV.rep b) : CV.Member.g5 a b h ∉ E.zeroSet := by
  rw [hE.1]; simp

theorem g3_mem_zeroSet {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    CV.Member.g3 e f g h3 ∈ E.zeroSet := by
  rw [hE.1]; simp

/-- A punctured parameter of the event (`t = ε/2`). -/
theorem exists_punctured_parameter (E : CV.Event n) : ∃ t : E.Parameter, t.val ≠ 0 :=
  ⟨E.sideTime true E.sideBase, E.sideTime_ne_zero true E.sideBase⟩

/-- lem:guardconst in filter form: a relevant member outside `Z` keeps the sign of its central
value near the centre. -/
theorem eventually_sign_eq_of_not_mem (m : CV.Member n)
    (hrel : ∃ t : E.Parameter, t.val ≠ 0 ∧ m.Relevant (E.curve t)) (hZ : m ∉ E.zeroSet) :
    ∀ᶠ t in nhds E.zeroParameter, m.eval (E.curve t) ≠ 0 ∧
      SignType.sign (m.eval (E.curve t)) = SignType.sign (m.eval E.center) := by
  obtain ⟨-, ε, hε, hεr, h⟩ := CV.guardconst E m hrel hZ
  exact (E.eventually_center_iff_radius _).mpr ⟨ε, hε, hεr, h⟩

/-- The four `G2` members of a remote pair are unconditional and outside `Z`, so nonzero at the
centre: two edges meeting at an interior point at the centre are active there. -/
theorem crosses_center_of_interior {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    {a b : ZMod n} (hr : remote a b) {x : Plane}
    (hxa : x ∈ edgeInterior E.center a) (hxb : x ∈ edgeInterior E.center b) :
    CV.Crosses E.center a b := by
  obtain ⟨h0, h1, h2, h3'⟩ := remote_endpoints a b hr
  obtain ⟨t0, ht0⟩ := exists_punctured_parameter E
  have hne : ∀ (i j : ZMod n) (h : j ≠ i ∧ j ≠ i + 1), CV.G2 E.center i j ≠ 0 := fun i j h =>
    (CV.guardconst E (CV.Member.g2 i j h) ⟨t0, ht0, Or.inl (CV.Member.unconditional_g2 i j h)⟩
      (g2_not_mem_zeroSet hE i j h)).1
  refine CV.crosses_of_meet hr ⟨hne a b ⟨h0, h1⟩, hne a (b + 1) ⟨h2, h3'⟩,
    hne b a ⟨h0.symm, h2.symm⟩, hne b (a + 1) ⟨h1.symm, h3'.symm⟩⟩ ⟨x, ?_, ?_⟩
  · obtain ⟨s, hs0, hs1, rfl⟩ := hxa
    exact ⟨s, hs0.le, hs1.le, rfl⟩
  · obtain ⟨s, hs0, hs1, rfl⟩ := hxb
    exact ⟨s, hs0.le, hs1.le, rfl⟩

/-- At the centre the three bundle pairs are active (concurrency at a point interior to all three). -/
theorem crosses_center {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    CV.Crosses E.center e f ∧ CV.Crosses E.center f g ∧ CV.Crosses E.center e g := by
  obtain ⟨x, hxe, hxf, hxg⟩ := hE.2.1
  exact ⟨crosses_center_of_interior hE h3.1 hxe hxf, crosses_center_of_interior hE h3.2.1 hxf hxg,
    crosses_center_of_interior hE h3.2.2.1 hxe hxg⟩

/-- Activation of a remote pair active at the centre persists near the centre (the four `G2`
members keep their signs, lem:guardconst). -/
theorem eventually_crosses {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    {a b : ZMod n} (hr : remote a b) (hc : CV.Crosses E.center a b) :
    ∀ᶠ t in nhds E.zeroParameter, CV.Crosses (E.curve t) a b := by
  obtain ⟨h0, h1, h2, h3'⟩ := remote_endpoints a b hr
  obtain ⟨t0, ht0⟩ := exists_punctured_parameter E
  have ev : ∀ (i j : ZMod n) (h : j ≠ i ∧ j ≠ i + 1), ∀ᶠ t in nhds E.zeroParameter,
      SignType.sign (CV.G2 (E.curve t) i j) = SignType.sign (CV.G2 E.center i j) := fun i j h =>
    (eventually_sign_eq_of_not_mem (CV.Member.g2 i j h)
      ⟨t0, ht0, Or.inl (CV.Member.unconditional_g2 i j h)⟩
      (g2_not_mem_zeroSet hE i j h)).mono fun t ht => ht.2
  filter_upwards [ev a b ⟨h0, h1⟩, ev a (b + 1) ⟨h2, h3'⟩, ev b a ⟨h0.symm, h2.symm⟩,
    ev b (a + 1) ⟨h1.symm, h3'.symm⟩] with t e1 e2 e3 e4
  exact ⟨hr, (mul_neg_iff_of_sign_eq e1 e2).mpr hc.2.1, (mul_neg_iff_of_sign_eq e3 e4).mpr hc.2.2⟩

/-- A `G5` member active at the centre is active on a punctured parameter, hence relevant there and
outside `Z`: its sign near the centre is its central sign. -/
theorem eventually_strandSign_eq {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    {a b : ZMod n} (h : remote a b ∧ CV.rep a < CV.rep b) (hc : CV.Crosses E.center a b) :
    ∀ᶠ t in nhds E.zeroParameter, strandSign (E.curve t) a b = strandSign E.center a b := by
  obtain ⟨δ, hδ, hδr, hδc⟩ := (E.eventually_center_iff_radius _).mp (eventually_crosses hE h.1 hc)
  have ht0 : (⟨δ / 2, by constructor <;> linarith [E.radius_pos]⟩ : E.Parameter).val ≠ 0 :=
    (half_pos hδ).ne'
  have htc : CV.Crosses (E.curve ⟨δ / 2, by constructor <;> linarith [E.radius_pos]⟩) a b :=
    hδc _ (by rw [abs_of_pos (half_pos hδ)]; exact half_lt_self hδ)
  exact (eventually_sign_eq_of_not_mem (CV.Member.g5 a b h) ⟨_, ht0, Or.inr htc⟩
    (g5_not_mem_zeroSet hE a b h)).mono fun t ht => ht.2

/-- The radius data of unit G1: on `|t| < δ` the three bundle pairs cross and the three strand signs
equal their central values; `G3 ∈ Z` changes sign across the wall within `δ` (transversality). -/
structure GoodRadius (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  pos : 0 < δ
  le_radius : δ ≤ E.radius
  crosses : ∀ t : E.Parameter, |t.val| < δ →
    CV.Crosses (E.curve t) e f ∧ CV.Crosses (E.curve t) f g ∧ CV.Crosses (E.curve t) e g
  strand : ∀ t : E.Parameter, |t.val| < δ →
    strandSign (E.curve t) e f = strandSign E.center e f ∧
    strandSign (E.curve t) e g = strandSign E.center e g ∧
    strandSign (E.curve t) f g = strandSign E.center f g
  g3_flip : ∀ s : E.SideParameter, s.val < δ →
    CV.G3 (E.sideCurve true s) e f g * CV.G3 (E.sideCurve false s) e f g < 0

/-- The radius exists for every simple transversal RIII event. -/
theorem exists_goodRadius {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, GoodRadius E e f g δ := by
  obtain ⟨cef, cfg, ceg⟩ := crosses_center hE
  have hev : ∀ᶠ t in nhds E.zeroParameter,
      (CV.Crosses (E.curve t) e f ∧ CV.Crosses (E.curve t) f g ∧ CV.Crosses (E.curve t) e g) ∧
      (strandSign (E.curve t) e f = strandSign E.center e f ∧
        strandSign (E.curve t) e g = strandSign E.center e g ∧
        strandSign (E.curve t) f g = strandSign E.center f g) := by
    filter_upwards [eventually_crosses hE h3.1 cef, eventually_crosses hE h3.2.1 cfg,
      eventually_crosses hE h3.2.2.1 ceg,
      eventually_strandSign_eq hE ⟨h3.1, h3.2.2.2.1⟩ cef,
      eventually_strandSign_eq hE ⟨h3.2.2.1, h4f.2.2.2⟩ ceg,
      eventually_strandSign_eq hE ⟨h3.2.1, h3.2.2.2.2⟩ cfg] with t a1 a2 a3 b1 b2 b3
    exact ⟨⟨a1, a2, a3⟩, b1, b2, b3⟩
  obtain ⟨δ₁, hδ₁, hδ₁r, h1⟩ := (E.eventually_center_iff_radius _).mp hev
  obtain ⟨δ₂, hδ₂, -, h2⟩ := hE.2.2 _ (g3_mem_zeroSet hE)
  exact ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, (min_le_left _ _).trans hδ₁r,
    fun t ht => (h1 t (lt_of_lt_of_le ht (min_le_left _ _))).1,
    fun t ht => (h1 t (lt_of_lt_of_le ht (min_le_left _ _))).2,
    fun s hs => h2 s (lt_of_lt_of_le hs (min_le_right _ _))⟩

/-! ### Constant sign on one side of the wall (each side is connected) -/

/-- Within the radius, a continuous quantity that does not vanish on the punctured neighbourhood has
the same sign at any two parameters of one side. -/
theorem sign_eq_of_sameSide {δ : ℝ} (hδr : δ ≤ E.radius) (φ : LabelledTuple n → ℝ)
    (hφ : Continuous φ) (h0 : ∀ t : E.Parameter, Punctured E δ t → φ (E.curve t) ≠ 0)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hs : SameSide E t t') :
    SignType.sign (φ (E.curve t)) = SignType.sign (φ (E.curve t')) := by
  have key : ∀ a b : ℝ, -δ ≤ a → b ≤ δ → (0 ≤ a ∨ b ≤ 0) → a < t.val → t.val < b →
      a < t'.val → t'.val < b →
      SignType.sign (φ (E.curve t)) = SignType.sign (φ (E.curve t')) := by
    intro a b ha hb hab hat htb hat' htb'
    have hSc : IsPreconnected ((Subtype.val : E.Parameter → ℝ) ⁻¹' Set.Ioo a b) := by
      refine isPreconnected_Ioo.preimage_of_isOpenMap Subtype.val_injective
        isOpen_Ioo.isOpenMap_subtype_val ?_
      intro x hx
      exact ⟨⟨x, by constructor <;> linarith [hx.1, hx.2, E.radius_pos]⟩, rfl⟩
    have hpunct : ∀ u ∈ (Subtype.val : E.Parameter → ℝ) ⁻¹' Set.Ioo a b, Punctured E δ u := by
      intro u hu
      have h1 : a < u.val := hu.1
      have h2 : u.val < b := hu.2
      refine ⟨?_, ?_⟩
      · rcases hab with h | h
        · exact (show 0 < u.val by linarith).ne'
        · exact (show u.val < 0 by linarith).ne
      · rw [abs_lt]; constructor <;> linarith
    have hcont : ContinuousOn (fun u : E.Parameter => φ (E.curve u))
        ((Subtype.val : E.Parameter → ℝ) ⁻¹' Set.Ioo a b) :=
      (hφ.comp E.continuous_curve).continuousOn
    have hne : ∀ u ∈ (Subtype.val : E.Parameter → ℝ) ⁻¹' Set.Ioo a b, φ (E.curve u) ≠ 0 :=
      fun u hu => h0 u (hpunct u hu)
    have htS : t ∈ (Subtype.val : E.Parameter → ℝ) ⁻¹' Set.Ioo a b := ⟨hat, htb⟩
    have ht'S : t' ∈ (Subtype.val : E.Parameter → ℝ) ⁻¹' Set.Ioo a b := ⟨hat', htb'⟩
    have hpos : 0 < φ (E.curve t) * φ (E.curve t') := by
      rcases lt_or_gt_of_ne (hne t htS) with h1 | h1 <;>
        rcases lt_or_gt_of_ne (hne t' ht'S) with h2 | h2
      · exact mul_pos_of_neg_of_neg h1 h2
      · exfalso
        obtain ⟨u, hu, hu0⟩ := hSc.intermediate_value htS ht'S hcont ⟨h1.le, h2.le⟩
        exact hne u hu hu0
      · exfalso
        obtain ⟨u, hu, hu0⟩ := hSc.intermediate_value ht'S htS hcont ⟨h2.le, h1.le⟩
        exact hne u hu hu0
      · exact mul_pos h1 h2
    rcases mul_pos_iff.mp hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [sign_pos h1, sign_pos h2]
    · rw [sign_neg h1, sign_neg h2]
  obtain ⟨hta, htb⟩ := abs_lt.mp ht.2
  obtain ⟨hta', htb'⟩ := abs_lt.mp ht'.2
  rcases mul_pos_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key 0 δ (by linarith) le_rfl (Or.inl le_rfl) h1 htb h2 htb'
  · exact key (-δ) 0 le_rfl (by linarith) (Or.inr le_rfl) hta h1 hta' h2

/-! ### The fields -/

/-- `nonzero`: "All four quantities are nonzero on either chamber of a simple wall". -/
theorem nonzero {δ : ℝ} (hδ : GoodRadius E e f g δ) : ∀ t : E.Parameter, Punctured E δ t →
    CV.G5 (E.curve t) e f ≠ 0 ∧ CV.G5 (E.curve t) e g ≠ 0 ∧ CV.G5 (E.curve t) f g ≠ 0 ∧
      CV.G3 (E.curve t) e f g ≠ 0 := by
  intro t ht
  obtain ⟨cef, cfg, ceg⟩ := hδ.crosses t ht.2
  exact ⟨cef.det_ne_zero, ceg.det_ne_zero, cfg.det_ne_zero, (genericAt E t ht.1).g3 cef cfg ceg⟩

/-- `cramer`: the three identities (1). -/
theorem cramer {δ : ℝ} (hδ : GoodRadius E e f g δ) : ∀ t : E.Parameter, Punctured E δ t →
    CV.crossParam (E.curve t) e f - CV.crossParam (E.curve t) e g =
        -CV.G3 (E.curve t) e f g / (CV.G5 (E.curve t) e f * CV.G5 (E.curve t) e g) ∧
    CV.crossParam (E.curve t) f e - CV.crossParam (E.curve t) f g =
        -CV.G3 (E.curve t) e f g / (CV.G5 (E.curve t) e f * CV.G5 (E.curve t) f g) ∧
    CV.crossParam (E.curve t) g e - CV.crossParam (E.curve t) g f =
        -CV.G3 (E.curve t) e f g / (CV.G5 (E.curve t) e g * CV.G5 (E.curve t) f g) := by
  intro t ht
  obtain ⟨h1, h2, h3, -⟩ := nonzero hδ t ht
  exact cramer_of_ne _ e f g h1 h2 h3

/-- `sign_vector`: (2). -/
theorem sign_vector {δ : ℝ} (hδ : GoodRadius E e f g δ) : ∀ t : E.Parameter, Punctured E δ t →
    orderSign (E.curve t) e f g =
        -concurrenceSign (E.curve t) e f g * (strandSign (E.curve t) e f * strandSign (E.curve t) e g) ∧
    orderSign (E.curve t) f e g =
        -concurrenceSign (E.curve t) e f g * (strandSign (E.curve t) e f * strandSign (E.curve t) f g) ∧
    orderSign (E.curve t) g e f =
        -concurrenceSign (E.curve t) e f g * (strandSign (E.curve t) e g * strandSign (E.curve t) f g) := by
  intro t ht
  obtain ⟨h1, h2, h3, -⟩ := nonzero hδ t ht
  exact sign_vector_of_ne _ e f g h1 h2 h3

/-- The four signs are nonzero on the punctured neighbourhood. -/
theorem signs_ne_zero {δ : ℝ} (hδ : GoodRadius E e f g δ) (t : E.Parameter) (ht : Punctured E δ t) :
    strandSign (E.curve t) e f ≠ 0 ∧ strandSign (E.curve t) e g ≠ 0 ∧
      strandSign (E.curve t) f g ≠ 0 ∧ concurrenceSign (E.curve t) e f g ≠ 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := nonzero hδ t ht
  exact ⟨sign_ne_zero.mpr h1, sign_ne_zero.mpr h2, sign_ne_zero.mpr h3, sign_ne_zero.mpr h4⟩

/-- `δ` flips across the wall: `G3 ∈ Z` changes sign (transversality) and has constant sign on each
side (`nonzero` + connectedness). -/
theorem concurrenceSign_flip {δ : ℝ} (hδ : GoodRadius E e f g δ) {t t' : E.Parameter}
    (ht : Punctured E δ t) (ht' : Punctured E δ t') (hs : OppositeSides E t t') :
    concurrenceSign (E.curve t') e f g = -concurrenceSign (E.curve t) e f g := by
  have h0 : ∀ u : E.Parameter, Punctured E δ u → CV.G3 (E.curve u) e f g ≠ 0 :=
    fun u hu => (nonzero hδ u hu).2.2.2
  have hcont : Continuous fun P : LabelledTuple n => CV.G3 P e f g := CV.continuous_G3 e f g
  -- the symmetric pair `±|t|`
  let s : E.SideParameter := ⟨|t.val|, abs_pos.mpr ht.1, lt_of_lt_of_le ht.2 hδ.le_radius⟩
  have hflip := hδ.g3_flip s ht.2
  have hp_val : (E.sideTime true s).val = |t.val| := rfl
  have hm_val : (E.sideTime false s).val = -|t.val| := rfl
  have hp : Punctured E δ (E.sideTime true s) := by
    refine ⟨?_, ?_⟩ <;> rw [hp_val]
    · exact (abs_pos.mpr ht.1).ne'
    · rw [abs_abs]; exact ht.2
  have hm : Punctured E δ (E.sideTime false s) := by
    refine ⟨?_, ?_⟩ <;> rw [hm_val]
    · exact (neg_ne_zero.mpr (abs_pos.mpr ht.1).ne')
    · rw [abs_neg, abs_abs]; exact ht.2
  have hsign : SignType.sign (CV.G3 (E.curve (E.sideTime false s)) e f g) =
      -SignType.sign (CV.G3 (E.curve (E.sideTime true s)) e f g) := by
    apply eq_neg_of_mul_eq_neg_one_abstract
    rw [← sign_mul, sign_eq_neg_one_iff]
    exact hflip
  unfold concurrenceSign
  rcases mul_neg_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `t > 0 > t'`: `t = |t|`, `t'` on the side of `−|t|`
    have hteq : E.sideTime true s = t := Subtype.ext (by rw [hp_val, abs_of_pos h1])
    have hsame : SameSide E t' (E.sideTime false s) := by
      show 0 < t'.val * (E.sideTime false s).val
      rw [hm_val]; exact mul_pos_of_neg_of_neg h2 (neg_neg_of_pos (abs_pos.mpr ht.1))
    rw [← hteq, sign_eq_of_sameSide hδ.le_radius _ hcont h0 ht' hm hsame, hsign]
  · -- `t < 0 < t'`: `t = −|t|`, `t'` on the side of `|t|`
    have hteq : E.sideTime false s = t := Subtype.ext (by rw [hm_val, abs_of_neg h1, neg_neg])
    have hsame : SameSide E t' (E.sideTime true s) := by
      show 0 < t'.val * (E.sideTime true s).val
      rw [hp_val]; exact mul_pos h2 (abs_pos.mpr ht.1)
    rw [← hteq, sign_eq_of_sameSide hδ.le_radius _ hcont h0 ht' hp hsame, hsign, neg_neg]

/-- `chamber_change`: "Changing chamber changes the sign of `Delta`, so (2) negates all three `q`'s"
— with the three strand signs unchanged (lem:guardconst on the active `G5` members). -/
theorem chamber_change {δ : ℝ} (hδ : GoodRadius E e f g δ) :
    ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' → OppositeSides E t t' →
    concurrenceSign (E.curve t') e f g = -concurrenceSign (E.curve t) e f g ∧
    (strandSign (E.curve t') e f = strandSign (E.curve t) e f ∧
      strandSign (E.curve t') e g = strandSign (E.curve t) e g ∧
      strandSign (E.curve t') f g = strandSign (E.curve t) f g) ∧
    (orderSign (E.curve t') e f g = -orderSign (E.curve t) e f g ∧
      orderSign (E.curve t') f e g = -orderSign (E.curve t) f e g ∧
      orderSign (E.curve t') g e f = -orderSign (E.curve t) g e f) := by
  intro t t' ht ht' hs
  have hc := concurrenceSign_flip hδ ht ht' hs
  obtain ⟨s1, s2, s3⟩ := hδ.strand t ht.2
  obtain ⟨s1', s2', s3'⟩ := hδ.strand t' ht'.2
  have hst : strandSign (E.curve t') e f = strandSign (E.curve t) e f ∧
      strandSign (E.curve t') e g = strandSign (E.curve t) e g ∧
      strandSign (E.curve t') f g = strandSign (E.curve t) f g :=
    ⟨s1'.trans s1.symm, s2'.trans s2.symm, s3'.trans s3.symm⟩
  obtain ⟨q1, q2, q3⟩ := sign_vector hδ t ht
  obtain ⟨q1', q2', q3'⟩ := sign_vector hδ t' ht'
  refine ⟨hc, hst, ?_, ?_, ?_⟩
  · rw [q1', q1, hc, hst.1, hst.2.1]; exact neg_neg_mul_abstract _ _ _
  · rw [q2', q2, hc, hst.1, hst.2.2]; exact neg_neg_mul_abstract _ _ _
  · rw [q3', q3, hc, hst.2.1, hst.2.2]; exact neg_neg_mul_abstract _ _ _

/-! ### `edges_iff`: the local edges read off the traversal keys

The six triangle visits sit on the edges `e, f, g`, whose values are in cyclic order (`e < f < g` in
representatives; the traversal cut at value `0` is either after `g` or at `g`). Two visits on
different bundle edges compare by edge value; two visits on the same bundle edge compare by their
parameters `t_ij = crossParam P i j`. CV:def:interlace ("exactly one occurrence between") is then a
finite check of the three-way `traversalBetween` disjunctions. No adjacency is needed. -/

section Keys

variable {P : LabelledTuple n}

omit [NeZero n] in
theorem visitParameter_visitOn_left (hP : CrossingGeometry P) {i j : ZMod n}
    (h : IsCrossing P {i, j}) :
    visitParameter (visitOn (xPair h) i (mem_pair_left i j)) = CV.crossParam P i j := by
  rw [CV.crossParam_eq_edgeParameter]
  exact visitParameter_eq_of_support_pair_of_geometry hP _ j rfl

omit [NeZero n] in
theorem visitParameter_visitOn_right (hP : CrossingGeometry P) {i j : ZMod n}
    (h : IsCrossing P {i, j}) :
    visitParameter (visitOn (xPair h) j (mem_pair_right i j)) = CV.crossParam P j i := by
  rw [CV.crossParam_eq_edgeParameter]
  exact visitParameter_eq_of_support_pair_of_geometry hP _ i (Finset.pair_comm i j)

omit [NeZero n] in
theorem key_lt_of_val_lt (hP : CrossingGeometry P) {v w : Visit P}
    (h : v.2.val.val < w.2.val.val) :
    traversalKey (geometricVisitPosition hP v) < traversalKey (geometricVisitPosition hP w) :=
  traversalKey_lt_of_edge_lt h

theorem key_lt_iff_of_edge_eq (hP : CrossingGeometry P) {v w : Visit P} (h : v.2.val = w.2.val) :
    traversalKey (geometricVisitPosition hP v) < traversalKey (geometricVisitPosition hP w) ↔
      visitParameter v < visitParameter w := by
  rw [traversalKey_lt_iff]
  constructor
  · rintro (h1 | ⟨-, h2⟩)
    · exact absurd h1 (by show ¬ v.2.val.val < w.2.val.val; rw [h]; exact lt_irrefl _)
    · exact h2
  · intro h2
    exact Or.inr ⟨h, h2⟩

end Keys

theorem val_eq_rep_of_lt {i : ZMod n} (h : CV.rep i < n) : i.val = CV.rep i := by
  conv_lhs => rw [← CV.rep_cast i]
  exact ZMod.val_natCast_of_lt h

theorem val_eq_zero_of_rep_eq {i : ZMod n} (h : CV.rep i = n) : i.val = 0 := by
  rw [← CV.rep_cast i, h, ZMod.natCast_self, ZMod.val_zero]

/-- `e < f < g` in representatives: the edge values are in the cyclic order `e, f, g` — either
`e < f < g` as values, or the cut is at `g` (`g = 0 < e < f`). -/
theorem val_order (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧
    CV.rep f < CV.rep g) :
    e.val < f.val ∧ (f.val < g.val ∨ (g.val < e.val ∧ g.val < f.val)) := by
  have hg := CV.rep_le g
  have he : CV.rep e < n := lt_of_lt_of_le (h3.2.2.2.1.trans h3.2.2.2.2) hg
  have hf : CV.rep f < n := lt_of_lt_of_le h3.2.2.2.2 hg
  rw [val_eq_rep_of_lt he, val_eq_rep_of_lt hf]
  refine ⟨h3.2.2.2.1, ?_⟩
  rcases lt_or_eq_of_le hg with hg' | hg'
  · rw [val_eq_rep_of_lt hg']
    exact Or.inl h3.2.2.2.2
  · rw [val_eq_zero_of_rep_eq hg']
    exact Or.inr ⟨CV.rep_pos e, CV.rep_pos f⟩

theorem existsUnique_iff_of_two {α : Type*} {p : α → Prop} {i j : α}
    (hex : ∀ k, k = i ∨ k = j) (hj : ¬ p j) : (∃! k, p k) ↔ p i := by
  constructor
  · rintro ⟨k, hk, -⟩
    rcases hex k with rfl | rfl
    · exact hk
    · exact (hj hk).elim
  · intro hi
    refine ⟨i, hi, fun k hk => ?_⟩
    rcases hex k with rfl | rfl
    · rfl
    · exact (hj hk).elim

theorem existsUnique_iff_of_two' {α : Type*} {p : α → Prop} {i j : α} (hij : i ≠ j)
    (hex : ∀ k, k = i ∨ k = j) (hi : p i) : (∃! k, p k) ↔ ¬ p j := by
  constructor
  · rintro ⟨k, -, huniq⟩ hj
    exact hij ((huniq i hi).trans (huniq j hj).symm)
  · intro hj
    refine ⟨i, hi, fun k hk => ?_⟩
    rcases hex k with rfl | rfl
    · rfl
    · exact (hj hk).elim


omit [NeZero n] in
theorem pair_ne_of_left_not_mem {i j k l : ZMod n} (hi : i ∉ ({k, l} : Finset (ZMod n))) :
    ({i, j} : Finset (ZMod n)) ≠ {k, l} := fun h => hi (h ▸ mem_pair_left i j)

omit [NeZero n] in
theorem pair_ne_of_right_not_mem {i j k l : ZMod n} (hj : j ∉ ({k, l} : Finset (ZMod n))) :
    ({i, j} : Finset (ZMod n)) ≠ {k, l} := fun h => hj (h ▸ mem_pair_right i j)

/-! The three-way disjunction `traversalBetween p q r` under known key comparisons. -/
section Between

variable {p q r : TraversalPoint n}

omit [NeZero n] in
theorem between_of_lt_lt (h1 : traversalKey p < traversalKey q)
    (h2 : traversalKey q < traversalKey r) : traversalBetween p q r := Or.inl ⟨h1, h2⟩

omit [NeZero n] in
theorem between_of_lt_lt' (h1 : traversalKey r < traversalKey p)
    (h2 : traversalKey p < traversalKey q) : traversalBetween p q r := Or.inr (Or.inr ⟨h1, h2⟩)

omit [NeZero n] in
theorem not_between_of_lt_lt (h1 : traversalKey p < traversalKey r)
    (h2 : traversalKey r < traversalKey q) : ¬ traversalBetween p q r := by
  unfold traversalBetween
  rintro (⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩) <;> linarith

omit [NeZero n] in
theorem not_between_of_lt_lt' (h1 : traversalKey q < traversalKey p)
    (h2 : traversalKey p < traversalKey r) : ¬ traversalBetween p q r := by
  unfold traversalBetween
  rintro (⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩) <;> linarith

omit [NeZero n] in
theorem between_iff_first (h1 : traversalKey p < traversalKey r)
    (h2 : traversalKey q < traversalKey r) :
    traversalBetween p q r ↔ traversalKey p < traversalKey q := by
  unfold traversalBetween
  constructor
  · rintro (⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩)
    · exact a
    · linarith
    · linarith
  · intro h
    exact Or.inl ⟨h, h2⟩

omit [NeZero n] in
theorem between_iff_second (h1 : traversalKey p < traversalKey r)
    (h2 : traversalKey p < traversalKey q) :
    traversalBetween p q r ↔ traversalKey q < traversalKey r := by
  unfold traversalBetween
  constructor
  · rintro (⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩)
    · exact b
    · linarith
    · linarith
  · intro h
    exact Or.inl ⟨h2, h⟩

omit [NeZero n] in
theorem between_iff_second' (h1 : traversalKey r < traversalKey p)
    (h2 : traversalKey q < traversalKey p) :
    traversalBetween p q r ↔ traversalKey q < traversalKey r := by
  unfold traversalBetween
  constructor
  · rintro (⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩)
    · linarith
    · exact a
    · linarith
  · intro h
    exact Or.inr (Or.inl ⟨h, h1⟩)

end Between

/-- (3) on any CV-generic polygon carrying the three crossings, with `e < f < g` in representatives:
`ab ↔ q_e = −1`, `ac ↔ q_f = +1`, `bc ↔ q_g = −1` — read off the traversal keys of the six visits. -/
theorem edges_iff_of_generic {P : LabelledTuple n}
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (hG : CV.Generic P) (hP : CrossingGeometry P)
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) :
    (EdgeAB hP hef heg ↔ orderSign P e f g = -1) ∧
    (EdgeAC hP hef hfg ↔ orderSign P f e g = 1) ∧
    (EdgeBC hP heg hfg ↔ orderSign P g e f = -1) := by
  -- distinct labels and their cyclic value order
  have hfe : f ≠ e := (remote_endpoints e f h3.1).1
  have hgf : g ≠ f := (remote_endpoints f g h3.2.1).1
  have hge : g ≠ e := (remote_endpoints e g h3.2.2.1).1
  obtain ⟨hef_val, hcyc⟩ := val_order h3
  -- the three crossings and their six visits
  let a : Crossing P := xPair hef
  let b : Crossing P := xPair heg
  let c : Crossing P := xPair hfg
  let ae : {i // i ∈ a.val} := ⟨e, mem_pair_left e f⟩
  let af : {i // i ∈ a.val} := ⟨f, mem_pair_right e f⟩
  let be : {i // i ∈ b.val} := ⟨e, mem_pair_left e g⟩
  let bg : {i // i ∈ b.val} := ⟨g, mem_pair_right e g⟩
  let cf : {i // i ∈ c.val} := ⟨f, mem_pair_left f g⟩
  let cg : {i // i ∈ c.val} := ⟨g, mem_pair_right f g⟩
  have hae_af : ae ≠ af := fun h => hfe (congrArg Subtype.val h).symm
  have hbe_bg : be ≠ bg := fun h => hge (congrArg Subtype.val h).symm
  have hcf_cg : cf ≠ cg := fun h => hgf (congrArg Subtype.val h).symm
  have hab : a ≠ b := fun h => pair_ne_of_right_not_mem (i := e) (j := f) (k := e) (l := g)
    (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hfe, hgf.symm⟩)
    (congrArg Subtype.val h)
  have hac : a ≠ c := fun h => pair_ne_of_left_not_mem (i := e) (j := f) (k := f) (l := g)
    (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hfe.symm, hge.symm⟩)
    (congrArg Subtype.val h)
  have hbc : b ≠ c := fun h => pair_ne_of_left_not_mem (i := e) (j := g) (k := f) (l := g)
    (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hfe.symm, hge.symm⟩)
    (congrArg Subtype.val h)
  -- the visit parameters are the printed `t_ij`
  have pae : visitParameter (⟨a, ae⟩ : Visit P) = CV.crossParam P e f :=
    visitParameter_visitOn_left hP hef
  have paf : visitParameter (⟨a, af⟩ : Visit P) = CV.crossParam P f e :=
    visitParameter_visitOn_right hP hef
  have pbe : visitParameter (⟨b, be⟩ : Visit P) = CV.crossParam P e g :=
    visitParameter_visitOn_left hP heg
  have pbg : visitParameter (⟨b, bg⟩ : Visit P) = CV.crossParam P g e :=
    visitParameter_visitOn_right hP heg
  have pcf : visitParameter (⟨c, cf⟩ : Visit P) = CV.crossParam P f g :=
    visitParameter_visitOn_left hP hfg
  have pcg : visitParameter (⟨c, cg⟩ : Visit P) = CV.crossParam P g f :=
    visitParameter_visitOn_right hP hfg
  -- keys across the edges `e < f`
  have kAE_AF := key_lt_of_val_lt hP (v := ⟨a, ae⟩) (w := ⟨a, af⟩) hef_val
  have kBE_AF := key_lt_of_val_lt hP (v := ⟨b, be⟩) (w := ⟨a, af⟩) hef_val
  have kAE_CF := key_lt_of_val_lt hP (v := ⟨a, ae⟩) (w := ⟨c, cf⟩) hef_val
  have kBE_CF := key_lt_of_val_lt hP (v := ⟨b, be⟩) (w := ⟨c, cf⟩) hef_val
  -- the order signs as parameter comparisons
  have hq_e : orderSign P e f g = -1 ↔ CV.crossParam P e f < CV.crossParam P e g := by
    unfold orderSign; rw [sign_eq_neg_one_iff, sub_neg]
  have hq_f : orderSign P f e g = 1 ↔ CV.crossParam P f g < CV.crossParam P f e := by
    unfold orderSign; rw [sign_eq_one_iff, sub_pos]
  have hq_g : orderSign P g e f = -1 ↔ CV.crossParam P g e < CV.crossParam P g f := by
    unfold orderSign; rw [sign_eq_neg_one_iff, sub_neg]
  -- no tie along `g` (CV-generic: `G4_{g;e,f} ≠ 0`)
  have hne_g : CV.crossParam P g e ≠ CV.crossParam P g f :=
    hG.crossParam_ne ((hG.crosses_iff g e).mpr (by rw [Finset.pair_comm]; exact heg))
      ((hG.crosses_iff g f).mpr (by rw [Finset.pair_comm]; exact hfg)) hfe.symm
  -- the between-relations of the six visits
  have hAB : geometricCrossingVisitBetween hP a ae af b be ↔
      CV.crossParam P e f < CV.crossParam P e g :=
    (between_iff_first kAE_AF kBE_AF).trans
      ((key_lt_iff_of_edge_eq hP (v := ⟨a, ae⟩) (w := ⟨b, be⟩) rfl).trans (by rw [pae, pbe]))
  have hAB' : ¬ geometricCrossingVisitBetween hP a ae af b bg := by
    rcases hcyc with h | ⟨h, -⟩
    · exact not_between_of_lt_lt kAE_AF (key_lt_of_val_lt hP (v := ⟨a, af⟩) (w := ⟨b, bg⟩) h)
    · exact not_between_of_lt_lt' (key_lt_of_val_lt hP (v := ⟨b, bg⟩) (w := ⟨a, ae⟩) h) kAE_AF
  have hAC : geometricCrossingVisitBetween hP a ae af c cf ↔
      CV.crossParam P f g < CV.crossParam P f e :=
    (between_iff_second kAE_AF kAE_CF).trans
      ((key_lt_iff_of_edge_eq hP (v := ⟨c, cf⟩) (w := ⟨a, af⟩) rfl).trans (by rw [pcf, paf]))
  have hAC' : ¬ geometricCrossingVisitBetween hP a ae af c cg := by
    rcases hcyc with h | ⟨h, -⟩
    · exact not_between_of_lt_lt kAE_AF (key_lt_of_val_lt hP (v := ⟨a, af⟩) (w := ⟨c, cg⟩) h)
    · exact not_between_of_lt_lt' (key_lt_of_val_lt hP (v := ⟨c, cg⟩) (w := ⟨a, ae⟩) h) kAE_AF
  have hBC : geometricCrossingVisitBetween hP b be bg c cf := by
    rcases hcyc with h | ⟨h, -⟩
    · exact between_of_lt_lt kBE_CF (key_lt_of_val_lt hP (v := ⟨c, cf⟩) (w := ⟨b, bg⟩) h)
    · exact between_of_lt_lt' (key_lt_of_val_lt hP (v := ⟨b, bg⟩) (w := ⟨b, be⟩) h) kBE_CF
  have hBC' : geometricCrossingVisitBetween hP b be bg c cg ↔
      CV.crossParam P g f < CV.crossParam P g e := by
    refine Iff.trans ?_
      ((key_lt_iff_of_edge_eq hP (v := ⟨c, cg⟩) (w := ⟨b, bg⟩) rfl).trans (by rw [pcg, pbg]))
    rcases hcyc with h | ⟨h, -⟩
    · exact between_iff_second
        (key_lt_of_val_lt hP (v := ⟨b, be⟩) (w := ⟨b, bg⟩) (hef_val.trans h))
        (key_lt_of_val_lt hP (v := ⟨b, be⟩) (w := ⟨c, cg⟩) (hef_val.trans h))
    · exact between_iff_second'
        (key_lt_of_val_lt hP (v := ⟨b, bg⟩) (w := ⟨b, be⟩) h)
        (key_lt_of_val_lt hP (v := ⟨c, cg⟩) (w := ⟨b, be⟩) h)
  refine ⟨?_, ?_, ?_⟩
  · show GeometricInterlaces hP a b ↔ _
    rw [CV.geometricInterlaces_iff_unique hP a b ae af hae_af, and_iff_right hab,
      existsUnique_iff_of_two (p := fun k => geometricCrossingVisitBetween hP a ae af b k)
        (crossing_visits_exhaust b be bg hbe_bg) hAB', hAB, hq_e]
  · show GeometricInterlaces hP a c ↔ _
    rw [CV.geometricInterlaces_iff_unique hP a c ae af hae_af, and_iff_right hac,
      existsUnique_iff_of_two (p := fun k => geometricCrossingVisitBetween hP a ae af c k)
        (crossing_visits_exhaust c cf cg hcf_cg) hAC', hAC, hq_f]
  · show GeometricInterlaces hP b c ↔ _
    rw [CV.geometricInterlaces_iff_unique hP b c be bg hbe_bg, and_iff_right hbc,
      existsUnique_iff_of_two' (p := fun k => geometricCrossingVisitBetween hP b be bg c k) hcf_cg
        (crossing_visits_exhaust c cf cg hcf_cg) hBC, hBC', hq_g]
    exact ⟨fun h => lt_of_le_of_ne (not_lt.mp h) hne_g, fun h => not_lt.mpr h.le⟩

/-- `edges_iff` (3), for every punctured parameter (no radius needed beyond `t ≠ 0`). -/
theorem edges_iff (E : CV.Event n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (δ : ℝ) : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    (EdgeAB (geomAt E t ht.1) hef heg ↔ orderSign (E.curve t) e f g = -1) ∧
    (EdgeAC (geomAt E t ht.1) hef hfg ↔ orderSign (E.curve t) f e g = 1) ∧
    (EdgeBC (geomAt E t ht.1) heg hfg ↔ orderSign (E.curve t) g e f = -1) :=
  fun t ht hef heg hfg => edges_iff_of_generic h3 (genericAt E t ht.1) (geomAt E t ht.1) hef heg hfg

/-! ### The derived classification fields -/

theorem orderSigns_ne_zero {δ : ℝ} (hδ : GoodRadius E e f g δ) (t : E.Parameter)
    (ht : Punctured E δ t) :
    orderSign (E.curve t) e f g ≠ 0 ∧ orderSign (E.curve t) f e g ≠ 0 ∧
      orderSign (E.curve t) g e f ≠ 0 := by
  obtain ⟨q1, q2, q3⟩ := sign_vector hδ t ht
  obtain ⟨s1, s2, s3, s4⟩ := signs_ne_zero hδ t ht
  rw [q1, q2, q3]
  exact ⟨neg_mul_ne_zero_abstract _ _ _ s4 s1 s2, neg_mul_ne_zero_abstract _ _ _ s4 s1 s3,
    neg_mul_ne_zero_abstract _ _ _ s4 s2 s3⟩

/-- `extreme_iff_orders`: "The local graph is extreme exactly when all three indicators in (3)
agree. That requires `(q_e,q_f,q_g)` to be `(−,+,−)` or `(+,−,+)`." -/
theorem extreme_iff_orders
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    {δ : ℝ} (hδ : GoodRadius E e f g δ) : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ExtremeLocal (geomAt E t ht.1) hef heg hfg ↔
      ((orderSign (E.curve t) e f g = -1 ∧ orderSign (E.curve t) f e g = 1 ∧
          orderSign (E.curve t) g e f = -1) ∨
        (orderSign (E.curve t) e f g = 1 ∧ orderSign (E.curve t) f e g = -1 ∧
          orderSign (E.curve t) g e f = 1)) := by
  intro t ht hef heg hfg
  obtain ⟨h1, h2, h3'⟩ := edges_iff E h3 δ t ht hef heg hfg
  obtain ⟨n1, n2, n3⟩ := orderSigns_ne_zero hδ t ht
  unfold ExtremeLocal
  rw [h1, h2, h3']
  exact extreme_iff_orders_abstract _ _ _ n1 n2 n3

/-- `extreme_iff_alternating`: "… equivalent to `s_a = s_c = −s_b`, namely one of the two
alternating sign triples." -/
theorem extreme_iff_alternating
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    {δ : ℝ} (hδ : GoodRadius E e f g δ) : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ExtremeLocal (geomAt E t ht.1) hef heg hfg ↔
      IsAlternating (strandSign (E.curve t) e f) (strandSign (E.curve t) e g)
        (strandSign (E.curve t) f g) := by
  intro t ht hef heg hfg
  rw [extreme_iff_orders h3 hδ t ht hef heg hfg]
  obtain ⟨q1, q2, q3⟩ := sign_vector hδ t ht
  obtain ⟨s1, s2, s3, s4⟩ := signs_ne_zero hδ t ht
  rw [q1, q2, q3]
  exact orders_iff_alternating_abstract _ _ _ _ s4 s1 s2 s3

/-- `generic_iff_nonalternating`: "Therefore the generic orbit is exactly the other six,
nonalternating triples." -/
theorem generic_iff_nonalternating
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    {δ : ℝ} (hδ : GoodRadius E e f g δ) : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg ↔
      ¬ IsAlternating (strandSign (E.curve t) e f) (strandSign (E.curve t) e g)
        (strandSign (E.curve t) f g) :=
  fun t ht hef heg hfg => not_congr (extreme_iff_alternating h3 hδ t ht hef heg hfg)

/-- `selected_is_graph_selected`: (4) "the unique separating-strand pair is precisely the
graph-selected pair". -/
theorem selected_is_graph_selected
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    {δ : ℝ} (hδ : GoodRadius E e f g δ) : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    (SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g) ↔
      ((EdgeAB (geomAt E t ht.1) hef heg ∧ EdgeBC (geomAt E t ht.1) heg hfg) ∨
        (EdgeAC (geomAt E t ht.1) hef hfg ∧ ¬ EdgeAB (geomAt E t ht.1) hef heg ∧
          ¬ EdgeBC (geomAt E t ht.1) heg hfg))) ∧
    (SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) ↔
      ((EdgeAC (geomAt E t ht.1) hef hfg ∧ EdgeBC (geomAt E t ht.1) heg hfg) ∨
        (EdgeAB (geomAt E t ht.1) hef heg ∧ ¬ EdgeAC (geomAt E t ht.1) hef hfg ∧
          ¬ EdgeBC (geomAt E t ht.1) heg hfg))) ∧
    (SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g) ↔
      ((EdgeAB (geomAt E t ht.1) hef heg ∧ EdgeAC (geomAt E t ht.1) hef hfg) ∨
        (EdgeBC (geomAt E t ht.1) heg hfg ∧ ¬ EdgeAB (geomAt E t ht.1) hef heg ∧
          ¬ EdgeAC (geomAt E t ht.1) hef hfg))) := by
  intro t ht hef heg hfg hgen
  have halt := (generic_iff_nonalternating h3 hδ t ht hef heg hfg).mp hgen
  obtain ⟨h1, h2, h3'⟩ := edges_iff E h3 δ t ht hef heg hfg
  obtain ⟨q1, q2, q3⟩ := sign_vector hδ t ht
  obtain ⟨s1, s2, s3, s4⟩ := signs_ne_zero hδ t ht
  rw [h1, h2, h3', q1, q2, q3]
  exact selected_abstract _ _ _ _ s4 s1 s2 s3 halt

/-! ### The sign-classification fields under one radius -/

/-- The radius of unit G1 as the row theorem needs it (`0 < δ ≤ E.radius`). With `hδ` the
eleven sign-classification fields of `GenericTableData` are discharged verbatim by
`G1.nonzero hδ`, `G1.cramer hδ`, `G1.sign_vector hδ`, `G1.edges_iff E h3 δ`, `G1.chamber_change hδ`,
`G1.extreme_iff_orders h3 hδ`, `G1.extreme_iff_alternating h3 hδ`,
`G1.generic_iff_nonalternating h3 hδ`, `G1.branch_count`, `G1.selected_unique`,
`G1.selected_is_graph_selected h3 hδ` (checked by a test assembly, 2026-09-14). -/
theorem sign_classification (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GoodRadius E e f g δ := by
  obtain ⟨δ, hδ⟩ := exists_goodRadius hE
  exact ⟨δ, hδ.pos, hδ.le_radius, hδ⟩

end G1


/-! ## Unit G2 — the local word, the canonical words, the local supports and undominated sets, and
the mask sharpening of R:generic_table (proof lane, 2026-09-14)

Standalone lemmas `RProof.G2.<field>`, each stated with exactly the field's type. `local_word` and
`canonical_words` need only `h3` (and, for the canonical branch, the radius data `G1.GoodRadius`);
`local_supports` and `local_undominated` are read off `canonical_words` and `CV.mem_Ind_iff` /
`CV.mem_U`; `mask_sharpening` consumes the parity row (`ParityData.parity`,
`ParityData.interlaced_pair`), taken as an explicit hypothesis. Nothing in the fixed statements above
is changed. -/

namespace G2

variable {P : LabelledTuple n} {e f g : ZMod n}

/-! ### The triangle: its three crossings and six visits -/

theorem mem_triangleCrossings_iff (x : Crossing P) :
    x ∈ triangleCrossings P e f g ↔ x.val ∈ triangleSupports e f g := by
  simp [triangleCrossings]

omit [NeZero n] in
theorem xPair_ne_xPair {i j k l : ZMod n} (hij : IsCrossing P {i, j}) (hkl : IsCrossing P {k, l})
    (h : ({i, j} : Finset (ZMod n)) ≠ {k, l}) : xPair hij ≠ xPair hkl :=
  fun h' => h (congrArg Subtype.val h')

omit [NeZero n] in
/-- The three triangle crossings are distinct once the labels are. -/
theorem xPairs_ne (hfe : f ≠ e) (hgf : g ≠ f) (hge : g ≠ e)
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) :
    xPair hef ≠ xPair heg ∧ xPair hef ≠ xPair hfg ∧ xPair heg ≠ xPair hfg := by
  refine ⟨xPair_ne_xPair hef heg (G1.pair_ne_of_right_not_mem ?_),
    xPair_ne_xPair hef hfg (G1.pair_ne_of_left_not_mem ?_),
    xPair_ne_xPair heg hfg (G1.pair_ne_of_left_not_mem ?_)⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  · exact ⟨hfe, hgf.symm⟩
  · exact ⟨hfe.symm, hge.symm⟩
  · exact ⟨hfe.symm, hge.symm⟩

omit [NeZero n] in
theorem eq_xPair_of_val_mem (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) (x : Crossing P) (hx : x.val ∈ triangleSupports e f g) :
    x = xPair hef ∨ x = xPair heg ∨ x = xPair hfg := by
  simp only [triangleSupports, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Subtype.ext h))

omit [NeZero n] in
theorem val_mem_triangleSupports_iff (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) (x : Crossing P) :
    x.val ∈ triangleSupports e f g ↔ x = xPair hef ∨ x = xPair heg ∨ x = xPair hfg := by
  refine ⟨eq_xPair_of_val_mem hef heg hfg x, ?_⟩
  rintro (rfl | rfl | rfl) <;> simp [triangleSupports, xPair]

theorem triangleCrossings_eq (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) :
    triangleCrossings P e f g = {xPair hef, xPair heg, xPair hfg} := by
  ext x
  rw [mem_triangleCrossings_iff, val_mem_triangleSupports_iff hef heg hfg]
  simp only [Finset.mem_insert, Finset.mem_singleton]

omit [NeZero n] in
/-- A visit of a triangle crossing is one of the six printed visits. -/
theorem eq_visit_of_val_mem (hfe : f ≠ e) (hgf : g ≠ f) (hge : g ≠ e)
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    (v : Visit P) (hv : v.1.val ∈ triangleSupports e f g) :
    v = visitOn (xPair hef) e (mem_pair_left e f) ∨ v = visitOn (xPair hef) f (mem_pair_right e f) ∨
    v = visitOn (xPair heg) e (mem_pair_left e g) ∨ v = visitOn (xPair heg) g (mem_pair_right e g) ∨
    v = visitOn (xPair hfg) f (mem_pair_left f g) ∨ v = visitOn (xPair hfg) g (mem_pair_right f g) := by
  obtain ⟨c, i⟩ := v
  rcases eq_xPair_of_val_mem hef heg hfg c hv with rfl | rfl | rfl
  · rcases crossing_visits_exhaust (xPair hef) ⟨e, mem_pair_left e f⟩ ⟨f, mem_pair_right e f⟩
        (fun h => hfe (congrArg Subtype.val h).symm) i with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rcases crossing_visits_exhaust (xPair heg) ⟨e, mem_pair_left e g⟩ ⟨g, mem_pair_right e g⟩
        (fun h => hge (congrArg Subtype.val h).symm) i with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · rcases crossing_visits_exhaust (xPair hfg) ⟨f, mem_pair_left f g⟩ ⟨g, mem_pair_right f g⟩
        (fun h => hgf (congrArg Subtype.val h).symm) i with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-! ### The Gauss list is sorted by the traversal key -/

/-- The Gauss list is strictly increasing in the traversal key. -/
theorem gaussList_pairwise_key (hP : CrossingGeometry P) :
    (geometricGaussList hP).Pairwise fun v w =>
      traversalKey (geometricVisitPosition hP v) < traversalKey (geometricVisitPosition hP w) := by
  classical
  let _ := geometricVisitLinearOrder hP
  exact (Finset.sortedLT_sort (Finset.univ : Finset (Visit P))).pairwise

theorem triangleVisits_pairwise_key (hP : CrossingGeometry P) (e f g : ZMod n) :
    (triangleVisits hP e f g).Pairwise fun v w =>
      traversalKey (geometricVisitPosition hP v) < traversalKey (geometricVisitPosition hP w) :=
  (gaussList_pairwise_key hP).filter _

theorem mem_triangleVisits_iff (hP : CrossingGeometry P) (e f g : ZMod n) (v : Visit P) :
    v ∈ triangleVisits hP e f g ↔ v.1.val ∈ triangleSupports e f g := by
  unfold triangleVisits
  rw [List.mem_filter, decide_eq_true_iff]
  exact ⟨fun h => h.2, fun h => ⟨mem_geometricGaussList hP v, h⟩⟩

/-- Two lists strictly sorted by the key with the same members are equal. -/
theorem eq_of_pairwise_key_of_mem_iff (hP : CrossingGeometry P) {l₁ l₂ : List (Visit P)}
    (h₁ : l₁.Pairwise fun v w =>
      traversalKey (geometricVisitPosition hP v) < traversalKey (geometricVisitPosition hP w))
    (h₂ : l₂.Pairwise fun v w =>
      traversalKey (geometricVisitPosition hP v) < traversalKey (geometricVisitPosition hP w))
    (h : ∀ v, v ∈ l₁ ↔ v ∈ l₂) : l₁ = l₂ := by
  classical
  let _ := geometricVisitLinearOrder hP
  exact (List.sortedLT_iff_pairwise.mpr h₁).eq_of_mem_iff (List.sortedLT_iff_pairwise.mpr h₂) h

/-- A two-visit block on one edge, ordered by the order sign, is sorted by the key (no ties on a
CV-generic polygon). -/
theorem block_pairwise_key (hP : CrossingGeometry P) (u w : Visit P) (x y : ℝ)
    (huw : u.2.val = w.2.val) (hu : visitParameter u = x) (hw : visitParameter w = y) (hxy : x ≠ y) :
    (if SignType.sign (x - y) = -1 then [u, w] else [w, u]).Pairwise fun v v' =>
      traversalKey (geometricVisitPosition hP v) < traversalKey (geometricVisitPosition hP v') := by
  split_ifs with h
  · rw [List.pairwise_pair, G1.key_lt_iff_of_edge_eq hP huw, hu, hw]
    exact sub_neg.mp (sign_eq_neg_one_iff.mp h)
  · rw [List.pairwise_pair, G1.key_lt_iff_of_edge_eq hP huw.symm, hw, hu]
    exact lt_of_le_of_ne (not_lt.mp fun h' => h (sign_eq_neg_one_iff.mpr (sub_neg.mpr h'))) hxy.symm

/-! ### `local_word` -/

/-- `local_word` on any CV-generic polygon carrying the three crossings: the six triangle visits in
traversal order are the three blocks `e, f, g` (each ordered by its order sign) up to the rotation
that puts the traversal cut (edge value `0`) first. -/
theorem local_word_of_generic
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (hG : CV.Generic P) (hP : CrossingGeometry P)
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) :
    List.IsRotated (triangleVisits hP e f g) (blockWord hef heg hfg) := by
  have hfe : f ≠ e := (remote_endpoints e f h3.1).1
  have hgf : g ≠ f := (remote_endpoints f g h3.2.1).1
  have hge : g ≠ e := (remote_endpoints e g h3.2.2.1).1
  obtain ⟨hef_val, hcyc⟩ := G1.val_order h3
  -- the six visits
  let ae : Visit P := visitOn (xPair hef) e (mem_pair_left e f)
  let af : Visit P := visitOn (xPair hef) f (mem_pair_right e f)
  let be : Visit P := visitOn (xPair heg) e (mem_pair_left e g)
  let bg : Visit P := visitOn (xPair heg) g (mem_pair_right e g)
  let cf : Visit P := visitOn (xPair hfg) f (mem_pair_left f g)
  let cg : Visit P := visitOn (xPair hfg) g (mem_pair_right f g)
  -- the three blocks
  obtain ⟨BE, hBE⟩ : ∃ l : List (Visit P), l = if orderSign P e f g = -1 then [ae, be] else [be, ae] :=
    ⟨_, rfl⟩
  obtain ⟨BF, hBF⟩ : ∃ l : List (Visit P), l = if orderSign P f e g = -1 then [af, cf] else [cf, af] :=
    ⟨_, rfl⟩
  obtain ⟨BG, hBG⟩ : ∃ l : List (Visit P), l = if orderSign P g e f = -1 then [bg, cg] else [cg, bg] :=
    ⟨_, rfl⟩
  have hBW : blockWord hef heg hfg = BE ++ BF ++ BG := by rw [hBE, hBF, hBG]; rfl
  -- no ties along the three edges
  have hne_e : CV.crossParam P e f ≠ CV.crossParam P e g :=
    hG.crossParam_ne ((hG.crosses_iff e f).mpr hef) ((hG.crosses_iff e g).mpr heg) hgf.symm
  have hne_f : CV.crossParam P f e ≠ CV.crossParam P f g :=
    hG.crossParam_ne ((hG.crosses_iff f e).mpr (by rw [Finset.pair_comm]; exact hef))
      ((hG.crosses_iff f g).mpr hfg) hge.symm
  have hne_g : CV.crossParam P g e ≠ CV.crossParam P g f :=
    hG.crossParam_ne ((hG.crosses_iff g e).mpr (by rw [Finset.pair_comm]; exact heg))
      ((hG.crosses_iff g f).mpr (by rw [Finset.pair_comm]; exact hfg)) hfe.symm
  -- each block is sorted
  have sE : BE.Pairwise fun v w =>
      traversalKey (geometricVisitPosition hP v) < traversalKey (geometricVisitPosition hP w) := by
    rw [hBE]
    exact block_pairwise_key hP ae be _ _ rfl (G1.visitParameter_visitOn_left hP hef)
      (G1.visitParameter_visitOn_left hP heg) hne_e
  have sF : BF.Pairwise fun v w =>
      traversalKey (geometricVisitPosition hP v) < traversalKey (geometricVisitPosition hP w) := by
    rw [hBF]
    exact block_pairwise_key hP af cf _ _ rfl (G1.visitParameter_visitOn_right hP hef)
      (G1.visitParameter_visitOn_left hP hfg) hne_f
  have sG : BG.Pairwise fun v w =>
      traversalKey (geometricVisitPosition hP v) < traversalKey (geometricVisitPosition hP w) := by
    rw [hBG]
    exact block_pairwise_key hP bg cg _ _ rfl (G1.visitParameter_visitOn_right hP heg)
      (G1.visitParameter_visitOn_right hP hfg) hne_g
  -- each block lies on its edge
  have eE : ∀ v ∈ BE, v.2.val = e := by
    intro v hv; rw [hBE] at hv
    split_ifs at hv <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hv <;>
      rcases hv with rfl | rfl <;> rfl
  have eF : ∀ v ∈ BF, v.2.val = f := by
    intro v hv; rw [hBF] at hv
    split_ifs at hv <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hv <;>
      rcases hv with rfl | rfl <;> rfl
  have eG : ∀ v ∈ BG, v.2.val = g := by
    intro v hv; rw [hBG] at hv
    split_ifs at hv <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hv <;>
      rcases hv with rfl | rfl <;> rfl
  -- the members of each block
  have mE : ∀ v, v ∈ BE ↔ v = ae ∨ v = be := by
    intro v; rw [hBE]
    split_ifs
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; exact or_comm
  have mF : ∀ v, v ∈ BF ↔ v = af ∨ v = cf := by
    intro v; rw [hBF]
    split_ifs
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; exact or_comm
  have mG : ∀ v, v ∈ BG ↔ v = bg ∨ v = cg := by
    intro v; rw [hBG]
    split_ifs
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; exact or_comm
  -- the members of the triangle visits
  have hmem : ∀ v, v ∈ triangleVisits hP e f g ↔ v ∈ BE ∨ v ∈ BF ∨ v ∈ BG := by
    intro v
    rw [mem_triangleVisits_iff, mE, mF, mG]
    constructor
    · intro hv
      rcases eq_visit_of_val_mem hfe hgf hge hef heg hfg v hv with
        rfl | rfl | rfl | rfl | rfl | rfl <;> tauto
    · rintro ((rfl | rfl) | (rfl | rfl) | (rfl | rfl)) <;>
        simp only [triangleSupports, Finset.mem_insert, Finset.mem_singleton] <;>
        first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
  -- cross-block comparisons
  have cEF : ∀ a ∈ BE, ∀ b ∈ BF,
      traversalKey (geometricVisitPosition hP a) < traversalKey (geometricVisitPosition hP b) :=
    fun a ha b hb => G1.key_lt_of_val_lt hP (by rw [eE a ha, eF b hb]; exact hef_val)
  rcases hcyc with hfg_val | ⟨hge_val, hgf_val⟩
  · -- `e < f < g` as values: the word is the block word itself
    have cEG : ∀ a ∈ BE, ∀ b ∈ BG,
        traversalKey (geometricVisitPosition hP a) < traversalKey (geometricVisitPosition hP b) :=
      fun a ha b hb => G1.key_lt_of_val_lt hP (by rw [eE a ha, eG b hb]; exact hef_val.trans hfg_val)
    have cFG : ∀ a ∈ BF, ∀ b ∈ BG,
        traversalKey (geometricVisitPosition hP a) < traversalKey (geometricVisitPosition hP b) :=
      fun a ha b hb => G1.key_lt_of_val_lt hP (by rw [eF a ha, eG b hb]; exact hfg_val)
    have heq : triangleVisits hP e f g = BE ++ BF ++ BG := by
      refine eq_of_pairwise_key_of_mem_iff hP (triangleVisits_pairwise_key hP e f g) ?_ ?_
      · refine List.pairwise_append.mpr ⟨List.pairwise_append.mpr ⟨sE, sF, cEF⟩, sG, ?_⟩
        intro a ha b hb
        rcases List.mem_append.mp ha with ha | ha
        · exact cEG a ha b hb
        · exact cFG a ha b hb
      · intro v
        rw [hmem]
        simp only [List.mem_append, or_assoc]
    rw [heq, hBW]
  · -- the cut is at `g` (`g = 0 < e < f`): the word starts with the `g` block
    have cGE : ∀ a ∈ BG, ∀ b ∈ BE,
        traversalKey (geometricVisitPosition hP a) < traversalKey (geometricVisitPosition hP b) :=
      fun a ha b hb => G1.key_lt_of_val_lt hP (by rw [eG a ha, eE b hb]; exact hge_val)
    have cGF : ∀ a ∈ BG, ∀ b ∈ BF,
        traversalKey (geometricVisitPosition hP a) < traversalKey (geometricVisitPosition hP b) :=
      fun a ha b hb => G1.key_lt_of_val_lt hP (by rw [eG a ha, eF b hb]; exact hgf_val)
    have heq : triangleVisits hP e f g = BG ++ (BE ++ BF) := by
      refine eq_of_pairwise_key_of_mem_iff hP (triangleVisits_pairwise_key hP e f g) ?_ ?_
      · refine List.pairwise_append.mpr ⟨sG, List.pairwise_append.mpr ⟨sE, sF, cEF⟩, ?_⟩
        intro a ha b hb
        rcases List.mem_append.mp hb with hb | hb
        · exact cGE a ha b hb
        · exact cGF a ha b hb
      · intro v
        rw [hmem]
        simp only [List.mem_append]
        tauto
    rw [heq, hBW]
    exact List.isRotated_append

/-- `local_word`, for every punctured parameter (no radius needed beyond `t ≠ 0`). -/
theorem local_word (E : CV.Event n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (δ : ℝ) : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    List.IsRotated (triangleVisits (geomAt E t ht.1) e f g) (blockWord hef heg hfg) :=
  fun t ht hef heg hfg =>
    local_word_of_generic h3 (genericAt E t ht.1) (geomAt E t ht.1) hef heg hfg

/-! ### `canonical_words` -/

/-- In the canonical branch `s_a = s_b = s_c` (nonzero), `δ = +1` gives `q ≡ −1` and `δ = −1` gives
`q ≡ +1`. -/
theorem canonical_orders_abstract : ∀ d sa sb sc : SignType, sa ≠ 0 → sa = sb → sb = sc →
    (d = 1 → -d * (sa * sb) = -1 ∧ -d * (sa * sc) = -1 ∧ -d * (sb * sc) = -1) ∧
    (d = -1 → -d * (sa * sb) = 1 ∧ -d * (sa * sc) = 1 ∧ -d * (sb * sc) = 1) := by
  decide

variable {E : CV.Event n}

/-- `canonical_words`: `P = a b A a c B b c C` on the side `δ = +1`, `E = b a A c a B c b C` on the
side `δ = −1`, with the printed edges. -/
theorem canonical_words
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    {δ : ℝ} (hδ : G1.GoodRadius E e f g δ) : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    strandSign (E.curve t) e f = strandSign (E.curve t) e g →
    strandSign (E.curve t) e g = strandSign (E.curve t) f g →
    (concurrenceSign (E.curve t) e f g = 1 →
      List.IsRotated (triangleVisits (geomAt E t ht.1) e f g) (wordPVisits hef heg hfg) ∧
      EdgeAB (geomAt E t ht.1) hef heg ∧ EdgeBC (geomAt E t ht.1) heg hfg ∧
      ¬ EdgeAC (geomAt E t ht.1) hef hfg) ∧
    (concurrenceSign (E.curve t) e f g = -1 →
      List.IsRotated (triangleVisits (geomAt E t ht.1) e f g) (wordEVisits hef heg hfg) ∧
      EdgeAC (geomAt E t ht.1) hef hfg ∧ ¬ EdgeAB (geomAt E t ht.1) hef heg ∧
      ¬ EdgeBC (geomAt E t ht.1) heg hfg) := by
  intro t ht hef heg hfg hab hbc
  obtain ⟨q1, q2, q3⟩ := G1.sign_vector hδ t ht
  obtain ⟨s1, -, -, -⟩ := G1.signs_ne_zero hδ t ht
  obtain ⟨e1, e2, e3⟩ := G1.edges_iff E h3 δ t ht hef heg hfg
  have hw := local_word E h3 δ t ht hef heg hfg
  have hq := canonical_orders_abstract (concurrenceSign (E.curve t) e f g) _ _ _ s1 hab hbc
  rw [← q1, ← q2, ← q3] at hq
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · obtain ⟨h1, h2, h3'⟩ := hq.1 hd
    have hbw : blockWord hef heg hfg = wordPVisits hef heg hfg := by
      unfold blockWord wordPVisits
      rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h3']
      rfl
    refine ⟨hbw ▸ hw, e1.mpr h1, e3.mpr h3', fun h => ?_⟩
    have := e2.mp h
    rw [h2] at this
    exact absurd this (by decide)
  · obtain ⟨h1, h2, h3'⟩ := hq.2 hd
    have hbw : blockWord hef heg hfg = wordEVisits hef heg hfg := by
      unfold blockWord wordEVisits
      rw [ite_eq_right (by rw [h1]; decide), ite_eq_right (by rw [h2]; decide),
        ite_eq_right (by rw [h3']; decide)]
      rfl
    refine ⟨hbw ▸ hw, e2.mpr h2, fun h => ?_, fun h => ?_⟩
    · have := e1.mp h
      rw [h1] at this
      exact absurd this (by decide)
    · have := e3.mp h
      rw [h3'] at this
      exact absurd this (by decide)

/-! ### `local_supports` -/

/-- A pair of interlacing crossings is not independent. -/
theorem pair_not_mem_Ind (hP : CrossingGeometry P) {x y : Crossing P}
    (h : GeometricInterlaces hP x y) : ({x, y} : Finset (Crossing P)) ∉ CV.Ind hP := by
  rw [CV.mem_Ind_iff]
  intro hI
  exact hI x (by simp) y (by simp) h.1 h

theorem triple_not_mem_Ind_of_first_second (hP : CrossingGeometry P) {x y z : Crossing P}
    (h : GeometricInterlaces hP x y) : ({x, y, z} : Finset (Crossing P)) ∉ CV.Ind hP := by
  rw [CV.mem_Ind_iff]
  intro hI
  exact hI x (by simp) y (by simp) h.1 h

theorem triple_not_mem_Ind_of_first_third (hP : CrossingGeometry P) {x y z : Crossing P}
    (h : GeometricInterlaces hP x z) : ({x, y, z} : Finset (Crossing P)) ∉ CV.Ind hP := by
  rw [CV.mem_Ind_iff]
  intro hI
  exact hI x (by simp) z (by simp) h.1 h

theorem singleton_mem_Ind (hP : CrossingGeometry P) (x : Crossing P) :
    ({x} : Finset (Crossing P)) ∈ CV.Ind hP := by
  rw [CV.mem_Ind_iff]
  simp

/-- A pair of non-interlacing crossings is independent. -/
theorem pair_mem_Ind (hP : CrossingGeometry P) {x y : Crossing P}
    (h : ¬ GeometricInterlaces hP x y) : ({x, y} : Finset (Crossing P)) ∈ CV.Ind hP := by
  rw [CV.mem_Ind_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro a (rfl | rfl) b (rfl | rfl) hab
  · exact absurd rfl hab
  · exact h
  · exact fun h' => h (geometricInterlaces_symm hP h')
  · exact absurd rfl hab

/-- `local_supports`: "The supports `ab, bc, T` are absent on P; `ac, T` are absent on E", and the
tabulated rows are present, on the event in the canonical branch. -/
theorem local_supports
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    {δ : ℝ} (hδ : G1.GoodRadius E e f g δ) : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    strandSign (E.curve t) e f = strandSign (E.curve t) e g →
    strandSign (E.curve t) e g = strandSign (E.curve t) f g →
    (concurrenceSign (E.curve t) e f g = 1 →
      ({xPair hef, xPair heg} : Finset (Crossing (E.curve t))) ∉ CV.Ind (geomAt E t ht.1) ∧
      ({xPair heg, xPair hfg} : Finset (Crossing (E.curve t))) ∉ CV.Ind (geomAt E t ht.1) ∧
      ({xPair hef, xPair heg, xPair hfg} : Finset (Crossing (E.curve t))) ∉ CV.Ind (geomAt E t ht.1) ∧
      (∅ : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair hef} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair heg} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair hfg} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair hef, xPair hfg} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1)) ∧
    (concurrenceSign (E.curve t) e f g = -1 →
      ({xPair hef, xPair hfg} : Finset (Crossing (E.curve t))) ∉ CV.Ind (geomAt E t ht.1) ∧
      ({xPair hef, xPair heg, xPair hfg} : Finset (Crossing (E.curve t))) ∉ CV.Ind (geomAt E t ht.1) ∧
      (∅ : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair hef} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair heg} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair hfg} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair hef, xPair heg} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1) ∧
      ({xPair heg, xPair hfg} : Finset (Crossing (E.curve t))) ∈ CV.Ind (geomAt E t ht.1)) := by
  intro t ht hef heg hfg hab hbc
  obtain ⟨hPside, hEside⟩ := canonical_words h3 hδ t ht hef heg hfg hab hbc
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · obtain ⟨-, eAB, eBC, nAC⟩ := hPside hd
    exact ⟨pair_not_mem_Ind _ eAB, pair_not_mem_Ind _ eBC, triple_not_mem_Ind_of_first_second _ eAB,
      CV.empty_mem_Ind _, singleton_mem_Ind _ _, singleton_mem_Ind _ _, singleton_mem_Ind _ _,
      pair_mem_Ind _ nAC⟩
  · obtain ⟨-, eAC, nAB, nBC⟩ := hEside hd
    exact ⟨pair_not_mem_Ind _ eAC, triple_not_mem_Ind_of_first_third _ eAC, CV.empty_mem_Ind _,
      singleton_mem_Ind _ _, singleton_mem_Ind _ _, singleton_mem_Ind _ _, pair_mem_Ind _ nAB,
      pair_mem_Ind _ nBC⟩

/-! ### `local_undominated` -/

theorem mem_U_inter_triangle_iff (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (x : Crossing P) :
    x ∈ CV.U hP S ∩ triangleCrossings P e f g ↔
      x.val ∈ triangleSupports e f g ∧ x ∉ S ∧ ∀ s ∈ S, ¬ GeometricInterlaces hP x s := by
  rw [Finset.mem_inter, CV.mem_U, CV.mem_N, mem_triangleCrossings_iff]
  simp only [not_exists, not_and]
  tauto

/-- `U(S) ∩ T` is determined by the three membership tests of `a, b, c`. -/
theorem U_inter_triangle_eq (hP : CrossingGeometry P)
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    (S X : Finset (Crossing P)) (hX : X ⊆ {xPair hef, xPair heg, xPair hfg})
    (ha : xPair hef ∈ X ↔ xPair hef ∉ S ∧ ∀ s ∈ S, ¬ GeometricInterlaces hP (xPair hef) s)
    (hb : xPair heg ∈ X ↔ xPair heg ∉ S ∧ ∀ s ∈ S, ¬ GeometricInterlaces hP (xPair heg) s)
    (hc : xPair hfg ∈ X ↔ xPair hfg ∉ S ∧ ∀ s ∈ S, ¬ GeometricInterlaces hP (xPair hfg) s) :
    CV.U hP S ∩ triangleCrossings P e f g = X := by
  ext x
  rw [mem_U_inter_triangle_iff, val_mem_triangleSupports_iff hef heg hfg]
  constructor
  · rintro ⟨(rfl | rfl | rfl), h⟩
    · exact ha.mpr h
    · exact hb.mpr h
    · exact hc.mpr h
  · intro hx
    have hx' := hX hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    refine ⟨hx', ?_⟩
    rcases hx' with rfl | rfl | rfl
    · exact ha.mp hx
    · exact hb.mp hx
    · exact hc.mp hx

/-- `local_undominated`: the printed "Local undominated table" (`U(S) ∩ T`, `U` = `CV.U`) on the
event in the canonical branch. -/
theorem local_undominated
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    {δ : ℝ} (hδ : G1.GoodRadius E e f g δ) : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    strandSign (E.curve t) e f = strandSign (E.curve t) e g →
    strandSign (E.curve t) e g = strandSign (E.curve t) f g →
    (concurrenceSign (E.curve t) e f g = 1 →
      CV.U (geomAt E t ht.1) ∅ ∩ triangleCrossings (E.curve t) e f g = {xPair hef, xPair heg, xPair hfg} ∧
      CV.U (geomAt E t ht.1) {xPair hef} ∩ triangleCrossings (E.curve t) e f g = {xPair hfg} ∧
      CV.U (geomAt E t ht.1) {xPair heg} ∩ triangleCrossings (E.curve t) e f g = ∅ ∧
      CV.U (geomAt E t ht.1) {xPair hfg} ∩ triangleCrossings (E.curve t) e f g = {xPair hef} ∧
      CV.U (geomAt E t ht.1) {xPair hef, xPair hfg} ∩ triangleCrossings (E.curve t) e f g = ∅) ∧
    (concurrenceSign (E.curve t) e f g = -1 →
      CV.U (geomAt E t ht.1) ∅ ∩ triangleCrossings (E.curve t) e f g = {xPair hef, xPair heg, xPair hfg} ∧
      CV.U (geomAt E t ht.1) {xPair hef} ∩ triangleCrossings (E.curve t) e f g = {xPair heg} ∧
      (CV.U (geomAt E t ht.1) {xPair heg} ∩ triangleCrossings (E.curve t) e f g = {xPair hef, xPair hfg} ∧
        EdgeAC (geomAt E t ht.1) hef hfg) ∧
      CV.U (geomAt E t ht.1) {xPair hfg} ∩ triangleCrossings (E.curve t) e f g = {xPair heg} ∧
      CV.U (geomAt E t ht.1) {xPair hef, xPair heg} ∩ triangleCrossings (E.curve t) e f g = ∅ ∧
      CV.U (geomAt E t ht.1) {xPair heg, xPair hfg} ∩ triangleCrossings (E.curve t) e f g = ∅) := by
  intro t ht hef heg hfg hab hbc
  have hfe : f ≠ e := (remote_endpoints e f h3.1).1
  have hgf : g ≠ f := (remote_endpoints f g h3.2.1).1
  have hge : g ≠ e := (remote_endpoints e g h3.2.2.1).1
  obtain ⟨nab, nac, nbc⟩ := xPairs_ne hfe hgf hge hef heg hfg
  have nba := nab.symm
  have nca := nac.symm
  have ncb := nbc.symm
  have iAA := geometricInterlaces_irrefl (geomAt E t ht.1) (xPair hef)
  have iBB := geometricInterlaces_irrefl (geomAt E t ht.1) (xPair heg)
  have iCC := geometricInterlaces_irrefl (geomAt E t ht.1) (xPair hfg)
  obtain ⟨hPside, hEside⟩ := canonical_words h3 hδ t ht hef heg hfg hab hbc
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · obtain ⟨-, eAB, eBC, nAC⟩ := hPside hd
    have iAB : GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair heg) := eAB
    have iBC : GeometricInterlaces (geomAt E t ht.1) (xPair heg) (xPair hfg) := eBC
    have iAC : ¬ GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair hfg) := nAC
    have iBA := geometricInterlaces_symm _ iAB
    have iCB := geometricInterlaces_symm _ iBC
    have iCA : ¬ GeometricInterlaces (geomAt E t ht.1) (xPair hfg) (xPair hef) :=
      fun h => iAC (geometricInterlaces_symm _ h)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      refine U_inter_triangle_eq _ hef heg hfg _ _ (by simp) ?_ ?_ ?_ <;>
      simp [nab, nac, nbc, nba, nca, ncb, iAB, iBC, iAC, iBA, iCB, iCA, iAA, iBB, iCC]
  · obtain ⟨-, eAC, nAB, nBC⟩ := hEside hd
    have iAC : GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair hfg) := eAC
    have iAB : ¬ GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair heg) := nAB
    have iBC : ¬ GeometricInterlaces (geomAt E t ht.1) (xPair heg) (xPair hfg) := nBC
    have iCA := geometricInterlaces_symm _ iAC
    have iBA : ¬ GeometricInterlaces (geomAt E t ht.1) (xPair heg) (xPair hef) :=
      fun h => iAB (geometricInterlaces_symm _ h)
    have iCB : ¬ GeometricInterlaces (geomAt E t ht.1) (xPair hfg) (xPair heg) :=
      fun h => iBC (geometricInterlaces_symm _ h)
    refine ⟨?_, ?_, ⟨?_, eAC⟩, ?_, ?_, ?_⟩ <;>
      refine U_inter_triangle_eq _ hef heg hfg _ _ (by simp) ?_ ?_ ?_ <;>
      simp [nab, nac, nbc, nba, nca, ncb, iAB, iBC, iAC, iBA, iCB, iCA, iAA, iBB, iCC]

/-! ### `mask_sharpening` -/

theorem mem_interlacedTriangle_iff (hP : CrossingGeometry P) (y x : Crossing P) :
    x ∈ interlacedTriangle hP e f g y ↔
      x.val ∈ triangleSupports e f g ∧ GeometricInterlaces hP y x := by
  classical
  unfold interlacedTriangle
  rw [Finset.mem_filter, mem_triangleCrossings_iff]

theorem interlacedTriangle_subset (hP : CrossingGeometry P) (y : Crossing P) :
    interlacedTriangle hP e f g y ⊆ triangleCrossings P e f g := by
  classical
  unfold interlacedTriangle
  exact Finset.filter_subset _ _

/-- A survivor `y ∈ U(S)` interlaces no member of `S`. -/
theorem not_interlaces_of_mem_U (hP : CrossingGeometry P) {S : Finset (Crossing P)}
    {y : Crossing P} (hy : y ∈ CV.U hP S) {x : Crossing P} (hx : x ∈ S) :
    ¬ GeometricInterlaces hP y x := by
  rw [CV.mem_U, CV.mem_N] at hy
  exact fun h => hy.2 ⟨x, hx, h⟩

/-- The interlaced pair of a survivor of `insert x Q` (`x` a triangle crossing) is a bundle pair
`{z ∈ T : k ∈ z.val}` with `k ∉ x.val`, or empty. -/
theorem mask_of_survivor {δ : ℝ} (hPar : ParityData E e f g δ) (t : E.Parameter)
    (ht : Punctured E δ t) (Q : Finset (Crossing (E.curve t))) (x y : Crossing (E.curve t))
    (hxT : x.val ∈ triangleSupports e f g)
    (hy : y ∈ CV.U (geomAt E t ht.1) (insert x Q)) (hyT : y.val ∉ triangleSupports e f g) :
    interlacedTriangle (geomAt E t ht.1) e f g y = ∅ ∨
    ∃ k ∈ ({e, f, g} : Finset (ZMod n)), k ∉ x.val ∧
      ∀ z, z ∈ interlacedTriangle (geomAt E t ht.1) e f g y ↔
        z.val ∈ triangleSupports e f g ∧ k ∈ z.val := by
  have hyx := not_interlaces_of_mem_U _ hy (Finset.mem_insert_self x Q)
  rcases Finset.eq_empty_or_nonempty (interlacedTriangle (geomAt E t ht.1) e f g y) with hM | hM
  · exact Or.inl hM
  · right
    obtain ⟨k, hk, hM'⟩ := hPar.interlaced_pair t ht y hyT hM
    have key : ∀ z, z ∈ interlacedTriangle (geomAt E t ht.1) e f g y ↔
        z.val ∈ triangleSupports e f g ∧ k ∈ z.val := by
      intro z
      rw [hM', Finset.mem_filter, mem_triangleCrossings_iff]
    refine ⟨k, hk, fun hkx => hyx ?_, key⟩
    exact ((mem_interlacedTriangle_iff _ y x).mp ((key x).mpr ⟨hxT, hkx⟩)).2

/-- `mask_sharpening`: "after `a`, survivors have mask `0` or `bc`; after `c`, mask `0` or `ab`;
after `b`, mask `0` or `ac`; after any present pair only mask-zero outsiders survive" — from
R-PAR (P1) (`ParityData.parity`, `ParityData.interlaced_pair`) and `CV.mem_U`; full availability
is not needed. -/
theorem mask_sharpening
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    {δ : ℝ} (hPar : ParityData E e f g δ) : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      avail (geomAt E t ht.1) e f g Q = triangleCrossings (E.curve t) e f g →
      (∀ y ∈ CV.U (geomAt E t ht.1) (insert (xPair hef) Q), y.val ∉ triangleSupports e f g →
        interlacedTriangle (geomAt E t ht.1) e f g y = ∅ ∨
        interlacedTriangle (geomAt E t ht.1) e f g y = {xPair heg, xPair hfg}) ∧
      (∀ y ∈ CV.U (geomAt E t ht.1) (insert (xPair hfg) Q), y.val ∉ triangleSupports e f g →
        interlacedTriangle (geomAt E t ht.1) e f g y = ∅ ∨
        interlacedTriangle (geomAt E t ht.1) e f g y = {xPair hef, xPair heg}) ∧
      (∀ y ∈ CV.U (geomAt E t ht.1) (insert (xPair heg) Q), y.val ∉ triangleSupports e f g →
        interlacedTriangle (geomAt E t ht.1) e f g y = ∅ ∨
        interlacedTriangle (geomAt E t ht.1) e f g y = {xPair hef, xPair hfg}) ∧
      (∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
        Q ∪ J ∈ CV.Ind (geomAt E t ht.1) →
        ∀ y ∈ CV.U (geomAt E t ht.1) (Q ∪ J), y.val ∉ triangleSupports e f g →
          interlacedTriangle (geomAt E t ht.1) e f g y = ∅) := by
  intro t ht hef heg hfg Q _ _
  have hfe : f ≠ e := (remote_endpoints e f h3.1).1
  have hgf : g ≠ f := (remote_endpoints f g h3.2.1).1
  have hge : g ≠ e := (remote_endpoints e g h3.2.2.1).1
  have haT : (xPair hef).val ∈ triangleSupports e f g :=
    (val_mem_triangleSupports_iff hef heg hfg _).mpr (Or.inl rfl)
  have hbT : (xPair heg).val ∈ triangleSupports e f g :=
    (val_mem_triangleSupports_iff hef heg hfg _).mpr (Or.inr (Or.inl rfl))
  have hcT : (xPair hfg).val ∈ triangleSupports e f g :=
    (val_mem_triangleSupports_iff hef heg hfg _).mpr (Or.inr (Or.inr rfl))
  refine ⟨fun y hy hyT => ?_, fun y hy hyT => ?_, fun y hy hyT => ?_, fun J hJ hJ2 _ y hy hyT => ?_⟩
  · -- after `a = {e, f}`: the pair avoiding `a` is `bc` (bundle edge `g`)
    rcases mask_of_survivor hPar t ht Q _ y haT hy hyT with hM | ⟨k, hk, hkx, key⟩
    · exact Or.inl hM
    · right
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      simp only [xPair, Finset.mem_insert, Finset.mem_singleton, not_or] at hkx
      rcases hk with hk | hk | hk <;> subst k
      · exact absurd rfl hkx.1
      · exact absurd rfl hkx.2
      · ext z
        rw [key, val_mem_triangleSupports_iff hef heg hfg]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨(rfl | rfl | rfl), hz⟩
          · simp only [xPair, Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with hz | hz
            · exact absurd hz hge
            · exact absurd hz hgf
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact ⟨Or.inr (Or.inl rfl), mem_pair_right e g⟩
          · exact ⟨Or.inr (Or.inr rfl), mem_pair_right f g⟩
  · -- after `c = {f, g}`: the pair avoiding `c` is `ab` (bundle edge `e`)
    rcases mask_of_survivor hPar t ht Q _ y hcT hy hyT with hM | ⟨k, hk, hkx, key⟩
    · exact Or.inl hM
    · right
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      simp only [xPair, Finset.mem_insert, Finset.mem_singleton, not_or] at hkx
      rcases hk with hk | hk | hk <;> subst k
      · ext z
        rw [key, val_mem_triangleSupports_iff hef heg hfg]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨(rfl | rfl | rfl), hz⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
          · simp only [xPair, Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with hz | hz
            · exact absurd hz.symm hfe
            · exact absurd hz.symm hge
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, mem_pair_left e f⟩
          · exact ⟨Or.inr (Or.inl rfl), mem_pair_left e g⟩
      · exact absurd rfl hkx.1
      · exact absurd rfl hkx.2
  · -- after `b = {e, g}`: the pair avoiding `b` is `ac` (bundle edge `f`)
    rcases mask_of_survivor hPar t ht Q _ y hbT hy hyT with hM | ⟨k, hk, hkx, key⟩
    · exact Or.inl hM
    · right
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      simp only [xPair, Finset.mem_insert, Finset.mem_singleton, not_or] at hkx
      rcases hk with hk | hk | hk <;> subst k
      · exact absurd rfl hkx.1
      · ext z
        rw [key, val_mem_triangleSupports_iff hef heg hfg]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨(rfl | rfl | rfl), hz⟩
          · exact Or.inl rfl
          · simp only [xPair, Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with hz | hz
            · exact absurd hz hfe
            · exact absurd hz.symm hgf
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, mem_pair_right e f⟩
          · exact ⟨Or.inr (Or.inr rfl), mem_pair_left f g⟩
      · exact absurd rfl hkx.2
  · -- after a present pair `J`: a nonempty mask (two elements of `T`) meets `J` (two elements of `T`)
    by_contra hne
    have hcard : (interlacedTriangle (geomAt E t ht.1) e f g y).card = 2 := by
      rcases hPar.parity t ht y hyT with h | h
      · exact absurd (Finset.card_eq_zero.mp h) hne
      · exact h
    have hT3 := hPar.triangle_card t ht
    have hunion : (J ∪ interlacedTriangle (geomAt E t ht.1) e f g y).card ≤ 3 :=
      hT3 ▸ Finset.card_le_card (Finset.union_subset hJ (interlacedTriangle_subset _ y))
    have hsum := Finset.card_union_add_card_inter J (interlacedTriangle (geomAt E t ht.1) e f g y)
    have hinter : 0 < (J ∩ interlacedTriangle (geomAt E t ht.1) e f g y).card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hinter
    rw [Finset.mem_inter] at hx
    exact not_interlaces_of_mem_U _ hy (Finset.mem_union_right Q hx.1)
      ((mem_interlacedTriangle_iff _ y x).mp hx.2).2

end G2

/-! ### Test assembly: the bundle from the two radius data -/

namespace G2

variable {E : CV.Event n} {e f g : ZMod n}

/-- The radius data of unit G1 shrink to any smaller positive radius. -/
theorem goodRadius_of_le {δ δ' : ℝ} (hδ : G1.GoodRadius E e f g δ) (h0 : 0 < δ') (h : δ' ≤ δ) :
    G1.GoodRadius E e f g δ' :=
  ⟨h0, h.trans hδ.le_radius, fun t ht => hδ.crosses t (lt_of_lt_of_le ht h),
    fun t ht => hδ.strand t (lt_of_lt_of_le ht h), fun s hs => hδ.g3_flip s (lt_of_lt_of_le hs h)⟩

theorem punctured_of_le {δ δ' : ℝ} (h : δ' ≤ δ) {t : E.Parameter} (ht : Punctured E δ' t) :
    Punctured E δ t :=
  ⟨ht.1, lt_of_lt_of_le ht.2 h⟩

/-- The parity row shrinks to any smaller radius. -/
theorem parityData_of_le {δ δ' : ℝ} (hPar : ParityData E e f g δ) (h : δ' ≤ δ) :
    ParityData E e f g δ' where
  triangle_card t ht := hPar.triangle_card t (punctured_of_le h ht)
  parity t ht y hy := hPar.parity t (punctured_of_le h ht) y hy
  interlaced_pair t ht y hy hne := hPar.interlaced_pair t (punctured_of_le h ht) y hy hne
  trichotomy t ht S' hS := hPar.trichotomy t (punctured_of_le h ht) S' hS
  avail_wall_invariant t t' ht ht' hs hs' S' hS :=
    hPar.avail_wall_invariant t t' (punctured_of_le h ht) (punctured_of_le h ht') hs hs' S' hS

/-- **Test assembly.** With the radius data of unit G1 and the parity row at the same radius, every
field of `GenericTableData` is discharged verbatim by the `G1.*` and `G2.*` lemmas and the three
proved skeleton tables (checked 2026-09-14). -/
theorem genericTableData
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    {δ : ℝ} (hδ : G1.GoodRadius E e f g δ) (hPar : ParityData E e f g δ) :
    GenericTableData E e f g δ where
  nonzero := G1.nonzero hδ
  cramer := G1.cramer hδ
  sign_vector := G1.sign_vector hδ
  edges_iff := G1.edges_iff E h3 δ
  chamber_change := G1.chamber_change hδ
  extreme_iff_orders := G1.extreme_iff_orders h3 hδ
  extreme_iff_alternating := G1.extreme_iff_alternating h3 hδ
  generic_iff_nonalternating := G1.generic_iff_nonalternating h3 hδ
  branch_count := G1.branch_count
  selected_unique := G1.selected_unique
  selected_is_graph_selected := G1.selected_is_graph_selected h3 hδ
  local_word := local_word E h3 δ
  canonical_words := canonical_words h3 hδ
  local_supports := local_supports h3 hδ
  local_undominated := local_undominated h3 hδ
  mask_sharpening := mask_sharpening h3 hPar
  skeleton_table := LocalTable.skeletonTable
  successor_table := LocalTable.successorTable
  residual_table := LocalTable.residualWordTable

/-- The row modulo the parity row: from any radius carrying `ParityData`, the common radius
`min` carries `GenericTableData`. -/
theorem generic_table_of_parity {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (hpar : ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ParityData E e f g δ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericTableData E e f g δ := by
  obtain ⟨δ₁, hδ₁⟩ := G1.exists_goodRadius hE
  obtain ⟨δ₂, hδ₂, -, hPar⟩ := hpar
  have hmin : 0 < min δ₁ δ₂ := lt_min hδ₁.pos hδ₂
  have hδ := goodRadius_of_le hδ₁ hmin (min_le_left _ _)
  exact ⟨min δ₁ δ₂, hmin, hδ.le_radius,
    genericTableData h3 hδ (parityData_of_le hPar (min_le_right _ _))⟩

end G2
/-- **Row 172, R:generic_table** (R_GENERIC_ORBIT_ACTUAL_TABLE.md with the sign classification of
R_GENERIC_NONSELECTED_SELECTOR_PROOF.md). -/
theorem generic_table (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericTableData E e f g δ := by
  sorry

end RProof
