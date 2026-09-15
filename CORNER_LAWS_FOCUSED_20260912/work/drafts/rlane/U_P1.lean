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

/-! ### Unit P1 — the fields of `ParityData` from the localization data (proof of R-PAR-v6)

The five clauses of R-PAR-v6 are proved below as standalone lemmas `RProof.P1.<field>`, each with the
exact hypotheses the field needs. Every field rests on R-LOC-2 (row 164, unit L — another unit), so
each takes `hL : LocalizationData E e f g δ` and uses only the named fields:
`triangle_card` — `hL.triangle_crossings`; `parity`, `interlaced_pair`, `trichotomy` —
`hL.triangle_crossings` and `hL.adjacent` (clause (2), the three adjacent visit pairs);
`avail_wall_invariant` — `hL.interlace_toggle` (clause (4)). The geometric content is proved for one
polygon with `CrossingGeometry` (`P1.mask`, `P1.parity_of_adjacent`, …, `P1.avail_map_of_toggle`);
the event-level lemmas instantiate them at `E.curve t`.

The RA proof (R_ATTACHMENT_WARRANTS.md, R-PAR-v6): the six visits of the three triangle crossings form
the three clumps `C_e, C_f, C_g` = the adjacent visit pairs of R-LOC-2 (2); the two visits `u, v` of a
crossing `y ∉ T` cut the traversal circle `Γ` into two arcs; "no crossing-visit lies between the two
members of a clump", so each clump lies wholly in one arc (`P1.col_of_adjacent`: two adjacent visits
have the same colour `P1.Col`); `y` interlaces a triangle crossing iff its two clumps have different
colours (`P1.interlaces_iff_col`, CV:def:interlace read on the arcs); "A 2-colouring of three objects
has either 0 bichromatic pairs or exactly 2" (`P1.three_xor_cases`, the propositional form of
`two_colouring_bichromatic_pairs`), and the odd clump `C_h` names the interlaced pair
`{x ∈ T : h ∈ x}`. (P2) follows: each `q ∈ S'` removes nothing or a bundle pair from `T`, so
`avail(S')` is `T` or a subset of the third crossing; wall invariance is (4) of R-LOC-2 restricted to
the `W`-to-`T` pairs, which do not toggle. -/

namespace P1

variable {P : LabelledTuple n}

/-! #### The supports of the triangle -/

omit [NeZero n] in
theorem xPair_val {i j : ZMod n} (h : IsCrossing P {i, j}) : (xPair h).val = {i, j} := rfl

omit [NeZero n] in
theorem mem_triangleSupports {e f g : ZMod n} (s : Finset (ZMod n)) :
    s ∈ triangleSupports e f g ↔ s = {e, f} ∨ s = {e, g} ∨ s = {f, g} := by
  simp [triangleSupports]

theorem mem_triangleCrossings {e f g : ZMod n} (x : Crossing P) :
    x ∈ triangleCrossings P e f g ↔ x.val ∈ triangleSupports e f g := by
  simp [triangleCrossings]

omit [NeZero n] in
/-- The two edges carrying a crossing are distinct (its support has two elements). -/
theorem ne_of_isCrossing_pair {i j : ZMod n} (h : IsCrossing P {i, j}) : i ≠ j := by
  intro hij
  have h2 := crossing_card_two (xPair h)
  rw [xPair_val, hij, Finset.pair_eq_singleton, Finset.card_singleton] at h2
  exact absurd h2 (by norm_num)

theorem mem_triangleCrossings_iff {e f g : ZMod n} (hef : IsCrossing P {e, f})
    (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) (x : Crossing P) :
    x ∈ triangleCrossings P e f g ↔ x = xPair hef ∨ x = xPair heg ∨ x = xPair hfg := by
  rw [mem_triangleCrossings, mem_triangleSupports]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  · rintro (rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

omit [NeZero n] in
theorem xPair_ef_ne_eg {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) : xPair hef ≠ xPair heg := by
  intro h
  have hg : g ∈ ({e, f} : Finset (ZMod n)) := by
    rw [show ({e, f} : Finset (ZMod n)) = {e, g} from congrArg Subtype.val h]
    exact mem_pair_right e g
  simp only [Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with h' | h'
  · exact ne_of_isCrossing_pair heg h'.symm
  · exact ne_of_isCrossing_pair hfg h'.symm

omit [NeZero n] in
theorem xPair_ef_ne_fg {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) : xPair hef ≠ xPair hfg := by
  intro h
  have he : e ∈ ({f, g} : Finset (ZMod n)) := by
    rw [← show ({e, f} : Finset (ZMod n)) = {f, g} from congrArg Subtype.val h]
    exact mem_pair_left e f
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with h' | h'
  · exact ne_of_isCrossing_pair hef h'
  · exact ne_of_isCrossing_pair heg h'

omit [NeZero n] in
theorem xPair_eg_ne_fg {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) : xPair heg ≠ xPair hfg := by
  intro h
  have he : e ∈ ({f, g} : Finset (ZMod n)) := by
    rw [← show ({e, g} : Finset (ZMod n)) = {f, g} from congrArg Subtype.val h]
    exact mem_pair_left e g
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with h' | h'
  · exact ne_of_isCrossing_pair hef h'
  · exact ne_of_isCrossing_pair heg h'

/-- "the three crossings of `T`": `T = {x_ef, x_eg, x_fg}` has three elements. -/
theorem triangleCrossings_card {e f g : ZMod n} (hef : IsCrossing P {e, f})
    (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) :
    (triangleCrossings P e f g).card = 3 := by
  rw [Finset.card_eq_three]
  refine ⟨xPair hef, xPair heg, xPair hfg, xPair_ef_ne_eg hef heg hfg, xPair_ef_ne_fg hef heg hfg,
    xPair_eg_ne_fg hef heg hfg, ?_⟩
  ext x
  rw [mem_triangleCrossings_iff hef heg hfg]
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- "the two crossings sharing the bundle edge `e`": `{x ∈ T : e ∈ x} = {x_ef, x_eg}`. -/
theorem filter_e_eq {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) :
    (triangleCrossings P e f g).filter (fun x => e ∈ x.val) = {xPair hef, xPair heg} := by
  ext x
  rw [Finset.mem_filter, mem_triangleCrossings_iff hef heg hfg]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | rfl | rfl, hx⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      rw [xPair_val] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h
      · exact ne_of_isCrossing_pair hef h
      · exact ne_of_isCrossing_pair heg h
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, mem_pair_left e f⟩
    · exact ⟨Or.inr (Or.inl rfl), mem_pair_left e g⟩

/-- `{x ∈ T : f ∈ x} = {x_ef, x_fg}`. -/
theorem filter_f_eq {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) :
    (triangleCrossings P e f g).filter (fun x => f ∈ x.val) = {xPair hef, xPair hfg} := by
  ext x
  rw [Finset.mem_filter, mem_triangleCrossings_iff hef heg hfg]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | rfl | rfl, hx⟩
    · exact Or.inl rfl
    · exfalso
      rw [xPair_val] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h
      · exact ne_of_isCrossing_pair hef h.symm
      · exact ne_of_isCrossing_pair hfg h
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, mem_pair_right e f⟩
    · exact ⟨Or.inr (Or.inr rfl), mem_pair_left f g⟩

/-- `{x ∈ T : g ∈ x} = {x_eg, x_fg}`. -/
theorem filter_g_eq {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) :
    (triangleCrossings P e f g).filter (fun x => g ∈ x.val) = {xPair heg, xPair hfg} := by
  ext x
  rw [Finset.mem_filter, mem_triangleCrossings_iff hef heg hfg]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | rfl | rfl, hx⟩
    · exfalso
      rw [xPair_val] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h
      · exact ne_of_isCrossing_pair heg h.symm
      · exact ne_of_isCrossing_pair hfg h.symm
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inl rfl), mem_pair_right e g⟩
    · exact ⟨Or.inr (Or.inr rfl), mem_pair_right f g⟩

/-- The pair of `T` through a bundle edge `h ∈ {e, f, g}` has two elements. -/
theorem filter_card_two {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) (h : ZMod n) (hh : h ∈ ({e, f, g} : Finset (ZMod n))) :
    ((triangleCrossings P e f g).filter (fun x => h ∈ x.val)).card = 2 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with rfl | rfl | rfl
  · rw [filter_e_eq hef heg hfg]; exact Finset.card_pair (xPair_ef_ne_eg hef heg hfg)
  · rw [filter_f_eq hef heg hfg]; exact Finset.card_pair (xPair_ef_ne_fg hef heg hfg)
  · rw [filter_g_eq hef heg hfg]; exact Finset.card_pair (xPair_eg_ne_fg hef heg hfg)

/-- The crossing of `T` not carried by `e` is `x_fg`. -/
theorem eq_of_not_mem_e {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) {x : Crossing P} (hx : x ∈ triangleCrossings P e f g)
    (hx' : e ∉ x.val) : x = xPair hfg := by
  rcases (mem_triangleCrossings_iff hef heg hfg x).mp hx with rfl | rfl | rfl
  · exact absurd (mem_pair_left e f) hx'
  · exact absurd (mem_pair_left e g) hx'
  · rfl

/-- The crossing of `T` not carried by `f` is `x_eg`. -/
theorem eq_of_not_mem_f {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) {x : Crossing P} (hx : x ∈ triangleCrossings P e f g)
    (hx' : f ∉ x.val) : x = xPair heg := by
  rcases (mem_triangleCrossings_iff hef heg hfg x).mp hx with rfl | rfl | rfl
  · exact absurd (mem_pair_right e f) hx'
  · rfl
  · exact absurd (mem_pair_left f g) hx'

/-- The crossing of `T` not carried by `g` is `x_ef`. -/
theorem eq_of_not_mem_g {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) {x : Crossing P} (hx : x ∈ triangleCrossings P e f g)
    (hx' : g ∉ x.val) : x = xPair hef := by
  rcases (mem_triangleCrossings_iff hef heg hfg x).mp hx with rfl | rfl | rfl
  · rfl
  · exact absurd (mem_pair_right e g) hx'
  · exact absurd (mem_pair_right f g) hx'

/-- At most one crossing of `T` avoids a bundle edge `h ∈ {e, f, g}`. -/
theorem filter_not_card_le_one {e f g : ZMod n} (hef : IsCrossing P {e, f})
    (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) (h : ZMod n)
    (hh : h ∈ ({e, f, g} : Finset (ZMod n))) :
    ((triangleCrossings P e f g).filter (fun x => h ∉ x.val)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx x' hx'
  rw [Finset.mem_filter] at hx hx'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with rfl | rfl | rfl
  · rw [eq_of_not_mem_e hef heg hfg hx.1 hx.2, eq_of_not_mem_e hef heg hfg hx'.1 hx'.2]
  · rw [eq_of_not_mem_f hef heg hfg hx.1 hx.2, eq_of_not_mem_f hef heg hfg hx'.1 hx'.2]
  · rw [eq_of_not_mem_g hef heg hfg hx.1 hx.2, eq_of_not_mem_g hef heg hfg hx'.1 hx'.2]

/-! #### Visits, arcs and colours -/

omit [NeZero n] in
/-- Visits of distinct crossings are distinct. -/
theorem visit_ne_of_ne {x y : Crossing P} (h : x ≠ y) (i : {k // k ∈ x.val})
    (j : {k // k ∈ y.val}) : (⟨x, i⟩ : Visit P) ≠ ⟨y, j⟩ :=
  fun heq => h (congrArg Sigma.fst heq)

omit [NeZero n] in
/-- The two visits of one crossing on distinct edges are distinct. -/
theorem visit_ne_of_edge_ne {x : Crossing P} {i j : {k // k ∈ x.val}} (h : i ≠ j) :
    (⟨x, i⟩ : Visit P) ≠ ⟨x, j⟩ :=
  fun heq => h (eq_of_heq (Sigma.mk.inj_iff.mp heq).2)

omit [NeZero n] in
/-- Distinct visits have distinct positions on the traversal circle. -/
theorem pos_ne (hP : CrossingGeometry P) {v w : Visit P} (h : v ≠ w) :
    geometricVisitPosition hP v ≠ geometricVisitPosition hP w :=
  fun heq => h (geometricVisitPosition_injective hP heq)

omit [NeZero n] in
/-- A crossing has exactly two edges: every edge of `c` is one of two given distinct ones. -/
theorem edge_two (c : Crossing P) {p q : {i // i ∈ c.val}} (hpq : p ≠ q) (r : {i // i ∈ c.val}) :
    r = p ∨ r = q := by
  obtain ⟨a, b, -, hs⟩ := Finset.card_eq_two.mp (crossing_card_two c)
  have hp : p.val ∈ ({a, b} : Finset (ZMod n)) := (Finset.ext_iff.mp hs p.val).mp p.property
  have hq : q.val ∈ ({a, b} : Finset (ZMod n)) := (Finset.ext_iff.mp hs q.val).mp q.property
  have hr : r.val ∈ ({a, b} : Finset (ZMod n)) := (Finset.ext_iff.mp hs r.val).mp r.property
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq hr
  have hpq' : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> rcases hr with hr | hr <;>
    first
    | exact absurd (hp.trans hq.symm) hpq'
    | exact Or.inl (Subtype.ext (hr.trans hp.symm))
    | exact Or.inr (Subtype.ext (hr.trans hq.symm))

omit [NeZero n] in
/-- The strict cyclic order is asymmetric. -/
theorem between_asymm {p q r : TraversalPoint n} (h : traversalBetween p q r) :
    ¬ traversalBetween r q p := by
  unfold traversalBetween at *
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rintro (⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩) <;> linarith

/-- R-PAR-v6, proof: "the two arcs that `u, v` cut `Γ` into" — the colour of a visit `w` relative
to the two visits `u, v` of the outside crossing: `w` lies on the arc from `u` to `v`. -/
def Col (hP : CrossingGeometry P) (u v w : Visit P) : Prop :=
  traversalBetween (geometricVisitPosition hP u) (geometricVisitPosition hP w)
    (geometricVisitPosition hP v)

/-- A visit other than `u, v` lies on exactly one of the two arcs. -/
theorem col_iff_not (hP : CrossingGeometry P) {u v w : Visit P} (huv : u ≠ v) (hwu : w ≠ u)
    (hwv : w ≠ v) : Col hP u v w ↔ ¬ Col hP v u w :=
  traversalBetween_complement (pos_ne hP hwu.symm) (pos_ne hP hwv) (pos_ne hP huv.symm)

/-- R-PAR-v6, proof: "no crossing-visit lies between the two members of a clump … each clump lies
wholly in one of the two arcs" — two adjacent visits, neither a visit of the outside crossing, have
the same colour. -/
theorem col_of_adjacent (hP : CrossingGeometry P) {u v x y : Visit P}
    (hadj : AdjacentVisits hP x y) (huv : u ≠ v) (hxu : x ≠ u) (hxv : x ≠ v) (hyu : y ≠ u)
    (hyv : y ≠ v) : Col hP u v x ↔ Col hP u v y := by
  obtain ⟨-, harc⟩ := hadj
  constructor
  · intro hx
    by_contra hy
    have hy' : Col hP v u y := by
      by_contra hy'
      exact hy ((col_iff_not hP huv hyu hyv).mpr hy')
    obtain ⟨h1, h2⟩ := traversalAlternating_rotate hx hy'
    rcases harc with h | h
    · exact h v h1
    · exact h u h2
  · intro hy
    by_contra hx
    have hx' : Col hP v u x := by
      by_contra hx'
      exact hx ((col_iff_not hP huv hxu hxv).mpr hx')
    obtain ⟨h1, h2⟩ := traversalAlternating_rotate hy hx'
    rcases harc with h | h
    · exact h u h2
    · exact h v h1

/-- CV:def:interlace read on the two arcs: `y` interlaces `x` iff the two visits of `x` have
different colours relative to the two visits `⟨y, i₀⟩, ⟨y, i₁⟩` of `y` ("exactly one of the two
occurrences of `x` lies between the two occurrences of `y`"). -/
theorem interlaces_iff_col (hP : CrossingGeometry P) {y x : Crossing P} (hyx : y ≠ x)
    {i₀ i₁ : {i // i ∈ y.val}} (hi : i₀ ≠ i₁) {j₀ j₁ : {i // i ∈ x.val}} (hj : j₀ ≠ j₁) :
    GeometricInterlaces hP y x ↔
      Xor (Col hP ⟨y, i₀⟩ ⟨y, i₁⟩ ⟨x, j₀⟩) (Col hP ⟨y, i₀⟩ ⟨y, i₁⟩ ⟨x, j₁⟩) := by
  have huv : (⟨y, i₀⟩ : Visit P) ≠ ⟨y, i₁⟩ := visit_ne_of_edge_ne hi
  have hx₀ : ∀ i : {i // i ∈ y.val}, (⟨x, j₀⟩ : Visit P) ≠ ⟨y, i⟩ :=
    fun i => visit_ne_of_ne hyx.symm j₀ i
  have hx₁ : ∀ i : {i // i ∈ y.val}, (⟨x, j₁⟩ : Visit P) ≠ ⟨y, i⟩ :=
    fun i => visit_ne_of_ne hyx.symm j₁ i
  constructor
  · rintro ⟨-, y₀, y₁, x₀, x₁, hy, hx, h₀, h₁⟩
    rcases edge_two y hi y₀ with rfl | rfl <;> rcases edge_two y hi y₁ with rfl | rfl
    · exact absurd rfl hy
    · rcases edge_two x hj x₀ with rfl | rfl <;> rcases edge_two x hj x₁ with rfl | rfl
      · exact absurd rfl hx
      · exact Or.inl ⟨h₀, between_asymm h₁⟩
      · exact Or.inr ⟨h₀, between_asymm h₁⟩
      · exact absurd rfl hx
    · rcases edge_two x hj x₀ with rfl | rfl <;> rcases edge_two x hj x₁ with rfl | rfl
      · exact absurd rfl hx
      · exact Or.inr ⟨h₁, between_asymm h₀⟩
      · exact Or.inl ⟨h₁, between_asymm h₀⟩
      · exact absurd rfl hx
    · exact absurd rfl hy
  · rintro (⟨h₀, h₁⟩ | ⟨h₀, h₁⟩)
    · refine ⟨hyx, i₀, i₁, j₀, j₁, hi, hj, h₀, ?_⟩
      by_contra hc
      exact h₁ ((col_iff_not hP huv (hx₁ i₀) (hx₁ i₁)).mpr hc)
    · refine ⟨hyx, i₀, i₁, j₁, j₀, hi, hj.symm, h₀, ?_⟩
      by_contra hc
      exact h₁ ((col_iff_not hP huv (hx₀ i₀) (hx₀ i₁)).mpr hc)

/-- "A 2-colouring of three objects has either 0 bichromatic pairs (monochromatic) or exactly 2 (the
odd object pairs bichromatically with each of the other two, while those two pair monochromatically).
Never 1, never 3." — propositional form (`two_colouring_bichromatic_pairs` is the counting form):
if `A, B, C` say that the colour pairs `(χe, χf)`, `(χe, χg)`, `(χf, χg)` are bichromatic (each colour
read on either of the two visits of the clump), then none holds or exactly the two through one clump. -/
theorem three_xor_cases {A B C χe χe' χf χf' χg χg' : Prop}
    (hA : A ↔ Xor χe χf) (hB : B ↔ Xor χe' χg) (hC : C ↔ Xor χf' χg')
    (he : χe ↔ χe') (hf : χf ↔ χf') (hg : χg ↔ χg') :
    (¬ A ∧ ¬ B ∧ ¬ C) ∨ (A ∧ B ∧ ¬ C) ∨ (A ∧ ¬ B ∧ C) ∨ (¬ A ∧ B ∧ C) := by
  rw [← he] at hB
  rw [← hf, ← hg] at hC
  unfold Xor at hA hB hC
  by_cases h1 : χe <;> by_cases h2 : χf <;> by_cases h3 : χg <;> simp_all

/-! #### The mask of an outside crossing -/

theorem interlacedTriangle_eq_empty (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    {y : Crossing P} (ha : ¬ GeometricInterlaces hP y (xPair hef))
    (hb : ¬ GeometricInterlaces hP y (xPair heg)) (hc : ¬ GeometricInterlaces hP y (xPair hfg)) :
    interlacedTriangle hP e f g y = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  unfold interlacedTriangle at hx
  rw [Finset.mem_filter] at hx
  rcases (mem_triangleCrossings_iff hef heg hfg x).mp hx.1 with rfl | rfl | rfl
  exacts [ha hx.2, hb hx.2, hc hx.2]

theorem interlacedTriangle_eq_filter (hP : CrossingGeometry P) {e f g : ZMod n} {y : Crossing P}
    (h : ZMod n)
    (hall : ∀ x ∈ triangleCrossings P e f g, GeometricInterlaces hP y x ↔ h ∈ x.val) :
    interlacedTriangle hP e f g y = (triangleCrossings P e f g).filter fun x => h ∈ x.val := by
  classical
  ext x
  unfold interlacedTriangle
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hi⟩
    exact ⟨hx, (hall x hx).mp hi⟩
  · rintro ⟨hx, hi⟩
    exact ⟨hx, (hall x hx).mpr hi⟩

theorem interlacedTriangle_eq_filter_e (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    {y : Crossing P} (ha : GeometricInterlaces hP y (xPair hef))
    (hb : GeometricInterlaces hP y (xPair heg)) (hc : ¬ GeometricInterlaces hP y (xPair hfg)) :
    interlacedTriangle hP e f g y = (triangleCrossings P e f g).filter fun x => e ∈ x.val := by
  apply interlacedTriangle_eq_filter hP e
  intro x hx
  rcases (mem_triangleCrossings_iff hef heg hfg x).mp hx with rfl | rfl | rfl
  · exact iff_of_true ha (mem_pair_left e f)
  · exact iff_of_true hb (mem_pair_left e g)
  · refine iff_of_false hc ?_
    rw [xPair_val]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne_of_isCrossing_pair hef, ne_of_isCrossing_pair heg⟩

theorem interlacedTriangle_eq_filter_f (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    {y : Crossing P} (ha : GeometricInterlaces hP y (xPair hef))
    (hb : ¬ GeometricInterlaces hP y (xPair heg)) (hc : GeometricInterlaces hP y (xPair hfg)) :
    interlacedTriangle hP e f g y = (triangleCrossings P e f g).filter fun x => f ∈ x.val := by
  apply interlacedTriangle_eq_filter hP f
  intro x hx
  rcases (mem_triangleCrossings_iff hef heg hfg x).mp hx with rfl | rfl | rfl
  · exact iff_of_true ha (mem_pair_right e f)
  · refine iff_of_false hb ?_
    rw [xPair_val]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(ne_of_isCrossing_pair hef).symm, ne_of_isCrossing_pair hfg⟩
  · exact iff_of_true hc (mem_pair_left f g)

theorem interlacedTriangle_eq_filter_g (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    {y : Crossing P} (ha : ¬ GeometricInterlaces hP y (xPair hef))
    (hb : GeometricInterlaces hP y (xPair heg)) (hc : GeometricInterlaces hP y (xPair hfg)) :
    interlacedTriangle hP e f g y = (triangleCrossings P e f g).filter fun x => g ∈ x.val := by
  apply interlacedTriangle_eq_filter hP g
  intro x hx
  rcases (mem_triangleCrossings_iff hef heg hfg x).mp hx with rfl | rfl | rfl
  · refine iff_of_false ha ?_
    rw [xPair_val]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(ne_of_isCrossing_pair heg).symm, (ne_of_isCrossing_pair hfg).symm⟩
  · exact iff_of_true hb (mem_pair_right e g)
  · exact iff_of_true hc (mem_pair_right f g)

/-- **The mask of an outside crossing** (R-PAR-v6 (P1), both sentences, for one polygon): given the
three triangle crossings and the three adjacent visit pairs of R-LOC-2 (2), a crossing `y ∉ T`
interlaces no crossing of `T` or exactly the pair `{x ∈ T : h ∈ x}` through one bundle edge `h`. -/
theorem mask (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    (hadj_e : AdjacentVisits hP (visitOn (xPair hef) e (mem_pair_left e f))
      (visitOn (xPair heg) e (mem_pair_left e g)))
    (hadj_f : AdjacentVisits hP (visitOn (xPair hef) f (mem_pair_right e f))
      (visitOn (xPair hfg) f (mem_pair_left f g)))
    (hadj_g : AdjacentVisits hP (visitOn (xPair heg) g (mem_pair_right e g))
      (visitOn (xPair hfg) g (mem_pair_right f g)))
    (y : Crossing P) (hy : y.val ∉ triangleSupports e f g) :
    interlacedTriangle hP e f g y = ∅ ∨
      ∃ h ∈ ({e, f, g} : Finset (ZMod n)),
        interlacedTriangle hP e f g y = (triangleCrossings P e f g).filter fun x => h ∈ x.val := by
  have hef' : e ≠ f := ne_of_isCrossing_pair hef
  have heg' : e ≠ g := ne_of_isCrossing_pair heg
  have hfg' : f ≠ g := ne_of_isCrossing_pair hfg
  have hya : y ≠ xPair hef := fun h => hy (by
    rw [h, xPair_val, mem_triangleSupports]; exact Or.inl rfl)
  have hyb : y ≠ xPair heg := fun h => hy (by
    rw [h, xPair_val, mem_triangleSupports]; exact Or.inr (Or.inl rfl))
  have hyc : y ≠ xPair hfg := fun h => hy (by
    rw [h, xPair_val, mem_triangleSupports]; exact Or.inr (Or.inr rfl))
  -- the two visits `u, v` of `y`
  obtain ⟨i₀, i₁, hi₀₁, hyv⟩ := Finset.card_eq_two.mp (crossing_card_two y)
  have hi₀ : i₀ ∈ y.val := by rw [hyv]; exact mem_pair_left i₀ i₁
  have hi₁ : i₁ ∈ y.val := by rw [hyv]; exact mem_pair_right i₀ i₁
  have hi : (⟨i₀, hi₀⟩ : {i // i ∈ y.val}) ≠ ⟨i₁, hi₁⟩ := fun h => hi₀₁ (congrArg Subtype.val h)
  have huv : (⟨y, ⟨i₀, hi₀⟩⟩ : Visit P) ≠ ⟨y, ⟨i₁, hi₁⟩⟩ := visit_ne_of_edge_ne hi
  have hne : ∀ (x : Crossing P) (j : {i // i ∈ x.val}), y ≠ x →
      (⟨x, j⟩ : Visit P) ≠ ⟨y, ⟨i₀, hi₀⟩⟩ ∧ (⟨x, j⟩ : Visit P) ≠ ⟨y, ⟨i₁, hi₁⟩⟩ :=
    fun x j hyx => ⟨visit_ne_of_ne hyx.symm j _, visit_ne_of_ne hyx.symm j _⟩
  -- interlacement with the three triangle crossings, read on the colours of their visits
  have ia := interlaces_iff_col hP hya hi (j₀ := ⟨e, mem_pair_left e f⟩)
    (j₁ := ⟨f, mem_pair_right e f⟩) (fun h => hef' (congrArg Subtype.val h))
  have ib := interlaces_iff_col hP hyb hi (j₀ := ⟨e, mem_pair_left e g⟩)
    (j₁ := ⟨g, mem_pair_right e g⟩) (fun h => heg' (congrArg Subtype.val h))
  have ic := interlaces_iff_col hP hyc hi (j₀ := ⟨f, mem_pair_left f g⟩)
    (j₁ := ⟨g, mem_pair_right f g⟩) (fun h => hfg' (congrArg Subtype.val h))
  -- the three clumps are monochromatic
  have ce := col_of_adjacent hP hadj_e huv (hne _ _ hya).1 (hne _ _ hya).2 (hne _ _ hyb).1
    (hne _ _ hyb).2
  have cf := col_of_adjacent hP hadj_f huv (hne _ _ hya).1 (hne _ _ hya).2 (hne _ _ hyc).1
    (hne _ _ hyc).2
  have cg := col_of_adjacent hP hadj_g huv (hne _ _ hyb).1 (hne _ _ hyb).2 (hne _ _ hyc).1
    (hne _ _ hyc).2
  -- the 2-colouring count
  rcases three_xor_cases ia ib ic ce cf cg with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ |
    ⟨ha, hb, hc⟩
  · exact Or.inl (interlacedTriangle_eq_empty hP hef heg hfg ha hb hc)
  · exact Or.inr ⟨e, by simp, interlacedTriangle_eq_filter_e hP hef heg hfg ha hb hc⟩
  · exact Or.inr ⟨f, by simp, interlacedTriangle_eq_filter_f hP hef heg hfg ha hb hc⟩
  · exact Or.inr ⟨g, by simp, interlacedTriangle_eq_filter_g hP hef heg hfg ha hb hc⟩

/-! #### The clauses of R-PAR-v6 for one polygon -/

/-- (P1), first sentence, for one polygon. -/
theorem parity_of_adjacent (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    (hadj_e : AdjacentVisits hP (visitOn (xPair hef) e (mem_pair_left e f))
      (visitOn (xPair heg) e (mem_pair_left e g)))
    (hadj_f : AdjacentVisits hP (visitOn (xPair hef) f (mem_pair_right e f))
      (visitOn (xPair hfg) f (mem_pair_left f g)))
    (hadj_g : AdjacentVisits hP (visitOn (xPair heg) g (mem_pair_right e g))
      (visitOn (xPair hfg) g (mem_pair_right f g)))
    (y : Crossing P) (hy : y.val ∉ triangleSupports e f g) :
    (interlacedTriangle hP e f g y).card = 0 ∨ (interlacedTriangle hP e f g y).card = 2 := by
  rcases mask hP hef heg hfg hadj_e hadj_f hadj_g y hy with h | ⟨h, hh, hmask⟩
  · left
    rw [h, Finset.card_empty]
  · right
    rw [hmask]
    exact filter_card_two hef heg hfg h hh

/-- (P1), second sentence, for one polygon. -/
theorem interlaced_pair_of_adjacent (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    (hadj_e : AdjacentVisits hP (visitOn (xPair hef) e (mem_pair_left e f))
      (visitOn (xPair heg) e (mem_pair_left e g)))
    (hadj_f : AdjacentVisits hP (visitOn (xPair hef) f (mem_pair_right e f))
      (visitOn (xPair hfg) f (mem_pair_left f g)))
    (hadj_g : AdjacentVisits hP (visitOn (xPair heg) g (mem_pair_right e g))
      (visitOn (xPair hfg) g (mem_pair_right f g)))
    (y : Crossing P) (hy : y.val ∉ triangleSupports e f g)
    (hne : (interlacedTriangle hP e f g y).Nonempty) :
    ∃ h ∈ ({e, f, g} : Finset (ZMod n)),
      interlacedTriangle hP e f g y = (triangleCrossings P e f g).filter fun x => h ∈ x.val := by
  rcases mask hP hef heg hfg hadj_e hadj_f hadj_g y hy with h | hm
  · rw [h] at hne
    exact absurd hne Finset.not_nonempty_empty
  · exact hm

/-- (P2), first sentence, for one polygon. -/
theorem trichotomy_of_adjacent (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g})
    (hadj_e : AdjacentVisits hP (visitOn (xPair hef) e (mem_pair_left e f))
      (visitOn (xPair heg) e (mem_pair_left e g)))
    (hadj_f : AdjacentVisits hP (visitOn (xPair hef) f (mem_pair_right e f))
      (visitOn (xPair hfg) f (mem_pair_left f g)))
    (hadj_g : AdjacentVisits hP (visitOn (xPair heg) g (mem_pair_right e g))
      (visitOn (xPair hfg) g (mem_pair_right f g)))
    (S' : Finset (Crossing P)) (hS : Disjoint S' (triangleCrossings P e f g)) :
    (avail hP e f g S').card = 3 ∨ (avail hP e f g S').card = 1 ∨
      (avail hP e f g S').card = 0 := by
  classical
  by_cases hall : ∀ q ∈ S', interlacedTriangle hP e f g q = ∅
  · left
    have heq : avail hP e f g S' = triangleCrossings P e f g := by
      unfold avail
      apply Finset.filter_true_of_mem
      intro x hx q hq hqx
      have hmem : x ∈ interlacedTriangle hP e f g q := by
        unfold interlacedTriangle
        exact Finset.mem_filter.mpr ⟨hx, hqx⟩
      rw [hall q hq] at hmem
      exact Finset.notMem_empty x hmem
    rw [heq]
    exact triangleCrossings_card hef heg hfg
  · right
    have hex : ∃ q ∈ S', interlacedTriangle hP e f g q ≠ ∅ := by
      by_contra hcon
      exact hall fun q hq => by_contra fun hne => hcon ⟨q, hq, hne⟩
    obtain ⟨q, hq, hne⟩ := hex
    have hqT : q.val ∉ triangleSupports e f g :=
      fun h => Finset.disjoint_left.mp hS hq ((mem_triangleCrossings q).mpr h)
    rcases mask hP hef heg hfg hadj_e hadj_f hadj_g q hqT with h0 | ⟨h, hh, hmask⟩
    · exact absurd h0 hne
    · have hsub : avail hP e f g S' ⊆ (triangleCrossings P e f g).filter fun x => h ∉ x.val := by
        intro x hx
        unfold avail at hx
        rw [Finset.mem_filter] at hx ⊢
        refine ⟨hx.1, fun hhx => hx.2 q hq ?_⟩
        have hmem : x ∈ interlacedTriangle hP e f g q := by
          rw [hmask]
          exact Finset.mem_filter.mpr ⟨hx.1, hhx⟩
        unfold interlacedTriangle at hmem
        exact (Finset.mem_filter.mp hmem).2
      have hle := (Finset.card_le_card hsub).trans (filter_not_card_le_one hef heg hfg h hh)
      omega

/-- (P2), second sentence, for two polygons with the same crossing set whose interlacement graphs
differ exactly on the internal pairs of `T` (R-LOC-2 (4)): `avail` commutes with the transport. -/
theorem avail_map_of_toggle {Q : LabelledTuple n} (hP : CrossingGeometry P)
    (hQ : CrossingGeometry Q) {e f g : ZMod n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (htog : ∀ x y : Crossing P,
      GeometricInterlaces hQ (crossingTransport hs x) (crossingTransport hs y) ↔
        Xor (GeometricInterlaces hP x y)
          (x ≠ y ∧ x.val ∈ triangleSupports e f g ∧ y.val ∈ triangleSupports e f g))
    (S' : Finset (Crossing P)) (hS : Disjoint S' (triangleCrossings P e f g)) :
    avail hQ e f g (S'.map (crossingTransport hs).toEmbedding) =
      (avail hP e f g S').map (crossingTransport hs).toEmbedding := by
  classical
  have hS' : ∀ q ∈ S', q.val ∉ triangleSupports e f g :=
    fun q hq h => Finset.disjoint_left.mp hS hq ((mem_triangleCrossings q).mpr h)
  ext z
  obtain ⟨x, rfl⟩ := (crossingTransport hs).surjective z
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  unfold avail
  rw [Finset.mem_filter, Finset.mem_filter, mem_triangleCrossings, mem_triangleCrossings,
    crossingTransport_support]
  apply and_congr Iff.rfl
  constructor
  · intro H q hq hqx
    apply H (crossingTransport hs q) (Finset.mem_map_of_mem _ hq)
    rw [htog]
    exact Or.inl ⟨hqx, fun h => hS' q hq h.2.1⟩
  · intro H q' hq' hq'x
    rw [Finset.mem_map_equiv] at hq'
    apply H _ hq'
    have hx := (htog ((crossingTransport hs).symm q') x).mp (by rwa [Equiv.apply_symm_apply])
    rcases hx with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h.2.1 (hS' _ hq')

/-! #### The fields of `ParityData` at the event -/

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- `ParityData.triangle_card`, from `LocalizationData.triangle_crossings` (the presupposition
"`T = {x_ef, x_eg, x_fg}`" of R-LOC-2) alone. -/
theorem triangle_card (hL : LocalizationData E e f g δ) :
    ∀ t : E.Parameter, Punctured E δ t → (triangleCrossings (E.curve t) e f g).card = 3 := by
  intro t ht
  obtain ⟨hef, heg, hfg⟩ := hL.triangle_crossings t ht
  exact triangleCrossings_card hef heg hfg

/-- `ParityData.parity` (P1, first sentence), from `LocalizationData.triangle_crossings` and
`LocalizationData.adjacent` (R-LOC-2 (2), adjacency). -/
theorem parity (hL : LocalizationData E e f g δ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t, ∀ y : Crossing (E.curve t),
    y.val ∉ triangleSupports e f g →
    (interlacedTriangle (geomAt E t ht.1) e f g y).card = 0 ∨
      (interlacedTriangle (geomAt E t ht.1) e f g y).card = 2 := by
  intro t ht y hy
  obtain ⟨hef, heg, hfg⟩ := hL.triangle_crossings t ht
  obtain ⟨he, hf, hg⟩ := hL.adjacent t ht hef heg hfg
  exact parity_of_adjacent (geomAt E t ht.1) hef heg hfg he hf hg y hy

/-- `ParityData.interlaced_pair` (P1, second sentence), from `LocalizationData.triangle_crossings`
and `LocalizationData.adjacent`. -/
theorem interlaced_pair (hL : LocalizationData E e f g δ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t, ∀ y : Crossing (E.curve t),
    y.val ∉ triangleSupports e f g → (interlacedTriangle (geomAt E t ht.1) e f g y).Nonempty →
    ∃ h ∈ ({e, f, g} : Finset (ZMod n)),
      interlacedTriangle (geomAt E t ht.1) e f g y =
        (triangleCrossings (E.curve t) e f g).filter fun x => h ∈ x.val := by
  intro t ht y hy hne
  obtain ⟨hef, heg, hfg⟩ := hL.triangle_crossings t ht
  obtain ⟨he, hf, hg⟩ := hL.adjacent t ht hef heg hfg
  exact interlaced_pair_of_adjacent (geomAt E t ht.1) hef heg hfg he hf hg y hy hne

/-- `ParityData.trichotomy` (P2, first sentence), from `LocalizationData.triangle_crossings` and
`LocalizationData.adjacent`. -/
theorem trichotomy (hL : LocalizationData E e f g δ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t, ∀ S' : Finset (Crossing (E.curve t)),
    Disjoint S' (triangleCrossings (E.curve t) e f g) →
    (avail (geomAt E t ht.1) e f g S').card = 3 ∨ (avail (geomAt E t ht.1) e f g S').card = 1 ∨
      (avail (geomAt E t ht.1) e f g S').card = 0 := by
  intro t ht S' hS
  obtain ⟨hef, heg, hfg⟩ := hL.triangle_crossings t ht
  obtain ⟨he, hf, hg⟩ := hL.adjacent t ht hef heg hfg
  exact trichotomy_of_adjacent (geomAt E t ht.1) hef heg hfg he hf hg S' hS

/-- `ParityData.avail_wall_invariant` (P2, second sentence), from
`LocalizationData.interlace_toggle` (R-LOC-2 (4)) alone. -/
theorem avail_wall_invariant (hL : LocalizationData E e f g δ) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ S' : Finset (Crossing (E.curve t)), Disjoint S' (triangleCrossings (E.curve t) e f g) →
      avail (geomAt E t' ht'.1) e f g (S'.map (crossingTransport hs).toEmbedding) =
        (avail (geomAt E t ht.1) e f g S').map (crossingTransport hs).toEmbedding := by
  intro t t' ht ht' hopp hs S' hS
  exact avail_map_of_toggle (geomAt E t ht.1) (geomAt E t' ht'.1) hs
    (hL.interlace_toggle t t' ht ht' hopp hs) S' hS

/-- **All five fields**: `ParityData` from `LocalizationData` at the same punctured radius. The row
theorem `RProof.parity` is this applied to the `δ` of `RProof.localization`. -/
theorem parityData (hL : LocalizationData E e f g δ) : ParityData E e f g δ :=
  ⟨triangle_card hL, parity hL, interlaced_pair hL, trichotomy hL, avail_wall_invariant hL⟩

end P1

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
