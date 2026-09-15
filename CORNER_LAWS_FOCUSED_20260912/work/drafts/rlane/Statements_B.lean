import Bridge.B3
import SM.TripleWallSides
import SM.GaussAdjacencyTransport
import SM.GeometricRecords
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! # R lane, Designer B — statements for the four X₁-free R rows

Rows 166 R:localization (`RProof.localization`), 167 R:parity (`RProof.parity`), 169
R:fibre_partition (`RProof.fibre_partition`), 171 R:generic_table (`RProof.generic_table`).
Draft written 2026-09-14 by a statement-designer subagent (Designer B, text-first) of the pod
executor; checked with `lake env lean` (every row theorem is `sorry`; the abstract tables are
proved by `decide`). Companion notes: work/drafts/rlane/NOTES_B.md.

Sources (frozen): reference/R/RA/R_ATTACHMENT_WARRANTS.md (R-LOC-2 lines 16–29 and its proof, R-PAR-v6
lines 107–121 and its proof), R_ASSEMBLY_SPEC.md (fibre sums (1)–(3)), reference/R/RA/
R_GENERIC_ORBIT_ACTUAL_TABLE.md (the generic orbit table), R_GENERIC_NONSELECTED_SELECTOR_PROOF.md
("Oriented line-order calculation" (1)–(3), "Which pair is selected" (4) and the six-case table),
R_GENERIC_COMMON_TRANSPORT_PROOF.md ("Statement and canonical branch" (1)).

## Domain (decision F2(A), work/AUTHOR_NOTES.md 2026-09-13): no narrowing

Every row is stated on CV's own locus: a CV event `E : CV.Event n` (CV:def:event, CV/Events.lean)
that is a simple transversal Reidemeister III event `E.IsSimpleRIII e f g h3 h4e h4f h4g` (the forced
bundle of CV ax:R, d10_axioms.tex:18–24, defined in CV/Events.lean). The sides are the CV-generic
polygons `E.curve t`, `t ≠ 0` (`CV.Generic`, CV/Setup.lean); the Gauss word, visits and
interlacement graph of a CV-generic polygon are the accepted geometric objects on
`CrossingGeometry (E.curve t)` (`CV.Generic.crossingGeometry`): `SM.geometricVisitPosition`,
`SM.geometricGaussList`, `SM.GeometricInterlaces`, `CV.Ind`, `CV.U` (CV:def:interlace, row 134, is
stated on exactly these). Where the RA text speaks of "the SM triple germ" — R-LOC-2's proof route
through lem:triple-sides — the SM instance is the CV event `Bridge.eventOfTriple hn g h` of a germ
`g.TripleAt e f k` (Bridge:B1–B3), and the row is restated for it (`localization_of_tripleAt`).

## Notion map (RA text → Lean)

| RA text | Lean |
|---|---|
| simple transversal RIII event `t ↦ P(t)`, zero set the forced bundle | `E : CV.Event n`, `E.IsSimpleRIII e f g …` |
| "on a punctured neighbourhood of t = 0" | `∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ ∀ t, Punctured E δ t → …` |
| "the two sides", `P₊`, `P₋` | `t t'` with `Opposite E t t'` (`t·t' < 0`); one side: `SameSide E t t'` |
| the crossing set indexed by carrying edge pairs | `IsCrossing (E.curve t) s`, `s : Finset (ZMod n)` (SM def:crossings); identification `crossingTransport hs` |
| `T = {x_ef, x_eg, x_fg}` | `triangleSupports e f g`, `triangleCrossings P e f g`, `xPair hef : Crossing P` |
| the two visits of a crossing, "crossing-visits of the traversal circle" | `Visit P`, `visitOn x h hh`, position `geometricVisitPosition hP v` |
| "adjacent crossing-visits of the traversal circle" | `AdjacentVisits hP v w` (no crossing visit strictly inside one of the two arcs) |
| "their order along that edge", `t_f` | `CV.crossParam P e f` (= `SM.edgeParameter P e f`, `CV.crossParam_eq_edgeParameter`) |
| interlacement `G^±`, `c ∼ c'` | `GeometricInterlaces (geomAt E t ht) x y`, graph `geometricInterlacementGraph` |
| `G⁺ = G⁻ △ binom(T,2)` | `Xor (GeometricInterlaces …) (x ≠ y ∧ x ∈ T ∧ y ∈ T)` |
| clumps `C_e, C_f, C_g` | `clump P e f g h` |
| the interlaced pair `I(y)` | `interlacedTriangle hP e f g y` |
| `avail(S')`, `𝓐(Q)` | `avail hP e f g S'` |
| `Ind(G_P)` | `CV.Ind hP` (row 134) |
| `Ind(G[W])` (outside independent supports) | `outsideSupports hP e f g` |
| `Ind(G_±[𝓐(Q)])` (the local fibre) | `localFibre hP e f g Q` |
| `F_±(S)`, the complete summand of def:X1 | an arbitrary `F : Finset (Crossing P) → M` (X₁ is not in Lean; see NOTES_B) |
| `Φ_±(Q) = Σ_J F_±(Q ∪ J)` | `fibreSum hP e f g F Q` |
| `D_ef = det(u_e,u_f)`, `s_a` | `CV.G5 P e f`, `strandSign P e f` |
| `Δ = G3(e,f,g)`, `δ` | `CV.G3 P e f g`, `concurrenceSign P e f g` |
| `q_e = sgn(t_ef − t_eg)` | `orderSign P e f g` |
| alternating / nonalternating sign triples | `IsAlternating sa sb sc` |
| selected-conditions (4) | `SelectedAB`, `SelectedAC`, `SelectedBC` |
| the local words `P = a b A a c B b c C`, `E = b a A c a B c b C` | `triangleVisits hP e f g` is a rotation of the printed visit list; abstract skeleton `wordP`, `wordE` |
| successor cycles of the table | `cycleList (localSucc word twin S) i`, clauses of `SuccessorTable` |
| residual words (`c B c C`, …) | `residualWord`, clauses of `ResidualWordTable` |
| local undominated table | `CV.U hP S ∩ triangleCrossings P e f g` |
-/

namespace RProof

open SM

/-! ## Part 0 — abstract combinatorics (no geometry)

### The fibre partition of a state sum over independent sets (R_ASSEMBLY_SPEC.md (1)–(3), abstract form) -/

section AbstractGraph

variable {V : Type*} [DecidableEq V]

/-- R_ASSEMBLY_SPEC.md (1): "For each independent outside support `Q` in `W`, define its availability
set by `𝓐(Q) = {t ∈ T : no element of Q is adjacent to t}`" — for an arbitrary graph. -/
def graphAvail (G : SimpleGraph V) [DecidableRel G.Adj] (T Q : Finset V) : Finset V :=
  T.filter fun x => ∀ q ∈ Q, ¬ G.Adj q x

open scoped Classical in
/-- The abstract engine of R:fibre_partition (proof-lane lemma, not a row): "Every independent
support `S` on either side decomposes uniquely into `Q = S ∩ W` and `J = S ∩ T` … This proves a
bijection of supports … The finite bijection just established partitions the exact state sum",
R_ASSEMBLY_SPEC.md (2)–(3), for an arbitrary finite graph `G`, vertex set `T` and summand `F`. -/
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
bichromatic pairs (monochromatic) or exactly 2 … Never 1, never 3." (proof-lane lemma, proved). -/
theorem two_colouring_bichromatic_pairs (χ : Fin 3 → Bool) :
    ((Finset.univ : Finset (Fin 3 × Fin 3)).filter fun p => p.1 < p.2 ∧ χ p.1 ≠ χ p.2).card = 0 ∨
    ((Finset.univ : Finset (Fin 3 × Fin 3)).filter fun p => p.1 < p.2 ∧ χ p.1 ≠ χ p.2).card = 2 := by
  revert χ; decide

/-! ### The local skeleton of R_GENERIC_ORBIT_ACTUAL_TABLE.md

"Use the three unchanged exterior gaps `A,B,C` between the RIII strand blocks:
`P = a b A a c B b c C` (edges ab, bc; centre b), `E = b a A c a B c b C` (edge ac; b isolated)."
The nine positions `Fin 9` of a local word carry a letter: a local crossing `a, b, c` (`Sum.inl 0/1/2`)
or an opaque exterior gap `A, B, C` (`Sum.inr 0/1/2`); the six crossing positions are the printed
visits `1,…,6` in order (positions `0,1,3,4,6,7`), the gaps sit at positions `2,5,8`. Oriented
smoothing at a selected crossing reconnects the traversal at its two visits: the strand arriving at
a selected visit continues after the *twin* visit (`localSucc`). The successor cycles of the table are
the cycles of that map; the identification of this skeleton with the actual carriers
(`smoothingSuccessor`, Carrier lane / CV:def:smoothing) is NOT part of this file (see NOTES_B). -/

/-- A letter of the local word: a local crossing (`inl`: `0 = a`, `1 = b`, `2 = c`) or an exterior gap
(`inr`: `0 = A`, `1 = B`, `2 = C`). -/
abbrev LocalLetter := Fin 3 ⊕ Fin 3

/-- "`P = a b A a c B b c C`". -/
def wordP : Fin 9 → LocalLetter :=
  ![.inl 0, .inl 1, .inr 0, .inl 0, .inl 2, .inr 1, .inl 1, .inl 2, .inr 2]

/-- The twin (other visit of the same crossing) of each position of `P`; gaps are their own twin. -/
def twinP : Fin 9 → Fin 9 := ![3, 6, 2, 0, 7, 5, 1, 4, 8]

/-- "`E = b a A c a B c b C`". -/
def wordE : Fin 9 → LocalLetter :=
  ![.inl 1, .inl 0, .inr 0, .inl 2, .inl 0, .inr 1, .inl 2, .inl 1, .inr 2]

/-- The twin of each position of `E`. -/
def twinE : Fin 9 → Fin 9 := ![7, 4, 2, 6, 1, 5, 3, 0, 8]

/-- Well-formedness of the two skeletons: the twin map is an involution exchanging the two positions
of every crossing letter and fixing the gaps. -/
theorem skeleton_wellFormed :
    (∀ i, wordP (twinP i) = wordP i ∧ twinP (twinP i) = i ∧
      ((∃ x, wordP i = .inl x) → twinP i ≠ i)) ∧
    (∀ i, wordE (twinE i) = wordE i ∧ twinE (twinE i) = i ∧
      ((∃ x, wordE i = .inl x) → twinE i ≠ i)) := by
  decide

/-- Whether position `i` is a visit of a selected local crossing (`S ⊆ {a, b, c}`). -/
def isSelected (w : Fin 9 → LocalLetter) (S : Finset (Fin 3)) (i : Fin 9) : Bool :=
  match w i with
  | .inl x => decide (x ∈ S)
  | .inr _ => false

/-- The oriented-smoothing successor on the local skeleton: "Regard oriented smoothing as
reconnecting the traversal circle at the two visits of each selected crossing" (R-EXTERIOR-1 §1):
after a selected visit the strand continues after its twin, otherwise it continues to the next
position (gaps are single opaque positions, "fixed boundary-to-boundary successor paths"). -/
def localSucc (w : Fin 9 → LocalLetter) (tw : Fin 9 → Fin 9) (S : Finset (Fin 3)) (i : Fin 9) :
    Fin 9 :=
  if isSelected w S i then tw i + 1 else i + 1

/-- The cycle of the successor map through position `i`, as a list in cyclic order (a rotation of the
printed cycle). -/
def cycleList (f : Fin 9 → Fin 9) (i : Fin 9) : List (Fin 9) :=
  ((List.range 9).map fun k => f^[k] i).dedup

/-- The underlying set of that cycle. -/
def localCycle (f : Fin 9 → Fin 9) (i : Fin 9) : Finset (Fin 9) := (cycleList f i).toFinset

/-- The residual word of a cycle: its letters read in cyclic order, keeping the gaps and the local
crossings in `U` (the local undominated set) and erasing the rest. -/
def residualWord (w : Fin 9 → LocalLetter) (U : Finset (Fin 3)) (f : Fin 9 → Fin 9) (i : Fin 9) :
    List LocalLetter :=
  (cycleList f i).filterMap fun j =>
    match w j with
    | .inl x => if x ∈ U then some (.inl x) else none
    | .inr g => some (.inr g)

/-- The printed "Successor cycles" table (R_GENERIC_ORBIT_ACTUAL_TABLE.md), on the local skeleton.
Visits `1…6` are positions `0,1,3,4,6,7`; gaps `A,B,C` are positions `2,5,8`; each printed cycle
`(…)[…]` is one cycle of `localSucc`, listed here as a rotation class of positions. -/
def SuccessorTable : Prop :=
  -- P empty : (123456)[ABC]
  List.IsRotated (cycleList (localSucc wordP twinP ∅) 0) [0, 1, 2, 3, 4, 5, 6, 7, 8] ∧
  -- P a : (1456)[BC] (23)[A]
  List.IsRotated (cycleList (localSucc wordP twinP {0}) 0) [0, 4, 5, 6, 7, 8] ∧
  List.IsRotated (cycleList (localSucc wordP twinP {0}) 1) [1, 2, 3] ∧
  -- P b : (126)[C] (345)[AB]
  List.IsRotated (cycleList (localSucc wordP twinP {1}) 0) [0, 1, 7, 8] ∧
  List.IsRotated (cycleList (localSucc wordP twinP {1}) 3) [3, 4, 5, 6, 2] ∧
  -- P c : (1234)[AC] (56)[B]
  List.IsRotated (cycleList (localSucc wordP twinP {2}) 0) [0, 1, 2, 3, 4, 8] ∧
  List.IsRotated (cycleList (localSucc wordP twinP {2}) 6) [6, 7, 5] ∧
  -- P ac : (14)[C] (23)[A] (56)[B]
  List.IsRotated (cycleList (localSucc wordP twinP {0, 2}) 0) [0, 4, 8] ∧
  List.IsRotated (cycleList (localSucc wordP twinP {0, 2}) 1) [1, 2, 3] ∧
  List.IsRotated (cycleList (localSucc wordP twinP {0, 2}) 6) [6, 7, 5] ∧
  -- E empty : (123456)[ABC]
  List.IsRotated (cycleList (localSucc wordE twinE ∅) 0) [0, 1, 2, 3, 4, 5, 6, 7, 8] ∧
  -- E a : (1256)[BC] (34)[A]
  List.IsRotated (cycleList (localSucc wordE twinE {0}) 0) [0, 1, 5, 6, 7, 8] ∧
  List.IsRotated (cycleList (localSucc wordE twinE {0}) 3) [3, 4, 2] ∧
  -- E b : (1)[C] (23456)[AB]
  List.IsRotated (cycleList (localSucc wordE twinE {1}) 0) [0, 8] ∧
  List.IsRotated (cycleList (localSucc wordE twinE {1}) 1) [1, 2, 3, 4, 5, 6, 7] ∧
  -- E c : (1236)[AC] (45)[B]
  List.IsRotated (cycleList (localSucc wordE twinE {2}) 0) [0, 1, 2, 3, 7, 8] ∧
  List.IsRotated (cycleList (localSucc wordE twinE {2}) 4) [4, 5, 6] ∧
  -- E ab : (1)[C] (256)[B] (34)[A]
  List.IsRotated (cycleList (localSucc wordE twinE {0, 1}) 0) [0, 8] ∧
  List.IsRotated (cycleList (localSucc wordE twinE {0, 1}) 1) [1, 5, 6, 7] ∧
  List.IsRotated (cycleList (localSucc wordE twinE {0, 1}) 3) [3, 4, 2] ∧
  -- E bc : (1)[C] (236)[A] (45)[B]
  List.IsRotated (cycleList (localSucc wordE twinE {1, 2}) 0) [0, 8] ∧
  List.IsRotated (cycleList (localSucc wordE twinE {1, 2}) 1) [1, 2, 3, 7] ∧
  List.IsRotated (cycleList (localSucc wordE twinE {1, 2}) 4) [4, 5, 6]

/-- The printed residual words (R_GENERIC_ORBIT_ACTUAL_TABLE.md, "Earliest remaining interface"
and the preceding paragraph), on the local skeleton with the local undominated sets of the table:
"For endpoint `a`, the unsigned residual word is `c B c C` on P versus `b B b C` on E, with the
A-carrier unchanged. For endpoint `c`, it is `a A a C` versus `b A b C`, with the B-carrier unchanged.
For the selected row, P-`b` has no local residual on carriers `C|AB`; E-`b` has residual
`a A c a B c` on `AB` …; and P-`ac` has three local-empty carriers `C|A|B`." -/
def ResidualWordTable : Prop :=
  -- endpoint a: U_P(a) = {c}, U_E(a) = {b}
  List.IsRotated (residualWord wordP {2} (localSucc wordP twinP {0}) 0) [.inl 2, .inr 1, .inl 2, .inr 2] ∧
  List.IsRotated (residualWord wordP {2} (localSucc wordP twinP {0}) 1) [.inr 0] ∧
  List.IsRotated (residualWord wordE {1} (localSucc wordE twinE {0}) 0) [.inl 1, .inr 1, .inl 1, .inr 2] ∧
  List.IsRotated (residualWord wordE {1} (localSucc wordE twinE {0}) 3) [.inr 0] ∧
  -- endpoint c: U_P(c) = {a}, U_E(c) = {b}
  List.IsRotated (residualWord wordP {0} (localSucc wordP twinP {2}) 0) [.inl 0, .inr 0, .inl 0, .inr 2] ∧
  List.IsRotated (residualWord wordP {0} (localSucc wordP twinP {2}) 6) [.inr 1] ∧
  List.IsRotated (residualWord wordE {1} (localSucc wordE twinE {2}) 0) [.inl 1, .inr 0, .inl 1, .inr 2] ∧
  List.IsRotated (residualWord wordE {1} (localSucc wordE twinE {2}) 4) [.inr 1] ∧
  -- selected row: U_P(b) = ∅ (carriers C | AB), U_E(b) = {a, c} (carriers C | AB)
  List.IsRotated (residualWord wordP ∅ (localSucc wordP twinP {1}) 0) [.inr 2] ∧
  List.IsRotated (residualWord wordP ∅ (localSucc wordP twinP {1}) 3) [.inr 0, .inr 1] ∧
  List.IsRotated (residualWord wordE {0, 2} (localSucc wordE twinE {1}) 0) [.inr 2] ∧
  List.IsRotated (residualWord wordE {0, 2} (localSucc wordE twinE {1}) 1)
    [.inl 0, .inr 0, .inl 2, .inl 0, .inr 1, .inl 2] ∧
  -- P-ac: U_P(ac) = ∅, three local-empty carriers C | A | B
  List.IsRotated (residualWord wordP ∅ (localSucc wordP twinP {0, 2}) 0) [.inr 2] ∧
  List.IsRotated (residualWord wordP ∅ (localSucc wordP twinP {0, 2}) 1) [.inr 0] ∧
  List.IsRotated (residualWord wordP ∅ (localSucc wordP twinP {0, 2}) 6) [.inr 1]

/-- The two tables hold on the skeleton (finite computation). -/
theorem successorTable : SuccessorTable := by
  unfold SuccessorTable; decide

theorem residualWordTable : ResidualWordTable := by
  unfold ResidualWordTable; decide

/-! ## Part 1 — the triangle of a simple RIII event, sides, visits -/

variable {n : ℕ} [NeZero n]

/-- Crossings are carried by their edge pairs (`Finset (ZMod n)`), so equality of crossings is
decidable; this lets the supports be handled with `∪`, `∩`, `\\` (no classical choice). -/
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

/-- The crossing `x_{ij}` carried by the edge pair `{i, j}`. -/
def xPair {P : LabelledTuple n} {i j : ZMod n} (h : IsCrossing P {i, j}) : Crossing P := ⟨{i, j}, h⟩

/-- The visit of the crossing `x` on its edge `h` (one of the two "occurrences of `x` in the Gauss
word"). -/
def visitOn {P : LabelledTuple n} (x : Crossing P) (h : ZMod n) (hh : h ∈ x.val) : Visit P := ⟨x, h, hh⟩

/-- "adjacent crossing-visits of the traversal circle": `v ≠ w` and no crossing visit lies strictly
inside one of the two arcs into which `v, w` cut the traversal circle `Γ` (R-LOC-2 (2b): "the two
visits are adjacent among crossing visits"). The traversal circle is the one of def:gauss, cyclic
order `traversalBetween`; positions are the geometric visit positions of the CV-generic polygon. -/
def AdjacentVisits {P : LabelledTuple n} (hP : CrossingGeometry P) (v w : Visit P) : Prop :=
  v ≠ w ∧
  ((∀ u : Visit P, ¬ traversalBetween (geometricVisitPosition hP v) (geometricVisitPosition hP u)
      (geometricVisitPosition hP w)) ∨
   (∀ u : Visit P, ¬ traversalBetween (geometricVisitPosition hP w) (geometricVisitPosition hP u)
      (geometricVisitPosition hP v)))

/-- "the two crossings of `T` carried by that edge" (R-PAR: "Write the three adjacent pairs as clumps
`C_e = {visits of x_ef, x_eg on e}`, `C_f`, `C_g`"): the visits of triangle crossings on the edge `h`. -/
noncomputable def clump (P : LabelledTuple n) (e f g h : ZMod n) : Finset (Visit P) :=
  Finset.univ.filter fun v => v.1.val ∈ triangleSupports e f g ∧ v.2.val = h

/-- "each clump lies wholly in one of the two arcs that `u, v` cut `Γ` into. This is a 2-colouring": the
colour of a set of visits `C` relative to the visits `u, v` — `C` lies in the arc from `u` to `v`. -/
def InArc {P : LabelledTuple n} (hP : CrossingGeometry P) (u v : Visit P) (C : Finset (Visit P)) :
    Prop :=
  ∀ w ∈ C, traversalBetween (geometricVisitPosition hP u) (geometricVisitPosition hP w)
    (geometricVisitPosition hP v)

/-- "the interlaced pair" `I(y)`: the triangle crossings interlacing `y`. -/
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
`F` (the complete summand `F_±` of CV:def:X1 is not yet in Lean; see NOTES_B). -/
noncomputable def fibreSum {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n)
    {M : Type} [AddCommMonoid M] (F : Finset (Crossing P) → M) (Q : Finset (Crossing P)) : M :=
  ∑ J ∈ localFibre hP e f g Q, F (Q ∪ J)

/-! ### Sides of an event -/

/-- The CV genericity of the side polygon `P(t)`, `t ≠ 0`. -/
theorem genericAt (E : CV.Event n) (t : E.Parameter) (ht : t.val ≠ 0) : CV.Generic (E.curve t) :=
  E.generic_punctured t ht

/-- The crossing geometry of the side polygon `P(t)` (the domain of the Gauss word and of
CV:def:interlace). -/
theorem geomAt (E : CV.Event n) (t : E.Parameter) (ht : t.val ≠ 0) : CrossingGeometry (E.curve t) :=
  (genericAt E t ht).crossingGeometry

/-- "on a punctured neighbourhood of `t = 0`": `0 < |t| < δ`. -/
def Punctured (E : CV.Event n) (δ : ℝ) (t : E.Parameter) : Prop := t.val ≠ 0 ∧ |t.val| < δ

/-- "the two sides" of the wall: parameters of opposite signs. -/
def Opposite (E : CV.Event n) (t t' : E.Parameter) : Prop := t.val * t'.val < 0

/-- One side of the wall: parameters of the same sign. -/
def SameSide (E : CV.Event n) (t t' : E.Parameter) : Prop := 0 < t.val * t'.val

/-! ## Row 166 — R:localization (R-LOC-2, R_ATTACHMENT_WARRANTS.md lines 12–29)

Printed statement: "Let `t ↦ P(t)` be a simple transversal Reidemeister-III event with zero set
exactly the forced bundle `Z = {G3_{e,f,g}, G4_{e;f,g}, G4_{f;e,g}, G4_{g;e,f}}`, `e < f < g` pairwise
remote and concurrent at `t = 0` at a point interior to all three. Let `T = {x_ef, x_eg, x_fg}`. Then on
a punctured neighbourhood of `t = 0`:
1. the crossing set, indexed by carrying edge pairs, is constant;
2. on each of `e, f, g` the two crossings of `T` carried by that edge occupy adjacent crossing-visits
   of the traversal circle, and their order along that edge is opposite on the two sides;
3. every other pair of crossings keeps its order along every edge;
4. hence `G⁺ = G⁻ △ binom(T,2)`: the three internal pairs of `T` toggle and no other pair changes.
Corollary. The induced graph `G[T]` maps to its complement in `T` across the wall." -/

/-- R-LOC-2, clause by clause, for the event `E`, the triangle `e, f, g` and the punctured radius `δ`. -/
structure LocalizationData (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "Let `T = {x_ef, x_eg, x_fg}`": the three crossings of the triangle exist on the whole punctured
  neighbourhood (presupposed by the statement; the three pairs are active there). -/
  triangle_crossings : ∀ t : E.Parameter, Punctured E δ t →
    IsCrossing (E.curve t) {e, f} ∧ IsCrossing (E.curve t) {e, g} ∧ IsCrossing (E.curve t) {f, g}
  /-- (1) "the crossing set, indexed by carrying edge pairs, is constant". -/
  crossing_set_constant : ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' →
    ∀ s : Finset (ZMod n), IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s
  /-- (2), adjacency: "on each of `e, f, g` the two crossings of `T` carried by that edge occupy adjacent
  crossing-visits of the traversal circle". -/
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
  parameters `t_f = crossParam P e f` along `e` (def:guarded), likewise along `f` and `g`. -/
  order_reverses : ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' → Opposite E t t' →
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
  /-- Implicit in "on the two sides": on one side the order of any two crossings along a common edge
  is constant (the side is one chamber; lem:guardconst on the active `G4`). -/
  order_same_side : ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' → SameSide E t t' →
    ∀ h i j : ZMod n, IsCrossing (E.curve t) {h, i} → IsCrossing (E.curve t) {h, j} →
      (CV.crossParam (E.curve t) h i < CV.crossParam (E.curve t) h j ↔
        CV.crossParam (E.curve t') h i < CV.crossParam (E.curve t') h j)
  /-- (3) "every other pair of crossings keeps its order along every edge": two crossings on the edge
  `h` that are not both triangle crossings (a bundle pair is two triangle crossings sharing `h`). -/
  other_orders_persist : ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' → Opposite E t t' →
    ∀ h i j : ZMod n, IsCrossing (E.curve t) {h, i} → IsCrossing (E.curve t) {h, j} →
      ¬ (({h, i} : Finset (ZMod n)) ∈ triangleSupports e f g ∧
          ({h, j} : Finset (ZMod n)) ∈ triangleSupports e f g) →
      (CV.crossParam (E.curve t) h i < CV.crossParam (E.curve t) h j ↔
        CV.crossParam (E.curve t') h i < CV.crossParam (E.curve t') h j)
  /-- (3), at the level of the Gauss words: "the two Gauss words differ by exactly the three
  transpositions of (2a)" — exactly the visit pairs of a bundle pair (two crossings on a common edge
  with `x.val ∪ y.val = {e, f, g}`) reverse, every other same-edge visit pair keeps its order (the
  accepted predicate `SM.ExactTriangleVisitOrders`, transported along (1)). -/
  gauss_words : ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' → Opposite E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
      ExactTriangleVisitOrders (E.curve t) (E.curve t') e f g hs
  /-- (4) "hence `G⁺ = G⁻ △ binom(T,2)`: the three internal pairs of `T` toggle and no other pair
  changes" — crossings identified across the wall by their carrying edge pairs (`crossingTransport`). -/
  interlace_toggle : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    Opposite E t t' →
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
  /-- Corollary: "The induced graph `G[T]` maps to its complement in `T` across the wall." -/
  complement_on_triangle : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    Opposite E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ x y : Crossing (E.curve t), x.val ∈ triangleSupports e f g → y.val ∈ triangleSupports e f g →
      x ≠ y →
      (GeometricInterlaces (geomAt E t' ht'.1) (crossingTransport hs x) (crossingTransport hs y) ↔
        ¬ GeometricInterlaces (geomAt E t ht.1) x y)

/-- **Row 166, R:localization** (R-LOC-2): for every simple transversal RIII event of CV ax:R, on a
punctured neighbourhood of `t = 0` of some radius `δ`, all clauses of `LocalizationData`. -/
theorem localization (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ LocalizationData E e f g δ := by
  sorry

/-- The CV event of an SM type-`T` germ (Bridge:B1) is a simple transversal RIII event of CV ax:R
(Bridge:B2 for the zero set, the concurrency point of `TripleAt`, Bridge:B3 for transversality). -/
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

/-- R-LOC-2 for the SM triple germ (the route of the scout plan and of lem:triple-sides): the CV event
`Bridge.eventOfTriple hn g h` of a germ `g.TripleAt e f k` satisfies `LocalizationData`. This is the
proof-lane entry point; `localization` follows for such events by `isSimpleRIII_eventOfTriple`, and the
accepted `SM.TripleWallSidesData`/`triple_wall_sides` supplies clauses (1)–(3) on the SM locus. -/
theorem localization_of_tripleAt (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ LocalizationData (Bridge.eventOfTriple hn g h) e f k δ := by
  sorry

/-- The number of edges of the local graph `G[T]` (`0` or `3`: the extreme orbit; `1` or `2`: the
generic orbit). -/
noncomputable def localEdgeCount {P : LabelledTuple n} (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) : ℕ := by
  classical
  exact (if GeometricInterlaces hP (xPair hef) (xPair heg) then 1 else 0) +
    (if GeometricInterlaces hP (xPair hef) (xPair hfg) then 1 else 0) +
    (if GeometricInterlaces hP (xPair heg) (xPair hfg) then 1 else 0)

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

/-- Corollary of R-LOC-2, second sentence: "Both orbits of that map occur — the extreme orbit
(empty ↔ complete) and the one-edge ↔ two-edge orbit." An existence claim about events, NOT
consumed by CV:ax:R (kept outside the row bundle; see NOTES_B). -/
theorem both_orbits_occur :
    (∃ (X : SimpleRIIIEvent) (t : X.E.Parameter) (ht : t.val ≠ 0)
        (hef : IsCrossing (X.E.curve t) {X.e, X.f}) (heg : IsCrossing (X.E.curve t) {X.e, X.g})
        (hfg : IsCrossing (X.E.curve t) {X.f, X.g}),
        localEdgeCount (geomAt X.E t ht) hef heg hfg = 0) ∧
    (∃ (X : SimpleRIIIEvent) (t : X.E.Parameter) (ht : t.val ≠ 0)
        (hef : IsCrossing (X.E.curve t) {X.e, X.f}) (heg : IsCrossing (X.E.curve t) {X.e, X.g})
        (hfg : IsCrossing (X.E.curve t) {X.f, X.g}),
        localEdgeCount (geomAt X.E t ht) hef heg hfg = 1) := by
  sorry

/-! ## Row 167 — R:parity (R-PAR-v6, R_ATTACHMENT_WARRANTS.md lines 103–121)

Printed statement: "Let `t ↦ P(t)` be a simple transversal Reidemeister-III event with triangle
`T = {x_ef, x_eg, x_fg}`, and let `P` be either side's polygon, near the wall. Then:
(P1) Parity. Every crossing `y ∉ T` interlaces exactly 0 or exactly 2 of the three crossings of `T` —
never 1, never 3. Moreover the interlaced pair, when nonempty, is one of `{x_ef,x_eg}`, `{x_ef,x_fg}`,
`{x_eg,x_fg}` — the two crossings sharing one of the three bundle edges.
(P2) Trichotomy. For any set `S'` of crossings disjoint from `T`, the set
`avail(S') = {x ∈ T : x interlaces no member of S'}` has size 3, 1, or 0 — never 2. And `avail(S')` is
the same set on the two sides of the wall." -/

/-- R-PAR-v6, clause by clause, for the event `E`, the triangle `e, f, g`, "near the wall" = `0 < |t| < δ`. -/
structure ParityData (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "the three crossings of `T`": the triangle has exactly three crossings on either side. -/
  triangle_card : ∀ t : E.Parameter, Punctured E δ t → (triangleCrossings (E.curve t) e f g).card = 3
  /-- (P1) "Every crossing `y ∉ T` interlaces exactly 0 or exactly 2 of the three crossings of `T` …
  Moreover the interlaced pair, when nonempty, is … the two crossings sharing one of the three bundle
  edges" `h ∈ {e, f, g}`. -/
  parity : ∀ t : E.Parameter, ∀ ht : Punctured E δ t, ∀ y : Crossing (E.curve t),
    y.val ∉ triangleSupports e f g →
    (interlacedTriangle (geomAt E t ht.1) e f g y).card = 0 ∨
    ((interlacedTriangle (geomAt E t ht.1) e f g y).card = 2 ∧
      ∃ h ∈ ({e, f, g} : Finset (ZMod n)),
        interlacedTriangle (geomAt E t ht.1) e f g y =
          (triangleCrossings (E.curve t) e f g).filter fun x => h ∈ x.val)
  /-- (P2) "For any set `S'` of crossings disjoint from `T`, the set `avail(S')` has size 3, 1, or 0". -/
  trichotomy : ∀ t : E.Parameter, ∀ ht : Punctured E δ t, ∀ S' : Finset (Crossing (E.curve t)),
    Disjoint S' (triangleCrossings (E.curve t) e f g) →
    (avail (geomAt E t ht.1) e f g S').card = 3 ∨ (avail (geomAt E t ht.1) e f g S').card = 1 ∨
      (avail (geomAt E t ht.1) e f g S').card = 0
  /-- (P2) "And `avail(S')` is the same set on the two sides of the wall" (crossings identified by
  their carrying edge pairs). -/
  avail_wall_invariant : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    Opposite E t t' →
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

/-! ## Row 169 — R:fibre_partition (R_ASSEMBLY_SPEC.md, paragraphs 2–4 and displays (1)–(3))

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
`X_1(P_±) = Σ_{Q ∈ Ind(G[W])} Φ_±(Q)` (3)."

`X_1` and `F_±` are not in Lean (CV:def:X1 is blocked on the diagram/record layer); (3) is stated for
an arbitrary summand `F`, which is exactly what "partitions the exact state sum" asserts once
`X_1(P) = Σ_{S ∈ Ind(G_P)} F(S)` is available (see NOTES_B). -/

/-- R:fibre_partition, clause by clause. -/
structure FibrePartitionData (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "both graphs induce the same graph on `W`". -/
  graph_on_W_same : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    Opposite E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ x y : Crossing (E.curve t), x.val ∉ triangleSupports e f g → y.val ∉ triangleSupports e f g →
      (GeometricInterlaces (geomAt E t' ht'.1) (crossingTransport hs x) (crossingTransport hs y) ↔
        GeometricInterlaces (geomAt E t ht.1) x y)
  /-- "and have the same adjacencies between `W` and `T`". -/
  W_to_T_same : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    Opposite E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ x y : Crossing (E.curve t), x.val ∉ triangleSupports e f g → y.val ∈ triangleSupports e f g →
      (GeometricInterlaces (geomAt E t' ht'.1) (crossingTransport hs x) (crossingTransport hs y) ↔
        GeometricInterlaces (geomAt E t ht.1) x y)
  /-- (1) "`𝓐(Q)` … It is the same on both sides because the `W`-to-`T` adjacencies are unchanged." -/
  avail_same : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    Opposite E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      avail (geomAt E t' ht'.1) e f g (Q.map (crossingTransport hs).toEmbedding) =
        (avail (geomAt E t ht.1) e f g Q).map (crossingTransport hs).toEmbedding
  /-- "Every independent support `S` on either side decomposes uniquely into `Q = S ∩ W` and
  `J = S ∩ T`. `Q` is independent in the outside graph. `J` is independent in the local graph and
  belongs to the availability set". -/
  decompose : ∀ t : E.Parameter, ∀ ht : Punctured E δ t, ∀ S ∈ CV.Ind (geomAt E t ht.1),
    S = (S \ triangleCrossings (E.curve t) e f g) ∪ (S ∩ triangleCrossings (E.curve t) e f g) ∧
    Disjoint (S \ triangleCrossings (E.curve t) e f g) (S ∩ triangleCrossings (E.curve t) e f g) ∧
    (S \ triangleCrossings (E.curve t) e f g) ∈ outsideSupports (geomAt E t ht.1) e f g ∧
    (S ∩ triangleCrossings (E.curve t) e f g) ∈ CV.Ind (geomAt E t ht.1) ∧
    S ∩ triangleCrossings (E.curve t) e f g ⊆
      avail (geomAt E t ht.1) e f g (S \ triangleCrossings (E.curve t) e f g)
  /-- "Conversely, these three conditions imply that `Q ∪ J` is independent". -/
  compose : ∀ t : E.Parameter, ∀ ht : Punctured E δ t, ∀ Q J : Finset (Crossing (E.curve t)),
    Q ∈ outsideSupports (geomAt E t ht.1) e f g → J ∈ CV.Ind (geomAt E t ht.1) →
    J ⊆ avail (geomAt E t ht.1) e f g Q → Q ∪ J ∈ CV.Ind (geomAt E t ht.1)
  /-- "This proves a bijection of supports": `S ↦ (S ∩ W, S ∩ T)` is a bijection from `Ind(G_P)` onto
  the pairs `(Q, J)` with `Q ∈ Ind(G[W])` and `J ∈ Ind(G[𝓐(Q)])`. -/
  bijection : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    Set.BijOn
      (fun S : Finset (Crossing (E.curve t)) =>
        (S \ triangleCrossings (E.curve t) e f g, S ∩ triangleCrossings (E.curve t) e f g))
      (↑(CV.Ind (geomAt E t ht.1)) : Set (Finset (Crossing (E.curve t))))
      {p | p.1 ∈ outsideSupports (geomAt E t ht.1) e f g ∧
        p.2 ∈ localFibre (geomAt E t ht.1) e f g p.1}
  /-- (2)–(3) "The finite bijection just established partitions the exact state sum, so
  `X_1(P_±) = Σ_{Q ∈ Ind(G[W])} Φ_±(Q)`": for every summand `F` on the supports of either side,
  `Σ_{S ∈ Ind(G_P)} F(S) = Σ_{Q ∈ Ind(G[W])} Σ_{J ∈ Ind(G[𝓐(Q)])} F(Q ∪ J)` (X₁-free form). -/
  state_sum_partition : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ {M : Type} [AddCommMonoid M] (F : Finset (Crossing (E.curve t)) → M),
      ∑ S ∈ CV.Ind (geomAt E t ht.1), F S =
        ∑ Q ∈ outsideSupports (geomAt E t ht.1) e f g, fibreSum (geomAt E t ht.1) e f g F Q

/-- **Row 169, R:fibre_partition** (R_ASSEMBLY_SPEC.md (1)–(3)). -/
theorem fibre_partition (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ FibrePartitionData E e f g δ := by
  sorry

/-! ## Row 171 — R:generic_table (R_GENERIC_ORBIT_ACTUAL_TABLE.md, with the sign classification of
R_GENERIC_NONSELECTED_SELECTOR_PROOF.md (1)–(4) it cites)

The strands are `u_e, u_f, u_g` (edge directions), the local crossings `a = x_ef = (u_1,u_2)`,
`b = x_eg = (u_1,u_3)`, `c = x_fg = (u_2,u_3)` (R_GENERIC_COMMON_TRANSPORT_PROOF.md); the determinants
`D_ef = det(u_e,u_f)` etc. are the (G5) members, `Δ = G3(e,f,g)`; `t_ij` is the parameter on line `i`
of its intersection with line `j` (`CV.crossParam P i j`). -/

/-- "`s_a = sgn(D_ef)`, `s_b = sgn(D_eg)`, `s_c = sgn(D_fg)`": the sign of `det(u_i, u_j) = G5_{i,j}`. -/
noncomputable def strandSign (P : LabelledTuple n) (i j : ZMod n) : SignType := SignType.sign (CV.G5 P i j)

/-- "`δ = sgn(Δ)`", `Δ = G3(e,f,g)`. -/
noncomputable def concurrenceSign (P : LabelledTuple n) (e f g : ZMod n) : SignType := SignType.sign (CV.G3 P e f g)

/-- "`q_e = sgn(t_ef − t_eg)`" (and `q_f = orderSign P f e g`, `q_g = orderSign P g e f`). -/
noncomputable def orderSign (P : LabelledTuple n) (h i j : ZMod n) : SignType :=
  SignType.sign (CV.crossParam P h i - CV.crossParam P h j)

/-- "one of the two alternating sign triples", `s_a = s_c = −s_b` (the extreme orbit). -/
def IsAlternating (sa sb sc : SignType) : Prop := sa = sc ∧ sb = -sa

instance (sa sb sc : SignType) : Decidable (IsAlternating sa sb sc) :=
  inferInstanceAs (Decidable (sa = sc ∧ sb = -sa))

/-- (4) "pair ab selected-condition: `s_a = −s_b`" (the shared strand `u_1` separates `u_2, u_3`). -/
def SelectedAB (sa sb : SignType) : Prop := sa = -sb

/-- (4) "pair ac selected-condition: `s_a = s_c`". -/
def SelectedAC (sa sc : SignType) : Prop := sa = sc

/-- (4) "pair bc selected-condition: `s_b = −s_c`". -/
def SelectedBC (sb sc : SignType) : Prop := sb = -sc

instance (sa sb : SignType) : Decidable (SelectedAB sa sb) := inferInstanceAs (Decidable (sa = -sb))
instance (sa sc : SignType) : Decidable (SelectedAC sa sc) := inferInstanceAs (Decidable (sa = sc))
instance (sb sc : SignType) : Decidable (SelectedBC sb sc) := inferInstanceAs (Decidable (sb = -sc))

/-- The six visits of the triangle in traversal order — the local word "after erasing every outside
visit". -/
noncomputable def triangleVisits {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n) : List (Visit P) :=
  (geometricGaussList hP).filter fun v => decide (v.1.val ∈ triangleSupports e f g)

/-- The local word predicted by the order signs: "the traversal encounters the `e`, `f`, and `g`
two-crossing blocks in that order", each block ordered by its `q` (`a` before `b` on `e` iff
`t_ef < t_eg`, i.e. `q_e = −1`; `a` before `c` on `f` iff `q_f = −1`; `b` before `c` on `g` iff `q_g = −1`). -/
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

/-- R:generic_table, clause by clause: the sign classification (NONSELECTED (1)–(4)) on either side of
the wall, the local words, the local independent supports, the local undominated table, the exterior
mask sharpening, and the successor/residual tables on the local skeleton. -/
structure GenericTableData (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "All four quantities are nonzero on either chamber of a simple wall." -/
  nonzero : ∀ t : E.Parameter, Punctured E δ t →
    CV.G5 (E.curve t) e f ≠ 0 ∧ CV.G5 (E.curve t) e g ≠ 0 ∧ CV.G5 (E.curve t) f g ≠ 0 ∧
      CV.G3 (E.curve t) e f g ≠ 0
  /-- (1) "`t_ef − t_eg = −Δ/(D_ef D_eg)`, `t_fe − t_fg = −Δ/(D_ef D_fg)`, `t_ge − t_gf = −Δ/(D_eg D_fg)`"
  (Cramer; the accepted `SM.concurrenceDet_order_identity` and `CV.G3_eq_concurrenceDet`). -/
  cramer : ∀ t : E.Parameter, Punctured E δ t →
    CV.crossParam (E.curve t) e f - CV.crossParam (E.curve t) e g =
        -CV.G3 (E.curve t) e f g / (CV.G5 (E.curve t) e f * CV.G5 (E.curve t) e g) ∧
    CV.crossParam (E.curve t) f e - CV.crossParam (E.curve t) f g =
        -CV.G3 (E.curve t) e f g / (CV.G5 (E.curve t) e f * CV.G5 (E.curve t) f g) ∧
    CV.crossParam (E.curve t) g e - CV.crossParam (E.curve t) g f =
        -CV.G3 (E.curve t) e f g / (CV.G5 (E.curve t) e g * CV.G5 (E.curve t) f g)
  /-- (2) "`(q_e, q_f, q_g) = −δ (s_a s_b, s_a s_c, s_b s_c)`". -/
  sign_vector : ∀ t : E.Parameter, Punctured E δ t →
    orderSign (E.curve t) e f g =
        -concurrenceSign (E.curve t) e f g * (strandSign (E.curve t) e f * strandSign (E.curve t) e g) ∧
    orderSign (E.curve t) f e g =
        -concurrenceSign (E.curve t) e f g * (strandSign (E.curve t) e f * strandSign (E.curve t) f g) ∧
    orderSign (E.curve t) g e f =
        -concurrenceSign (E.curve t) e f g * (strandSign (E.curve t) e g * strandSign (E.curve t) f g)
  /-- (3) "edge(a,b) is present iff `q_e = −1`, edge(a,c) is present iff `q_f = +1`, edge(b,c) is present
  iff `q_g = −1`" ("direct reading of the six-letter word"). -/
  edges_iff : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    (GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair heg) ↔ orderSign (E.curve t) e f g = -1) ∧
    (GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair hfg) ↔ orderSign (E.curve t) f e g = 1) ∧
    (GeometricInterlaces (geomAt E t ht.1) (xPair heg) (xPair hfg) ↔ orderSign (E.curve t) g e f = -1)
  /-- "Changing chamber changes the sign of `Δ`, so (2) negates all three `q`'s" — the strand signs
  `s` are constant across the wall (active (G5) members, lem:guardconst). -/
  chamber_change : ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' → Opposite E t t' →
    concurrenceSign (E.curve t') e f g = -concurrenceSign (E.curve t) e f g ∧
    strandSign (E.curve t') e f = strandSign (E.curve t) e f ∧
    strandSign (E.curve t') e g = strandSign (E.curve t) e g ∧
    strandSign (E.curve t') f g = strandSign (E.curve t) f g ∧
    orderSign (E.curve t') e f g = -orderSign (E.curve t) e f g ∧
    orderSign (E.curve t') f e g = -orderSign (E.curve t) f e g ∧
    orderSign (E.curve t') g e f = -orderSign (E.curve t) g e f
  /-- "The local graph is extreme exactly when all three indicators in (3) agree … equivalent to
  `s_a = s_c = −s_b`, namely one of the two alternating sign triples. Therefore the generic orbit is
  exactly the other six, nonalternating triples." -/
  orbit_classification : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ((localEdgeCount (geomAt E t ht.1) hef heg hfg = 0 ∨ localEdgeCount (geomAt E t ht.1) hef heg hfg = 3) ↔
      IsAlternating (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) (strandSign (E.curve t) f g)) ∧
    ((localEdgeCount (geomAt E t ht.1) hef heg hfg = 1 ∨ localEdgeCount (geomAt E t ht.1) hef heg hfg = 2) ↔
      ¬ IsAlternating (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) (strandSign (E.curve t) f g))
  /-- "six generic nonalternating sign branches and two extreme alternating branches" (finite count over
  the nonzero sign triples). -/
  branch_count :
    ((Finset.univ : Finset (SignType × SignType × SignType)).filter fun s =>
      s.1 ≠ 0 ∧ s.2.1 ≠ 0 ∧ s.2.2 ≠ 0 ∧ IsAlternating s.1 s.2.1 s.2.2).card = 2 ∧
    ((Finset.univ : Finset (SignType × SignType × SignType)).filter fun s =>
      s.1 ≠ 0 ∧ s.2.1 ≠ 0 ∧ s.2.2 ≠ 0 ∧ ¬ IsAlternating s.1 s.2.1 s.2.2).card = 6
  /-- (4) "For each nonalternating sign triple exactly one condition in (4) holds", with the six-case
  table: `+++`/`−−−` → `ac` selected, `++−`/`−−+` → `bc`, `+−−`/`−++` → `ab`. -/
  selected_unique : ∀ sa sb sc : SignType, sa ≠ 0 → sb ≠ 0 → sc ≠ 0 → ¬ IsAlternating sa sb sc →
    ((SelectedAB sa sb ∧ ¬ SelectedAC sa sc ∧ ¬ SelectedBC sb sc) ∨
     (¬ SelectedAB sa sb ∧ SelectedAC sa sc ∧ ¬ SelectedBC sb sc) ∨
     (¬ SelectedAB sa sb ∧ ¬ SelectedAC sa sc ∧ SelectedBC sb sc)) ∧
    ((sa = sb ∧ sb = sc) → SelectedAC sa sc) ∧
    ((sa = sb ∧ sc = -sb) → SelectedBC sb sc) ∧
    ((sb = sc ∧ sa = -sb) → SelectedAB sa sb)
  /-- "the `P3` graph on either chamber has as its degree-two vertex the crossing complementary to that
  pair. Thus the unique separating-strand pair is precisely the graph-selected pair": in the generic
  orbit, on either side, the selected pair is either the unique edge (third vertex isolated) or the
  non-edge of the path (third vertex of degree two). -/
  selected_is_graph_selected : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ IsAlternating (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) (strandSign (E.curve t) f g) →
    (SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g) →
      ((GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair hfg) ∧
          ¬ GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair heg) ∧
          ¬ GeometricInterlaces (geomAt E t ht.1) (xPair heg) (xPair hfg)) ∨
       (¬ GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair hfg) ∧
          GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair heg) ∧
          GeometricInterlaces (geomAt E t ht.1) (xPair heg) (xPair hfg)))) ∧
    (SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) →
      ((GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair heg) ∧
          ¬ GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair hfg) ∧
          ¬ GeometricInterlaces (geomAt E t ht.1) (xPair heg) (xPair hfg)) ∨
       (¬ GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair heg) ∧
          GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair hfg) ∧
          GeometricInterlaces (geomAt E t ht.1) (xPair heg) (xPair hfg)))) ∧
    (SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g) →
      ((GeometricInterlaces (geomAt E t ht.1) (xPair heg) (xPair hfg) ∧
          ¬ GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair heg) ∧
          ¬ GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair hfg)) ∨
       (¬ GeometricInterlaces (geomAt E t ht.1) (xPair heg) (xPair hfg) ∧
          GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair heg) ∧
          GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair hfg))))
  /-- "After erasing every outside visit, the traversal encounters the `e`, `f`, and `g` two-crossing
  blocks in that order": the six triangle visits, in traversal order, form (up to rotation) the three
  blocks, each ordered by its order sign. -/
  local_word : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    List.IsRotated (triangleVisits (geomAt E t ht.1) e f g) (blockWord hef heg hfg)
  /-- The printed words in the canonical branch `sgn det(u1,u2) = sgn det(u1,u3) = sgn det(u2,u3) = σ`
  (R_GENERIC_COMMON_TRANSPORT_PROOF.md (1)): "`P = a b A a c B b c C` (edges ab, bc; centre b)" is the
  side `δ = +1`, "`E = b a A c a B c b C` (edge ac; b isolated)" the side `δ = −1`. -/
  canonical_words : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    strandSign (E.curve t) e f = strandSign (E.curve t) e g →
    strandSign (E.curve t) e g = strandSign (E.curve t) f g →
    (concurrenceSign (E.curve t) e f g = 1 →
      List.IsRotated (triangleVisits (geomAt E t ht.1) e f g) (wordPVisits hef heg hfg) ∧
      GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair heg) ∧
      GeometricInterlaces (geomAt E t ht.1) (xPair heg) (xPair hfg) ∧
      ¬ GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair hfg)) ∧
    (concurrenceSign (E.curve t) e f g = -1 →
      List.IsRotated (triangleVisits (geomAt E t ht.1) e f g) (wordEVisits hef heg hfg) ∧
      GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair hfg) ∧
      ¬ GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair heg) ∧
      ¬ GeometricInterlaces (geomAt E t ht.1) (xPair heg) (xPair hfg))
  /-- "The supports `ab, bc, T` are absent on P; `ac, T` are absent on E" — and the rows of the table are
  the present local supports (`∅, a, b, c, ac` on P; `∅, a, b, c, ab, bc` on E), in the canonical branch. -/
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
  `CV.U`), in the canonical branch. -/
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
      CV.U (geomAt E t ht.1) {xPair heg} ∩ triangleCrossings (E.curve t) e f g = {xPair hef, xPair hfg} ∧
      GeometricInterlaces (geomAt E t ht.1) (xPair hef) (xPair hfg) ∧
      CV.U (geomAt E t ht.1) {xPair hfg} ∩ triangleCrossings (E.curve t) e f g = {xPair heg} ∧
      CV.U (geomAt E t ht.1) {xPair hef, xPair heg} ∩ triangleCrossings (E.curve t) e f g = ∅ ∧
      CV.U (geomAt E t ht.1) {xPair heg, xPair hfg} ∩ triangleCrossings (E.curve t) e f g = ∅)
  /-- "Full availability plus R-PAR sharpens the exterior masks: after `a`, survivors have mask `0` or
  `bc`, so `b,c` are twins; after `c`, mask `0` or `ab`, so `a,b` are twins; after `b`, mask `0` or `ac`,
  so `a,c` are twins; after any present pair only mask-zero outsiders survive": an outside crossing not
  adjacent to one triangle crossing is adjacent to both or to neither of the other two. -/
  exterior_masks : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ∀ y : Crossing (E.curve t), y.val ∉ triangleSupports e f g →
    (¬ GeometricInterlaces (geomAt E t ht.1) y (xPair hef) →
      (GeometricInterlaces (geomAt E t ht.1) y (xPair heg) ↔ GeometricInterlaces (geomAt E t ht.1) y (xPair hfg))) ∧
    (¬ GeometricInterlaces (geomAt E t ht.1) y (xPair hfg) →
      (GeometricInterlaces (geomAt E t ht.1) y (xPair hef) ↔ GeometricInterlaces (geomAt E t ht.1) y (xPair heg))) ∧
    (¬ GeometricInterlaces (geomAt E t ht.1) y (xPair heg) →
      (GeometricInterlaces (geomAt E t ht.1) y (xPair hef) ↔ GeometricInterlaces (geomAt E t ht.1) y (xPair hfg)))
  /-- The printed "Successor cycles" table, on the local skeleton (`wordP`, `wordE`; see the Part-0
  docstring: the identification with the actual carriers is deferred to the Carrier lane). -/
  successor_table : SuccessorTable
  /-- The printed residual words (`c B c C` vs `b B b C`, `a A a C` vs `b A b C`, `C|AB`, `a A c a B c`,
  `C|A|B`), on the local skeleton. -/
  residual_words : ResidualWordTable

/-- **Row 171, R:generic_table** (R_GENERIC_ORBIT_ACTUAL_TABLE.md with the sign classification of
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
