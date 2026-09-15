import CV.Events
import Bridge.B3
import SM.TripleVisitExchanges
import SM.TripleSides
import SM.InterlaceDefinition
import SM.GaussAdjacencyTransport
import SM.GeometricInterlacement
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! # R lane, designer A (spec-first): statements of the four X₁-free obligation rows

Rows (blueprint/ORDER.md 164, 167, 171, 172; fixed names, work/lean/axiom-policy.json `targets`):
`R:localization → RProof.localization`, `R:parity → RProof.parity`,
`R:fibre_partition → RProof.fibre_partition`, `R:generic_table → RProof.generic_table`.

Sources (frozen): R_ASSEMBLY_SPEC.md (the fibre-sum assembly (1)–(4)), OPEN_WORK.md items 1 and 3,
reference/R/RA/R_ATTACHMENT_WARRANTS.md (R-LOC-2 lines 12–101, R-PAR-v6 lines 103–148),
reference/R/RA/R_GENERIC_ORBIT_ACTUAL_TABLE.md (the whole file) and
reference/R/RA/R_GENERIC_NONSELECTED_SELECTOR_PROOF.md, sections "Oriented line-order calculation"
(1)–(3) and "Which pair is selected" (4) (the sign classification that
R_GENERIC_ORBIT_ACTUAL_TABLE.md, "Earliest remaining interface", cites as the classification of the
wall into six generic and two extreme branches). The R rows have no printed theorem statement; each
bundle below renders the clauses of these texts, one field per clause, with the clause quoted in the
field's docstring. Written 2026-09-14 by a Claude Code statement-designer subagent (designer A) of the
pod executor; checked with `lake env lean` (the four row theorems are `sorry`; no other sorry).

## Domain (decision F2(A), work/AUTHOR_NOTES.md: no narrowing)

Every row is stated for a CV event `E : CV.Event n` (row 148, CV/Events.lean) that is a simple
transversal Reidemeister-III event in the sense of CV ax:R, `E.IsSimpleRIII e f g h3 h4e h4f h4g`
(CV/Events.lean: zero set exactly the forced bundle `{G3_{e,f,g}, G4_{e;f,g}, G4_{f;e,g}, G4_{g;e,f}}`
with `e < f < g` in CV's one-based representatives `CV.rep`, pairwise remote, concurrent at `t = 0`
at a point interior to all three edges, transversal). "On a punctured neighbourhood of `t = 0`"
(R-LOC-2) / "near the wall" (R-PAR-v6) is rendered by an existential radius `δ` with
`0 < δ ≤ E.radius` and the predicate `Punctured E δ t : t ≠ 0 ∧ |t| < δ`; "the two sides" are
`OppositeSides E s t : s·t < 0`. Every punctured value `E.curve t` is CV-generic
(`E.generic_punctured`), hence in the accepted geometric class `SM.CrossingGeometry`
(`CV.Generic.crossingGeometry`, CV/Setup.lean), on which the CV Gauss word and interlacement graph of
CV:def:interlace live: `SM.geometricGaussList`, `SM.geometricVisitPosition` (SM/GeometricVisits.lean),
`SM.GeometricInterlaces`, `SM.geometricInterlacementGraph` (SM/GeometricInterlacement.lean),
`CV.Ind`, `CV.N`, `CV.U` (CV/Events.lean). No SM (all-triple) genericity is assumed anywhere.

The SM triple germ. R-LOC-2's text is about the CV event, and so are the statements below. The SM
triple germ `SM.WallGerm.TripleAt e f k` (SM/NamedWallPredicates.lean) is a CV simple RIII event
through `Bridge.eventOfTriple` with zero set and transversality by `Bridge.B2`, `Bridge.B3`
(Bridge/B1.lean, Bridge/B3.lean); for that event the accepted lem:triple-sides lane
(`SM.triple_sides`, `SM.WallGerm.triple_exact_visit_orders`, `SM.WallGerm.triple_sides_crossing_equiv`,
`SM.pairVisits_adjacent`; SM/Triple*.lean) already proves clauses (1)–(3) of R-LOC-2 on the SM-generic
punctured sides — the proof lane's route (see NOTES_A.md). Nothing below is *restricted* to that germ.

## Vocabulary (RA text → Lean)

* crossing `x_{ef}` "indexed by carrying edge pairs" → the accepted unordered crossing `SM.Crossing P`
  (`{s : Finset (ZMod n) // IsCrossing P s}`, SM/Crossings.lean); across the wall crossings are
  identified by their supports `x.val : Finset (ZMod n)` (`triangleSupports e f g = {{e,f},{e,g},{f,g}}`),
  which is what R-LOC-2 (1) makes legitimate. Statements comparing the two sides are therefore written
  on supports (`SupportInterlaces`, `Finset.image Subtype.val`), never through a chosen bijection.
* the triangle `T` → `triangle P e f g : Finset (Crossing P)`, its three members named as in the RA files:
  `a = x_{ef} = {e,f}`, `b = x_{eg} = {e,g}`, `c = x_{fg} = {f,g}` (R_GENERIC_COMMON_TRANSPORT_PROOF.md:
  "`a=(u1,u2)`, `b=(u1,u3)`, `c=(u2,u3)`").
* a crossing-visit and its position on the traversal circle `Γ` → `SM.Visit P` (a crossing with one
  of its two edges) at `SM.geometricVisitPosition hP v`; "the visit of `x_{ef}` on `e`" is
  `SM.pairVisit hef` for `hef : IsCrossing P {e,f}` (SM/PairVisits.lean).
* "adjacent crossing-visits of the traversal circle" → `GaussAdjacent hP v w`: one of the two open
  arcs of `Γ` between the two visits carries no crossing visit (the empty-arc form of the accepted
  `SM.GaussVisitsAdjacent`, cf. `SM.gauss_adjacent_empty_arc`).
* "order along the edge `e`" → CV's parameter `t_f = CV.crossParam P e f` (CV/Setup.lean:397, equal to
  SM's `edgeParameter` by `CV.crossParam_eq_edgeParameter`).
* the interlacement graph `G`, "interlaces", `Ind`, `N`, `U(S)` → `SM.GeometricInterlaces hP`,
  `CV.Ind hP`, `CV.N hP`, `CV.U hP` (row 134).
* availability `𝓐(Q) = avail(Q)` → `avail hP T Q := T.filter (fun x => ∀ y ∈ Q, ¬ x ~ y)`.
* the sign data of the line-order calculation → `strandSign P i j = sgn det(d_i,d_j) = sgn G5_{i,j}`,
  `concurrenceSign P e f g = sgn G3_{e,f,g}`, `orderSign P i j k = sgn (t_{ij} − t_{ik})`.
* the printed local words `P = a b A a c B b c C`, `E = b a A c a B c b C` and their successor cycles
  → the finite model `RProof.LocalTable` (six local visits and three gap symbols at the positions
  `0..8`; oriented smoothing at a selected letter exchanges the successors of its two visits).

What cannot be stated without X₁ / the carrier definitions is recorded at the corresponding field and
in NOTES_A.md: the complete summand `F_±(S)` of CV def:X1 (row 146, blocked) enters the fibre partition
only as an arbitrary integer-valued summand `F`; the identification of the abstract successor cycles
with the actual carriers of the event's polygons (CV def:smoothing, row 135, deferred under F2(A)) is
not asserted. -/

namespace RProof

open SM CV
open scoped Classical

variable {n : ℕ} [NeZero n]

/-! ## Common vocabulary -/

/-- "on a punctured neighbourhood of `t = 0`" (R-LOC-2), "near the wall" (R-PAR-v6): the parameter
`t` of the event is nonzero and within `δ` of the wall. -/
def Punctured (E : CV.Event n) (δ : ℝ) (t : E.Parameter) : Prop := t.val ≠ 0 ∧ |t.val| < δ

/-- "the two sides" of the wall: `s` and `t` have opposite signs. -/
def OppositeSides (E : CV.Event n) (s t : E.Parameter) : Prop := s.val * t.val < 0

/-- Two parameters on one side of the wall. -/
def SameSide (E : CV.Event n) (s t : E.Parameter) : Prop := 0 < s.val * t.val

/-- Every punctured value of the event is CV-generic, hence in the geometric class on which the CV
Gauss word and interlacement graph are read (rows 132, 134). -/
theorem sideGeometry (E : CV.Event n) {δ : ℝ} {t : E.Parameter} (ht : Punctured E δ t) :
    CrossingGeometry (E.curve t) :=
  (E.generic_punctured t ht.1).crossingGeometry

/-- The three carrying edge pairs of the triangle `T = {x_{ef}, x_{eg}, x_{fg}}`. -/
def triangleSupports (e f g : ZMod n) : Finset (Finset (ZMod n)) := {{e, f}, {e, g}, {f, g}}

/-- "Let `T = {x_{ef}, x_{eg}, x_{fg}}`" (R-LOC-2): the crossings of `P` carried by the three bundle
pairs. -/
noncomputable def triangle (P : LabelledTuple n) (e f g : ZMod n) : Finset (Crossing P) :=
  Finset.univ.filter fun x => x.val ∈ triangleSupports e f g

/-- The support form of the crossing supports of `P` ("the crossing set, indexed by carrying edge
pairs"). -/
noncomputable def supports (P : LabelledTuple n) (S : Finset (Crossing P)) : Finset (Finset (ZMod n)) :=
  S.image Subtype.val

/-- Interlacement read on carrying edge pairs: the crossings with supports `a`, `b` interlace
(CV:def:interlace, `SM.GeometricInterlaces`). False unless both are crossings of `P`. -/
def SupportInterlaces {P : LabelledTuple n} (hP : CrossingGeometry P) (a b : Finset (ZMod n)) : Prop :=
  ∃ x y : Crossing P, x.val = a ∧ y.val = b ∧ GeometricInterlaces hP x y

/-- "occupy adjacent crossing-visits of the traversal circle" (R-LOC-2 (2)): the two visits are
distinct and one of the two open arcs of `Γ` between them contains no crossing visit. On SM-generic
polygons this is the empty-arc consequence of `SM.GaussVisitsAdjacent`
(`SM.gauss_adjacent_empty_arc`, SM/GaussCyclicGap.lean). -/
def GaussAdjacent {P : LabelledTuple n} (hP : CrossingGeometry P) (v w : Visit P) : Prop :=
  v ≠ w ∧
    ((∀ u : Visit P, ¬ traversalBetween (geometricVisitPosition hP v) (geometricVisitPosition hP u)
        (geometricVisitPosition hP w)) ∨
      (∀ u : Visit P, ¬ traversalBetween (geometricVisitPosition hP w) (geometricVisitPosition hP u)
        (geometricVisitPosition hP v)))

/-- "`avail(S') = {x ∈ T : x interlaces no member of S'}`" (R-PAR-v6 (P2)); R_ASSEMBLY_SPEC.md (1):
"`𝓐(Q) = {t ∈ T : no element of Q is adjacent to t}`". -/
noncomputable def avail {P : LabelledTuple n} (hP : CrossingGeometry P) (T Q : Finset (Crossing P)) :
    Finset (Crossing P) := by
  classical exact T.filter fun x => ∀ y ∈ Q, ¬ GeometricInterlaces hP x y

/-- The crossings of `T` that a crossing `y` interlaces (R-PAR-v6 (P1): "the interlaced pair"). -/
noncomputable def interlacedTriangle {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n)
    (y : Crossing P) : Finset (Crossing P) := by
  classical exact (triangle P e f g).filter fun x => GeometricInterlaces hP y x

/-- The "mask" of an outside crossing (R_GENERIC_ORBIT_ACTUAL_TABLE.md): the supports of the triangle
crossings it interlaces. -/
noncomputable def mask {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n) (y : Crossing P) :
    Finset (Finset (ZMod n)) :=
  supports P (interlacedTriangle hP e f g y)

/-- "Clumps" (R-PAR-v6, proof): `C_h` = the visits of the two triangle crossings carried by the bundle
edge `h` ("`C_e = {visits of x_{ef}, x_{eg} on e}`, `C_f`, `C_g`"). -/
noncomputable def clump (P : LabelledTuple n) (e f g h : ZMod n) : Finset (Visit P) :=
  Finset.univ.filter fun v => v.1.val ∈ triangleSupports e f g ∧ v.2.val = h

/-- The 2-colouring of R-PAR-v6's proof: the visit `w` lies in the arc from `u` to `v` of the two arcs
"that `u, v` cut `Γ` into". -/
def ArcSide {P : LabelledTuple n} (hP : CrossingGeometry P) (u v : TraversalPoint n) (w : Visit P) :
    Prop :=
  traversalBetween u (geometricVisitPosition hP w) v

/-! ### The three local edges and the two orbits (R-LOC-2 corollary; R_GENERIC_* files) -/

/-- The local edge `ab` = "`x_{ef} ∼ x_{eg}`". -/
def EdgeAB {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n) : Prop :=
  SupportInterlaces hP {e, f} {e, g}

/-- The local edge `ac` = "`x_{ef} ∼ x_{fg}`". -/
def EdgeAC {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n) : Prop :=
  SupportInterlaces hP {e, f} {f, g}

/-- The local edge `bc` = "`x_{eg} ∼ x_{fg}`". -/
def EdgeBC {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n) : Prop :=
  SupportInterlaces hP {e, g} {f, g}

/-- "the extreme orbit (empty ↔ complete)" (R-LOC-2 corollary): the induced graph `G[T]` is `K₃` or
empty. -/
def Extreme {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n) : Prop :=
  (EdgeAB hP e f g ∧ EdgeAC hP e f g ∧ EdgeBC hP e f g) ∨
    (¬ EdgeAB hP e f g ∧ ¬ EdgeAC hP e f g ∧ ¬ EdgeBC hP e f g)

/-- "the one-edge ↔ two-edge orbit" = "the generic graph orbit `P3 ↔ (one edge plus one isolated
vertex)`": `G[T]` has one or two edges. -/
def GenericOrbit {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n) : Prop :=
  ¬ Extreme hP e f g

/-! ### Sign data of the oriented line-order calculation (R_GENERIC_NONSELECTED_SELECTOR_PROOF.md) -/

/-- "`D_ef = det(u_e,u_f)`, …" with `s_a = sgn D_ef`, `s_b = sgn D_eg`, `s_c = sgn D_fg`: the sign of
the strand determinant `det(d_i, d_j) = G5_{i,j}` (CV/Setup.lean:383). -/
noncomputable def strandSign (P : LabelledTuple n) (i j : ZMod n) : SignType :=
  SignType.sign (CV.G5 P i j)

/-- "`Delta = G3(e,f,g)`" with `delta = sgn Delta` (CV/Setup.lean:387). -/
noncomputable def concurrenceSign (P : LabelledTuple n) (e f g : ZMod n) : SignType :=
  SignType.sign (CV.G3 P e f g)

/-- "`q_e = sgn(t_ef − t_eg)`, `q_f = sgn(t_fe − t_fg)`, `q_g = sgn(t_ge − t_gf)`", with
`t_ij = CV.crossParam P i j` "the parameter on oriented line `i` of its intersection with line `j`". -/
noncomputable def orderSign (P : LabelledTuple n) (i j k : ZMod n) : SignType :=
  SignType.sign (CV.crossParam P i j - CV.crossParam P i k)

/-- "one of the two alternating sign triples", "`s_a = s_c = −s_b`". -/
def Alternating (P : LabelledTuple n) (e f g : ZMod n) : Prop :=
  strandSign P e f = strandSign P f g ∧ strandSign P e g = - strandSign P e f

/-- (4) "pair `ab` selected-condition: `s_a = −s_b`". -/
def SelectedAB (P : LabelledTuple n) (e f g : ZMod n) : Prop := strandSign P e f = - strandSign P e g

/-- (4) "pair `ac` selected-condition: `s_a = s_c`". -/
def SelectedAC (P : LabelledTuple n) (e f g : ZMod n) : Prop := strandSign P e f = strandSign P f g

/-- (4) "pair `bc` selected-condition: `s_b = −s_c`". -/
def SelectedBC (P : LabelledTuple n) (e f g : ZMod n) : Prop := strandSign P e g = - strandSign P f g

/-! ### The local word of the triangle on the traversal circle -/

/-- The cyclic word of the six triangle visits in traversal order ("after erasing every outside
visit"), each visit written as the support of its crossing. -/
noncomputable def triangleWord {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n) :
    Cycle (Finset (ZMod n)) :=
  (((geometricGaussList hP).filter fun v => decide (v.1.val ∈ triangleSupports e f g)).map
    fun v => v.1.val : List (Finset (ZMod n)))

/-- The `e`-block of the local word: the two triangle visits on `e` in the order of their parameters
along `e` (`x_{ef}` first iff `t_ef < t_eg`, i.e. `q_e = −1`). -/
def blockE (e f g : ZMod n) (q : SignType) : List (Finset (ZMod n)) :=
  if q = SignType.neg then [{e, f}, {e, g}] else [{e, g}, {e, f}]

/-- The `f`-block: `x_{ef}` before `x_{fg}` along `f` iff `t_fe < t_fg`, i.e. `q_f = −1`. -/
def blockF (e f g : ZMod n) (q : SignType) : List (Finset (ZMod n)) :=
  if q = SignType.neg then [{e, f}, {f, g}] else [{f, g}, {e, f}]

/-- The `g`-block: `x_{eg}` before `x_{fg}` along `g` iff `t_ge < t_gf`, i.e. `q_g = −1`. -/
def blockG (e f g : ZMod n) (q : SignType) : List (Finset (ZMod n)) :=
  if q = SignType.neg then [{e, g}, {f, g}] else [{f, g}, {e, g}]

/-- The printed word `P = a b A a c B b c C` read on supports (`a = {e,f}`, `b = {e,g}`, `c = {f,g}`;
the gaps `A, B, C` are the outside strings between the three blocks). -/
def wordPSupports (e f g : ZMod n) : List (Finset (ZMod n)) :=
  [{e, f}, {e, g}, {e, f}, {f, g}, {e, g}, {f, g}]

/-- The printed word `E = b a A c a B c b C` read on supports. -/
def wordESupports (e f g : ZMod n) : List (Finset (ZMod n)) :=
  [{e, g}, {e, f}, {f, g}, {e, f}, {f, g}, {e, g}]

/-! ## The abstract local table (R_GENERIC_ORBIT_ACTUAL_TABLE.md)

"Use the three unchanged exterior gaps `A,B,C` between the RIII strand blocks:
`P = a b A a c B b c C` (edges ab, bc; centre b), `E = b a A c a B c b C` (edge ac; b isolated)."
The nine letters occupy the positions `0..8` of a cyclic word; the table's visit numbering `1..6` is
positions `0,1,3,4,6,7` and the gaps `A,B,C` are positions `2,5,8` (both words). Oriented smoothing at a
selected crossing letter with visits at positions `p, q` gives the successor `p ↦ q+1`, `q ↦ p+1`
(reconnection at the two visits, as in the Carrier lane's `smoothingSuccessor = selectedMarkPerm ∘
markSuccessor`); a successor cycle is written as the list of positions it visits, in traversal order,
so the table's `(126)[C]` is `[0, 1, 7, 8]`. -/

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

/-- "Successor cycles": the listed cycles are cycles of `σ` and together visit every position once. -/
abbrev IsCycleDecomposition (σ : Fin 9 → Fin 9) (ls : List (List (Fin 9))) : Prop :=
  (∀ l ∈ ls, IsCycle σ l) ∧ ls.flatten.Perm (List.finRange 9)

/-- The "unsigned residual word" of a successor cycle: its letters with every local crossing that is
selected or dominated erased (only undominated local crossings and gaps remain). -/
def residual (w : Fin 9 → Letter) (S : Finset Letter) (l : List (Fin 9)) : List Letter :=
  (l.map w).filter fun ℓ => !ℓ.isLocal || decide (ℓ ∈ undominated w S)

end LocalTable

/-! ## Abstract independent-set partition (R_ASSEMBLY_SPEC.md, the bijection of supports) -/

/-- `Ind(G)`: the independent sets of a finite graph, "including `∅`". -/
noncomputable def indepSets {V : Type} [Fintype V] (G : SimpleGraph V) : Finset (Finset V) := by
  classical exact Finset.univ.powerset.filter fun S => G.IsIndepSet (↑S : Set V)

/-- R_ASSEMBLY_SPEC.md (1): "`𝓐(Q) = {t ∈ T : no element of Q is adjacent to t}`", for a graph `G`
and a local set `T`. -/
noncomputable def availSet {V : Type} (G : SimpleGraph V) (T Q : Finset V) : Finset V := by
  classical exact T.filter fun x => ∀ q ∈ Q, ¬ G.Adj q x

/-- R_ASSEMBLY_SPEC.md (2): the fibre sum `Φ(Q) = ∑_{J ∈ Ind(G[𝓐(Q)])} F(Q ∪ J)` of a summand `F`. -/
noncomputable def fibreSum {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T : Finset V)
    (F : Finset V → ℤ) (Q : Finset V) : ℤ :=
  ∑ J ∈ (indepSets G).filter (fun J => J ⊆ availSet G T Q), F (Q ∪ J)

/-! ## Row 164 — R:localization (R-LOC-2, R_ATTACHMENT_WARRANTS.md:12–101) -/

/-- **R-LOC-2 — localization** (R_ATTACHMENT_WARRANTS.md:14–37), clause by clause, on the punctured
`δ`-neighbourhood of the wall of a simple transversal RIII event with triangle
`T = {x_{ef}, x_{eg}, x_{fg}}`. -/
structure LocalizationData (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "Let `T = {x_{ef}, x_{eg}, x_{fg}}`": the three bundle pairs are crossings on every punctured
  value (the presupposition of the statement, from the activation of the `G3` member of `Z`). -/
  triangle_present : ∀ (t : E.Parameter), Punctured E δ t →
    IsCrossing (E.curve t) {e, f} ∧ IsCrossing (E.curve t) {e, g} ∧ IsCrossing (E.curve t) {f, g}
  /-- (1) "the crossing set, indexed by carrying edge pairs, is constant". -/
  crossing_set_constant : ∀ (s t : E.Parameter), Punctured E δ s → Punctured E δ t →
    ∀ c : Finset (ZMod n), IsCrossing (E.curve s) c ↔ IsCrossing (E.curve t) c
  /-- (2) "on each of `e, f, g` the two crossings of `T` carried by that edge occupy adjacent
  crossing-visits of the traversal circle": on `e` the visits of `x_{ef}` and `x_{eg}` on `e`, on `f`
  those of `x_{fe}` and `x_{fg}` on `f`, on `g` those of `x_{ge}` and `x_{gf}` on `g`. -/
  adjacent : ∀ (t : E.Parameter) (ht : Punctured E δ t),
    (∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g}),
      GaussAdjacent (sideGeometry E ht) (pairVisit hef) (pairVisit heg)) ∧
    (∀ (hfe : IsCrossing (E.curve t) {f, e}) (hfg : IsCrossing (E.curve t) {f, g}),
      GaussAdjacent (sideGeometry E ht) (pairVisit hfe) (pairVisit hfg)) ∧
    (∀ (hge : IsCrossing (E.curve t) {g, e}) (hgf : IsCrossing (E.curve t) {g, f}),
      GaussAdjacent (sideGeometry E ht) (pairVisit hge) (pairVisit hgf))
  /-- (2) "and their order along that edge is opposite on the two sides": with `t_{ij}` the
  parameter along `i` of the crossing with `j` (`CV.crossParam`), the order of `x_{ef}, x_{eg}` along
  `e` reverses across the wall, likewise on `f` and on `g`. -/
  order_reverses : ∀ (s t : E.Parameter), Punctured E δ s → Punctured E δ t → OppositeSides E s t →
    (CV.crossParam (E.curve s) e f < CV.crossParam (E.curve s) e g ↔
      CV.crossParam (E.curve t) e g < CV.crossParam (E.curve t) e f) ∧
    (CV.crossParam (E.curve s) f e < CV.crossParam (E.curve s) f g ↔
      CV.crossParam (E.curve t) f g < CV.crossParam (E.curve t) f e) ∧
    (CV.crossParam (E.curve s) g e < CV.crossParam (E.curve s) g f ↔
      CV.crossParam (E.curve t) g f < CV.crossParam (E.curve t) g e)
  /-- (3) "every other pair of crossings keeps its order along every edge" — across the wall: for
  every edge `i` and every pair of crossings `x_{ij}, x_{ik}` on it other than a bundle pair
  (`{i,j,k} ≠ {e,f,g}`), the order along `i` is the same on the two sides. -/
  other_orders_persist : ∀ (s t : E.Parameter), Punctured E δ s → Punctured E δ t →
    OppositeSides E s t → ∀ i j k : ZMod n,
      IsCrossing (E.curve s) {i, j} → IsCrossing (E.curve s) {i, k} →
      ({i, j, k} : Finset (ZMod n)) ≠ {e, f, g} →
      (CV.crossParam (E.curve s) i j < CV.crossParam (E.curve s) i k ↔
        CV.crossParam (E.curve t) i j < CV.crossParam (E.curve t) i k)
  /-- "on a punctured neighbourhood": on one side every order along every edge, bundle pairs
  included, is constant (so `G^+` and `G^-` are well defined). -/
  same_side_orders : ∀ (s t : E.Parameter), Punctured E δ s → Punctured E δ t → SameSide E s t →
    ∀ i j k : ZMod n, IsCrossing (E.curve s) {i, j} → IsCrossing (E.curve s) {i, k} →
      (CV.crossParam (E.curve s) i j < CV.crossParam (E.curve s) i k ↔
        CV.crossParam (E.curve t) i j < CV.crossParam (E.curve t) i k)
  /-- (4) "hence `G^+ = G^- △ binom(T,2)`: the three internal pairs of `T` toggle": for two distinct
  supports of `T`, interlacement holds on one side exactly when it fails on the other. -/
  triangle_pairs_toggle : ∀ (s t : E.Parameter) (hs : Punctured E δ s) (ht : Punctured E δ t),
    OppositeSides E s t → ∀ a b : Finset (ZMod n),
      a ∈ triangleSupports e f g → b ∈ triangleSupports e f g → a ≠ b →
      (SupportInterlaces (sideGeometry E hs) a b ↔ ¬ SupportInterlaces (sideGeometry E ht) a b)
  /-- (4) "and no other pair changes": every pair of supports not an internal pair of `T` has the
  same interlacement on the two sides. -/
  other_pairs_unchanged : ∀ (s t : E.Parameter) (hs : Punctured E δ s) (ht : Punctured E δ t),
    OppositeSides E s t → ∀ a b : Finset (ZMod n),
      ¬ (a ∈ triangleSupports e f g ∧ b ∈ triangleSupports e f g ∧ a ≠ b) →
      (SupportInterlaces (sideGeometry E hs) a b ↔ SupportInterlaces (sideGeometry E ht) a b)
  /-- The graph is constant on each side (the two graphs `G^±` of clause (4)). -/
  same_side_graph : ∀ (s t : E.Parameter) (hs : Punctured E δ s) (ht : Punctured E δ t),
    SameSide E s t → ∀ a b : Finset (ZMod n),
      (SupportInterlaces (sideGeometry E hs) a b ↔ SupportInterlaces (sideGeometry E ht) a b)
  /-- **Corollary.** "The induced graph `G[T]` maps to its complement in `T` across the wall." -/
  induced_graph_complement : ∀ (s t : E.Parameter) (hs : Punctured E δ s) (ht : Punctured E δ t),
    OppositeSides E s t →
      (EdgeAB (sideGeometry E hs) e f g ↔ ¬ EdgeAB (sideGeometry E ht) e f g) ∧
      (EdgeAC (sideGeometry E hs) e f g ↔ ¬ EdgeAC (sideGeometry E ht) e f g) ∧
      (EdgeBC (sideGeometry E hs) e f g ↔ ¬ EdgeBC (sideGeometry E ht) e f g)
  /-- **Corollary.** "Both orbits of that map occur — the extreme orbit (empty ↔ complete) and the
  one-edge ↔ two-edge orbit": the map preserves the orbit, so an event is either of the extreme kind
  on both sides or of the generic kind on both sides (the exhaustive case split consumed by the
  assembly; the existence of events of each kind is not rendered, see NOTES_A.md). -/
  orbit_preserved : ∀ (s t : E.Parameter) (hs : Punctured E δ s) (ht : Punctured E δ t),
    OppositeSides E s t → (Extreme (sideGeometry E hs) e f g ↔ Extreme (sideGeometry E ht) e f g)

/-- Row 164, R:localization (R-LOC-2): for a simple transversal RIII event there is a punctured
neighbourhood of the wall on which all clauses of `LocalizationData` hold. -/
theorem localization (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ LocalizationData E e f g δ := by
  sorry

/-! ## Row 167 — R:parity (R-PAR-v6, R_ATTACHMENT_WARRANTS.md:103–148) -/

/-- **R-PAR-v6 — parity and availability** (R_ATTACHMENT_WARRANTS.md:105–121), clause by clause,
"for either side's polygon, near the wall", plus the proof's combinatorial core (the 2-colouring of
the three clumps) as an abstract clause. -/
structure ParityData (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- The proof's core, abstractly (R_ATTACHMENT_WARRANTS.md:136–141): "A 2-colouring of three objects
  has either 0 bichromatic pairs (monochromatic) or exactly 2 (the odd object pairs bichromatically
  with each of the other two, while those two pair monochromatically). Never 1, never 3." -/
  two_colouring : ∀ χ : Fin 3 → Bool,
    (∀ i j : Fin 3, χ i = χ j) ∨
      ∃ h : Fin 3, ∀ i j : Fin 3, i ≠ j → (χ i ≠ χ j ↔ (i = h ∨ j = h))
  /-- The clumps of the proof (R_ATTACHMENT_WARRANTS.md:125–129): "`C_e = {visits of x_{ef}, x_{eg} on
  e}`, `C_f`, `C_g`. Each crossing of `T` has one visit in each of two clumps." -/
  clumps : ∀ (t : E.Parameter), Punctured E δ t →
    (∀ v : Visit (E.curve t), v.1.val ∈ triangleSupports e f g →
      v ∈ clump (E.curve t) e f g e ∨ v ∈ clump (E.curve t) e f g f ∨ v ∈ clump (E.curve t) e f g g) ∧
    (clump (E.curve t) e f g e).card = 2 ∧ (clump (E.curve t) e f g f).card = 2 ∧
    (clump (E.curve t) e f g g).card = 2
  /-- "no crossing-visit lies between the two members of a clump (adjacency), so … each clump lies
  wholly in one of the two arcs that `u, v` cut `Γ` into" (R_ATTACHMENT_WARRANTS.md:131–134): for
  the two visits `u ≠ v` of a crossing `y ∉ T`, the two visits of each clump are on the same arc. -/
  clump_monochromatic : ∀ (t : E.Parameter) (ht : Punctured E δ t) (y : Crossing (E.curve t)),
    y.val ∉ triangleSupports e f g → ∀ (u v : Visit (E.curve t)), u.1 = y → v.1 = y → u ≠ v →
      ∀ h ∈ ({e, f, g} : Finset (ZMod n)), ∀ w ∈ clump (E.curve t) e f g h,
        ∀ w' ∈ clump (E.curve t) e f g h,
        (ArcSide (sideGeometry E ht) (geometricVisitPosition (sideGeometry E ht) u)
            (geometricVisitPosition (sideGeometry E ht) v) w ↔
          ArcSide (sideGeometry E ht) (geometricVisitPosition (sideGeometry E ht) u)
            (geometricVisitPosition (sideGeometry E ht) v) w')
  /-- **(P1) Parity.** "Every crossing `y ∉ T` interlaces exactly `0` or exactly `2` of the three
  crossings of `T` — never `1`, never `3`." -/
  parity : ∀ (t : E.Parameter) (ht : Punctured E δ t) (y : Crossing (E.curve t)),
    y.val ∉ triangleSupports e f g →
      (interlacedTriangle (sideGeometry E ht) e f g y).card = 0 ∨
        (interlacedTriangle (sideGeometry E ht) e f g y).card = 2
  /-- **(P1)** "Moreover the interlaced pair, when nonempty, is one of `{x_{ef},x_{eg}}`,
  `{x_{ef},x_{fg}}`, `{x_{eg},x_{fg}}` — the two crossings sharing one of the three bundle edges." -/
  interlaced_pair : ∀ (t : E.Parameter) (ht : Punctured E δ t) (y : Crossing (E.curve t)),
    y.val ∉ triangleSupports e f g → (interlacedTriangle (sideGeometry E ht) e f g y).Nonempty →
      mask (sideGeometry E ht) e f g y = {{e, f}, {e, g}} ∨
      mask (sideGeometry E ht) e f g y = {{e, f}, {f, g}} ∨
      mask (sideGeometry E ht) e f g y = {{e, g}, {f, g}}
  /-- **(P2) Trichotomy.** "For any set `S'` of crossings disjoint from `T`, the set
  `avail(S') = {x ∈ T : x interlaces no member of S'}` has size `3`, `1`, or `0` — never `2`." -/
  trichotomy : ∀ (t : E.Parameter) (ht : Punctured E δ t) (S' : Finset (Crossing (E.curve t))),
    (∀ y ∈ S', y.val ∉ triangleSupports e f g) →
      (avail (sideGeometry E ht) (triangle (E.curve t) e f g) S').card = 3 ∨
      (avail (sideGeometry E ht) (triangle (E.curve t) e f g) S').card = 1 ∨
      (avail (sideGeometry E ht) (triangle (E.curve t) e f g) S').card = 0
  /-- **(P2)** "And `avail(S')` is the same set on the two sides of the wall": for the same set of
  crossing supports on the two sides, the availability sets have the same supports. -/
  avail_wall_invariant : ∀ (s t : E.Parameter) (hs : Punctured E δ s) (ht : Punctured E δ t),
    ∀ (S' : Finset (Crossing (E.curve s))) (S'' : Finset (Crossing (E.curve t))),
      (∀ y ∈ S', y.val ∉ triangleSupports e f g) → supports (E.curve s) S' = supports (E.curve t) S'' →
      supports (E.curve s) (avail (sideGeometry E hs) (triangle (E.curve s) e f g) S') =
        supports (E.curve t) (avail (sideGeometry E ht) (triangle (E.curve t) e f g) S'')

/-- Row 167, R:parity (R-PAR-v6). -/
theorem parity (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ParityData E e f g δ := by
  sorry

/-! ## Row 171 — R:fibre_partition (R_ASSEMBLY_SPEC.md (1)–(3); OPEN_WORK.md item 1) -/

/-- **The fibre partition** (R_ASSEMBLY_SPEC.md, paragraphs 2–4 and the availability-size paragraph;
OPEN_WORK.md item 1: "Partition supports by outside independent support `Q` and available local set.
Prove exhaustion, disjointness and availability sizes 0, 1 or 3 on both sides."). The bijection of
supports is stated first for an arbitrary finite graph and local set (the spec's argument uses only
the graph), then on the CV interlacement graph of each punctured side with `T` the triangle and `W`
its complement. The complete summand `F_±(S)` of CV def:X1 (row 146, not yet in Lean) enters only as
an arbitrary summand `F : Finset (Crossing P) → ℤ`; (3) is the instance `F := wind(S)·∏_L Ω₁(S,L)`. -/
structure FibrePartitionData (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "Every independent support `S` on either side decomposes uniquely into `Q = S ∩ W` and
  `J = S ∩ T`. `Q` is independent in the outside graph. `J` is independent in the local graph and
  belongs to the availability set because independence forbids every `Q`-to-`J` edge." (abstract) -/
  abstract_decompose : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T : Finset V),
    ∀ S ∈ indepSets G, (S \ T) ∪ (S ∩ T) = S ∧ Disjoint (S \ T) T ∧ S \ T ∈ indepSets G ∧
      S ∩ T ∈ indepSets G ∧ S ∩ T ⊆ availSet G T (S \ T)
  /-- "Conversely, these three conditions imply that `Q ∪ J` is independent: its possible edges are
  outside, inside `T`, or between the two parts, and the respective conditions exclude all three
  kinds. This proves a bijection of supports": the decomposition of `Q ∪ J` is `(Q, J)`. (abstract) -/
  abstract_compose : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T Q J : Finset V),
    Q ∈ indepSets G → Disjoint Q T → J ∈ indepSets G → J ⊆ availSet G T Q →
      Q ∪ J ∈ indepSets G ∧ (Q ∪ J) \ T = Q ∧ (Q ∪ J) ∩ T = J
  /-- (2), (3): "The finite bijection just established partitions the exact state sum, so
  `X₁(P_±) = ∑_{Q ∈ Ind(G[W])} Φ_±(Q)`" with "`Φ_±(Q) = ∑_{J ∈ Ind(G_±[𝓐(Q)])} F_±(Q ∪ J)`", for any
  summand `F`. (abstract) -/
  abstract_partition_sum : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T : Finset V)
    (F : Finset V → ℤ),
    ∑ S ∈ indepSets G, F S = ∑ Q ∈ (indepSets G).filter (fun Q => Disjoint Q T), fibreSum G T F Q
  /-- "R-LOC-2 says only the three internal pairs of `T` toggle. Consequently both graphs induce the
  same graph on `W` and have the same adjacencies between `W` and `T`." -/
  outside_graph_unchanged : ∀ (s t : E.Parameter) (hs : Punctured E δ s) (ht : Punctured E δ t),
    ∀ a b : Finset (ZMod n), ¬ (a ∈ triangleSupports e f g ∧ b ∈ triangleSupports e f g) →
      (SupportInterlaces (sideGeometry E hs) a b ↔ SupportInterlaces (sideGeometry E ht) a b)
  /-- (1) "For each independent outside support `Q` in `W`, define its availability set by
  `𝓐(Q) = {t ∈ T : no element of Q is adjacent to t}`. It is the same on both sides because the
  `W`-to-`T` adjacencies are unchanged." -/
  avail_wall_invariant : ∀ (s t : E.Parameter) (hs : Punctured E δ s) (ht : Punctured E δ t),
    ∀ (Q : Finset (Crossing (E.curve s))) (Q' : Finset (Crossing (E.curve t))),
      Q ∈ CV.Ind (sideGeometry E hs) → Disjoint Q (triangle (E.curve s) e f g) →
      supports (E.curve s) Q = supports (E.curve t) Q' →
      supports (E.curve s) (avail (sideGeometry E hs) (triangle (E.curve s) e f g) Q) =
        supports (E.curve t) (avail (sideGeometry E ht) (triangle (E.curve t) e f g) Q')
  /-- The decomposition on the event's sides: `Ind(G_P)` (`CV.Ind`), `T` the triangle, `W = Tᶜ`. -/
  decompose : ∀ (t : E.Parameter) (ht : Punctured E δ t), ∀ S ∈ CV.Ind (sideGeometry E ht),
    (S \ triangle (E.curve t) e f g) ∪ (S ∩ triangle (E.curve t) e f g) = S ∧
    Disjoint (S \ triangle (E.curve t) e f g) (triangle (E.curve t) e f g) ∧
    S \ triangle (E.curve t) e f g ∈ CV.Ind (sideGeometry E ht) ∧
    S ∩ triangle (E.curve t) e f g ∈ CV.Ind (sideGeometry E ht) ∧
    S ∩ triangle (E.curve t) e f g ⊆
      avail (sideGeometry E ht) (triangle (E.curve t) e f g) (S \ triangle (E.curve t) e f g)
  /-- The converse on the event's sides. -/
  compose : ∀ (t : E.Parameter) (ht : Punctured E δ t) (Q J : Finset (Crossing (E.curve t))),
    Q ∈ CV.Ind (sideGeometry E ht) → Disjoint Q (triangle (E.curve t) e f g) →
    J ∈ CV.Ind (sideGeometry E ht) → J ⊆ avail (sideGeometry E ht) (triangle (E.curve t) e f g) Q →
      Q ∪ J ∈ CV.Ind (sideGeometry E ht) ∧ (Q ∪ J) \ triangle (E.curve t) e f g = Q ∧
        (Q ∪ J) ∩ triangle (E.curve t) e f g = J
  /-- (2), (3) on the event's sides: "`X₁(P_±) = ∑_{Q ∈ Ind(G[W])} Φ_±(Q)`" for any summand `F`
  (the complete summand `wind(S)∏_L Ω₁(S,L)` of def:X1 once row 146 exists). -/
  partition_sum : ∀ (t : E.Parameter) (ht : Punctured E δ t) (F : Finset (Crossing (E.curve t)) → ℤ),
    ∑ S ∈ CV.Ind (sideGeometry E ht), F S =
      ∑ Q ∈ (CV.Ind (sideGeometry E ht)).filter (fun Q => Disjoint Q (triangle (E.curve t) e f g)),
        fibreSum (geometricInterlacementGraph (sideGeometry E ht)) (triangle (E.curve t) e f g) F Q
  /-- "Thus availability has size three, one or zero" (from R-PAR-v6 (P1)), for every outside
  independent `Q`. -/
  avail_card : ∀ (t : E.Parameter) (ht : Punctured E δ t) (Q : Finset (Crossing (E.curve t))),
    Q ∈ CV.Ind (sideGeometry E ht) → Disjoint Q (triangle (E.curve t) e f g) →
      (avail (sideGeometry E ht) (triangle (E.curve t) e f g) Q).card = 3 ∨
      (avail (sideGeometry E ht) (triangle (E.curve t) e f g) Q).card = 1 ∨
      (avail (sideGeometry E ht) (triangle (E.curve t) e f g) Q).card = 0

/-- Row 171, R:fibre_partition. -/
theorem fibre_partition (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ FibrePartitionData E e f g δ := by
  sorry

/-! ## Row 172 — R:generic_table (R_GENERIC_ORBIT_ACTUAL_TABLE.md; the sign classification of
R_GENERIC_NONSELECTED_SELECTOR_PROOF.md (1)–(4)) -/

open LocalTable in
/-- **The generic-orbit table and the sign classification.** Part A (abstract, decidable): the printed
successor-cycle, present/absent-support, undominated and residual-word tables of
R_GENERIC_ORBIT_ACTUAL_TABLE.md on the words `P`, `E`. Part B (on the event's sides): the oriented
line-order calculation (1)–(3), the wall toggle, the extreme/generic classification, "Which pair is
selected" (4), the identification of the triangle's local word with the block words (canonically `P`
and `E`), and the R-PAR mask sharpening. -/
structure GenericTableData (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "`P = a b A a c B b c C` (edges ab, bc; centre b)". -/
  graph_P : Interlaces wordP a b ∧ Interlaces wordP b c ∧ ¬ Interlaces wordP a c
  /-- "`E = b a A c a B c b C` (edge ac; b isolated)". -/
  graph_E : Interlaces wordE a c ∧ ¬ Interlaces wordE a b ∧ ¬ Interlaces wordE b c
  /-- "P empty : (123456)[ABC]". -/
  cycles_P_empty : IsCycleDecomposition (succ wordP ∅) [[0, 1, 2, 3, 4, 5, 6, 7, 8]]
  /-- "P a : (1456)[BC](23)[A]". -/
  cycles_P_a : IsCycleDecomposition (succ wordP {a}) [[0, 4, 5, 6, 7, 8], [1, 2, 3]]
  /-- "P b : (126)[C](345)[AB]". -/
  cycles_P_b : IsCycleDecomposition (succ wordP {b}) [[0, 1, 7, 8], [3, 4, 5, 6, 2]]
  /-- "P c : (1234)[AC](56)[B]". -/
  cycles_P_c : IsCycleDecomposition (succ wordP {c}) [[0, 1, 2, 3, 4, 8], [5, 6, 7]]
  /-- "P ac : (14)[C](23)[A](56)[B]". -/
  cycles_P_ac : IsCycleDecomposition (succ wordP {a, c}) [[0, 4, 8], [1, 2, 3], [5, 6, 7]]
  /-- "E empty : (123456)[ABC]". -/
  cycles_E_empty : IsCycleDecomposition (succ wordE ∅) [[0, 1, 2, 3, 4, 5, 6, 7, 8]]
  /-- "E a : (1256)[BC](34)[A]". -/
  cycles_E_a : IsCycleDecomposition (succ wordE {a}) [[0, 1, 5, 6, 7, 8], [2, 3, 4]]
  /-- "E b : (1)[C](23456)[AB]". -/
  cycles_E_b : IsCycleDecomposition (succ wordE {b}) [[0, 8], [1, 2, 3, 4, 5, 6, 7]]
  /-- "E c : (1236)[AC](45)[B]". -/
  cycles_E_c : IsCycleDecomposition (succ wordE {c}) [[0, 1, 2, 3, 7, 8], [4, 5, 6]]
  /-- "E ab : (1)[C](256)[B](34)[A]". -/
  cycles_E_ab : IsCycleDecomposition (succ wordE {a, b}) [[0, 8], [1, 5, 6, 7], [2, 3, 4]]
  /-- "E bc : (1)[C](236)[A](45)[B]". -/
  cycles_E_bc : IsCycleDecomposition (succ wordE {b, c}) [[0, 8], [1, 2, 3, 7], [4, 5, 6]]
  /-- "The supports `ab, bc, T` are absent on `P`; `ac, T` are absent on `E`" — and the tabulated
  supports are present: `∅, a, b, c, ac` on `P`; `∅, a, b, c, ab, bc` on `E`. -/
  present_absent :
    (Indep wordP ∅ ∧ Indep wordP {a} ∧ Indep wordP {b} ∧ Indep wordP {c} ∧ Indep wordP {a, c}) ∧
    (¬ Indep wordP {a, b} ∧ ¬ Indep wordP {b, c} ∧ ¬ Indep wordP {a, b, c}) ∧
    (Indep wordE ∅ ∧ Indep wordE {a} ∧ Indep wordE {b} ∧ Indep wordE {c} ∧ Indep wordE {a, b} ∧
      Indep wordE {b, c}) ∧
    (¬ Indep wordE {a, c} ∧ ¬ Indep wordE {a, b, c})
  /-- "Local undominated table. P: empty -> abc; a -> c; b -> empty; c -> a; ac -> empty". -/
  undominated_P : undominated wordP ∅ = {a, b, c} ∧ undominated wordP {a} = {c} ∧
    undominated wordP {b} = ∅ ∧ undominated wordP {c} = {a} ∧ undominated wordP {a, c} = ∅
  /-- "E: empty -> abc; a -> b; b -> ac (connected); c -> b; ab -> empty; bc -> empty". -/
  undominated_E : undominated wordE ∅ = {a, b, c} ∧ undominated wordE {a} = {b} ∧
    (undominated wordE {b} = {a, c} ∧ Interlaces wordE a c) ∧ undominated wordE {c} = {b} ∧
    undominated wordE {a, b} = ∅ ∧ undominated wordE {b, c} = ∅
  /-- "For endpoint `a`, the unsigned residual word is `c B c C` on `P` versus `b B b C` on `E`, with
  the `A`-carrier unchanged." -/
  residual_endpoint_a : residual wordP {a} [0, 4, 5, 6, 7, 8] = [c, B, c, C] ∧
    residual wordE {a} [0, 1, 5, 6, 7, 8] = [b, B, b, C] ∧
    residual wordP {a} [1, 2, 3] = [A] ∧ residual wordE {a} [2, 3, 4] = [A]
  /-- "For endpoint `c`, it is `a A a C` versus `b A b C`, with the `B`-carrier unchanged." -/
  residual_endpoint_c : residual wordP {c} [0, 1, 2, 3, 4, 8] = [a, A, a, C] ∧
    residual wordE {c} [0, 1, 2, 3, 7, 8] = [b, A, b, C] ∧
    residual wordP {c} [5, 6, 7] = [B] ∧ residual wordE {c} [4, 5, 6] = [B]
  /-- "For the selected row, P-`b` has no local residual on carriers `C|AB`; E-`b` has residual
  `a A c a B c` on `AB` …; and P-`ac` has three local-empty carriers `C|A|B`." -/
  residual_selected : residual wordP {b} [0, 1, 7, 8] = [C] ∧ residual wordP {b} [3, 4, 5, 6, 2] = [B, A] ∧
    residual wordE {b} [1, 2, 3, 4, 5, 6, 7] = [a, A, c, a, B, c] ∧
    residual wordP {a, c} [0, 4, 8] = [C] ∧ residual wordP {a, c} [1, 2, 3] = [A] ∧
    residual wordP {a, c} [5, 6, 7] = [B]
  /-- "All four quantities are nonzero on either chamber of a simple wall" (`D_ef, D_eg, D_fg, Delta`). -/
  nonzero : ∀ (t : E.Parameter), Punctured E δ t →
    CV.G5 (E.curve t) e f ≠ 0 ∧ CV.G5 (E.curve t) e g ≠ 0 ∧ CV.G5 (E.curve t) f g ≠ 0 ∧
      CV.G3 (E.curve t) e f g ≠ 0
  /-- (1) "`t_ef − t_eg = −Delta/(D_ef D_eg)`, `t_fe − t_fg = −Delta/(D_ef D_fg)`,
  `t_ge − t_gf = −Delta/(D_eg D_fg)`" (the Cramer identities). -/
  cramer : ∀ (t : E.Parameter), Punctured E δ t →
    CV.crossParam (E.curve t) e f - CV.crossParam (E.curve t) e g =
      -CV.G3 (E.curve t) e f g / (CV.G5 (E.curve t) e f * CV.G5 (E.curve t) e g) ∧
    CV.crossParam (E.curve t) f e - CV.crossParam (E.curve t) f g =
      -CV.G3 (E.curve t) e f g / (CV.G5 (E.curve t) e f * CV.G5 (E.curve t) f g) ∧
    CV.crossParam (E.curve t) g e - CV.crossParam (E.curve t) g f =
      -CV.G3 (E.curve t) e f g / (CV.G5 (E.curve t) e g * CV.G5 (E.curve t) f g)
  /-- (2) "`(q_e,q_f,q_g) = −delta (s_a s_b, s_a s_c, s_b s_c)`". -/
  sign_identity : ∀ (t : E.Parameter), Punctured E δ t →
    orderSign (E.curve t) e f g =
      -(concurrenceSign (E.curve t) e f g * (strandSign (E.curve t) e f * strandSign (E.curve t) e g)) ∧
    orderSign (E.curve t) f e g =
      -(concurrenceSign (E.curve t) e f g * (strandSign (E.curve t) e f * strandSign (E.curve t) f g)) ∧
    orderSign (E.curve t) g e f =
      -(concurrenceSign (E.curve t) e f g * (strandSign (E.curve t) e g * strandSign (E.curve t) f g))
  /-- (3) "After erasing every outside visit, the traversal encounters the `e`, `f`, and `g`
  two-crossing blocks in that order. Hence direct reading of the six-letter word gives: edge(a,b) is
  present iff `q_e = −1`, edge(a,c) is present iff `q_f = +1`, edge(b,c) is present iff `q_g = −1`." -/
  edge_reading : ∀ (t : E.Parameter) (ht : Punctured E δ t),
    (EdgeAB (sideGeometry E ht) e f g ↔ orderSign (E.curve t) e f g = SignType.neg) ∧
    (EdgeAC (sideGeometry E ht) e f g ↔ orderSign (E.curve t) f e g = SignType.pos) ∧
    (EdgeBC (sideGeometry E ht) e f g ↔ orderSign (E.curve t) g e f = SignType.neg)
  /-- "Changing chamber changes the sign of `Delta`, so (2) negates all three `q`'s; (3) therefore
  toggles exactly the three local graph edges, consistently with R-LOC": across the wall `delta`
  flips, the three strand signs are unchanged, and the three `q`'s negate. -/
  wall_toggle : ∀ (s t : E.Parameter), Punctured E δ s → Punctured E δ t → OppositeSides E s t →
    concurrenceSign (E.curve s) e f g = - concurrenceSign (E.curve t) e f g ∧
    (strandSign (E.curve s) e f = strandSign (E.curve t) e f ∧
      strandSign (E.curve s) e g = strandSign (E.curve t) e g ∧
      strandSign (E.curve s) f g = strandSign (E.curve t) f g) ∧
    (orderSign (E.curve s) e f g = - orderSign (E.curve t) e f g ∧
      orderSign (E.curve s) f e g = - orderSign (E.curve t) f e g ∧
      orderSign (E.curve s) g e f = - orderSign (E.curve t) g e f)
  /-- "The local graph is extreme exactly when all three indicators in (3) agree. That requires
  `(q_e,q_f,q_g)` to be `(−,+,−)` or `(+,−,+)`. … this is equivalent to `s_a = s_c = −s_b`, namely one
  of the two alternating sign triples." -/
  extreme_iff : ∀ (t : E.Parameter) (ht : Punctured E δ t),
    (Extreme (sideGeometry E ht) e f g ↔
      ((orderSign (E.curve t) e f g = SignType.neg ∧ orderSign (E.curve t) f e g = SignType.pos ∧
          orderSign (E.curve t) g e f = SignType.neg) ∨
        (orderSign (E.curve t) e f g = SignType.pos ∧ orderSign (E.curve t) f e g = SignType.neg ∧
          orderSign (E.curve t) g e f = SignType.pos))) ∧
    (Extreme (sideGeometry E ht) e f g ↔ Alternating (E.curve t) e f g)
  /-- "Therefore the generic orbit is exactly the other six, nonalternating triples." -/
  generic_iff : ∀ (t : E.Parameter) (ht : Punctured E δ t),
    GenericOrbit (sideGeometry E ht) e f g ↔ ¬ Alternating (E.curve t) e f g
  /-- (4) "For each nonalternating sign triple exactly one condition in (4) holds" (the printed
  six-row table: `+++`/`---` → `ac`; `++-`/`--+` → `bc`; `+--`/`-++` → `ab`). -/
  exactly_one_selected : ∀ (t : E.Parameter), Punctured E δ t → ¬ Alternating (E.curve t) e f g →
    (SelectedAC (E.curve t) e f g ∧ ¬ SelectedAB (E.curve t) e f g ∧ ¬ SelectedBC (E.curve t) e f g) ∨
    (SelectedBC (E.curve t) e f g ∧ ¬ SelectedAB (E.curve t) e f g ∧ ¬ SelectedAC (E.curve t) e f g) ∨
    (SelectedAB (E.curve t) e f g ∧ ¬ SelectedAC (E.curve t) e f g ∧ ¬ SelectedBC (E.curve t) e f g)
  /-- (4) "Using (2)–(3), the `P3` graph on either chamber has as its degree-two vertex the crossing
  complementary to that pair. Thus the unique separating-strand pair is precisely the graph-selected
  pair": in the generic orbit, on the two-edge side the selected pair is the complement of the
  degree-two vertex, and on the one-edge side it is the present edge. -/
  selected_is_graph_selected : ∀ (t : E.Parameter) (ht : Punctured E δ t),
    GenericOrbit (sideGeometry E ht) e f g →
      (SelectedAC (E.curve t) e f g ↔
        ((EdgeAB (sideGeometry E ht) e f g ∧ EdgeBC (sideGeometry E ht) e f g) ∨
          (EdgeAC (sideGeometry E ht) e f g ∧ ¬ EdgeAB (sideGeometry E ht) e f g ∧
            ¬ EdgeBC (sideGeometry E ht) e f g))) ∧
      (SelectedAB (E.curve t) e f g ↔
        ((EdgeAC (sideGeometry E ht) e f g ∧ EdgeBC (sideGeometry E ht) e f g) ∨
          (EdgeAB (sideGeometry E ht) e f g ∧ ¬ EdgeAC (sideGeometry E ht) e f g ∧
            ¬ EdgeBC (sideGeometry E ht) e f g))) ∧
      (SelectedBC (E.curve t) e f g ↔
        ((EdgeAB (sideGeometry E ht) e f g ∧ EdgeAC (sideGeometry E ht) e f g) ∨
          (EdgeBC (sideGeometry E ht) e f g ∧ ¬ EdgeAB (sideGeometry E ht) e f g ∧
            ¬ EdgeAC (sideGeometry E ht) e f g)))
  /-- The local word of the triangle on the event's sides: the six triangle visits form the `e`-, `f`-
  and `g`-blocks in that cyclic order, each block ordered by its `q` ("After erasing every outside
  visit, the traversal encounters the `e`, `f`, and `g` two-crossing blocks in that order"). -/
  local_word : ∀ (t : E.Parameter) (ht : Punctured E δ t),
    triangleWord (sideGeometry E ht) e f g =
      (blockE e f g (orderSign (E.curve t) e f g) ++ blockF e f g (orderSign (E.curve t) f e g) ++
        blockG e f g (orderSign (E.curve t) g e f) : List (Finset (ZMod n)))
  /-- "`P = a b A a c B b c C`, `E = b a A c a B c b C`" as the words of the event in the canonical
  branch `sgn det(u1,u2) = sgn det(u1,u3) = sgn det(u2,u3)` (R_GENERIC_COMMON_TRANSPORT_PROOF.md (1)):
  `P` on the side where `Delta > 0` and `E` on the side where `Delta < 0` (by (2), (3)). -/
  canonical_words : ∀ (t : E.Parameter) (ht : Punctured E δ t),
    strandSign (E.curve t) e f = strandSign (E.curve t) e g →
    strandSign (E.curve t) e g = strandSign (E.curve t) f g →
      (concurrenceSign (E.curve t) e f g = SignType.pos →
        triangleWord (sideGeometry E ht) e f g = (wordPSupports e f g : List (Finset (ZMod n)))) ∧
      (concurrenceSign (E.curve t) e f g = SignType.neg →
        triangleWord (sideGeometry E ht) e f g = (wordESupports e f g : List (Finset (ZMod n))))
  /-- "Full availability plus R-PAR sharpens the exterior masks: after `a`, survivors have mask `0`
  or `bc`, so `b,c` are twins; after `c`, mask `0` or `ab`, so `a,b` are twins; after `b`, mask `0` or
  `ac`, so `a,c` are twins; after any present pair only mask-zero outsiders survive." Survivors are
  the undominated crossings `U(S)` of CV def:pieces (`CV.U`). -/
  mask_sharpening : ∀ (t : E.Parameter) (ht : Punctured E δ t) (Q : Finset (Crossing (E.curve t))),
    Q ∈ CV.Ind (sideGeometry E ht) → Disjoint Q (triangle (E.curve t) e f g) →
    avail (sideGeometry E ht) (triangle (E.curve t) e f g) Q = triangle (E.curve t) e f g →
      (∀ x : Crossing (E.curve t), x.val = {e, f} →
        ∀ y ∈ CV.U (sideGeometry E ht) (insert x Q), y.val ∉ triangleSupports e f g →
          mask (sideGeometry E ht) e f g y = ∅ ∨ mask (sideGeometry E ht) e f g y = {{e, g}, {f, g}}) ∧
      (∀ x : Crossing (E.curve t), x.val = {f, g} →
        ∀ y ∈ CV.U (sideGeometry E ht) (insert x Q), y.val ∉ triangleSupports e f g →
          mask (sideGeometry E ht) e f g y = ∅ ∨ mask (sideGeometry E ht) e f g y = {{e, f}, {e, g}}) ∧
      (∀ x : Crossing (E.curve t), x.val = {e, g} →
        ∀ y ∈ CV.U (sideGeometry E ht) (insert x Q), y.val ∉ triangleSupports e f g →
          mask (sideGeometry E ht) e f g y = ∅ ∨ mask (sideGeometry E ht) e f g y = {{e, f}, {f, g}}) ∧
      (∀ J : Finset (Crossing (E.curve t)), J ⊆ triangle (E.curve t) e f g → J.card = 2 →
        Q ∪ J ∈ CV.Ind (sideGeometry E ht) →
        ∀ y ∈ CV.U (sideGeometry E ht) (Q ∪ J), y.val ∉ triangleSupports e f g →
          mask (sideGeometry E ht) e f g y = ∅)

/-- Row 172, R:generic_table. -/
theorem generic_table (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericTableData E e f g δ := by
  sorry

end RProof
