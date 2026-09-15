import SM.PolynomialBlock
import SM.ZeroLink
import SM.LinkRecordExtras
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Marked products and mixed rows — statements (designer B, diagram-first)

Source (frozen, frame SM15): reference/SM/sm-3-statesum.tex — the marked-join paragraph 1362-1426,
mp:join 1427-1437, mp:lowest 1582-1596, mp:blocks 1624-1636; reference/SM/sm-4-knotlaws.tex
lem:homflyrows 230-266.  Main declarations: `SM.join : JoinData`, `SM.lowest : LowestData`,
`SM.blocks : BlocksData`, `SM.homflyrows : HomflyRowsData` (all `sorry`; this file fixes the
statements only).  Design: work/drafts/markedproducts/NOTES_B.md (clause map, readings, reuse).

## Printed notion → Lean rendering (namespace `SM.Link` unless noted)

* "an actual nonempty (oriented) diagram" — `D : Diagram` (polygonal, `c ≥ 1` in the type,
  SM/LinkDiagram.lean:490); its components `Fin D.Γ.c`, crossings `D.Γ.Crossing`, crossing
  occurrences ("visits") `D.Γ.Visit`, the component of an occurrence `D.compOf`, the forward
  successor `D.nextVisit`, the pairing `D.twin`, the over bit `D.overBit`, the sign `D.sign`
  (SM/LinkDiagramRecord.lean); its named record `D.record` (ibid. 500) and named record
  isomorphism `RecordIso` (SM/LinkRecord.lean:539).
* "a marked diagram ... a specified closed nonsingular oriented interval `I` on one component; `I`
  contains no crossing and is contained in a clean disc" (1366-1369) — `Diagram.Mark`: an
  `Arc` `I` (SM/LinkMoves.lean:145) with the accepted `IsMarkedInterval D I` (SM/LinkMoves.lean:1107).
* "their marked gaps" (1375) — `Diagram.Mark.IsGap μ v`: `v` is the occurrence of the marked
  component met last before `I` (so `I` lies in the cyclic gap from `v` to `D.nextVisit v`).
* "a marked join ... Its finite data are precise: concatenate the marked component cycles at their
  marked gaps, retain every other component, and keep exactly all old crossing pairings, bits and
  signs. The component number is `c(A)+c(B)−1`" (1370-1379) — `MarkedJoinData A B μA μB J`
  (one field per printed clause, stated on the visits, successor, pairing, bits, signs and
  components of the actual diagrams) and `IsCleanMarkedJoin := Nonempty (MarkedJoinData …)`;
  comparison with the record-level `Record.joinRecord` (SM/LinkRecord.lean:1513):
  `markedJoin_record_statement`.
* "`P`" — `SM.P` (SM/LocalPolynomial.lean:66); "`H`" — `SM.homfly` (SM/LinkInterfaces.lean:131);
  "`δ`", "`(a−a⁻¹)/z`" — `R.delta`; "`[z^k] f`" — `zRow k f : LaurentPolynomial ℤ`
  (SM/LinkLaurentRing.lean:335); "`a`", "`a⁻¹`" in a `z`-row — `LaurentPolynomial.T 1`,
  `LaurentPolynomial.T (-1)`; "`a − a⁻¹`" — `aMinusAInv`.
* "their actual knot restrictions `D_i`" (1584) — `Diagram.knotRestrict D i := D.restrict {i} _`
  (SM/LinkDiagram.lean:1082).
* "`ℓ_ij = ½ Σ σ(x)` using ALL mixed crossings between the original components `i, j`" (1585-1586)
  — `2ℓ_ij = mixedSignSum D i j` (SM/ZeroLink.lean:31, the accepted mp:zero-link sum; an even
  integer by `SM.zero_link.half_sum_integer`); "`Λ = Σ_{i<j} ℓ_ij`" — `2Λ = twoLambda D`;
  "`a^{−2Λ}`" — `LaurentPolynomial.T (-twoLambda D)`.  "linking number `lk`" (sm-4:233) —
  `2·lk = mixedSignSum D 0 1`.
* "an actual oriented one-circle decorated record with a nonempty crossing set" (1625-1626) —
  `D₀.record` for `D₀ : Diagram` with `D₀.componentCount = 1` and `Nonempty D₀.Γ.Crossing`.
* "its interlacement graph" (1626-1627) — `Diagram.interlacementGraph D₀ : SimpleGraph D₀.Γ.Crossing`
  (two crossings interlace when their occurrences alternate along the oriented circle,
  `Diagram.Interlaces`, the multi-visit copy of the accepted `SM.Interlaces`,
  SM/Interlacement.lean:16); "its connected components `H`" — `SimpleGraph.ConnectedComponent`,
  the crossing set of `H` is `H.supp`.
* "that restricted named cyclic record" (1628) — `Diagram.blockRecord D₀ H.supp`, the record of
  `D₀` restricted to the occurrences of the crossings in `H` (first-return successor,
  `Record.restrictOcc`, the occurrence-level copy of the accepted `Record.restrict`,
  SM/LinkRecord.lean:1144).
* "a finite succession of clean marked joins of these actual diagrams" (1629) — `JoinTree C S J`
  (inductive: leaves `C i`, nodes clean marked joins, each leaf used once).
* "writhe" — `Diagram.writhe` (SM/LinkDiagram.lean:577). -/

namespace SM

open SM.Link Classical

namespace Link

/-! ## A. Marked diagrams (sm-3:1366-1369) -/

/-- sm-3:1366-1369: "A marked diagram is a nonempty actual diagram with a specified closed
nonsingular oriented interval `I` on one component; `I` contains no crossing and is contained in a
clean disc."  The diagram is `D` (nonempty: `c ≥ 1` in the type); the interval is the closed
traversal arc `I` on component `I.i`; "contains no crossing and is contained in a clean disc" is
the accepted `IsMarkedInterval D I` (no occurrence lies on `I`, and some disc meets `D` exactly in
`I`).  "All crossing discs used in a recursion are chosen disjoint from `I`" (1369-1370) is a
proof-side choice, not part of the data. -/
structure Diagram.Mark (D : Diagram) where
  /-- the specified closed oriented interval, on the component `I.i` -/
  I : D.Γ.Arc
  /-- "`I` contains no crossing and is contained in a clean disc" -/
  marked : IsMarkedInterval D I

namespace Diagram.Mark

variable {D : Diagram} (μ : D.Mark)

/-- The *marked gap* (sm-3:1375 "concatenate the marked component cycles at their marked gaps"):
`v` is the crossing occurrence of the marked component met last before the interval `I` — no
occurrence of that component lies cyclically strictly between `v` and the entering end `I.start`.
Since `I` carries no occurrence, `I` lies in the cyclic gap from `v` to its forward successor
`D.nextVisit v`.  A crossing-free marked component has no gap occurrence ("an arbitrary
crossing-free marked component", sm-3:1433-1434). -/
def IsGap (v : D.Γ.Visit) : Prop :=
  D.compOf v = μ.I.i ∧
    ∀ w : D.Γ.Visit, D.compOf w = μ.I.i →
      ¬ cycBetween (D.visitCoord v) (D.visitCoord w) (traversalKey μ.I.start)

/-- The marked component carries no crossing occurrence ("an arbitrary crossing-free marked
component", sm-3:1433-1434). -/
def IsCrossingFree : Prop := ∀ v : D.Γ.Visit, D.compOf v ≠ μ.I.i

end Diagram.Mark

/-! ## B. Clean marked joins, stated on the actual diagrams (sm-3:1370-1379)

"A marked join of `(A,I_A)` and `(B,I_B)` cuts a smaller open interval inside each mark and joins
the oriented ends crosswise, preserving the surviving collars. There are no additional crossings in
the joining arcs. Its finite data are precise: concatenate the marked component cycles at their
marked gaps, retain every other component, and keep exactly all old crossing pairings, bits and
signs. The component number is `c(A)+c(B)−1`. ... The operation is not defined as an unspecified
ambient isotopy class."  (1370-1379.)  The clean realizations "are compared only by
Lemma lc:presentations" (1417-1418), i.e. by their finite data; so an actual clean marked join is
an actual diagram `J` whose finite data are the printed concatenation.  Every field below is one
printed clause, stated on the occurrences, successor, pairing, bits, signs and components of the
actual diagrams `A`, `B`, `J`. -/

/-- The finite data of a clean marked join `J = J(A,B)` of the marked diagrams `(A, μA)`,
`(B, μB)` (sm-3:1370-1379). -/
structure MarkedJoinData (A B : Diagram) (μA : A.Mark) (μB : B.Mark) (J : Diagram) where
  /-- "There are no additional crossings in the joining arcs" and "keep exactly all old crossing
  ...": the crossing occurrences of `J` are exactly the old occurrences of `A` and of `B`. -/
  Φ : A.Γ.Visit ⊕ B.Γ.Visit ≃ J.Γ.Visit
  /-- "keep exactly all old crossing pairings" -/
  pair_eq : ∀ v, J.twin (Φ v) = Φ (Sum.map A.twin B.twin v)
  /-- "... bits" -/
  bit_eq : ∀ v, J.overBit (Φ v) = Sum.elim A.overBit B.overBit v
  /-- "... and signs" -/
  sgn_eq : ∀ v, J.sign (Φ v).1 = Sum.elim (fun a => A.sign a.1) (fun b => B.sign b.1) v
  /-- "retain every other component" / "The component number is `c(A)+c(B)−1`": the components of
  `J` are the components of `A` (the marked one now carrying the concatenated cycle) together with
  the unmarked components of `B`. -/
  e : Fin A.Γ.c ⊕ {j : Fin B.Γ.c // j ≠ μB.I.i} ≃ Fin J.Γ.c
  /-- occurrences of `A` stay on their component -/
  comp_inl : ∀ a, J.compOf (Φ (Sum.inl a)) = e (Sum.inl (A.compOf a))
  /-- occurrences of `B` on an unmarked component stay on it -/
  comp_inr : ∀ b (h : B.compOf b ≠ μB.I.i), J.compOf (Φ (Sum.inr b)) = e (Sum.inr ⟨B.compOf b, h⟩)
  /-- occurrences of `B` on its marked component now lie on the concatenated component -/
  comp_inr_marked : ∀ b, B.compOf b = μB.I.i → J.compOf (Φ (Sum.inr b)) = e (Sum.inl μA.I.i)
  /-- "concatenate the marked component cycles at their marked gaps": away from the gap of `A` the
  successor of `A` is kept -/
  succ_inl : ∀ a, ¬ μA.IsGap a → J.nextVisit (Φ (Sum.inl a)) = Φ (Sum.inl (A.nextVisit a))
  /-- away from the gap of `B` the successor of `B` is kept -/
  succ_inr : ∀ b, ¬ μB.IsGap b → J.nextVisit (Φ (Sum.inr b)) = Φ (Sum.inr (B.nextVisit b))
  /-- at the gap of `A` the traversal continues into `B` just after the gap of `B` -/
  succ_gap_left : ∀ a b, μA.IsGap a → μB.IsGap b →
    J.nextVisit (Φ (Sum.inl a)) = Φ (Sum.inr (B.nextVisit b))
  /-- at the gap of `B` the traversal continues into `A` just after the gap of `A` -/
  succ_gap_right : ∀ a b, μA.IsGap a → μB.IsGap b →
    J.nextVisit (Φ (Sum.inr b)) = Φ (Sum.inl (A.nextVisit a))
  /-- a marked component of `B` without gap occurrence (a crossing-free marked component,
  sm-3:1433-1434) inserts no occurrence: the gap of `A` keeps its successor -/
  succ_gap_left_free : ∀ a, μA.IsGap a → (∀ b, ¬ μB.IsGap b) →
    J.nextVisit (Φ (Sum.inl a)) = Φ (Sum.inl (A.nextVisit a))
  /-- symmetrically for a marked component of `A` without gap occurrence -/
  succ_gap_right_free : ∀ b, μB.IsGap b → (∀ a, ¬ μA.IsGap a) →
    J.nextVisit (Φ (Sum.inr b)) = Φ (Sum.inr (B.nextVisit b))

/-- `J` is an actual clean marked join `J(A,B)` of `(A, μA)` and `(B, μB)` (sm-3:1370-1379,
1427-1429 "any actual clean marked join `J(A,B)` just specified"). -/
def IsCleanMarkedJoin (A B : Diagram) (μA : A.Mark) (μB : B.Mark) (J : Diagram) : Prop :=
  Nonempty (MarkedJoinData A B μA μB J)

/-- Sanity (sm-3:1378-1379 "The component number is `c(A)+c(B)−1`"): a consequence of the
component clause of the definition. -/
theorem MarkedJoinData.componentCount {A B : Diagram} {μA : A.Mark} {μB : B.Mark} {J : Diagram}
    (h : MarkedJoinData A B μA μB J) :
    J.componentCount = A.componentCount + B.componentCount - 1 := by
  have h1 := Fintype.card_congr h.e
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h1
  have h2 : Fintype.card {j : Fin B.Γ.c // j ≠ μB.I.i} = B.Γ.c - 1 := by
    have := Fintype.card_subtype_compl (fun j : Fin B.Γ.c => j = μB.I.i)
    rw [Fintype.card_subtype_eq, Fintype.card_fin] at this
    exact (Fintype.card_congr (Equiv.refl _)).trans this
  have h3 : 1 ≤ B.Γ.c := B.Γ.hc
  unfold Diagram.componentCount
  omega

/-- Comparison with the record (the bridge to be proved in the proof phase, not a row): when the
record-level marks `νA`, `νB` (SM/LinkRecord.lean:1226) name the diagram-level gaps, `J` is a clean
marked join iff its named record is isomorphic to the record-level join `Record.joinRecord νA νB`
(SM/LinkRecord.lean:1513) — the printed "finite data" (sm-3:1374-1379). -/
def markedJoin_record_statement : Prop :=
  ∀ (A B : Diagram) (μA : A.Mark) (μB : B.Mark) (J : Diagram)
    (νA : A.record.Mark) (νB : B.record.Mark),
    νA.comp = μA.I.i → νB.comp = μB.I.i →
    (∀ v, νA.gap = some v ↔ μA.IsGap v) → (∀ v, νB.gap = some v ↔ μB.IsGap v) →
    (IsCleanMarkedJoin A B μA μB J ↔ Nonempty (RecordIso (Record.joinRecord νA νB) J.record))

/-! ## C. Knot restrictions, linking sums and `z`-rows (mp:lowest, sm-3:1583-1591) -/

/-- "their actual knot restrictions `D_i`" (sm-3:1584): the restriction of `D` to the single
component `i`, keeping its self-crossings (`Diagram.restrict`, mp:stack's `D_i` with a one-component
block). -/
noncomputable def Diagram.knotRestrict (D : Diagram) (i : Fin D.Γ.c) : Diagram :=
  D.restrict {i} (Finset.singleton_nonempty i)

/-- "`Λ = Σ_{i<j} ℓ_ij`" with "`ℓ_ij = ½ Σ σ(x)` using ALL mixed crossings between the original
components `i, j`" (sm-3:1585-1586), doubled: `twoLambda D = 2Λ = Σ_{i<j} mixedSignSum D i j`, the
total mixed sign sum (an integer; each `mixedSignSum D i j` is even by mp:zero-link). -/
noncomputable def twoLambda (D : Diagram) : ℤ :=
  ∑ i : Fin D.Γ.c, ∑ j : Fin D.Γ.c, if i < j then mixedSignSum D i j else 0

/-- "`a − a⁻¹`" inside a `z`-row, as an element of `ℤ[a^{±1}]`. -/
noncomputable def aMinusAInv : LaurentPolynomial ℤ :=
  LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)

/-! ## D. One-circle interlacement, restricted records and join trees (mp:blocks, sm-3:1625-1630) -/

/-- Two crossings of a one-circle diagram *interlace* when their occurrences alternate along the
oriented circle (the accepted `SM.Interlaces`, SM/Interlacement.lean:16, read on the occurrences of
a `Diagram`): some occurrence of `y` lies cyclically strictly between the over and the under
occurrence of `x`, and the other one strictly between the under and the over occurrence.  Meaningful
for `D.componentCount = 1`, where all occurrences share one parameter circle and `D.visitCoord` is
its cyclic coordinate. -/
def Diagram.Interlaces (D : Diagram) (x y : D.Γ.Crossing) : Prop :=
  x ≠ y ∧ ∃ y₀ y₁ : D.Γ.Visit, y₀.1 = y ∧ y₁.1 = y ∧ y₀ ≠ y₁ ∧
    cycBetween (D.visitCoord (D.overVisit x)) (D.visitCoord y₀) (D.visitCoord (D.underVisit x)) ∧
    cycBetween (D.visitCoord (D.underVisit x)) (D.visitCoord y₁) (D.visitCoord (D.overVisit x))

/-- "its interlacement graph" (sm-3:1626-1627): the simple graph on the crossings whose edges are
the interlacing pairs (`SimpleGraph.fromRel` symmetrises; the relation is symmetric by the rotation
of alternating visits, as for the accepted `interlaces_symm`). -/
def Diagram.interlacementGraph (D : Diagram) : SimpleGraph D.Γ.Crossing :=
  SimpleGraph.fromRel D.Interlaces

namespace Record

variable (ρ : Record) (p : ρ.M → Prop) [DecidablePred p] (hp : ∀ v, p (ρ.pair v) ↔ p v)

/-- The *restricted named cyclic record* of a record on a pair-invariant set of occurrences
(sm-3:1628 "exactly that restricted named cyclic record"; the occurrence-level copy of the
accepted block restriction `Record.restrict`, SM/LinkRecord.lean:1144): keep the circles, keep the
occurrences satisfying `p` with their pairing, bits and signs, and let the successor be the first
return of `s` to the retained occurrences (the inherited cyclic order). -/
noncomputable def restrictOcc : Record where
  comps := ρ.comps
  M := {v : ρ.M // p v}
  comp v := ρ.comp v.1
  succ := firstReturn ρ.succ p
  pair := ρ.pair.subtypePerm hp
  isOver v := ρ.isOver v.1
  sgn v := ρ.sgn v.1
  succ_comp v := by
    show ρ.comp (firstReturn ρ.succ p v).1 = ρ.comp v.1
    rw [firstReturn_apply, ρ.comp_pow]
  succ_cycle v w h := firstReturn_sameCycle_of_sameCycle _ _ (ρ.succ_cycle _ _ h)
  pair_ne v h := ρ.pair_ne v.1 (congrArg Subtype.val h)
  pair_invol v := Subtype.ext (ρ.pair_invol v.1)
  bit_pair v := ρ.bit_pair v.1
  sgn_pair v := ρ.sgn_pair v.1
  sgn_ne v := ρ.sgn_ne v.1

@[simp] theorem restrictOcc_M : (ρ.restrictOcc p hp).M = {v : ρ.M // p v} := rfl
@[simp] theorem restrictOcc_comps : (ρ.restrictOcc p hp).comps = ρ.comps := rfl
@[simp] theorem restrictOcc_sgn (v : (ρ.restrictOcc p hp).M) : (ρ.restrictOcc p hp).sgn v = ρ.sgn v.1 := rfl

end Record

/-- The restricted named cyclic record of the crossing subset `H` of a diagram (sm-3:1627-1628
"for every component `H` an actual retained diagram `C_H` with exactly that restricted named cyclic
record"): the record of `D` restricted to the occurrences of the crossings in `H`. -/
noncomputable def Diagram.blockRecord (D : Diagram) (H : Set D.Γ.Crossing) : Record :=
  D.record.restrictOcc (fun v => v.1 ∈ H) (fun _ => Iff.rfl)

/-- "a finite succession of clean marked joins of these actual diagrams" (sm-3:1629): `JoinTree C S J`
holds when `J` is obtained from the diagrams `C i`, `i ∈ S`, each used exactly once, by finitely
many clean marked joins (a leaf is a supplied diagram; a node is a clean marked join of two
subtrees with disjoint leaf sets). -/
inductive JoinTree {ι : Type} (C : ι → Diagram) : Set ι → Diagram → Prop
  | leaf (i : ι) : JoinTree C {i} (C i)
  | node {S₁ S₂ : Set ι} {A B J : Diagram} (μA : A.Mark) (μB : B.Mark) :
      JoinTree C S₁ A → JoinTree C S₂ B → Disjoint S₁ S₂ → IsCleanMarkedJoin A B μA μB J →
      JoinTree C (S₁ ∪ S₂) J

end Link

/-! ## E. The four rows -/

/-- mp:join (sm-3:1427-1437) as printed. -/
structure JoinData : Prop where
  /-- "For two nonempty actual marked diagrams and any actual clean marked join `J(A,B)` just
  specified, `P_{J(A,B)} = P_A P_B`" (eq. mp:join-value). -/
  value : ∀ (A B : Diagram) (μA : A.Mark) (μB : B.Mark) (J : Diagram),
    IsCleanMarkedJoin A B μA μB J → P J = P A * P B
  /-- "This includes ... an arbitrary crossing-free marked component" (sm-3:1433-1434): the case of
  a marked component carrying no crossing (the printed special case, implied by `value`).  The other
  inclusion, "smoothing-created multi-component factors", is the absence of any restriction on the
  component number of the factors in `value`. -/
  crossing_free_marked : ∀ (A B : Diagram) (μA : A.Mark) (μB : B.Mark) (J : Diagram),
    (μA.IsCrossingFree ∨ μB.IsCrossingFree) → IsCleanMarkedJoin A B μA μB J → P J = P A * P B

/-- mp:join. -/
theorem join : JoinData := by
  sorry

/-- mp:lowest (sm-3:1582-1596) as printed. -/
structure LowestData : Prop where
  /-- eq. mp:lowest-value: "`[z^{1−c}] P_D = a^{−2Λ} (a − a⁻¹)^{c−1} ∏_{i=1}^c [z^0] P_{D_i}`" for an
  actual diagram `D` with `c ≥ 1` tagged oriented components and knot restrictions `D_i`, `Λ`
  computed from ALL mixed crossings of `D` (`twoLambda D = 2Λ`). -/
  lowest : ∀ D : Diagram,
    zRow (1 - (D.componentCount : ℤ)) (P D) =
      LaurentPolynomial.T (-twoLambda D) * aMinusAInv ^ (D.componentCount - 1) *
        ∏ i : Fin D.Γ.c, zRow 0 (P (D.knotRestrict i))
  /-- "For `c = 2` this is the two-component mixed row; the two tagged restrictions are intrinsic
  knot diagrams while `ℓ_12` is computed in their original common diagram" (the printed
  specialisation, implied by `lowest`): `[z^{−1}] P_D = a^{−2ℓ_12} (a − a⁻¹) [z^0]P_{D_1} [z^0]P_{D_2}`. -/
  two_component : ∀ (D : Diagram) (hc : D.Γ.c = 2),
    zRow (-1) (P D) =
      LaurentPolynomial.T (-mixedSignSum D ⟨0, by omega⟩ ⟨1, by omega⟩) * aMinusAInv *
        (zRow 0 (P (D.knotRestrict ⟨0, by omega⟩)) * zRow 0 (P (D.knotRestrict ⟨1, by omega⟩)))

/-- mp:lowest. -/
theorem lowest : LowestData := by
  sorry

/-- mp:blocks (sm-3:1624-1636) as printed.  Throughout: `D₀` is an actual one-circle diagram with a
nonempty crossing set (its record is "the actual oriented one-circle decorated record"), `C H` the
supplied actual retained diagram of the connected component `H` of the interlacement graph, with
"exactly that restricted named cyclic record" (`RecordIso (C H).record (D₀.blockRecord H.supp)`);
"the full record" is `D₀.record`. -/
structure BlocksData : Prop where
  /-- "Then a finite succession of clean marked joins of these actual diagrams realizes the full
  record". -/
  realizes : ∀ (D₀ : Diagram), D₀.componentCount = 1 → Nonempty D₀.Γ.Crossing →
    ∀ (C : D₀.interlacementGraph.ConnectedComponent → Diagram),
    (∀ H, Nonempty (RecordIso (C H).record (D₀.blockRecord H.supp))) →
    ∃ J : Diagram, JoinTree C Set.univ J ∧ Nonempty (RecordIso J.record D₀.record)
  /-- "and every actual diagram with that full record has polynomial `∏_H P_{C_H}`". -/
  product : ∀ (D₀ : Diagram), D₀.componentCount = 1 → Nonempty D₀.Γ.Crossing →
    ∀ (C : D₀.interlacementGraph.ConnectedComponent → Diagram),
    (∀ H, Nonempty (RecordIso (C H).record (D₀.blockRecord H.supp))) →
    ∀ D : Diagram, Nonempty (RecordIso D.record D₀.record) →
      P D = ∏ H : D₀.interlacementGraph.ConnectedComponent, P (C H)
  /-- "The joins preserve the sign of every crossing": in every realizing succession of joins each
  crossing of the result is one crossing of one supplied `C_H`, with its sign ("Every old crossing
  is present once, with its old sign", 1682-1683). -/
  sign_preserved : ∀ (D₀ : Diagram), D₀.componentCount = 1 → Nonempty D₀.Γ.Crossing →
    ∀ (C : D₀.interlacementGraph.ConnectedComponent → Diagram),
    (∀ H, Nonempty (RecordIso (C H).record (D₀.blockRecord H.supp))) →
    ∀ J : Diagram, JoinTree C Set.univ J →
      ∃ φ : (Σ H : D₀.interlacementGraph.ConnectedComponent, (C H).Γ.Crossing) ≃ J.Γ.Crossing,
        ∀ q, J.sign (φ q) = (C q.1).sign q.2
  /-- "and the writhe is the sum of the writhes of `C_H`" (for every actual diagram with the full
  record). -/
  writhe_sum : ∀ (D₀ : Diagram), D₀.componentCount = 1 → Nonempty D₀.Γ.Crossing →
    ∀ (C : D₀.interlacementGraph.ConnectedComponent → Diagram),
    (∀ H, Nonempty (RecordIso (C H).record (D₀.blockRecord H.supp))) →
    ∀ D : Diagram, Nonempty (RecordIso D.record D₀.record) →
      D.writhe = ∑ H : D₀.interlacementGraph.ConnectedComponent, (C H).writhe

/-- mp:blocks. -/
theorem blocks : BlocksData := by
  sorry

/-- lem:homflyrows (sm-4:230-236) as printed, on `H = homfly` (lit:homfly's witness).  "Oriented
knots `K, J`" are read on actual one-component diagrams (the printed proof: "Choose actual knot
diagrams for `K, J` with clean marked intervals. The clean joining construction preceding
Theorem mp:join gives a diagram of their ordinary oriented connected sum"; "For split union, choose
representatives with disjoint page images"); the passage to knot classes is lit:homfly's descent
(`homfly_descent`), "not a conclusion of the local construction alone" (sm-4:247-250). -/
structure HomflyRowsData : Prop where
  /-- "For oriented knots `K, J`, `H_{K#J} = H_K H_J`": for one-component diagrams `K`, `J` with marks
  and any clean marked join `S` of them (a diagram of the oriented connected sum). -/
  connected_sum : ∀ (K J : Diagram), K.componentCount = 1 → J.componentCount = 1 →
    ∀ (μK : K.Mark) (μJ : J.Mark) (S : Diagram), IsCleanMarkedJoin K J μK μJ S →
      homfly S = homfly K * homfly J
  /-- "and `H_{K⊔J} = (a−a⁻¹)/z · H_K H_J`": for a two-component diagram without mixed crossings
  (a split union of the two knot diagrams `D_1 = K`, `D_2 = J`). -/
  split_union : ∀ (D : Diagram) (hc : D.Γ.c = 2),
    (∀ (x : D.Γ.Crossing) (s t : D.Γ.Strand), s ∈ x.val → t ∈ x.val → s.1 = t.1) →
    homfly D = R.delta * (homfly (D.knotRestrict ⟨0, by omega⟩) * homfly (D.knotRestrict ⟨1, by omega⟩))
  /-- "For a two-component oriented link diagram `D = D_1 ∪ D_2` with linking number `lk`,
  `[z^{−1}] H_D = (a − a⁻¹) a^{−2lk} [z^0](H_{D_1} H_{D_2})`", `2·lk = mixedSignSum D 0 1` (the
  half-sum of the decorated signs of the mixed crossings of the common diagram). -/
  two_component_row : ∀ (D : Diagram) (hc : D.Γ.c = 2),
    zRow (-1) (homfly D) =
      aMinusAInv * LaurentPolynomial.T (-mixedSignSum D ⟨0, by omega⟩ ⟨1, by omega⟩) *
        zRow 0 (homfly (D.knotRestrict ⟨0, by omega⟩) * homfly (D.knotRestrict ⟨1, by omega⟩))

/-- lem:homflyrows. -/
theorem homflyrows : HomflyRowsData := by
  sorry

end SM
