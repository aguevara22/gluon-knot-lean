import RProof.GenericTransport
import SM.MarkedProducts
import CV.GroupedKnot
import SM.Smoothing

/-! # Sketch_A — the "moves toolkit" (D-RM-1), architect A: CONSTRUCTOR ARCHITECTURE

Typechecked statements only (every theorem body is `sorry`; every `def` is real and compiles).
Design: work/drafts/moves/DESIGN_A.md.  Imports are accepted modules only.

The one geometric primitive is a VERTEX-CHAIN MOVE on an arbitrary `Diagram`: `r ≥ 1` consecutive
vertices `j, …, j+r−1` of one component are moved inside a disc `U`; the shadow TYPE is unchanged
(`Shadow.withVertices`, the strands are literally the same), the outside match is the identity on
labels, and the over data are pulled back on the surviving crossings (`Diagram.moveVertices`, the
`Diagram.deform` of LinkMoves with a one-way crossing inclusion).  The disc is the homothetic
enlargement of the convex hull `K = conv{p, chain, q}` of the chain and its two fixed neighbours
`p = j−1`, `q = j+r` — G11's template (`G11_discOf`, `G11_Params`).  Three local patterns share this
frame: B (empty bigon deletion, RII), K (kink insertion, RI), T (the G11 triangle, RIII, generalised
to arbitrary over data).  The record clause is one record operation `Record.erase` (the `restrict`
pattern with a different keep predicate and the components KEPT), proved as `restrictRecordIso` is
proved (LinkDiagramRecord §J: first return of the sorted cyclic successor). -/

namespace SM.Link

open SM

noncomputable section

/-! ## R. The record operation: erasing a pair-closed set of occurrences -/

namespace Record

variable (ρ : Record) (S : Finset ρ.M)

/-- Retained occurrences. -/
def EraseKeep (v : ρ.M) : Prop := v ∉ S

instance instDecidablePredEraseKeep : DecidablePred (ρ.EraseKeep S) :=
  fun v => inferInstanceAs (Decidable (v ∉ S))

/-- `S` is closed under the pairing (it is a union of whole crossings). -/
def PairClosed : Prop := ∀ v ∈ S, ρ.pair v ∈ S

theorem eraseKeep_pair_iff (hS : ρ.PairClosed S) (v : ρ.M) :
    ρ.EraseKeep S (ρ.pair v) ↔ ρ.EraseKeep S v := by
  unfold EraseKeep
  constructor
  · intro h hv; exact h (hS v hv)
  · intro h hv
    have := hS _ hv
    rw [ρ.pair_invol] at this
    exact h this

/-- **The erased record**: the circles are kept (a Reidemeister move never changes the components),
the occurrences of `S` are removed, the successor is the first return of `s` to the retained
occurrences (LinkRecord §A `firstReturn`, exactly as `Record.restrict` and `Record.smooth`). -/
def erase (hS : ρ.PairClosed S) : Record where
  comps := ρ.comps
  M := {v : ρ.M // ρ.EraseKeep S v}
  comp v := ρ.comp v.1
  succ := firstReturn ρ.succ (ρ.EraseKeep S)
  pair := ρ.pair.subtypePerm (ρ.eraseKeep_pair_iff S hS)
  isOver v := ρ.isOver v.1
  sgn v := ρ.sgn v.1
  succ_comp v := by
    show ρ.comp (firstReturn ρ.succ (ρ.EraseKeep S) v).1 = ρ.comp v.1
    rw [firstReturn_apply, ρ.comp_pow]
  succ_cycle v w h := firstReturn_sameCycle_of_sameCycle _ _ (ρ.succ_cycle _ _ h)
  pair_ne v h := ρ.pair_ne v.1 (congrArg Subtype.val h)
  pair_invol v := Subtype.ext (ρ.pair_invol v.1)
  bit_pair v := ρ.bit_pair v.1
  sgn_pair v := ρ.sgn_pair v.1
  sgn_ne v := ρ.sgn_ne v.1

/-- The two occurrences of one crossing. -/
def crossingSet (x : ρ.M) : Finset ρ.M := {x, ρ.pair x}

theorem pairClosed_crossingSet (x : ρ.M) : ρ.PairClosed (ρ.crossingSet x) := by
  intro v hv
  simp only [crossingSet, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (ρ.pair_invol _)

theorem pairClosed_union {S T : Finset ρ.M} (hS : ρ.PairClosed S) (hT : ρ.PairClosed T) :
    ρ.PairClosed (S ∪ T) := by
  intro v hv
  rcases Finset.mem_union.mp hv with h | h
  · exact Finset.mem_union.mpr (Or.inl (hS v h))
  · exact Finset.mem_union.mpr (Or.inr (hT v h))

/-- Erasing one crossing (pattern K: the kink). -/
def eraseCrossing (x : ρ.M) : Record := ρ.erase (ρ.crossingSet x) (ρ.pairClosed_crossingSet x)

/-- Erasing two crossings (pattern B: the bigon `{x, y}` — "the record minus the four visits"). -/
def eraseTwo (x y : ρ.M) : Record :=
  ρ.erase (ρ.crossingSet x ∪ ρ.crossingSet y)
    (ρ.pairClosed_union (ρ.pairClosed_crossingSet x) (ρ.pairClosed_crossingSet y))

/-- Sanity (Unit R): components kept, `N − 2` crossings, writhe minus the two signs. -/
theorem eraseTwo_componentCount (x y : ρ.M) : (ρ.eraseTwo x y).componentCount = ρ.componentCount := rfl

theorem eraseTwo_crossingCount (x y : ρ.M) (hxy : y ≠ x) (hxy' : y ≠ ρ.pair x) :
    (ρ.eraseTwo x y).crossingCount + 2 = ρ.crossingCount := by
  sorry

/-- Erasing commutes with switching another crossing (needed to move the `switch` past the erase). -/
theorem eraseTwo_switch (x y z : ρ.M) (hz : z ∉ ρ.crossingSet x ∪ ρ.crossingSet y) :
    Nonempty (RecordIso ((ρ.switch z).eraseTwo x y) ((ρ.eraseTwo x y).switch ⟨z, hz⟩)) := by
  sorry

end Record

/-! ## M. The vertex-chain move -/

/-- A labelled tuple with the `r` consecutive vertices `j, …, j+r−1` replaced by `w 0, …, w (r−1)`. -/
def LabelledTuple.updateChain {k : ℕ} (P : LabelledTuple k) (j : ZMod k) {r : ℕ} (w : Fin r → Plane) :
    LabelledTuple k :=
  fun a => if h : ∃ s : Fin r, a = j + (s.val : ZMod k) then w (Classical.choose h) else P a

namespace Shadow

variable (Γ : Shadow)

/-- The vertex tuples of `Γ` with the chain `j, …, j+r−1` of component `i` moved to `w`. -/
def updateChain (i : Fin Γ.c) (j : ZMod (Γ.comp i).k) {r : ℕ} (w : Fin r → Plane) : Γ.Vertices :=
  Function.update Γ.vertices i (LabelledTuple.updateChain (Γ.comp i).P j w)

/-- `K = conv{p, chain, q}`: the closed convex hull of the two fixed neighbours `p = j−1`, `q = j+r`
and the `r` chain vertices (for `r = 1` the closed triangle `p M q` containing the empty bigon). -/
def chainHull (i : Fin Γ.c) (j : ZMod (Γ.comp i).k) (r : ℕ) : Set Plane :=
  convexHull ℝ (Set.range fun s : Fin (r + 2) => Γ.tail ⟨i, j - 1 + (s.val : ZMod (Γ.comp i).k)⟩)

/-- The disc of the move: the homothetic enlargement of `K` about a point `c` with ratio `1 + η`
(G11's `G11_discOf`; `Convex.subset_interior_image_homothety_of_one_lt` puts `K` in its interior). -/
def chainDisc (i : Fin Γ.c) (j : ZMod (Γ.comp i).k) (r : ℕ) (c : Plane) (η : ℝ) : Set Plane :=
  (AffineMap.homothety c (1 + η)) '' Γ.chainHull i j r

theorem isDisc_chainDisc (i : Fin Γ.c) (j : ZMod (Γ.comp i).k) (r : ℕ) {c : Plane}
    (hc : c ∈ _root_.interior (Γ.chainHull i j r)) {η : ℝ} (hη : 0 < η) :
    IsDisc (Γ.chainDisc i j r c η) := by
  sorry

end Shadow

namespace Diagram

variable (D : Diagram)

/-- **The vertex-chain move**: the diagram on the re-vertexed shadow whose crossing set is CONTAINED
in `D`'s, with `D`'s over data pulled back (`Diagram.deform` of LinkMoves asks for equality of the
crossing sets; a deletion has fewer crossings). -/
def moveVertices (V : D.Γ.Vertices) (hgen : (D.Γ.withVertices V).Generic)
    (hcross : ∀ x : Finset D.Γ.Strand, (D.Γ.withVertices V).IsCrossing x → D.Γ.IsCrossing x) :
    Diagram where
  Γ := D.Γ.withVertices V
  generic := hgen
  overStrand := fun x => D.overStrand ⟨x.val, hcross x.val x.2⟩
  over_mem := fun x => D.over_mem ⟨x.val, hcross x.val x.2⟩

@[simp] theorem moveVertices_Γ (V : D.Γ.Vertices) (hgen) (hcross) :
    (D.moveVertices V hgen hcross).Γ = D.Γ.withVertices V := rfl

theorem moveVertices_componentCount (V : D.Γ.Vertices) (hgen) (hcross) :
    (D.moveVertices V hgen hcross).componentCount = D.componentCount := rfl

end Diagram

/-! ## B. Pattern B — the empty bigon along a vertex chain (Reidemeister II, deletion) -/

/-- **The empty-bigon hypothesis** on an arbitrary diagram: the two crossings `x`, `y` of the chain
path `p → j → … → j+r−1 → q` with the remote strand `rem` sit on its first and last edges, the inner
chain edges carry no crossing, the same strand is over at both (sm-3:1982-1984 "an empty ordinary
bigon with one common over-strand"), and the closed hull `K = conv{p, chain, q}` is CLEAR: it meets
no other edge, contains no other vertex, and the two outer edges `(p−1, p)`, `(q, q+1)` touch it only
at `p`, `q`.  For `r = 1` this is the bigon triangle `x M y` with `p ∈ (M−1, x)`, `q ∈ (y, M+1)` two
flat subdivision vertices (row 110); for `r = 2` the smoothing arc `[s⁻, t⁺]` (rows 110 curl, 177). -/
structure BigonChain (D : Diagram) where
  i : Fin D.Γ.c
  j : ZMod (D.Γ.comp i).k
  r : ℕ
  hr : 1 ≤ r
  /-- `p, chain, q` and at least one more vertex: the chain path does not wrap -/
  hk : r + 3 ≤ (D.Γ.comp i).k
  rem : D.Γ.Strand
  rem_ne : ∀ s : ℕ, s ≤ r + 1 → rem ≠ ⟨i, j - 1 + (s : ZMod (D.Γ.comp i).k)⟩
  x : D.Γ.Crossing
  y : D.Γ.Crossing
  hx : x.val = {⟨i, j - 1⟩, rem}
  hy : y.val = {⟨i, j + ((r - 1 : ℕ) : ZMod (D.Γ.comp i).k)⟩, rem}
  same_over : D.overStrand x = rem ↔ D.overStrand y = rem
  inner_free : ∀ (z : D.Γ.Crossing) (s : ℕ), s + 1 < r →
    (⟨i, j + (s : ZMod (D.Γ.comp i).k)⟩ : D.Γ.Strand) ∉ z.val
  hull_clear : ∀ e : D.Γ.Strand, e ≠ rem →
    (∀ s : ℕ, s ≤ r → e ≠ ⟨i, j - 1 + (s : ZMod (D.Γ.comp i).k)⟩) →
    Disjoint (D.Γ.seg e) (D.Γ.chainHull i j r)
  hull_vertex : ∀ e : D.Γ.Strand,
    (∀ s : ℕ, s ≤ r + 1 → e ≠ ⟨i, j - 1 + (s : ZMod (D.Γ.comp i).k)⟩) →
    D.Γ.tail e ∉ D.Γ.chainHull i j r
  end_clear_p : ∀ z ∈ D.Γ.seg ⟨i, j - 2⟩, z ∈ D.Γ.chainHull i j r → z = D.Γ.tail ⟨i, j - 1⟩
  end_clear_q : ∀ z ∈ D.Γ.seg ⟨i, j + (r : ZMod (D.Γ.comp i).k)⟩, z ∈ D.Γ.chainHull i j r →
    z = D.Γ.tail ⟨i, j + (r : ZMod (D.Γ.comp i).k)⟩
  interior_nonempty : (_root_.interior (D.Γ.chainHull i j r)).Nonempty

namespace BigonChain

variable {D : Diagram} (B : BigonChain D)

/-- The moved vertices: the constructor CHOOSES them (inside `K`, on the side of `p`, `q` of the line
of `rem`, along a segment parallel to `[p, q]`); the parameters `w, c, η` are existential in the
theorem, as `G11_exists_params`. -/
def moved (w : Fin B.r → Plane) : D.Γ.Vertices := D.Γ.updateChain B.i B.j w

end BigonChain

/-- **THE GENERIC RII DELETION** (pattern B).  For every diagram and every empty bigon along a
vertex chain there are new chain positions `w`, a disc `U`, and the moved diagram `D' := D` with the
chain at `w` (same shadow type, over data pulled back) such that `RIIData U D' D` holds and the record
of `D'` is the record of `D` minus the four visits of `x`, `y`. -/
theorem exists_rii_deletion (D : Diagram) (B : BigonChain D) :
    ∃ (w : Fin B.r → Plane)
      (hgen : (D.Γ.withVertices (B.moved w)).Generic)
      (hcross : ∀ z : Finset D.Γ.Strand, (D.Γ.withVertices (B.moved w)).IsCrossing z → D.Γ.IsCrossing z)
      (U : Set Plane),
      Nonempty (RIIData U (D.moveVertices (B.moved w) hgen hcross) D) ∧
      Nonempty (RecordIso (D.moveVertices (B.moved w) hgen hcross).record
        (D.record.eraseTwo (D.overVisit B.x) (D.overVisit B.y))) := by
  sorry

/-- The relational corollary the consumers read. -/
theorem rii_of_bigonChain (D : Diagram) (B : BigonChain D) :
    ∃ D' : Diagram, RII D' D ∧
      Nonempty (RecordIso D'.record (D.record.eraseTwo (D.overVisit B.x) (D.overVisit B.y))) := by
  obtain ⟨w, hgen, hcross, U, ⟨M⟩, hrec⟩ := exists_rii_deletion D B
  exact ⟨_, ⟨U, Or.inl ⟨M⟩⟩, hrec⟩

/-- Value form: `P D = P D_L` as soon as `D_L`'s record is `D`'s record minus the bigon. -/
theorem P_eq_of_bigonChain (D DL : Diagram) (B : BigonChain D)
    (hrec : Nonempty (RecordIso (D.record.eraseTwo (D.overVisit B.x) (D.overVisit B.y)) DL.record)) :
    P D = P DL := by
  obtain ⟨D', hR, ⟨ι⟩⟩ := rii_of_bigonChain D B
  obtain ⟨κ⟩ := hrec
  exact (P_reidemeister_II hR).symm.trans (presentations _ _ ⟨ι.trans κ⟩)

/-! ## S. Preprocessing: flat subdivision of one edge of an arbitrary diagram (Reparam) -/

namespace Shadow

variable (Γ : Shadow)

/-- The shadow with the edge `e` of component `e.1` subdivided at parameter `t` (`SM.insertVertex`);
the other components are untouched. -/
def subdivide (e : Γ.Strand) (t : ℝ) : Shadow where
  c := Γ.c
  hc := Γ.hc
  comp i := if i = e.1 then
      ⟨(Γ.comp e.1).k + 1, Nat.le_succ_of_le (Γ.comp e.1).hk, insertVertex (Γ.comp e.1).P e.2 t⟩
    else Γ.comp i

end Shadow

/-- **Unit S**: subdividing one edge at a parameter off every other edge is a reparametrization of
ANY diagram (the multi-component, arbitrary-over-data form of CS3's
`reparam_positiveDiagram_single_appendVertex`); the subdivided diagram lives on `Γ.subdivide e t`. -/
theorem exists_subdivide_reparam (D : Diagram) (e : D.Γ.Strand) {t : ℝ} (h0 : 0 < t) (h1 : t < 1)
    (hoff : ∀ s : D.Γ.Strand, s ≠ e → D.Γ.edgePt e t ∉ D.Γ.seg s) :
    ∃ D' : Diagram, D'.Γ = D.Γ.subdivide e t ∧ Reparam D D' := by
  sorry

/-- Switching commutes with reparametrization (`ReparamData.over_map` names the corresponding
crossing). -/
theorem reparam_switch {D D' : Diagram} (h : Reparam D D') (x : D.Γ.Crossing) :
    ∃ x' : D'.Γ.Crossing, D'.Γ.crossingPoint x' = D.Γ.crossingPoint x ∧
      Reparam (D.switch x) (D'.switch x') := by
  sorry

/-! ## K. Pattern K — kink insertion on a crossing-free stretch (Reidemeister I) -/

/-- **The kink site**: a chain of `r = 2` vertices `j, j+1` on a crossing-free stretch whose hull
`conv{p, j, j+1, q}` is clear (same clauses as `BigonChain` without the crossings), plus the sign of
the kink to insert.  The constructor moves `j, j+1` so that `[p, w₀]` and `[w₁, q]` cross once. -/
structure KinkSite (D : Diagram) where
  i : Fin D.Γ.c
  j : ZMod (D.Γ.comp i).k
  hk : 5 ≤ (D.Γ.comp i).k
  free : ∀ (z : D.Γ.Crossing) (s : ℕ), s ≤ 2 → (⟨i, j - 1 + (s : ZMod (D.Γ.comp i).k)⟩ : D.Γ.Strand) ∉ z.val
  hull_clear : ∀ e : D.Γ.Strand, (∀ s : ℕ, s ≤ 2 → e ≠ ⟨i, j - 1 + (s : ZMod (D.Γ.comp i).k)⟩) →
    Disjoint (D.Γ.seg e) (D.Γ.chainHull i j 2)
  hull_vertex : ∀ e : D.Γ.Strand, (∀ s : ℕ, s ≤ 3 → e ≠ ⟨i, j - 1 + (s : ZMod (D.Γ.comp i).k)⟩) →
    D.Γ.tail e ∉ D.Γ.chainHull i j 2
  end_clear_p : ∀ z ∈ D.Γ.seg ⟨i, j - 2⟩, z ∈ D.Γ.chainHull i j 2 → z = D.Γ.tail ⟨i, j - 1⟩
  end_clear_q : ∀ z ∈ D.Γ.seg ⟨i, j + 2⟩, z ∈ D.Γ.chainHull i j 2 → z = D.Γ.tail ⟨i, j + 2⟩
  interior_nonempty : (_root_.interior (D.Γ.chainHull i j 2)).Nonempty
  /-- the sign of the kink to create -/
  sgn : SignType
  sgn_ne : sgn ≠ 0

/-- **The polygonal kink insertion** (pattern K; the opposite direction of `SM.Curl.k2_ri`, on a
polygon instead of a smooth-carried diagram): `RIData U D Dp` with the kink of the requested sign,
and `Dp`'s record minus the kink is `D`'s record. -/
theorem exists_ri_insertion (D : Diagram) (K : KinkSite D) :
    ∃ (Dp : Diagram) (U : Set Plane) (M : RIData U D Dp),
      Dp.sign M.kink = K.sgn ∧
      Nonempty (RecordIso (Dp.record.eraseCrossing (Dp.overVisit M.kink)) D.record) := by
  sorry

/-! ## T. Pattern T — the G11 triangle move for ARBITRARY over data (Reidemeister III) -/

/-- The strict height order at a triangle configuration of `G11_Config` read off the OVER DATA of an
arbitrary diagram on the polygon, the polygon's edges named by a strand embedding `ι` (for
`Shadow.single` it is `fun a => ⟨0, a⟩`).  G11 reads the order off `crossingSign` because `M₀` is
positive; after the matched switch of row 177 the diagram is positive except at one crossing. -/
structure HeightOrder {k : ℕ} [NeZero k] (C : RProof.G11_Config k) (D : Diagram)
    (ι : ZMod k → D.Γ.Strand) : Prop where
  /-- one of the six strict orders: "the over relation on `{m, p, q}` is transitive" -/
  transitive : ∀ (a b c : ZMod k), ({a, b, c} : Finset (ZMod k)) = {C.m, C.p, C.q} →
    ∀ (xab xbc xac : D.Γ.Crossing),
      xab.val = {ι a, ι b} → xbc.val = {ι b, ι c} → xac.val = {ι a, ι c} →
      D.overStrand xab = ι a → D.overStrand xbc = ι b → D.overStrand xac = ι a

/-- **Unit T** (G11 generalised): on the positive polygon `X` of a `G11_Config` with ANY over data
having a strict height order at the triangle there are a flat subdivision `M₀` (Reparam) and a moved
diagram `M₁` with `RIII M₀ M₁`; the record of `M₁` is that of `M₀` with the three local transpositions
(G11 Unit E; stated here through `homfly` and a visit bijection as `G11_core_statement`). -/
theorem exists_riii_of_heightOrder {k : ℕ} [NeZero k] (C : RProof.G11_Config k)
    (D : Diagram) (hD : D.Γ = Shadow.single C.comp) (ι : ZMod k → D.Γ.Strand)
    (hι : ∀ a, D.Γ.tail (ι a) = C.X a) (hH : HeightOrder C D ι) :
    ∃ (M₀ M₁ : Diagram), Reparam D M₀ ∧ RIII M₀ M₁ ∧ homfly M₁ = homfly D := by
  sorry

/-! ## I. Instantiation lemmas — the consumers' interface Props by instantiation -/

section Instantiation

/-- **Row 110, bigon branch** (`s7g_switch_value_of_rii`'s `hR`, `hrec`): an empty bigon on the switched
lift gives the R-II witness and, with the consumer's record identification (U110-A's persistent visit
orders: `(D.switch x).record` minus the four visits `≅ D_L.record`), the record hypothesis. -/
theorem inst_110_bigon (D : Diagram) (x : D.Γ.Crossing) (B : BigonChain (D.switch x)) (DL : Diagram)
    (hrec : Nonempty (RecordIso
      ((D.switch x).record.eraseTwo ((D.switch x).overVisit B.x) ((D.switch x).overVisit B.y)) DL.record)) :
    ∃ Dred : Diagram, RII Dred (D.switch x) ∧ Nonempty (RecordIso Dred.record DL.record) := by
  obtain ⟨Dred, hR, ⟨ι⟩⟩ := rii_of_bigonChain (D.switch x) B
  obtain ⟨κ⟩ := hrec
  exact ⟨Dred, hR, ⟨ι.trans κ⟩⟩

/-- Row 110 with the flat subdivision absorbed: the bigon is exhibited on a planar-isotopic copy `D₂`
of `D.switch x` (the lift with `p`, `q` inserted, Unit S) and the value identity still holds. -/
theorem inst_110_bigon_subdivided (D : Diagram) (x : D.Γ.Crossing) (D₂ DL : Diagram)
    (hiso : PlanarIsotopic (D.switch x) D₂) (B : BigonChain D₂)
    (hrec : Nonempty (RecordIso (D₂.record.eraseTwo (D₂.overVisit B.x) (D₂.overVisit B.y)) DL.record)) :
    P (D.switch x) = P DL :=
  (P_planar hiso).trans (P_eq_of_bigonChain D₂ DL B hrec)

/-- **Row 110, curl (AVOIDANCE of the RI deletion on the smoothing)**: instead of deleting the curl `y`
from component 1 of `D_A` (a diagram known only through `OrientedSmoothingData`), INSERT a kink of sign
`+1` into the clean polygonal lift `D₁` of the half contact carrier (pattern K) and identify records:
`P K = P D₁` for every diagram `K` whose record is `D₁`'s record with that kink (sm-4:491-503
"delete exactly that curl … Lemma rp:record-polynomial"; `K = component₁(D_A)` = a knot restriction). -/
theorem inst_110_curl_avoidance (D₁ : Diagram) (S : KinkSite D₁) (hs : S.sgn = 1)
    (K : Diagram)
    (hK : ∀ (Dp : Diagram) (U : Set Plane) (M : RIData U D₁ Dp), Dp.sign M.kink = 1 →
      Nonempty (RecordIso (Dp.record.eraseCrossing (Dp.overVisit M.kink)) D₁.record) →
      Nonempty (RecordIso K.record Dp.record)) :
    P K = P D₁ := by
  obtain ⟨Dp, U, M, hsgn, hrec⟩ := exists_ri_insertion D₁ S
  have hRI : RI D₁ Dp := ⟨U, Or.inl ⟨M⟩⟩
  exact (presentations _ _ (hK Dp U M (hs ▸ hsgn) hrec)).trans (P_reidemeister_I hRI).symm

/-- **Row 174** (`gsc_fulltwist_triple`'s move clause, in the form the constructor can deliver): the
G10 RII deletion of the switched empty pair on the `E`-side lift.  NOTE (fidelity, DESIGN_A §5): the
RII chain must start at a planar-isotopic copy `D_H'` of `D_H.switch q` (the flat subdivision); the
interface's literal `ReflTransGen RII (D_H.switch q) D_L'` needs the outside-match variant of Unit B
(+1.5k lines) or the one-line interface edit `∃ D_H', PlanarIsotopic (D_H.switch q) D_H' ∧ …`. -/
theorem inst_174_fulltwist_move (D_H D_L : Diagram) (q : D_H.Γ.Crossing) (D_H' : Diagram)
    (hiso : PlanarIsotopic (D_H.switch q) D_H') (B : BigonChain D_H')
    (hrec : Nonempty (RecordIso (D_H'.record.eraseTwo (D_H'.overVisit B.x) (D_H'.overVisit B.y)) D_L.record)) :
    ∃ D_L' : Diagram, Relation.ReflTransGen RII D_H' D_L' ∧ homfly D_L' = homfly D_L ∧
      homfly (D_H.switch q) = homfly D_L := by
  obtain ⟨D', hR, ⟨ι⟩⟩ := rii_of_bigonChain D_H' B
  obtain ⟨κ⟩ := hrec
  refine ⟨D', Relation.ReflTransGen.single hR.symm, ?_, ?_⟩
  · rw [← P_eq_homfly, ← P_eq_homfly]; exact presentations _ _ ⟨ι.trans κ⟩
  · rw [← P_eq_homfly, ← P_eq_homfly]
    exact (P_planar hiso).trans (P_eq_of_bigonChain D_H' D_L B ⟨ι.symm.trans (ι.trans κ)⟩)

/-- **Row 176** (`est_PortData.port`, deliverable form).  The literal field
`ReflTransGen RII ((carrierDiagram q').switch y) (carrierDiagram q)` is UNREALISABLE: the two lifts live on
different polygons and an RII site agrees pointwise outside its disc (`OutsideMatch.eval_eq`), so no RII
chain crosses the wall.  Deliverable: `∃ D₀', ReflTransGen RII D₊' D₀' ∧ homfly D₀' = homfly D₀` with
`D₊'` a planar-isotopic copy of the switched lift (the 174 unit's reading of lem:fulltwist (T2)). -/
theorem inst_176_port (Dp D0 : Diagram) (y : Dp.Γ.Crossing) (Dp' : Diagram)
    (hiso : PlanarIsotopic (Dp.switch y) Dp') (B : BigonChain Dp')
    (hrec : Nonempty (RecordIso (Dp'.record.eraseTwo (Dp'.overVisit B.x) (Dp'.overVisit B.y)) D0.record)) :
    ∃ D0' : Diagram, Relation.ReflTransGen RII Dp' D0' ∧ homfly D0' = homfly D0 ∧
      homfly (Dp.switch y) = homfly D0 :=
  inst_174_fulltwist_move Dp D0 y Dp' hiso B hrec

/-- **Row 177 (6)** (`esc_rii_after_smoothing`): the two switched smoothings carry empty bigons `{y, z}`
(pattern B with `r = 2`, the smoothing arc `[s⁻, t⁺]` as the chain, on planar-isotopic copies) and their
erased records are identified through the wall (the consumer's `ExactTriangleVisitOrders` bookkeeping):
`homfly (D_H0.switch y_H) = homfly (D_L0.switch y_L)`. -/
theorem inst_177_rii_after_smoothing (D_H0 D_L0 : Diagram) (y_H : D_H0.Γ.Crossing) (y_L : D_L0.Γ.Crossing)
    (D_H' D_L' : Diagram) (hH : PlanarIsotopic (D_H0.switch y_H) D_H') (hL : PlanarIsotopic (D_L0.switch y_L) D_L')
    (BH : BigonChain D_H') (BL : BigonChain D_L')
    (hrec : Nonempty (RecordIso (D_H'.record.eraseTwo (D_H'.overVisit BH.x) (D_H'.overVisit BH.y))
      (D_L'.record.eraseTwo (D_L'.overVisit BL.x) (D_L'.overVisit BL.y)))) :
    homfly (D_H0.switch y_H) = homfly (D_L0.switch y_L) := by
  obtain ⟨DH, hRH, ⟨ιH⟩⟩ := rii_of_bigonChain D_H' BH
  obtain ⟨DL, hRL, ⟨ιL⟩⟩ := rii_of_bigonChain D_L' BL
  obtain ⟨κ⟩ := hrec
  rw [← P_eq_homfly, ← P_eq_homfly, P_planar hH, P_planar hL, ← P_reidemeister_II hRH,
    ← P_reidemeister_II hRL]
  exact presentations _ _ ⟨ιH.trans (κ.trans ιL.symm)⟩

/-- **Row 177 (4)** (`esc_switch_riii`): the matched switch makes the height order at the K3 triangle
transitive; Unit T gives `RIII M₀ M₁` from the switched `H`-lift with `homfly M₁ = homfly (D_H.switch x_H)`;
the consumer identifies `M₁`'s record with `(D_L.switch x_L).record` (G11 Unit F). -/
theorem inst_177_switch_riii {k : ℕ} [NeZero k] (C : RProof.G11_Config k) (D_H D_L : Diagram)
    (x_H : D_H.Γ.Crossing) (x_L : D_L.Γ.Crossing) (hD : (D_H.switch x_H).Γ = Shadow.single C.comp)
    (ι : ZMod k → (D_H.switch x_H).Γ.Strand) (hι : ∀ a, (D_H.switch x_H).Γ.tail (ι a) = C.X a)
    (hH : HeightOrder C (D_H.switch x_H) ι)
    (hrec : ∀ M₀ M₁ : Diagram, Reparam (D_H.switch x_H) M₀ → RIII M₀ M₁ →
      Nonempty (RecordIso M₁.record (D_L.switch x_L).record)) :
    homfly (D_H.switch x_H) = homfly (D_L.switch x_L) := by
  obtain ⟨M₀, M₁, h₀, h₁, hval⟩ := exists_riii_of_heightOrder C (D_H.switch x_H) hD ι hι hH
  rw [← hval, ← P_eq_homfly, ← P_eq_homfly]
  exact presentations _ _ (hrec M₀ M₁ h₀ h₁)

end Instantiation

end

end SM.Link
