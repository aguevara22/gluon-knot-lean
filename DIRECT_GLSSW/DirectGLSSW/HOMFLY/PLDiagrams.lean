import DirectGLSSW.AffineSegments
import DirectGLSSW.PermutationOrbits
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

/-!
# Concrete finite PL link diagrams and crossing switch

A link diagram is an actual finite straight-segment drawing in the oriented
real plane. Crossings are declared vertices with transverse through-strands;
all other vertices are bivalent. The crossing sign is derived from the actual
determinant and the chosen over-strand. This module does not define HOMFLY,
smoothing, or diagram equivalence.
-/

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

open DirectGLSSW

/-- The unique other branch of a two-strand crossing. -/
def otherBranch (i : Fin 2) : Fin 2 := ⟨1 - i.val, by omega⟩

@[simp] theorem otherBranch_zero : otherBranch 0 = 1 := by
  apply Fin.ext
  norm_num [otherBranch]

@[simp] theorem otherBranch_one : otherBranch 1 = 0 := by
  apply Fin.ext
  norm_num [otherBranch]

private theorem finTwo_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

@[simp] theorem otherBranch_involutive (i : Fin 2) : otherBranch (otherBranch i) = i := by
  apply Fin.ext
  simp only [otherBranch]
  have hi := i.isLt
  omega

def incomingArcs {nVertex nArc : ℕ} (arcTarget : Fin nArc → Fin nVertex)
    (v : Fin nVertex) : Finset (Fin nArc) :=
  Finset.univ.filter (fun e => arcTarget e = v)

def outgoingArcs {nVertex nArc : ℕ} (arcSource : Fin nArc → Fin nVertex)
    (v : Fin nVertex) : Finset (Fin nArc) :=
  Finset.univ.filter (fun e => arcSource e = v)

/-- A finite real-plane drawing of an oriented link, with crossings subdivided
at actual intersection points. The finite continuation permutation determines
its oriented components. -/
structure PLLinkDiagram where
  nVertex : ℕ
  nArc : ℕ
  nCrossing : ℕ
  vertexPoint : Fin nVertex → PlanarPoint ℝ
  arcSource : Fin nArc → Fin nVertex
  arcTarget : Fin nArc → Fin nVertex
  crossingVertex : Fin nCrossing → Fin nVertex
  crossingVertex_injective : Function.Injective crossingVertex
  incoming : Fin nCrossing → Fin 2 → Fin nArc
  outgoing : Fin nCrossing → Fin 2 → Fin nArc
  incoming_target : ∀ c i, arcTarget (incoming c i) = crossingVertex c
  outgoing_source : ∀ c i, arcSource (outgoing c i) = crossingVertex c
  four_ports_distinct : ∀ c,
    incoming c 0 ≠ incoming c 1 ∧ outgoing c 0 ≠ outgoing c 1 ∧
      (∀ i j, incoming c i ≠ outgoing c j)
  crossing_incidence_complete : ∀ c e,
    (arcSource e = crossingVertex c ∨ arcTarget e = crossingVertex c) ↔
      (e = incoming c 0 ∨ e = incoming c 1 ∨
        e = outgoing c 0 ∨ e = outgoing c 1)
  regular_degree_one : ∀ v, (∀ c, crossingVertex c ≠ v) →
    (incomingArcs arcTarget v).card = 1 ∧
      (outgoingArcs arcSource v).card = 1
  through : Fin nCrossing → Equiv.Perm (Fin 2)
  continuation : Equiv.Perm (Fin nArc)
  continuation_incidence : ∀ e,
    arcTarget e = arcSource (continuation e)
  continuation_crossing : ∀ c i,
    continuation (incoming c i) = outgoing c (through c i)
  overBranch : Fin nCrossing → Fin 2
  vertexPoint_injective : Function.Injective vertexPoint
  arc_endpoints_distinct : ∀ e, arcSource e ≠ arcTarget e
  arc_interiors_disjoint : ∀ e f, e ≠ f → ∀ s t : ℝ,
    0 < s → s < 1 → 0 < t → t < 1 →
      affinePoint (vertexPoint (arcSource e)) (vertexPoint (arcTarget e)) s ≠
        affinePoint (vertexPoint (arcSource f)) (vertexPoint (arcTarget f)) t
  vertices_avoid_arc_interiors : ∀ (v : Fin nVertex) (e : Fin nArc) (t : ℝ),
    0 < t → t < 1 →
      vertexPoint v ≠
        affinePoint (vertexPoint (arcSource e)) (vertexPoint (arcTarget e)) t
  through_tangents_positive_collinear : ∀ c i,
    ∃ scale : ℝ, 0 < scale ∧
      (vertexPoint (crossingVertex c) - vertexPoint (arcSource (incoming c i))) =
        scale • (vertexPoint (arcTarget (outgoing c (through c i))) -
          vertexPoint (crossingVertex c))
  crossing_transverse : ∀ c,
    planarDet
      (vertexPoint (crossingVertex c) - vertexPoint (arcSource (incoming c 0)))
      (vertexPoint (crossingVertex c) - vertexPoint (arcSource (incoming c 1))) ≠ 0

/-- The directed tangent at the crossing along one of its two oriented strands. -/
def strandTangent (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    PlanarPoint ℝ :=
  D.vertexPoint (D.crossingVertex c) - D.vertexPoint (D.arcSource (D.incoming c i))

/-- Over-under determinant for the selected strand pair. -/
def crossingDet (D : PLLinkDiagram) (c : Fin D.nCrossing) : ℝ :=
  planarDet (strandTangent D c (D.overBranch c))
    (strandTangent D c (otherBranch (D.overBranch c)) )

/-- The selected over/under determinant is nonzero because the two geometric
strands are transverse. -/
theorem selectedDet_ne_zero (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    crossingDet D c ≠ 0 := by
  have h := D.crossing_transverse c
  rcases finTwo_cases (D.overBranch c) with hb | hb
  · simpa only [crossingDet, strandTangent, hb, otherBranch_zero] using h
  · have hswap : planarDet (strandTangent D c 1) (strandTangent D c 0) =
        -planarDet (strandTangent D c 0) (strandTangent D c 1) :=
        planarDet_swap _ _
    simpa only [crossingDet, strandTangent, hb, otherBranch_one] using
      (hswap ▸ neg_ne_zero.mpr h)

/-- The sign convention is computed from the real tangent determinant. -/
noncomputable def crossingSign (D : PLLinkDiagram) (c : Fin D.nCrossing) : Sign :=
  nonzeroScalarSign (crossingDet D c) (selectedDet_ne_zero D c)

/-- Link components are the orbit classes of the actual strand-continuation map. -/
noncomputable def diagramComponent (D : PLLinkDiagram) :=
  PermutationOrbits.Component D.continuation

noncomputable def diagramComponentCount (D : PLLinkDiagram) : ℕ :=
  PermutationOrbits.componentCount D.continuation

/-- Switch only which geometric strand is over at a crossing. -/
def switchCrossing (D : PLLinkDiagram) (c : Fin D.nCrossing) : PLLinkDiagram :=
  { D with overBranch := Function.update D.overBranch c (otherBranch (D.overBranch c)) }

theorem switch_drawing (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    (switchCrossing D c).vertexPoint = D.vertexPoint ∧
    (switchCrossing D c).arcSource = D.arcSource ∧
    (switchCrossing D c).arcTarget = D.arcTarget ∧
    (switchCrossing D c).crossingVertex = D.crossingVertex ∧
    (switchCrossing D c).incoming = D.incoming ∧
    (switchCrossing D c).outgoing = D.outgoing ∧
    (switchCrossing D c).through = D.through ∧
    (switchCrossing D c).continuation = D.continuation := by
  simp [switchCrossing]

theorem switch_components (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    diagramComponent (switchCrossing D c) = diagramComponent D := rfl

theorem switch_componentCount (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    diagramComponentCount (switchCrossing D c) = diagramComponentCount D := rfl

theorem switchCrossing_involutive (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    switchCrossing (switchCrossing D c) c = D := by
  cases D
  simp [switchCrossing, Function.update, otherBranch_involutive]

/-- Negating the scalar negates its exact nonzero sign. -/
theorem nonzeroScalarSign_neg (x : ℝ) (hx : x ≠ 0) :
    nonzeroScalarSign (-x) (neg_ne_zero.mpr hx) =
      (nonzeroScalarSign x hx).reverse := by
  by_cases h : x < 0
  · have hp : 0 < -x := by linarith
    have hn : ¬ -x < 0 := not_lt_of_gt hp
    simp [nonzeroScalarSign, h, hp, hn, Sign.reverse]
  · have hp : 0 < x := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hx)
    have hn : -x < 0 := by linarith
    simp [nonzeroScalarSign, h, hp, hn, Sign.reverse]

theorem crossingDet_switchCrossing (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    crossingDet (switchCrossing D c) c = -crossingDet D c := by
  simp only [crossingDet, strandTangent, switchCrossing, Function.update_same,
    otherBranch_involutive]
  exact planarDet_swap _ _

theorem crossingSign_switchCrossing (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    crossingSign (switchCrossing D c) c = (crossingSign D c).reverse := by
  unfold crossingSign nonzeroScalarSign
  rw [crossingDet_switchCrossing]
  exact nonzeroScalarSign_neg (crossingDet D c) (selectedDet_ne_zero D c)

private def trianglePoint : Fin 3 → PlanarPoint ℝ
  | ⟨0, _⟩ => (0, 0)
  | ⟨1, _⟩ => (1, 0)
  | ⟨2, _⟩ => (0, 1)

private def triangleNext : Equiv.Perm (Fin 3) where
  toFun := fun i =>
    if h : i.val = 0 then 1 else if h : i.val = 1 then 2 else 0
  invFun := fun i =>
    if h : i.val = 0 then 2 else if h : i.val = 1 then 0 else 1
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

/-- A concrete crossing-free counterclockwise triangle (the unknot diagram). -/
def triangleUnknot : PLLinkDiagram where
  nVertex := 3
  nArc := 3
  nCrossing := 0
  vertexPoint := trianglePoint
  arcSource := id
  arcTarget := triangleNext
  crossingVertex := Fin.elim0
  crossingVertex_injective := by intro a; exact Fin.elim0 a
  incoming := Fin.elim0
  outgoing := Fin.elim0
  incoming_target := by intro c; exact Fin.elim0 c
  outgoing_source := by intro c; exact Fin.elim0 c
  four_ports_distinct := by intro c; exact Fin.elim0 c
  crossing_incidence_complete := by intro c; exact Fin.elim0 c
  regular_degree_one := by
    intro v hv
    fin_cases v <;> decide
  through := Fin.elim0
  continuation := triangleNext
  continuation_incidence := by intro e; rfl
  continuation_crossing := by intro c; exact Fin.elim0 c
  overBranch := Fin.elim0
  vertexPoint_injective := by
    intro a b hab
    apply Fin.ext
    have ha := congrArg Prod.fst hab
    have hb := congrArg Prod.snd hab
    fin_cases a <;> fin_cases b <;> norm_num [trianglePoint] at ha hb ⊢
  arc_endpoints_distinct := by
    intro e
    fin_cases e <;> simp [triangleNext]
  arc_interiors_disjoint := by
    intro e f hef s t hs0 hs1 ht0 ht1
    fin_cases e <;> fin_cases f <;> intro heq
    all_goals
      have hfirst := congrArg Prod.fst heq
      have hsecond := congrArg Prod.snd heq
      norm_num [trianglePoint, triangleNext, affinePoint] at hef hfirst hsecond
      <;> nlinarith
  vertices_avoid_arc_interiors := by
    intro v e t ht0 ht1 h
    fin_cases v <;> fin_cases e <;>
      (have hfirst := congrArg Prod.fst h; have hsecond := congrArg Prod.snd h;
       norm_num [trianglePoint, triangleNext, affinePoint] at hfirst hsecond <;> nlinarith)
  through_tangents_positive_collinear := by
    intro c
    exact Fin.elim0 c
  crossing_transverse := by
    intro c
    exact Fin.elim0 c

/-- The empty oriented diagram is a valid finite input; no nonemptiness is
assumed by `PLLinkDiagram`. -/
def emptyDiagram : PLLinkDiagram where
  nVertex := 0
  nArc := 0
  nCrossing := 0
  vertexPoint := Fin.elim0
  arcSource := Fin.elim0
  arcTarget := Fin.elim0
  crossingVertex := Fin.elim0
  crossingVertex_injective := by intro a; exact Fin.elim0 a
  incoming := Fin.elim0
  outgoing := Fin.elim0
  incoming_target := by intro c; exact Fin.elim0 c
  outgoing_source := by intro c; exact Fin.elim0 c
  four_ports_distinct := by intro c; exact Fin.elim0 c
  crossing_incidence_complete := by intro c; exact Fin.elim0 c
  regular_degree_one := by intro v; exact Fin.elim0 v
  through := Fin.elim0
  continuation := Equiv.refl (Fin 0)
  continuation_incidence := by intro e; exact Fin.elim0 e
  continuation_crossing := by intro c; exact Fin.elim0 c
  overBranch := Fin.elim0
  vertexPoint_injective := by intro v; exact Fin.elim0 v
  arc_endpoints_distinct := by intro e; exact Fin.elim0 e
  arc_interiors_disjoint := by intro e; exact Fin.elim0 e
  vertices_avoid_arc_interiors := by intro v; exact Fin.elim0 v
  through_tangents_positive_collinear := by intro c; exact Fin.elim0 c
  crossing_transverse := by intro c; exact Fin.elim0 c

end DirectGLSSW.HOMFLY
