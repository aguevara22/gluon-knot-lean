import SM.RotationTheorem
import SM.Crossings
import SM.Generic
import SM.TurnLift

/-! Statement draft for row 104 cb:embedded-rotation, written 2026-09-14 by the pldiscs
feasibility probe (work/drafts/pldiscs/PLDISCS_FEASIBILITY.md §1). Typechecked with
`cd work/lean && lake env lean` (copy to /tmp): 0 errors, 3 `sorry` warnings (the row theorem and
the two bridge lemmas). Not a module of work/lean; nothing here is mapped. -/

/-! # cb:embedded-rotation (row 104) — statement draft
Source: reference/SM/sm-3-statesum.tex:4760-4764 (proof 4765-4800).
"Every embedded regular polygon has rotation +1 or −1, according to its traversal
orientation around the bounded complementary region." -/

namespace SM

open Set

variable {n : ℕ}

/-- **Embedded polygon** (sm-3:4762 "embedded"): the closed polygonal curve is simple. Rendered on
def:polygon's own vocabulary: every edge is nonzero, remote edge segments are disjoint, and two
consecutive edge segments meet exactly in their common vertex. Flat vertices (zero principal
turn, sm-3:4791 "including zero at a straight subdivision") are allowed. -/
structure Embedded (P : LabelledTuple n) : Prop where
  edge_ne_zero : ∀ i, edge P i ≠ 0
  remote_disjoint : ∀ i j, remote i j → Disjoint (edgeSegment P i) (edgeSegment P j)
  consecutive : ∀ i, edgeSegment P i ∩ edgeSegment P (i + 1) = {P (i + 1)}

/-- Vertex `i` is a supporting (convex-hull) vertex of `P` in direction `N`: the whole polygon
lies in the closed half-plane `{x | ⟪N, x − P i⟫ ≥ 0}`. At such a vertex the bounded complementary
region lies on the side of the polygon, so "traversal orientation around the bounded region" is
read there: left turn = bounded region on the left. -/
def IsSupportingVertex (P : LabelledTuple n) (N : Plane) (i : ZMod n) : Prop :=
  N ≠ 0 ∧ ∀ j, 0 ≤ planeDot N (P j - P i)

/-- Row 104, one field per printed clause (sm-3:4762-4764). -/
structure EmbeddedRotationData [NeZero n] (P : LabelledTuple n) : Prop where
  /-- "has rotation +1 or −1" -/
  pm_one : rotationNumber P = 1 ∨ rotationNumber P = -1
  /-- "according to its traversal orientation around the bounded complementary region":
  at every supporting vertex a left turn (bounded region on the left) forces `+1`, a right
  turn forces `−1`. -/
  orientation : ∀ (N : Plane) (i : ZMod n), IsSupportingVertex P N i →
    (0 < principalTurn P i → rotationNumber P = 1) ∧
    (principalTurn P i < 0 → rotationNumber P = -1)
  /-- non-vacuity of the orientation clause: an embedded polygon has a supporting vertex with a
  nonzero turn (the lowest-leftmost vertex), so the sign is determined. -/
  exists_supporting : ∃ (N : Plane) (i : ZMod n), IsSupportingVertex P N i ∧ principalTurn P i ≠ 0

/-- **cb:embedded-rotation** (sm-3:4760-4764). -/
theorem cb_embedded_rotation [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hreg : Regular P) (hemb : Embedded P) : EmbeddedRotationData P := by
  sorry

/-! ## Bridges (consumers) -/

/-- A generic polygon without crossings is embedded (lem:g1 (iv) for the consecutive clause;
`IsEmpty (Crossing P)` for the remote clause). This is the form used by lem:corner-values (i)
(`m_Q = 0`, sm-3:4803). -/
theorem embedded_of_generic_of_isEmpty_crossing [NeZero n] [Nontrivial (ZMod n)] (hn : 3 ≤ n)
    {P : LabelledTuple n} (hg : Generic P) (hc : IsEmpty (Crossing P)) : Embedded P := by
  sorry

/-- Embedded polygons are regular (a doubled-back consecutive pair would overlap). -/
theorem Embedded.regular (hn : 3 ≤ n) {P : LabelledTuple n} (h : Embedded P) : Regular P := by
  sorry

end SM
