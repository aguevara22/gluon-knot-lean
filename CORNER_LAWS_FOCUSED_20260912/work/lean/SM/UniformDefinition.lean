import SM.CarrierCornerPolygon
import SM.RotationNumber

/-! Source def:uniform (reference/SM/sm-3-statesum.tex:242, frame SM15): uniform subpolygons and
retained data. Main declaration: `SM.uniform_definition`.

Notation. `P` is a generic polygon with `n ≥ 3` vertices and `S` a finite set of its crossings; the
source speaks of decompositions (independent sets of crossings, def:decomposition,
`IsDecomposition hn hP S`), and only the clause `regular_carrier` needs that hypothesis — the other
definitions are stated for every `S`. A subpolygon (carrier) `Q` of `S` is a
component `q : Component hn hP S` of the smoothing (def:smoothing), read as its corner polygon
`ccpCornerPolygon hn hP S q : LabelledTuple (ccpCornerCount hn hP S q)` — the carrier at its
corners in inherited cyclic order (lem:carriers (ii): at least three corners, regular, its edges
positive multiples of the original edge directions). The turns of `Q` are
`turn (ccpCornerPolygon hn hP S q) j ∈ {-1, 0, +1}` (`SignType`, def:chirotope), a left turn being
`turn = 1`; `rot = rotationNumber = (Σ principal turns) / 2π` (lem:rot); the crossings of `Q` are
`carrierCrossings hn hP S q` with `m_Q = carrierCrossingCount hn hP S q` (def:smoothing);
`leftTurns` is the count `#{i : τ_i = 1}` of def:chirotope. -/

namespace SM

open Carrier

variable {n : ℕ} [NeZero n]

/-- A subpolygon `Q` is *uniform* if all its turns have one sign. -/
def CarrierUniform (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : Prop :=
  ∃ τ : SignType, τ ≠ 0 ∧ ∀ j, turn (ccpCornerPolygon hn hP S q) j = τ

/-- A subpolygon is *mixed* if it is not uniform. -/
def CarrierMixed (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : Prop :=
  ¬ CarrierUniform hn hP S q

/-- A decomposition `S` is *uniform* if all its subpolygons are. -/
def UniformDecomposition (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) : Prop :=
  ∀ q : Component hn hP S, CarrierUniform hn hP S q

/-- `r_Q = rot(Q)`, the rotation number of the subpolygon `Q`. -/
noncomputable def carrierRotation (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : ℝ :=
  rotationNumber (ccpCornerPolygon hn hP S q)

/-- `ℓ_Q`, the number of left turns of the subpolygon `Q`. -/
noncomputable def carrierLeftTurns (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : ℕ :=
  leftTurns (ccpCornerPolygon hn hP S q)

/-- def:uniform as printed on SM15, read on the carriers of def:smoothing. -/
structure UniformDefinitionData : Prop where
  /-- `Q` is uniform iff all its turns have one sign `τ ∈ {-1, +1}`. -/
  uniform : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S),
    CarrierUniform hn hP S q ↔
      ∃ τ : SignType, τ ≠ 0 ∧ ∀ j, turn (ccpCornerPolygon hn hP S q) j = τ
  /-- `Q` is mixed iff it is not uniform. -/
  mixed : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S),
    CarrierMixed hn hP S q ↔ ¬ CarrierUniform hn hP S q
  /-- `S` is uniform iff all its subpolygons are. -/
  uniform_decomposition : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Generic P) (S : Finset (Crossing P)),
    UniformDecomposition hn hP S ↔ ∀ q : Component hn hP S, CarrierUniform hn hP S q
  /-- lem:rot is applicable to every subpolygon of a decomposition (lem:carriers (ii)): the corner
  polygon has at least three vertices and is regular. -/
  regular_carrier : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)), IsDecomposition hn hP S → ∀ q : Component hn hP S,
    3 ≤ ccpCornerCount hn hP S q ∧ Regular (ccpCornerPolygon hn hP S q)
  /-- `r_Q = rot(Q) = (1/2π) Σ_i ϑ_i(Q)` over the corners of `Q`. -/
  rotation : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S),
    carrierRotation hn hP S q =
      (∑ j, principalTurn (ccpCornerPolygon hn hP S q) j) / (2 * Real.pi)
  /-- `m_Q` is the number of crossings of `Q` (def:smoothing). -/
  crossings : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S),
    carrierCrossingCount hn hP S q = (carrierCrossings hn hP S q).card
  /-- `ℓ_Q` is the number of left turns `#{j : τ_j(Q) = 1}` of `Q`. -/
  left_turns : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S),
    carrierLeftTurns hn hP S q =
      (Finset.univ.filter fun j => turn (ccpCornerPolygon hn hP S q) j = 1).card

theorem uniform_definition : UniformDefinitionData where
  uniform := fun _ _ _ _ _ _ _ => Iff.rfl
  mixed := fun _ _ _ _ _ _ _ => Iff.rfl
  uniform_decomposition := fun _ _ _ _ _ _ => Iff.rfl
  regular_carrier := fun _ _ hn _ hP _ hS q =>
    ⟨(carriers_clause_ii hn hP hS).2.2.1 q, (carriers_clause_ii hn hP hS).2.2.2.2.1 q⟩
  rotation := fun _ _ _ _ _ _ _ => rfl
  crossings := fun _ _ _ _ _ _ _ => rfl
  left_turns := fun _ _ _ _ _ _ _ => rfl

end SM
