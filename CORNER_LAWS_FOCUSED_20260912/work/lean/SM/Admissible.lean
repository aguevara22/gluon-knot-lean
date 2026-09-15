import SM.RotationNumber
import SM.CyclicChambers

/-! Source def:admissible, including the genuine rotation fibre in the actual
cyclic quotient of the generic locus. Integer parameters retain their exact
source domain; a tuple's vertex count is naturally a nonnegative integer. -/

namespace SM

def Admissible (n r : ℤ) : Prop :=
  3 ≤ n ∧ 2 * |r| < n ∧ (n, r) ≠ (3, 0)

def MinimalAdmissible (n r : ℤ) : Prop :=
  Admissible n r ∧ ((r ≠ 0 ∧ n = 2 * |r| + 1) ∨ (n, r) = (4, 0))

variable {n : ℕ} [NeZero n]

noncomputable def genericPolygonRotation : GenericPolygon n → ℝ :=
  Quotient.lift (fun P : GenericTuple n => rotationNumber P.val) (by
    intro P Q h
    obtain ⟨a, ha⟩ := h
    change Q.val = shift a P.val at ha
    rw [ha, rotationNumber_shift])

theorem genericPolygonRotation_projection (P : GenericTuple n) :
    genericPolygonRotation (polygonProjection P) = rotationNumber P.val := rfl

def genericFibre (r : ℤ) : Set (GenericPolygon n) :=
  {Q | genericPolygonRotation Q = (r : ℝ)}

theorem genericFibre_projection (r : ℤ) (P : GenericTuple n) :
    polygonProjection P ∈ genericFibre r ↔ rotationNumber P.val = (r : ℝ) := Iff.rfl

theorem genericFibre_shift (r : ℤ) (P : GenericTuple n) (a : ZMod n) :
    polygonProjection (genericShift a P) ∈ genericFibre r ↔
      polygonProjection P ∈ genericFibre r := by
  rw [projection_genericShift]

/-- All integer parameter clauses and the exact fibre on the source's
nondegenerate vertex-count domain. No existence or density is asserted. -/
theorem admissible_definition (hn : 3 ≤ n) (r : ℤ) :
    (∀ m s : ℤ, Admissible m s ↔ 3 ≤ m ∧ 2 * |s| < m ∧ (m, s) ≠ (3, 0)) ∧
    (∀ m s : ℤ, MinimalAdmissible m s ↔
      Admissible m s ∧ ((s ≠ 0 ∧ m = 2 * |s| + 1) ∨ (m, s) = (4, 0))) ∧
    (∀ Q : GenericPolygon n, Q ∈ genericFibre r ↔ genericPolygonRotation Q = (r : ℝ)) ∧
    (∀ P : GenericTuple n,
      polygonProjection P ∈ genericFibre r ↔ rotationNumber P.val = (r : ℝ)) ∧
    (∀ P : GenericTuple n, ∀ a : ZMod n,
      polygonProjection (genericShift a P) ∈ genericFibre r ↔
        polygonProjection P ∈ genericFibre r) :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl,
    genericFibre_projection r, genericFibre_shift r⟩

end SM
