import SM.RotationTheorem
import SM.Crossings
import SM.Generic
import SM.TurnLift

/-! Leaf skeleton for row 104 cb:embedded-rotation (polygonal secant / Hopf route), written
2026-09-14 by the pldiscs feasibility probe; plan in PLDISCS_FEASIBILITY.md §1.9. Every leaf is
`sorry`; the file typechecks (0 errors). `Embedded` and `IsSupportingVertex` are copied from
EmbeddedRotation_Statement.lean so that this file checks alone; a prover unit should put both
files in one module. -/

/-! Leaf skeleton for cb:embedded-rotation via the polygonal secant (Hopf) argument.
Every leaf is stated with `sorry`; the assembly `sum_principalTurn_eq_two_mul` is the key identity. -/

namespace SM

open Set

variable {n : ℕ}

/-- (Copied from EmbeddedRotation_Statement.lean.) -/
structure Embedded (P : LabelledTuple n) : Prop where
  edge_ne_zero : ∀ i, edge P i ≠ 0
  remote_disjoint : ∀ i j, remote i j → Disjoint (edgeSegment P i) (edgeSegment P j)
  consecutive : ∀ i, edgeSegment P i ∩ edgeSegment P (i + 1) = {P (i + 1)}

def IsSupportingVertex (P : LabelledTuple n) (N : Plane) (i : ZMod n) : Prop :=
  N ≠ 0 ∧ ∀ j, 0 ≤ planeDot N (P j - P i)

/-- The traversal `γ_P : ℝ → Plane`, `γ(x) = edgePoint P ⌊x⌋ (fract x)`; `n`-periodic, continuous,
`γ k = P k` at integers, `γ (k + t) = P k + t • edge P k` on `[k, k+1]`. -/
noncomputable def traversal [NeZero n] (P : LabelledTuple n) (x : ℝ) : Plane :=
  edgePoint P ((⌊x⌋ : ℤ) : ZMod n) (Int.fract x)

theorem traversal_add_nat [NeZero n] (P : LabelledTuple n) (x : ℝ) :
    traversal P (x + n) = traversal P x := by
  sorry

theorem continuous_traversal [NeZero n] (P : LabelledTuple n) : Continuous (traversal P) := by
  sorry

theorem traversal_int_add [NeZero n] (P : LabelledTuple n) (k : ℤ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : traversal P ((k : ℝ) + t) = P (k : ZMod n) + t • edge P (k : ZMod n) := by
  sorry

/-- L2: embedded ⇒ the traversal is injective modulo the period. -/
theorem Embedded.traversal_injective [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n}
    (h : Embedded P) {x y : ℝ} (hxy : traversal P x = traversal P y) :
    ∃ m : ℤ, y = x + m * n := by
  sorry

/-- L5b (sector lemma): a direction path staying in the closed positive cone of a regular pair
`(u, v)`, from the ray of `u` to the ray of `v`, has lift increment exactly `principalAngle u v`
(zero for a flat pair). -/
theorem increment_eq_principalAngle_of_cone {u v : Plane} (huv : RegularPair u v)
    {c : ℝ → Plane} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn c (Icc a b))
    (hcone : ∀ s ∈ Icc a b, ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ (α ≠ 0 ∨ β ≠ 0) ∧ c s = α • u + β • v)
    (ha : ∃ r : ℝ, 0 < r ∧ c a = r • u) (hb : ∃ r : ℝ, 0 < r ∧ c b = r • v)
    {θ : ℝ → ℝ} (hθ : IsLiftOn (fun s => normalize (c s)) θ a b) :
    θ b - θ a = principalAngle u v := by
  sorry

/-- L5c (half-plane bound): a nonvanishing path in a closed half-plane has |lift increment| ≤ π. -/
theorem abs_increment_le_pi_of_halfplane {N : Plane} (hN : N ≠ 0) {c : ℝ → Plane} {a b : ℝ}
    (hab : a ≤ b) (hc0 : ∀ s ∈ Icc a b, c s ≠ 0) (hhalf : ∀ s ∈ Icc a b, 0 ≤ planeDot N (c s))
    {θ : ℝ → ℝ} (hθ : IsLiftOn (fun s => normalize (c s)) θ a b) :
    |θ b - θ a| ≤ Real.pi := by
  sorry

/-- Negating a direction path shifts its lift by π (increments unchanged). -/
theorem IsLiftOn.neg {u : ℝ → Plane} {θ : ℝ → ℝ} {a b : ℝ} (h : IsLiftOn u θ a b) :
    IsLiftOn (fun s => -u s) (fun s => θ s + Real.pi) a b := by
  sorry

/-- Lift increment of a direction path from `r • u` to `r' • v` is `≡ arg v − arg u (mod 2π)`. -/
theorem increment_coe_angle {c : ℝ → Plane} {a b : ℝ} (hab : a ≤ b)
    (hca : c a ≠ 0) (hcb : c b ≠ 0)
    {θ : ℝ → ℝ} (hθ : IsLiftOn (fun s => normalize (c s)) θ a b) :
    ((θ b - θ a : ℝ) : Real.Angle) =
      ((planeComplex (c b)).arg : Real.Angle) - ((planeComplex (c a)).arg : Real.Angle) := by
  sorry

/-- The secant region in the `(s, t)` plane: `0 ≤ s`, `t ≤ n`, `1/2 ≤ t − s ≤ n − 1/2`
(convex; a continuous retraction of `ℝ²` onto it exists). -/
def secantRegion (n : ℕ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.2 ≤ n ∧ 1 / 2 ≤ p.2 - p.1 ∧ p.2 - p.1 ≤ n - 1 / 2}

/-- L3+L4: a global continuous angle `Θ` on `ℝ²` lifting the secant direction
`normalize (γ t − γ s)` on the secant region (retract, then `exists_lift_of_unit` on `ℝ × ℝ`). -/
theorem exists_secant_lift [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (h : Embedded P) :
    ∃ Θ : ℝ × ℝ → ℝ, Continuous Θ ∧ ∀ p ∈ secantRegion n,
      normalize (traversal P p.2 - traversal P p.1) = (Real.cos (Θ p), Real.sin (Θ p)) := by
  sorry

/-- L6+L8 (the key identity), for a polygon based at vertex `0`: with `I` the angle swept by the
secant from `P 0` along the rest of the polygon (`t ∈ [1/2, n − 1/2]`),
`Σ ϑ_i = 2 I + 2 ϑ_0`. Diagonal pieces: constant on `[k, k+1/2]`, sector `ϑ_{k+1}` on
`[k+1/2, k+1]`; cut piece: sector `ϑ_0`; top and left legs: `I` each. -/
theorem sum_principalTurn_eq_two_mul [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n}
    (h : Embedded P) (Θ : ℝ × ℝ → ℝ) (hΘc : Continuous Θ)
    (hΘ : ∀ p ∈ secantRegion n,
      normalize (traversal P p.2 - traversal P p.1) = (Real.cos (Θ p), Real.sin (Θ p))) :
    ∑ i : ZMod n, principalTurn P i =
      2 * (Θ (0, (n : ℝ) - 1 / 2) - Θ (0, 1 / 2)) + 2 * principalTurn P 0 := by
  sorry

/-- L7: the leg increment at a supporting base vertex: `|I| ≤ π` and `I ≡ π − ϑ_0 (mod 2π)`. -/
theorem leg_increment [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (h : Embedded P)
    {N : Plane} (hsupp : IsSupportingVertex P N 0) (Θ : ℝ × ℝ → ℝ) (hΘc : Continuous Θ)
    (hΘ : ∀ p ∈ secantRegion n,
      normalize (traversal P p.2 - traversal P p.1) = (Real.cos (Θ p), Real.sin (Θ p))) :
    |Θ (0, (n : ℝ) - 1 / 2) - Θ (0, 1 / 2)| ≤ Real.pi ∧
    ((Θ (0, (n : ℝ) - 1 / 2) - Θ (0, 1 / 2) : ℝ) : Real.Angle) =
      (Real.pi : Real.Angle) - (principalTurn P 0 : Real.Angle) := by
  sorry

/-- L7': the lowest-leftmost vertex is supporting (`N = (1,0)`) with nonzero turn. -/
theorem exists_supporting_vertex_turn_ne_zero [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n}
    (h : Embedded P) : ∃ (N : Plane) (i : ZMod n), IsSupportingVertex P N i ∧ principalTurn P i ≠ 0 := by
  sorry

/-- Shift-invariance of `Embedded` and of supporting vertices (to base the argument at vertex 0). -/
theorem Embedded.shift {P : LabelledTuple n} (h : Embedded P) (a : ZMod n) : Embedded (shift a P) := by
  sorry

theorem isSupportingVertex_shift (P : LabelledTuple n) (N : Plane) (i a : ZMod n) :
    IsSupportingVertex (shift a P) N i ↔ IsSupportingVertex P N (i + a) := by
  sorry

/-- Arithmetic assembly: from `Σϑ = 2I + 2ϑ_0`, `|I| ≤ π`, `I ≡ π − ϑ_0`, `|ϑ_0| < π`:
`Σϑ = ±2π`, and the sign follows the sign of `ϑ_0` when it is nonzero. -/
theorem assembly {S I t : ℝ} (hS : S = 2 * I + 2 * t) (hI : |I| ≤ Real.pi)
    (hcong : ((I : ℝ) : Real.Angle) = (Real.pi : Real.Angle) - (t : Real.Angle))
    (ht : -Real.pi < t ∧ t < Real.pi) :
    (S = 2 * Real.pi ∨ S = -(2 * Real.pi)) ∧ (0 < t → S = 2 * Real.pi) ∧
      (t < 0 → S = -(2 * Real.pi)) := by
  sorry

end SM
