import SM.RotationNumber
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Actual cyclic tuples of powers of a complex root of unity. Every edge,
including the closing edge, and every actual principal turn is computed. -/

namespace SM

def complexPlane (z : ℂ) : Plane := (z.re, z.im)

theorem planeComplex_complexPlane (z : ℂ) : planeComplex (complexPlane z) = z := rfl

theorem planeComplex_sub (u v : Plane) :
    planeComplex (u - v) = planeComplex u - planeComplex v := rfl

variable {n : ℕ} [NeZero n]

noncomputable def cyclicComplexSeed (q : ℂ) : LabelledTuple n :=
  fun i => complexPlane (q ^ i.val)

theorem cyclicPower_succ (hn : 1 < n) {q : ℂ} (hq : q ^ n = 1) (i : ZMod n) :
    q ^ (i + 1).val = q ^ i.val * q := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hn,
    ← pow_eq_pow_mod (i.val + 1) hq, pow_succ]

theorem cyclicComplexSeed_edge (hn : 1 < n) {q : ℂ} (hq : q ^ n = 1) (i : ZMod n) :
    planeComplex (edge (cyclicComplexSeed (n := n) q) i) = q ^ i.val * (q - 1) := by
  simp only [edge, planeComplex_sub, cyclicComplexSeed, planeComplex_complexPlane]
  rw [cyclicPower_succ hn hq]
  ring

theorem cyclicComplexSeed_edge_ne_zero (hn : 1 < n) {q : ℂ}
    (hq : q ^ n = 1) (hq0 : q ≠ 0) (hq1 : q ≠ 1) (i : ZMod n) :
    edge (cyclicComplexSeed (n := n) q) i ≠ 0 := by
  intro he
  have hz := cyclicComplexSeed_edge hn hq i
  rw [he, planeComplex_zero] at hz
  exact mul_ne_zero (pow_ne_zero _ hq0) (sub_ne_zero.mpr hq1) hz.symm

theorem cyclicComplexSeed_edge_step (hn : 1 < n) {q : ℂ} (hq : q ^ n = 1)
    (i : ZMod n) :
    planeComplex (edge (cyclicComplexSeed (n := n) q) i) =
      q * planeComplex (edge (cyclicComplexSeed (n := n) q) (i - 1)) := by
  have hs := cyclicPower_succ hn hq (i - 1)
  simp only [sub_add_cancel] at hs
  rw [cyclicComplexSeed_edge hn hq, cyclicComplexSeed_edge hn hq, hs]
  ring

theorem principalAngle_of_complex_step {u v : Plane} {q : ℂ}
    (hu : u ≠ 0) (hv : planeComplex v = q * planeComplex u) :
    principalAngle u v = q.arg := by
  have hn : 0 < Complex.normSq (planeComplex u) :=
    Complex.normSq_pos.mpr (planeComplex_ne_zero hu)
  have hc : cornerRotor u v = (Complex.normSq (planeComplex u) : ℂ) * q := by
    rw [cornerRotor, hv, Complex.normSq_eq_conj_mul_self]
    change star (planeComplex u) * (q * planeComplex u) =
      (star (planeComplex u) * planeComplex u) * q
    ring
  rw [principalAngle, hc, Complex.arg_real_mul _ hn]

theorem cyclicComplexSeed_principalTurn (hn : 1 < n) {q : ℂ}
    (hq : q ^ n = 1) (hq0 : q ≠ 0) (hq1 : q ≠ 1) (i : ZMod n) :
    principalTurn (cyclicComplexSeed (n := n) q) i = q.arg :=
  principalAngle_of_complex_step (cyclicComplexSeed_edge_ne_zero hn hq hq0 hq1 _)
    (cyclicComplexSeed_edge_step hn hq i)

theorem cyclicComplexSeed_regular (hn : 1 < n) {q : ℂ}
    (hq : q ^ n = 1) (hq0 : q ≠ 0) (hq1 : q ≠ 1) (ha : q.arg ≠ Real.pi) :
    Regular (cyclicComplexSeed (n := n) q) := by
  intro i
  have hu := cyclicComplexSeed_edge_ne_zero hn hq hq0 hq1 (i - 1)
  have hv := cyclicComplexSeed_edge_ne_zero hn hq hq0 hq1 i
  apply (regularPair_iff_slitPlane _ _).mpr
  refine ⟨hu, hv, Complex.mem_slitPlane_iff_arg.mpr ⟨?_, cornerRotor_ne_zero hu hv⟩⟩
  change principalTurn (cyclicComplexSeed q) i ≠ Real.pi
  rw [cyclicComplexSeed_principalTurn hn hq hq0 hq1]
  exact ha

theorem cyclicComplexSeed_rotation (hn : 1 < n) {q : ℂ}
    (hq : q ^ n = 1) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    rotationNumber (cyclicComplexSeed (n := n) q) = (n : ℝ) * q.arg / (2 * Real.pi) := by
  unfold rotationNumber
  simp_rw [cyclicComplexSeed_principalTurn hn hq hq0 hq1]
  simp

end SM
