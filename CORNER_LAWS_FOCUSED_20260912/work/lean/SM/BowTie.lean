import SM.ZeroRotationSeed
import SM.Crossings

/-! Towards def:star (K_0) and lem:star-generic (iv) (sm-5-transport.tex:5, 16). Written 2026-09-13 by a Claude Code prover subagent of the pod
executor (workflow prove-transport-lane / prove:bowtie), checked with `lake env lean` (placeholder-free, standard axioms) and
ported verbatim from work/drafts/BowTie.lean (only this header added and #print lines removed). -/

/-! SM def:star (the bow-tie `K₀`) and lem:star-generic clause (iv).

`K₀ = ((0,0),(2,2),(0,2),(2,0))` with source labels `1,2,3,4`; in `ZMod 4` the
label `4` is `0`.  Everything is a finite computation on rational coordinates. -/

namespace SM

/-- The bow-tie of SM def:star, with the source labels `1,2,3,4 ≡ 0`. -/
def bowTie : LabelledTuple 4 := fun i =>
  if i = 1 then (0, 0) else if i = 2 then (2, 2) else if i = 3 then (0, 2) else (2, 0)

theorem bowTie_apply_one : bowTie 1 = (0, 0) := rfl
theorem bowTie_apply_two : bowTie 2 = (2, 2) := by simp +decide [bowTie]
theorem bowTie_apply_three : bowTie 3 = (0, 2) := by simp +decide [bowTie]
theorem bowTie_apply_zero : bowTie 0 = (2, 0) := by simp +decide [bowTie]

/-- `bowtieSeed` (labels `0,1,2,3`) is the bow-tie relabelled by one step. -/
theorem bowTie_eq_shift : bowTie = shift 3 bowtieSeed := by
  funext i
  fin_cases i <;> simp +decide [bowTie, bowtieSeed, shift, ZMod]

/-! ### Genericity -/

/-- (G1): the four determinants `4, -4, -4, 4` (and their permutations) are nonzero. -/
theorem bowTie_G1 : G1 bowTie := by
  intro i j k hij hjk hik
  rw [chi, sign_ne_zero]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp +decide [bowTie, det, ZMod] at hij hjk hik ⊢

/-- (G2): `E₁ = [(0,0),(2,2)]` and `E₃ = [(0,2),(2,0)]` meet only at `(1,1)`, while
`E₂` and `E₄` are disjoint parallel segments; no point lies in three edge interiors. -/
theorem bowTie_G2 : G2 bowTie := by
  rintro ⟨i, j, k, x, hij, hjk, hik, ⟨t, ht0, ht1, rfl⟩, ⟨s, hs0, hs1, hs⟩, ⟨u, hu0, hu1, hu⟩⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp +decide [edgePoint, edge, bowTie, ZMod, Prod.ext_iff] at hij hjk hik hs hu <;> linarith

theorem bowTie_generic : Generic bowTie := ⟨bowTie_G1, bowTie_G2⟩

/-! ### Chirotope values `(χ₁₂₃, χ₁₂₄, χ₁₃₄, χ₂₃₄) = (+1, -1, -1, +1)` -/

theorem bowTie_chi_123 : chi bowTie 1 2 3 = 1 := by
  rw [chi, sign_eq_one_iff]
  simp +decide [bowTie, det]

theorem bowTie_chi_124 : chi bowTie 1 2 0 = -1 := by
  rw [chi, sign_eq_neg_one_iff]
  simp +decide [bowTie, det]

theorem bowTie_chi_134 : chi bowTie 1 3 0 = -1 := by
  rw [chi, sign_eq_neg_one_iff]
  simp +decide [bowTie, det]

theorem bowTie_chi_234 : chi bowTie 2 3 0 = 1 := by
  rw [chi, sign_eq_one_iff]
  simp +decide [bowTie, det]

theorem bowTie_chirotope :
    (chi bowTie 1 2 3, chi bowTie 1 2 0, chi bowTie 1 3 0, chi bowTie 2 3 0) =
      (1, -1, -1, 1) := by
  rw [bowTie_chi_123, bowTie_chi_124, bowTie_chi_134, bowTie_chi_234]

/-! ### Turns `(τ₁, τ₂, τ₃, τ₄) = (-1, +1, +1, -1)` -/

theorem bowTie_turn_one : turn bowTie 1 = -1 := by
  rw [turn, chi, sign_eq_neg_one_iff]
  simp +decide [bowTie, det]

theorem bowTie_turn_two : turn bowTie 2 = 1 := by
  rw [turn, chi, sign_eq_one_iff]
  simp +decide [bowTie, det]

theorem bowTie_turn_three : turn bowTie 3 = 1 := by
  rw [turn, chi, sign_eq_one_iff]
  simp +decide [bowTie, det]

theorem bowTie_turn_zero : turn bowTie 0 = -1 := by
  rw [turn, chi, sign_eq_neg_one_iff]
  simp +decide [bowTie, det]

theorem bowTie_turns :
    (turn bowTie 1, turn bowTie 2, turn bowTie 3, turn bowTie 0) = (-1, 1, 1, -1) := by
  rw [bowTie_turn_one, bowTie_turn_two, bowTie_turn_three, bowTie_turn_zero]

/-! ### Rotation number -/

theorem bowTie_regular : Regular bowTie := by
  rw [bowTie_eq_shift]
  exact regular_shift_forward 3 bowtieSeed_regular

theorem bowTie_rotation : rotationNumber bowTie = 0 := by
  rw [bowTie_eq_shift, rotationNumber_shift, bowtieSeed_rotation]

/-! ### The crossing set `X(K₀) = {{1,3}}` -/

theorem bowTie_remote_13 : remote (1 : ZMod 4) 3 := by
  unfold remote adjacent
  decide

theorem bowTie_remote_02 : remote (0 : ZMod 4) 2 := by
  unfold remote adjacent
  decide

/-- `E₁` and `E₃` meet at `(1,1)`, the midpoint of both. -/
theorem bowTie_edgePoint_one_half : edgePoint bowTie 1 (1 / 2) = (1, 1) := by
  simp +decide [edgePoint, edge, bowTie]

theorem bowTie_edgePoint_three_half : edgePoint bowTie 3 (1 / 2) = (1, 1) := by
  simp +decide [edgePoint, edge, bowTie]
  norm_num

theorem bowTie_isCrossing_13 : IsCrossing bowTie {1, 3} := by
  refine ⟨1, 3, rfl, bowTie_remote_13, (1, 1), ⟨1 / 2, by norm_num, by norm_num, ?_⟩,
    ⟨1 / 2, by norm_num, by norm_num, ?_⟩⟩
  · exact bowTie_edgePoint_one_half.symm
  · exact bowTie_edgePoint_three_half.symm

/-- `E₄ = [(2,0),(0,0)]` and `E₂ = [(2,2),(0,2)]` are disjoint parallel segments. -/
theorem bowTie_not_isCrossing_02 : ¬ IsCrossing bowTie {0, 2} := by
  rintro ⟨i, j, hs, hr, x, ⟨t, ht0, ht1, rfl⟩, ⟨u, hu0, hu1, hu⟩⟩
  fin_cases i <;> fin_cases j <;>
    simp +decide [remote, adjacent] at hr hs <;>
    simp +decide [edgePoint, edge, bowTie, ZMod, Prod.ext_iff] at hu

theorem bowTie_crossingSet : crossingSet bowTie = {{1, 3}} := by
  ext s
  rw [mem_crossingSet, Finset.mem_singleton]
  constructor
  · rintro ⟨i, j, rfl, hr, x, ⟨t, ht0, ht1, rfl⟩, ⟨u, hu0, hu1, hu⟩⟩
    fin_cases i <;> fin_cases j <;>
      simp +decide [remote, adjacent] at hr <;>
      simp +decide [edgePoint, edge, bowTie, ZMod, Prod.ext_iff] at hu <;>
      decide
  · rintro rfl
    exact bowTie_isCrossing_13

/-! ### The crossing test (lem:crossing-test) read on the bow-tie -/

/-- Both chirotope products of lem:crossing-test equal `-1` for the remote pair `{1,3}`. -/
theorem bowTie_crossing_test_13 :
    chi bowTie 1 (1 + 1) 3 * chi bowTie 1 (1 + 1) (3 + 1) = -1 ∧
    chi bowTie 3 (3 + 1) 1 * chi bowTie 3 (3 + 1) (1 + 1) = -1 := by
  have h1 : chi bowTie 1 (1 + 1) 3 = 1 := by
    rw [chi, sign_eq_one_iff]; simp +decide [bowTie, det]
  have h2 : chi bowTie 1 (1 + 1) (3 + 1) = -1 := by
    rw [chi, sign_eq_neg_one_iff]; simp +decide [bowTie, det]
  have h3 : chi bowTie 3 (3 + 1) 1 = -1 := by
    rw [chi, sign_eq_neg_one_iff]; simp +decide [bowTie, det]
  have h4 : chi bowTie 3 (3 + 1) (1 + 1) = 1 := by
    rw [chi, sign_eq_one_iff]; simp +decide [bowTie, det]
  rw [h1, h2, h3, h4]
  decide

/-- The first chirotope product of lem:crossing-test is `+1` for the remote pair `{0,2}`
(`E₄` and `E₂` are parallel; `μ₃, μ₄` lie on the same side of the line of `E₄`). -/
theorem bowTie_crossing_test_02 :
    chi bowTie 0 (0 + 1) 2 * chi bowTie 0 (0 + 1) (2 + 1) = 1 := by
  have h1 : chi bowTie 0 (0 + 1) 2 = -1 := by
    rw [chi, sign_eq_neg_one_iff]; simp +decide [bowTie, det]
  have h2 : chi bowTie 0 (0 + 1) (2 + 1) = -1 := by
    rw [chi, sign_eq_neg_one_iff]; simp +decide [bowTie, det]
  rw [h1, h2]
  decide

/-- `{1,3} ∈ X(K₀)` derived from `crossing_test` rather than from the explicit point. -/
theorem bowTie_isCrossing_13' : IsCrossing bowTie {1, 3} :=
  ((crossing_test (by norm_num) bowTie bowTie_G1).1 1 3 bowTie_remote_13).mpr
    bowTie_crossing_test_13

/-- `{0,2} ∉ X(K₀)` derived from `crossing_test`. -/
theorem bowTie_not_isCrossing_02' : ¬ IsCrossing bowTie {0, 2} := by
  intro h
  have h' := ((crossing_test (by norm_num) bowTie bowTie_G1).1 0 2 bowTie_remote_02).mp h
  rw [bowTie_crossing_test_02] at h'
  exact absurd h'.1 (by decide)

/-! ### Principal turns `-3π/4, 3π/4, 3π/4, -3π/4` (the last sentence of the proof of (iv))

The arguments are pinned down through `tan` on `(-π/2, π/2)` after a shift by `π`, so no
square roots appear. -/

theorem arg_eq_three_pi_div_four {x : ℂ} (hre : x.re < 0) (him : 0 < x.im)
    (h : x.im = -x.re) : x.arg = 3 * Real.pi / 4 := by
  have htan : Real.tan x.arg = -1 := by
    rw [Complex.tan_arg, h, neg_div, div_self hre.ne]
  have h1 : Real.pi / 2 < x.arg := by
    have : ¬ (x.arg ≤ Real.pi / 2) := by
      rw [Complex.arg_le_pi_div_two_iff, not_or, not_le, not_lt]
      exact ⟨hre, him.le⟩
    exact lt_of_not_ge this
  have h2 : x.arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr him.ne')
  have htan' : Real.tan (x.arg - Real.pi) = Real.tan (-(Real.pi / 4)) := by
    rw [Real.tan_sub_pi, htan, Real.tan_neg, Real.tan_pi_div_four]
  have := Real.tan_inj_of_lt_of_lt_pi_div_two (by linarith) (by linarith)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) htan'
  linarith

theorem arg_eq_neg_three_pi_div_four {x : ℂ} (hre : x.re < 0) (him : x.im < 0)
    (h : x.im = x.re) : x.arg = -(3 * Real.pi / 4) := by
  have htan : Real.tan x.arg = 1 := by
    rw [Complex.tan_arg, h, div_self hre.ne]
  have h1 : x.arg < -(Real.pi / 2) := by
    have : ¬ (-(Real.pi / 2) ≤ x.arg) := by
      rw [Complex.neg_pi_div_two_le_arg_iff, not_or, not_le, not_le]
      exact ⟨hre, him⟩
    exact lt_of_not_ge this
  have h2 : -Real.pi < x.arg := Complex.neg_pi_lt_arg x
  have htan' : Real.tan (x.arg + Real.pi) = Real.tan (Real.pi / 4) := by
    rw [Real.tan_periodic x.arg, htan, Real.tan_pi_div_four]
  have := Real.tan_inj_of_lt_of_lt_pi_div_two (by linarith) (by linarith)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) htan'
  linarith

theorem bowTie_principalTurn_one : principalTurn bowTie 1 = -(3 * Real.pi / 4) := by
  have hre : (cornerRotor (edge bowTie 0) (edge bowTie 1)).re = -4 := by
    rw [cornerRotor_re]; simp +decide [planeDot, edge, bowTie]; norm_num
  have him : (cornerRotor (edge bowTie 0) (edge bowTie 1)).im = -4 := by
    rw [cornerRotor_im]; simp +decide [det, edge, bowTie]; norm_num
  have h : principalTurn bowTie 1 = (cornerRotor (edge bowTie 0) (edge bowTie 1)).arg := rfl
  rw [h]
  exact arg_eq_neg_three_pi_div_four (by rw [hre]; norm_num) (by rw [him]; norm_num)
    (by rw [hre, him])

theorem bowTie_principalTurn_two : principalTurn bowTie 2 = 3 * Real.pi / 4 := by
  have hre : (cornerRotor (edge bowTie 1) (edge bowTie 2)).re = -4 := by
    rw [cornerRotor_re]; simp +decide [planeDot, edge, bowTie]; norm_num
  have him : (cornerRotor (edge bowTie 1) (edge bowTie 2)).im = 4 := by
    rw [cornerRotor_im]; simp +decide [det, edge, bowTie]; norm_num
  have h : principalTurn bowTie 2 = (cornerRotor (edge bowTie 1) (edge bowTie 2)).arg := rfl
  rw [h]
  exact arg_eq_three_pi_div_four (by rw [hre]; norm_num) (by rw [him]; norm_num)
    (by rw [hre, him]; norm_num)

theorem bowTie_principalTurn_three : principalTurn bowTie 3 = 3 * Real.pi / 4 := by
  have hre : (cornerRotor (edge bowTie 2) (edge bowTie 3)).re = -4 := by
    rw [cornerRotor_re]; simp +decide [planeDot, edge, bowTie]; norm_num
  have him : (cornerRotor (edge bowTie 2) (edge bowTie 3)).im = 4 := by
    rw [cornerRotor_im]; simp +decide [det, edge, bowTie]; norm_num
  have h : principalTurn bowTie 3 = (cornerRotor (edge bowTie 2) (edge bowTie 3)).arg := rfl
  rw [h]
  exact arg_eq_three_pi_div_four (by rw [hre]; norm_num) (by rw [him]; norm_num)
    (by rw [hre, him]; norm_num)

theorem bowTie_principalTurn_zero : principalTurn bowTie 0 = -(3 * Real.pi / 4) := by
  have hre : (cornerRotor (edge bowTie 3) (edge bowTie 0)).re = -4 := by
    rw [cornerRotor_re]; simp +decide [planeDot, edge, bowTie]; norm_num
  have him : (cornerRotor (edge bowTie 3) (edge bowTie 0)).im = -4 := by
    rw [cornerRotor_im]; simp +decide [det, edge, bowTie]; norm_num
  have h : principalTurn bowTie 0 = (cornerRotor (edge bowTie 3) (edge bowTie 0)).arg := rfl
  rw [h]
  exact arg_eq_neg_three_pi_div_four (by rw [hre]; norm_num) (by rw [him]; norm_num)
    (by rw [hre, him])

theorem bowTie_principalTurns :
    (principalTurn bowTie 1, principalTurn bowTie 2, principalTurn bowTie 3,
      principalTurn bowTie 0) =
    (-(3 * Real.pi / 4), 3 * Real.pi / 4, 3 * Real.pi / 4, -(3 * Real.pi / 4)) := by
  rw [bowTie_principalTurn_one, bowTie_principalTurn_two, bowTie_principalTurn_three,
    bowTie_principalTurn_zero]

/-- The four principal turns sum to `0`: a direct proof of `rot(K₀) = 0`. -/
theorem bowTie_sum_principalTurn : (∑ i : ZMod 4, principalTurn bowTie i) = 0 := by
  rw [sum_zmod_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    zero_add]
  norm_num only
  rw [bowTie_principalTurn_zero, bowTie_principalTurn_one, bowTie_principalTurn_two,
    bowTie_principalTurn_three]
  ring

theorem bowTie_rotation' : rotationNumber bowTie = 0 := by
  unfold rotationNumber
  rw [bowTie_sum_principalTurn, zero_div]

/-! ### lem:star-generic (iv), assembled -/

/-- SM lem:star-generic (iv): `K₀` is generic, with
`(χ₁₂₃, χ₁₂₄, χ₁₃₄, χ₂₃₄) = (+1, -1, -1, +1)`, turns `(τ₁, τ₂, τ₃, τ₄) = (-1, +1, +1, -1)`,
`rot(K₀) = 0` and `X(K₀) = {{1,3}}`.  (Label `4` is `0 : ZMod 4`.) -/
theorem star_generic_iv :
    Generic bowTie ∧
    (chi bowTie 1 2 3, chi bowTie 1 2 0, chi bowTie 1 3 0, chi bowTie 2 3 0) =
      (1, -1, -1, 1) ∧
    (turn bowTie 1, turn bowTie 2, turn bowTie 3, turn bowTie 0) = (-1, 1, 1, -1) ∧
    rotationNumber bowTie = 0 ∧
    crossingSet bowTie = {{1, 3}} :=
  ⟨bowTie_generic, bowTie_chirotope, bowTie_turns, bowTie_rotation, bowTie_crossingSet⟩

/-- The same statement with the source's label `4` written literally; `(4 : ZMod 4) = 0`. -/
theorem star_generic_iv_printed :
    Generic bowTie ∧
    (chi bowTie 1 2 3, chi bowTie 1 2 4, chi bowTie 1 3 4, chi bowTie 2 3 4) =
      (1, -1, -1, 1) ∧
    (turn bowTie 1, turn bowTie 2, turn bowTie 3, turn bowTie 4) = (-1, 1, 1, -1) ∧
    rotationNumber bowTie = 0 ∧
    crossingSet bowTie = {{1, 3}} := by
  have h4 : (4 : ZMod 4) = 0 := by decide
  rw [h4]
  exact star_generic_iv

end SM
