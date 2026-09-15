import SM.SoftRotation

/-! Source lem:soft-rotation (reference/SM/sm-5-transport.tex:317, frame SM15): rotation of a
soft insertion. Main declaration: `SM.soft_rotation_law`. Notation (def:soft, lem:soft-generic):
`softInsertion P j q ε = P_ε`, `softAttachmentMinus/Plus = χ_-, χ_+`, `turn P j = τ_j(P)`,
`rotationNumber = rot`; the sectors are same-sign (`χ_- = χ_+ = -τ_j`), mixed (`χ_- ≠ χ_+`) and
loop (`χ_- = χ_+ = τ_j`); "ε small (lem:soft-generic)" is `∃ ε₀ > 0, ∀ 0 < ε < ε₀` (with `P_ε`
generic there); `edge P (j-1) = ℓ_{j-1}`, `edge P j = ℓ_j`; `openCone u v = {a • u + b • v | a, b > 0}`
is the open cone of directions strictly between `u` and `v`. Proof: SM.SoftRotation (prover
subagent, ported verbatim). -/

namespace SM

variable {n : ℕ} [NeZero n]

/-- lem:soft-rotation as printed on SM15. -/
theorem soft_rotation_law (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    (∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Generic (softInsertion P j q ε) ∧
      (((softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) ∨
          softAttachmentMinus P j q ≠ softAttachmentPlus P j q) →
        rotationNumber (softInsertion P j q ε) = rotationNumber P) ∧
      ((softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) →
        rotationNumber (softInsertion P j q ε) = rotationNumber P - (turn P j : ℝ))) ∧
    ((softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) ↔
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ q = a • edge P (j - 1) + b • edge P j) ∧
    ((softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) ↔
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ q = a • (-edge P (j - 1)) + b • (-edge P j)) ∧
    (softAttachmentMinus P j q ≠ softAttachmentPlus P j q ↔
      q ∉ closure (openCone (edge P (j - 1)) (edge P j)) ∧
      q ∉ closure (openCone (-edge P (j - 1)) (-edge P j))) :=
  soft_rotation hn hP j q hq

end SM
