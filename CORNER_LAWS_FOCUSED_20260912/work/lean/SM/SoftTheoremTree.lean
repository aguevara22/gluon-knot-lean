import SM.SoftAmplitudeSource

/-! Source thm:A-soft (reference/SM/sm-2-amplitude.tex:1157, frame SM15): the soft theorem for the
tree coefficient `A_g`. Main declaration: `SM.SoftDuplication.soft_theorem_treeCoefficient`.

Notation. `P` generic, `q` admissible (`SoftAdmissible`), `softInsertion P j q ε = P_ε` (def:soft,
`SM.softInsertion_definition`); the soft edge is the edge `softOldIndex j j`; every other root `a`
of `P_ε` corresponds to exactly one root `g` of `P` through `softParentEdge j g` (the unchanged
edge `softOldIndex j g` for `g ≠ j`, and the return edge `softNewIndex j` for `g = j`, i.e. the
return edge corresponds to `E_j`); `softAmplitudeMultiplier P j q = (χ_- + χ_+)/2 ∈ ℚ` with
`χ_± = softAttachmentMinus/Plus P j q`; `turn P j = τ_j(P)`; `treeCoefficient = A_g`. The
parameter `ε0 > 0` is any positive bound, in particular the `ε₀` of lem:soft-generic; the theorem
supplies one `ε₁ ∈ (0, ε0]` for all roots at once. The proof is the previous executor's
kernel-checked candidate lane (prototype SoftAmplitudeSource), ported verbatim. -/

namespace SM.SoftDuplication

noncomputable section
variable {n : ℕ} [NeZero n]

/-- thm:A-soft (soft theorem for `A_g`), as printed on SM15: for `P` generic and `q` admissible
and every `ε0 > 0`, there is `ε₁ ∈ (0, ε0]` such that for `0 < ε < ε₁` the polygon `P_ε` is
generic and, for every root `a` of `P_ε` other than the soft edge, with `g` the unique
corresponding root of `P` (the return edge corresponding to `E_j`),
`A_a(P_ε) = ((χ_- + χ_+)/2) · A_g(P)`; equivalently the multiplier is `-τ_j(P)` in the same-sign
sector (`χ_- = χ_+ = -τ_j`), `0` in the mixed sector (`χ_- ≠ χ_+`) and `τ_j(P)` in the loop sector
(`χ_- = χ_+ = τ_j`). -/
theorem soft_theorem_treeCoefficient (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q)
    (ε0 : ℝ) (hε0 : 0 < ε0) :
    ∃ ε1 : ℝ, 0 < ε1 ∧ ε1 ≤ ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε1 →
      ∃ hQ : Generic (softInsertion P j q ε),
        ∀ a : ZMod (n + 1), a ≠ softOldIndex j j → ∃! g : ZMod n,
          a = softParentEdge j g ∧
          (treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1) : ℚ) =
            softAmplitudeMultiplier P j q * (treeCoefficient P hP.1 g hn : ℚ) ∧
          ((softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) →
            treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1) =
              -(turn P j : ℤ) * treeCoefficient P hP.1 g hn) ∧
          ((softAttachmentMinus P j q ≠ softAttachmentPlus P j q) →
            treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1) = 0) ∧
          ((softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) →
            treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1) =
              (turn P j : ℤ) * treeCoefficient P hP.1 g hn) :=
  soft_amplitude_source hn hP j q hq ε0 hε0

end
end SM.SoftDuplication
