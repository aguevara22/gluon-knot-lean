import LowestRowContract.Contract
import DirectGLSSW.HOMFLY.Coefficients

noncomputable section

namespace DirectGLSSW.HOMFLY.LowestRowContract
open DirectGLSSW.HOMFLY.Coefficients

private theorem aPower_mul (x y : ℤ) : aPower x * aPower y = aPower (x + y) := by
  simp [aPower, AddMonoidAlgebra.single_mul_single, add_comm]

/-- Conditional normalization of one skein relation across a two-component
smoothing. The skein identity is deliberately an explicit premise. -/
theorem framed_skein_normalization
    (h hSw hL hR : HOMFLYCoeff)
    (w r wL rL wR rR m : ℤ)
    (hs : aMonomial * h - aInvMonomial * hSw =
      aPower (-m) * (aMonomial - aInvMonomial) * hL * hR)
    (hw : w - 1 = wL + wR + m)
    (hr : r = rL + rR) :
    aPower (w + r) * (aMonomial - aInvMonomial) * h =
      aPower (w - 2 + r) * (aMonomial - aInvMonomial) * hSw +
        (aPower (wL + rL) * (aMonomial - aInvMonomial) * hL) *
          (aPower (wR + rR) * (aMonomial - aInvMonomial) * hR) := by
  have hA : aPower 1 = aMonomial := by
    rfl
  have hAinv : aPower (-1) = aInvMonomial := by
    rfl
  have hscaled := congrArg
    (fun X : HOMFLYCoeff => aPower (w - 1 + r) * (aMonomial - aInvMonomial) * X) hs
  change aPower (w - 1 + r) * (aMonomial - aInvMonomial) *
      (aMonomial * h - aInvMonomial * hSw) =
    aPower (w - 1 + r) * (aMonomial - aInvMonomial) *
      (aPower (-m) * (aMonomial - aInvMonomial) * hL * hR) at hscaled
  have hpowPos : aPower (w - 1 + r) * aMonomial = aPower (w + r) := by
    rw [← hA, aPower_mul]
    congr 1
    omega
  have hpowNeg : aPower (w - 1 + r) * aInvMonomial = aPower (w - 2 + r) := by
    rw [← hAinv, aPower_mul]
    congr 1
    omega
  have hwleft : w - 1 + r - m = (wL + rL) + (wR + rR) := by omega
  have hpowChild :
      aPower (w - 1 + r) * aPower (-m) =
        aPower ((wL + rL) + (wR + rR)) := by
    rw [aPower_mul]
    congr 1
  have htarget :
      aPower (w - 1 + r) * (aMonomial - aInvMonomial) *
          (aMonomial * h - aInvMonomial * hSw) =
        aPower (w + r) * (aMonomial - aInvMonomial) * h -
          aPower (w - 2 + r) * (aMonomial - aInvMonomial) * hSw := by
    rw [← hpowPos, ← hpowNeg]
    ring
  have hpowChildren :
      aPower (wL + rL) * aPower (wR + rR) =
        aPower ((wL + rL) + (wR + rR)) := by
    exact aPower_mul (wL + rL) (wR + rR)
  have hchild :
      aPower (w - 1 + r) * (aMonomial - aInvMonomial) *
          (aPower (-m) * (aMonomial - aInvMonomial) * hL * hR) =
        (aPower (wL + rL) * (aMonomial - aInvMonomial) * hL) *
          (aPower (wR + rR) * (aMonomial - aInvMonomial) * hR) := by
    calc
      _ = (aPower (w - 1 + r) * aPower (-m)) *
          (aMonomial - aInvMonomial) * (aMonomial - aInvMonomial) * hL * hR := by ring
      _ = aPower ((wL + rL) + (wR + rR)) *
          (aMonomial - aInvMonomial) * (aMonomial - aInvMonomial) * hL * hR := by
            rw [hpowChild]
      _ = (aPower (wL + rL) * aPower (wR + rR)) *
          (aMonomial - aInvMonomial) * (aMonomial - aInvMonomial) * hL * hR := by
            rw [← hpowChildren]
      _ = _ := by ring
  rw [htarget, hchild] at hscaled
  linear_combination hscaled

end DirectGLSSW.HOMFLY.LowestRowContract
