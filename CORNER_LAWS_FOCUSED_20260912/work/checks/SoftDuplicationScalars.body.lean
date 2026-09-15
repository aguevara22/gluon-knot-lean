namespace SM.SoftDuplication

/-- Two presentations at an interval starting at the duplicated occurrence.
The intermediate t-value cancels in both ordinary and root transforms. -/
theorem first_ordinary (eta tX tY : ℚ) :
    (eta - tX) / 2 + (tX - tY) / 2 = (eta - tY) / 2 := by
  ring

theorem first_root (eta tX tY : ℚ) :
    (eta - tX) / 2 + (tX + tY) / 2 = (eta + tY) / 2 := by
  ring

/-- The same cancellation applies to the last child, with the last boundary
and exterior endpoint playing the ordered roles from the source. -/
theorem last_ordinary (eta tY tX : ℚ) :
    (eta - tY) / 2 + (tY - tX) / 2 = (eta - tX) / 2 := by
  ring

theorem last_root (eta tY tX : ℚ) :
    (eta - tY) / 2 + (tY + tX) / 2 = (eta + tX) / 2 := by
  ring

/-- The exact residual for a spanning ordinary top before any sign identity.
This is not asserted zero for arbitrary independent far scalars. -/
theorem ordinary_residual (a b h : ℚ) :
    -(a + b) / 2 * ((a - h) / 2) + ((a - h) * (b - h)) / 4 =
      (h ^ 2 - a ^ 2) / 4 := by
  ring

/-- The root residual has the same value with the far signs reversed. -/
theorem root_residual (a b h : ℚ) :
    -(a + b) / 2 * ((a + h) / 2) + ((a + h) * (b + h)) / 4 =
      (h ^ 2 - a ^ 2) / 4 := by
  ring

/-- A nonzero SignType supplies precisely the square identity consumed below. -/
theorem sign_square (a : SignType) (ha : a ≠ 0) :
    (((a : ℤ) : ℚ)) ^ 2 = 1 := by
  cases a <;> norm_num at *

/-- Sum of the B-only, A-only and both-cut presentations at an ordinary top.
Only equality of a^2 and h^2 is needed; b and the neighbor data are arbitrary. -/
theorem three_ordinary (etaMinus etaPlus a b h : ℚ) (hsq : h ^ 2 = a ^ 2) :
    ((etaMinus - a) / 2) * ((a - h) / 2) +
      ((etaPlus - b) / 2) * ((a - h) / 2) +
      ((a - h) / 2) * ((b - h) / 2) =
        ((etaMinus + etaPlus) / 2) * ((a - h) / 2) := by
  calc
    _ = ((etaMinus + etaPlus) / 2) * ((a - h) / 2) +
        (h ^ 2 - a ^ 2) / 4 := by ring
    _ = _ := by rw [hsq]; ring

theorem three_root (etaMinus etaPlus a b h : ℚ) (hsq : h ^ 2 = a ^ 2) :
    ((etaMinus - a) / 2) * ((a + h) / 2) +
      ((etaPlus - b) / 2) * ((a + h) / 2) +
      ((a + h) / 2) * ((b + h) / 2) =
        ((etaMinus + etaPlus) / 2) * ((a + h) / 2) := by
  calc
    _ = ((etaMinus + etaPlus) / 2) * ((a + h) / 2) +
        (h ^ 2 - a ^ 2) / 4 := by ring
    _ = _ := by rw [hsq]; ring

/-- The three-row identities can be multiplied by any common exterior
product, including zero. No cancellation or division by that product occurs. -/
theorem three_ordinary_with_exterior (etaMinus etaPlus a b h F : ℚ)
    (hsq : h ^ 2 = a ^ 2) :
    (((etaMinus - a) / 2) * ((a - h) / 2)) * F +
      (((etaPlus - b) / 2) * ((a - h) / 2)) * F +
      (((a - h) / 2) * ((b - h) / 2)) * F =
        (((etaMinus + etaPlus) / 2) * ((a - h) / 2)) * F := by
  rw [← add_mul, ← add_mul, three_ordinary etaMinus etaPlus a b h hsq]

theorem three_root_with_exterior (etaMinus etaPlus a b h F : ℚ)
    (hsq : h ^ 2 = a ^ 2) :
    (((etaMinus - a) / 2) * ((a + h) / 2)) * F +
      (((etaPlus - b) / 2) * ((a + h) / 2)) * F +
      (((a + h) / 2) * ((b + h) / 2)) * F =
        (((etaMinus + etaPlus) / 2) * ((a + h) / 2)) * F := by
  rw [← add_mul, ← add_mul, three_root etaMinus etaPlus a b h hsq]

end SM.SoftDuplication
