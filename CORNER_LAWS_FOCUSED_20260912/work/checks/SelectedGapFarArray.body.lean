namespace SM

noncomputable section
variable {n k : ℕ} [NeZero n]

/-- The actual outer triple for a cut strictly inside a selected gap. -/
def selectedOuterCutTriple (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (j : Fin k) (u : Fin n) (hleft : r j.castSucc < u) (hright : u < r j.succ) :
    IncreasingBoundaryTriple n where
  lower := r 0
  middle := u
  upper := r (Fin.last k)
  lower_middle := lt_of_le_of_lt (hr.monotone (by change 0 ≤ j.val; omega)) hleft
  middle_upper := lt_of_lt_of_le hright (hr.monotone (by change j.val + 1 ≤ k; omega))

/-- The same physical cut with the actual selected gap endpoints. -/
def selectedGapCutTriple (r : Fin (k + 1) → Fin n) (j : Fin k) (u : Fin n)
    (hleft : r j.castSucc < u) (hright : u < r j.succ) : IncreasingBoundaryTriple n where
  lower := r j.castSucc
  middle := u
  upper := r j.succ
  lower_middle := hleft
  middle_upper := hright

theorem selected_gap_epsilon_nonzero (hk : 0 < k) (t : Fin (k + 1) → ℝ)
    (hinj : Function.Injective t) (j : Fin k) : lineGapEpsilon t j ≠ 0 := by
  have hgap : t j.succ ≠ t j.castSucc := by
    intro he
    have hv := congrArg Fin.val (hinj he)
    change j.val + 1 = j.val at hv
    omega
  exact sign_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr hgap)
    (selected_endpoint_difference_nonzero hk t hinj))

/-- Actual weak geometry supplies distinct scalar endpoints for every gap;
the further point u may lie on or off the selected line. -/
theorem weak_selected_gap_far_sign {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) (hk : 0 < k) (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω) (j : Fin k) (u : Fin n) :
    pointFarSign (boundaryWord P g (r 0)) (boundaryWord P g u)
      (boundaryWord P g (r (Fin.last k))) = lineGapEpsilon t j *
        pointFarSign (boundaryWord P g (r j.castSucc)) (boundaryWord P g u)
          (boundaryWord P g (r j.succ)) := by
  have hinj := weak_line_coordinate_injective hP g r hr p ω t hline
  have houter : t (Fin.last k) ≠ t 0 :=
    sub_ne_zero.mp (selected_endpoint_difference_nonzero hk t hinj)
  have hgap : t j.succ ≠ t j.castSucc := by
    intro he
    have hv := congrArg Fin.val (hinj he)
    change j.val + 1 = j.val at hv
    omega
  simpa only [hline, lineGapEpsilon] using
    affine_internal_gap_sign p ω (boundaryWord P g u)
      (t 0) (t (Fin.last k)) (t j.castSucc) (t j.succ) houter hgap

/-- Source pf:gap-sign-identity for the exact geometric array and physical
cut triples, over any commutative coefficient ring. -/
theorem weak_selected_gap_far_array {R : Type*} [CommRing R]
    {P : LabelledTuple n} (hP : WeakGeneric P) (g : ZMod n) (hk : 0 < k)
    (r : Fin (k + 1) → Fin n) (hr : StrictMono r) (p ω : Plane)
    (t : Fin (k + 1) → ℝ) (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω)
    (j : Fin k) (u : Fin n) (hleft : r j.castSucc < u) (hright : u < r j.succ) :
    geometricBoundaryArray (R := R) P g (selectedOuterCutTriple r hr j u hleft hright) =
      ((lineGapEpsilon t j : ℤ) : R) *
        geometricBoundaryArray P g (selectedGapCutTriple r j u hleft hright) := by
  change ((pointFarSign (boundaryWord P g (r 0)) (boundaryWord P g u)
      (boundaryWord P g (r (Fin.last k))) : ℤ) : R) =
    ((lineGapEpsilon t j : ℤ) : R) *
      ((pointFarSign (boundaryWord P g (r j.castSucc)) (boundaryWord P g u)
        (boundaryWord P g (r j.succ)) : ℤ) : R)
  have hs := congrArg (fun s : SignType => ((s : ℤ) : R))
    (weak_selected_gap_far_sign hP g hk r hr p ω t hline j u)
  simpa only [SignType.coe_mul, Int.cast_mul] using hs

/-- The array identity follows directly from determinant collinearity, with
the selected affine coordinates constructed from the actual polygon. -/
theorem weak_selected_gap_far_array_of_collinear {R : Type*} [CommRing R]
    {P : LabelledTuple n} (hP : WeakGeneric P) (g : ZMod n) (hk : 0 < k)
    (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (hcol : ∀ l, det (boundaryWord P g (r l) - boundaryWord P g (r 0))
      (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0)) = 0)
    (j : Fin k) (u : Fin n) (hleft : r j.castSucc < u) (hright : u < r j.succ) :
    geometricBoundaryArray (R := R) P g (selectedOuterCutTriple r hr j u hleft hright) =
      ((lineGapEpsilon (selectedLineCoordinate P g r) j : ℤ) : R) *
        geometricBoundaryArray P g (selectedGapCutTriple r j u hleft hright) := by
  have hcoords := weak_selected_line_coordinates hP g hk r hr hcol
  exact weak_selected_gap_far_array hP g hk r hr (boundaryWord P g (r 0))
    (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0))
    (selectedLineCoordinate P g r) hcoords.2.1 j u hleft hright

end
end SM
