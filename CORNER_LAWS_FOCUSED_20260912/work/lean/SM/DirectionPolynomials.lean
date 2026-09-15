import SM.CoordinatePolynomials
import SM.Segment

/-! Actual edge-direction polynomials. Pairwise separated endpoint coordinates
are changed to tails and directions using the explicit polynomial shear. This
proves the auxiliary H irreducibility used in the source's argument for T. -/

namespace SM

open MvPolynomial

noncomputable section

variable {n : ℕ}

def directionPolynomialX (e : ZMod n) : CoordinatePolynomial n :=
  coordinateX (e + 1) - coordinateX e

def directionPolynomialY (e : ZMod n) : CoordinatePolynomial n :=
  coordinateY (e + 1) - coordinateY e

@[simp] theorem eval_directionPolynomialX (P : LabelledTuple n) (e : ZMod n) :
    eval (scalarCoordinates P) (directionPolynomialX e) = (edge P e).1 := by
  simp [directionPolynomialX, edge]

@[simp] theorem eval_directionPolynomialY (P : LabelledTuple n) (e : ZMod n) :
    eval (scalarCoordinates P) (directionPolynomialY e) = (edge P e).2 := by
  simp [directionPolynomialY, edge]

/-- No selected head is also a selected tail. This is a proved combinatorial
condition on selected edges, not an independence assumption on real coordinates. -/
def SeparatedEdgeHeads (E : Finset (ZMod n)) : Prop :=
  ∀ e ∈ E, ∀ f ∈ E, e + 1 ≠ f

theorem separatedEdgeHeads_pair [Nontrivial (ZMod n)] (e f : ZMod n)
    (hr : remote e f) : SeparatedEdgeHeads {e, f} := by
  obtain ⟨hfe, hfe1, hf1e, hf1e1⟩ := remote_endpoints e f hr
  intro a ha b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact next_ne_self _
  · exact hfe1.symm
  · exact hf1e
  · exact next_ne_self _

def tailDirectionTranslation (E : Finset (ZMod n)) (hE : SeparatedEdgeHeads E) :
    CoordinatePolynomial n ≃ₐ[ℝ] CoordinatePolynomial n := by
  classical
  apply polynomialShear (fun c : ScalarCoordinate n => c.1 - 1 ∈ E)
    (fun c => (c.1 - 1, c.2))
  intro c hc hp
  exact hE (c.1 - 1 - 1) hp (c.1 - 1) hc (by abel)

theorem tailDirectionTranslation_X (E : Finset (ZMod n)) (hE : SeparatedEdgeHeads E)
    (e : ZMod n) (he : e ∈ E) :
    tailDirectionTranslation E hE (coordinateX (e + 1)) = directionPolynomialX e := by
  classical
  simp [tailDirectionTranslation, coordinateX, directionPolynomialX, he]

theorem tailDirectionTranslation_Y (E : Finset (ZMod n)) (hE : SeparatedEdgeHeads E)
    (e : ZMod n) (he : e ∈ E) :
    tailDirectionTranslation E hE (coordinateY (e + 1)) = directionPolynomialY e := by
  classical
  simp [tailDirectionTranslation, coordinateY, directionPolynomialY, he]

def directionDeterminantPolynomial (e f : ZMod n) : CoordinatePolynomial n :=
  directionPolynomialX e * directionPolynomialY f - directionPolynomialY e * directionPolynomialX f

@[simp] theorem eval_directionDeterminantPolynomial (P : LabelledTuple n) (e f : ZMod n) :
    eval (scalarCoordinates P) (directionDeterminantPolynomial e f) = det (edge P e) (edge P f) := by
  simp [directionDeterminantPolynomial, det]

theorem directionDeterminantPolynomial_irreducible [Nontrivial (ZMod n)]
    (e f : ZMod n) (hr : remote e f) : Irreducible (directionDeterminantPolynomial e f) := by
  have hef : e + 1 ≠ f + 1 := (remote_endpoints e f hr).2.2.2.symm
  have hq : Irreducible (coordinateX (e + 1) * coordinateY (f + 1) -
      coordinateY (e + 1) * coordinateX (f + 1)) :=
    determinantPolynomial_irreducible (e + 1, 0) (f + 1, 1) (e + 1, 1) (f + 1, 0)
      (by simp) (by simp) (by simpa using hef) (by simpa using hef.symm) (by simp)
  have hE := separatedEdgeHeads_pair e f hr
  have he : e ∈ ({e, f} : Finset (ZMod n)) := by simp
  have hf : f ∈ ({e, f} : Finset (ZMod n)) := by simp
  have ht := (MulEquiv.irreducible_iff (tailDirectionTranslation {e, f} hE)).mpr hq
  simpa only [map_sub, map_mul, tailDirectionTranslation_X _ hE e he,
    tailDirectionTranslation_Y _ hE e he, tailDirectionTranslation_X _ hE f hf,
    tailDirectionTranslation_Y _ hE f hf, directionDeterminantPolynomial] using ht

theorem directionDeterminantPolynomial_ne_zero [Nontrivial (ZMod n)]
    (e f : ZMod n) (hr : remote e f) : directionDeterminantPolynomial e f ≠ 0 :=
  (directionDeterminantPolynomial_irreducible e f hr).ne_zero

end

end SM
