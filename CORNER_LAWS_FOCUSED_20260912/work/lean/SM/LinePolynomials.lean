import SM.DirectionPolynomials
import SM.LineConcurrence

/-! Multivariate polynomials for the source's actual directed line rows and
their 3×3 determinant. Evaluation is proved against the existing geometry. -/

namespace SM

open MvPolynomial

noncomputable section

variable {n : ℕ}

def linePolynomialA (e : ZMod n) : CoordinatePolynomial n := -directionPolynomialY e
def linePolynomialB (e : ZMod n) : CoordinatePolynomial n := directionPolynomialX e
def linePolynomialC (e : ZMod n) : CoordinatePolynomial n :=
  coordinateX e * directionPolynomialY e - coordinateY e * directionPolynomialX e

def linePolynomialRow (e : ZMod n) : Fin 3 → CoordinatePolynomial n :=
  ![linePolynomialA e, linePolynomialB e, linePolynomialC e]

def concurrencePolynomial (e f g : ZMod n) : CoordinatePolynomial n :=
  (Matrix.of ![linePolynomialRow e, linePolynomialRow f, linePolynomialRow g]).det

@[simp] theorem eval_linePolynomialA (P : LabelledTuple n) (e : ZMod n) :
    eval (scalarCoordinates P) (linePolynomialA e) = edgeLineA P e := by
  simp [linePolynomialA, edgeLineA, edge]

@[simp] theorem eval_linePolynomialB (P : LabelledTuple n) (e : ZMod n) :
    eval (scalarCoordinates P) (linePolynomialB e) = edgeLineB P e := by
  simp [linePolynomialB, edgeLineB, edge]

@[simp] theorem eval_linePolynomialC (P : LabelledTuple n) (e : ZMod n) :
    eval (scalarCoordinates P) (linePolynomialC e) = edgeLineC P e := by
  simp [linePolynomialC, edgeLineC, edge]
  ring

theorem concurrencePolynomial_formula (e f g : ZMod n) :
    concurrencePolynomial e f g =
      linePolynomialA e * linePolynomialB f * linePolynomialC g -
      linePolynomialA e * linePolynomialC f * linePolynomialB g -
      linePolynomialB e * linePolynomialA f * linePolynomialC g +
      linePolynomialB e * linePolynomialC f * linePolynomialA g +
      linePolynomialC e * linePolynomialA f * linePolynomialB g -
      linePolynomialC e * linePolynomialB f * linePolynomialA g := by
  rw [concurrencePolynomial, Matrix.det_fin_three]
  rfl

@[simp] theorem eval_concurrencePolynomial (P : LabelledTuple n) (e f g : ZMod n) :
    eval (scalarCoordinates P) (concurrencePolynomial e f g) = concurrenceDet P e f g := by
  rw [concurrencePolynomial_formula, concurrenceDet_formula]
  simp

theorem separatedEdgeHeads_triple [Nontrivial (ZMod n)] (e f g : ZMod n)
    (hef : remote e f) (heg : remote e g) (hfg : remote f g) :
    SeparatedEdgeHeads {e, f, g} := by
  obtain ⟨hfe, hfe1, hf1e, hf1e1⟩ := remote_endpoints e f hef
  obtain ⟨hge, hge1, hg1e, hg1e1⟩ := remote_endpoints e g heg
  obtain ⟨hgf, hgf1, hg1f, hg1f1⟩ := remote_endpoints f g hfg
  intro a ha b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> subst a <;> subst b
  all_goals first | exact next_ne_self _ | exact hfe1.symm | exact hf1e |
    exact hge1.symm | exact hg1e | exact hgf1.symm | exact hg1f

theorem tailDirectionTranslation_tail_X (E : Finset (ZMod n)) (hE : SeparatedEdgeHeads E)
    (e : ZMod n) (he : e ∈ E) :
    tailDirectionTranslation E hE (coordinateX e) = coordinateX e := by
  classical
  have hn : e - 1 ∉ E := fun h => hE (e - 1) h e he (sub_add_cancel e 1)
  simp [tailDirectionTranslation, coordinateX, hn]

theorem tailDirectionTranslation_tail_Y (E : Finset (ZMod n)) (hE : SeparatedEdgeHeads E)
    (e : ZMod n) (he : e ∈ E) :
    tailDirectionTranslation E hE (coordinateY e) = coordinateY e := by
  classical
  have hn : e - 1 ∉ E := fun h => hE (e - 1) h e he (sub_add_cancel e 1)
  simp [tailDirectionTranslation, coordinateY, hn]

end

end SM
