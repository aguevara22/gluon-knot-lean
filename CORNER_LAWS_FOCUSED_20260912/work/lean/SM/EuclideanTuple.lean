import SM.PolygonalConnected
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Actual Euclidean balls on the 2n real vertex coordinates. The ambient
product topology agrees with this Euclidean topology; the default product
max metric is not used as a substitute for the Euclidean metric. -/

namespace SM

open Set Filter Topology

variable {n : ℕ}

noncomputable def tupleCoordinates (P : LabelledTuple n) :
    EuclideanSpace ℝ (Fin n × Fin 2) :=
  WithLp.toLp 2 (fun a => if a.2 = 0 then (P (a.1.val : ZMod n)).1
    else (P (a.1.val : ZMod n)).2)

noncomputable def coordinatesTuple [NeZero n]
    (z : EuclideanSpace ℝ (Fin n × Fin 2)) : LabelledTuple n :=
  fun i => (z (⟨i.val, i.val_lt⟩, 0), z (⟨i.val, i.val_lt⟩, 1))

theorem coordinatesTuple_tupleCoordinates [NeZero n] (P : LabelledTuple n) :
    coordinatesTuple (tupleCoordinates P) = P := by
  funext i
  simp [coordinatesTuple, tupleCoordinates]

theorem tupleCoordinates_coordinatesTuple [NeZero n]
    (z : EuclideanSpace ℝ (Fin n × Fin 2)) :
    tupleCoordinates (coordinatesTuple z) = z := by
  apply PiLp.ext
  rintro ⟨i, j⟩
  have hi : (⟨(i.val : ZMod n).val, (i.val : ZMod n).val_lt⟩ : Fin n) = i :=
    Fin.ext (ZMod.val_natCast_of_lt i.isLt)
  change (if j = 0 then z (⟨(i.val : ZMod n).val, (i.val : ZMod n).val_lt⟩, 0)
    else z (⟨(i.val : ZMod n).val, (i.val : ZMod n).val_lt⟩, 1)) = z (i, j)
  rw [hi]
  fin_cases j <;> simp

theorem continuous_tupleCoordinates : Continuous (tupleCoordinates (n := n)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n × Fin 2 => ℝ)).comp
  apply continuous_pi
  intro a
  by_cases h : a.2 = 0
  · simpa [h] using (continuous_vertex (a.1.val : ZMod n)).fst
  · simpa [h] using (continuous_vertex (a.1.val : ZMod n)).snd

theorem continuous_coordinatesTuple [NeZero n] :
    Continuous (coordinatesTuple (n := n)) := by
  apply continuous_pi
  intro i
  exact (PiLp.continuous_apply 2 (fun _ : Fin n × Fin 2 => ℝ)
    (⟨i.val, i.val_lt⟩, 0)).prodMk
    (PiLp.continuous_apply 2 (fun _ : Fin n × Fin 2 => ℝ) (⟨i.val, i.val_lt⟩, 1))

noncomputable def tupleEuclideanHomeomorph [NeZero n] :
    LabelledTuple n ≃ₜ EuclideanSpace ℝ (Fin n × Fin 2) where
  toFun := tupleCoordinates
  invFun := coordinatesTuple
  left_inv := coordinatesTuple_tupleCoordinates
  right_inv := tupleCoordinates_coordinatesTuple
  continuous_toFun := continuous_tupleCoordinates
  continuous_invFun := continuous_coordinatesTuple

/-- The usual radius-r open Euclidean ball, in the tuple's 2n coordinates. -/
def euclideanTupleBall (P : LabelledTuple n) (r : ℝ) : Set (LabelledTuple n) :=
  tupleCoordinates ⁻¹' Metric.ball (tupleCoordinates P) r

theorem isOpen_euclideanTupleBall (P : LabelledTuple n) (r : ℝ) :
    IsOpen (euclideanTupleBall P r) :=
  Metric.isOpen_ball.preimage continuous_tupleCoordinates

theorem mem_euclideanTupleBall {P : LabelledTuple n} {r : ℝ} (hr : 0 < r) :
    P ∈ euclideanTupleBall P r := by
  exact Metric.mem_ball_self hr

theorem exists_euclideanTupleBall_subset [NeZero n] {S : Set (LabelledTuple n)}
    (hS : IsOpen S) {P : LabelledTuple n} (hP : P ∈ S) :
    ∃ r > 0, euclideanTupleBall P r ⊆ S := by
  have hopen := hS.preimage continuous_coordinatesTuple
  have hmem : tupleCoordinates P ∈ coordinatesTuple ⁻¹' S := by
    simpa only [mem_preimage, coordinatesTuple_tupleCoordinates] using hP
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hopen _ hmem
  refine ⟨r, hr, fun Q hQ => ?_⟩
  have h := hsub hQ
  simpa only [mem_preimage, coordinatesTuple_tupleCoordinates] using h

end SM
