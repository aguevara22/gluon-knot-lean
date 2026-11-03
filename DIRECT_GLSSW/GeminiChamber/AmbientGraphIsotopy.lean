import GeminiChamber.ChamberPathInvariance
import GeminiChamber.ContractionIsotopy
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical Topology
noncomputable section

namespace DirectGLSSW.GeminiChamber

open DirectGLSSW
open DirectGLSSW.HOMFLY
open DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW.HOMFLY.SharpDaughter
open DirectGLSSW.HOMFLY.SharpDaughterRotation
open DirectGLSSW.HOMFLY.SharpDaughterRotationLocality
open DirectGLSSW.PermutationOrbits
open DirectGLSSW.LocalCrossingTransport
open DirectGLSSW.LocalSupportConjugacy
open DirectGLSSW.UniformDaughterSupportLocality
open DirectGLSSW.CrossingRationalParameters
open DirectGLSSW.CrossingIncidenceNeighborhood
open DirectGLSSW.LabelledCrossingContinuity
open DirectGLSSW.ConfigurationEventLocality
open DirectGLSSW.CrossingOrientationLocality
open DirectGLSSW.OriginalLeftTurnLocality
open Filter Topology

/-!
# Constructive McShane-Barycentric Ambient Plane Isotopy for Generic Polygon Paths

This module constructs the `AmbientPlaneIsotopy` along any continuous path
`p : Time → Fin n → Plane` in `CyclicGeneric`, transporting all original vertices,
crossings, original edges, and sharp daughter diagrams simultaneously, and proves
`DirectGLSSW.GeminiChamber.full_chamber_geometry`.
-/

section ClampedProjection

theorem abs_max_sub_max_le (a b c d : ℝ) :
    |max a b - max c d| ≤ max |a - c| |b - d| := by
  rw [abs_le]
  have h1 : a - c ≤ |a - c| := le_abs_self _
  have h2 : c - a ≤ |a - c| := neg_sub a c ▸ neg_le_abs _
  have h3 : b - d ≤ |b - d| := le_abs_self _
  have h4 : d - b ≤ |b - d| := neg_sub b d ▸ neg_le_abs _
  constructor
  · have hca : c ≤ a + max |a - c| |b - d| := by
      have : |a - c| ≤ max |a - c| |b - d| := le_max_left _ _
      linarith
    have hdb : d ≤ b + max |a - c| |b - d| := by
      have : |b - d| ≤ max |a - c| |b - d| := le_max_right _ _
      linarith
    have hcd : max c d ≤ max a b + max |a - c| |b - d| := by
      apply max_le
      · linarith [le_max_left a b]
      · linarith [le_max_right a b]
    linarith
  · have hac : a ≤ c + max |a - c| |b - d| := by
      have : |a - c| ≤ max |a - c| |b - d| := le_max_left _ _
      linarith
    have hbd : b ≤ d + max |a - c| |b - d| := by
      have : |b - d| ≤ max |a - c| |b - d| := le_max_right _ _
      linarith
    have hab : max a b ≤ max c d + max |a - c| |b - d| := by
      apply max_le
      · linarith [le_max_left c d]
      · linarith [le_max_right c d]
    linarith

theorem abs_min_sub_min_le (a b c d : ℝ) :
    |min a b - min c d| ≤ max |a - c| |b - d| := by
  rw [abs_le]
  have h1 : a - c ≤ |a - c| := le_abs_self _
  have h2 : c - a ≤ |a - c| := neg_sub a c ▸ neg_le_abs _
  have h3 : b - d ≤ |b - d| := le_abs_self _
  have h4 : d - b ≤ |b - d| := neg_sub b d ▸ neg_le_abs _
  constructor
  · have hmin : min a b + max |a - c| |b - d| ≥ min c d := by
      have ha : min c d ≤ a + max |a - c| |b - d| := by
        have : |a - c| ≤ max |a - c| |b - d| := le_max_left _ _
        linarith [min_le_left c d]
      have hb : min c d ≤ b + max |a - c| |b - d| := by
        have : |b - d| ≤ max |a - c| |b - d| := le_max_right _ _
        linarith [min_le_right c d]
      rcases min_choice a b with h | h <;> linarith
    linarith
  · have hmin : min c d + max |a - c| |b - d| ≥ min a b := by
      have hc : min a b ≤ c + max |a - c| |b - d| := by
        have : |a - c| ≤ max |a - c| |b - d| := le_max_left _ _
        linarith [min_le_left a b]
      have hd : min a b ≤ d + max |a - c| |b - d| := by
        have : |b - d| ≤ max |a - c| |b - d| := le_max_right _ _
        linarith [min_le_right a b]
      rcases min_choice c d with h | h <;> linarith
    linarith

/-- Clamping a real scalar to `[0, 1]`. -/
def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

theorem clamp01_mem_Icc (t : ℝ) : clamp01 t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold clamp01
  refine ⟨le_max_left 0 (min 1 t), ?_⟩
  exact max_le zero_le_one (min_le_left 1 t)

theorem clamp01_eq_self {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : clamp01 t = t := by
  unfold clamp01
  rw [min_eq_right ht.2, max_eq_right ht.1]

theorem abs_clamp01_sub_le (s t : ℝ) : |clamp01 s - clamp01 t| ≤ |s - t| := by
  unfold clamp01
  calc
    |max 0 (min 1 s) - max 0 (min 1 t)|
        ≤ max |(0 : ℝ) - 0| |min 1 s - min 1 t| := abs_max_sub_max_le 0 (min 1 s) 0 (min 1 t)
    _ = |min 1 s - min 1 t| := by simp [abs_nonneg]
    _ ≤ max |(1 : ℝ) - 1| |s - t| := abs_min_sub_min_le 1 s 1 t
    _ = |s - t| := by simp [abs_nonneg]

theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_const.min continuous_id)

/-- Squared Euclidean length of segment `[a, b]`. -/
def segLenSq (a b : Plane) : ℝ := (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2

theorem segLenSq_nonneg (a b : Plane) : 0 ≤ segLenSq a b := by
  unfold segLenSq
  positivity

theorem segLenSq_pos_of_ne {a b : Plane} (hab : a ≠ b) : 0 < segLenSq a b := by
  unfold segLenSq
  by_contra hnot
  have hle : (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 ≤ 0 := le_of_not_gt hnot
  have h1 : (b.1 - a.1) ^ 2 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
  have h2 : (b.2 - a.2) ^ 2 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
  have hb1 : b.1 = a.1 := sub_eq_zero.mp (sq_eq_zero_iff.mp h1)
  have hb2 : b.2 = a.2 := sub_eq_zero.mp (sq_eq_zero_iff.mp h2)
  exact hab (Prod.ext hb1.symm hb2.symm)

theorem dist_mul_abs_add_le_two_mul_segLenSq (a b : Plane) :
    dist a b * (|b.1 - a.1| + |b.2 - a.2|) ≤ 2 * segLenSq a b := by
  let X := |b.1 - a.1|
  let Y := |b.2 - a.2|
  have hdist : dist a b = max X Y := by
    rw [plane_dist_eq, abs_sub_comm a.1 b.1, abs_sub_comm a.2 b.2]
  have hlen : segLenSq a b = X ^ 2 + Y ^ 2 := by
    dsimp [segLenSq, X, Y]
    rw [sq_abs, sq_abs]
  rw [hdist, hlen]
  rcases max_choice X Y with h | h <;> rw [h]
  · nlinarith [sq_nonneg (X - Y), sq_nonneg X, sq_nonneg Y]
  · nlinarith [sq_nonneg (X - Y), sq_nonneg X, sq_nonneg Y]

/-- Unclamped orthogonal projection parameter of `z` onto `[a, b]`. -/
noncomputable def rawProjParam (a b z : Plane) : ℝ :=
  ((z.1 - a.1) * (b.1 - a.1) + (z.2 - a.2) * (b.2 - a.2)) / segLenSq a b

theorem rawProjParam_affinePoint {a b : Plane} (hab : a ≠ b) (α : ℝ) :
    rawProjParam a b (affinePoint a b α) = α := by
  have hpos : segLenSq a b ≠ 0 := ne_of_gt (segLenSq_pos_of_ne hab)
  unfold rawProjParam
  have hnum :
      (((affinePoint a b α).1 - a.1) * (b.1 - a.1) +
        ((affinePoint a b α).2 - a.2) * (b.2 - a.2)) =
      α * segLenSq a b := by
    dsimp [affinePoint, segLenSq]
    ring
  rw [hnum, mul_div_cancel_right₀ α hpos]

theorem abs_rawProjParam_sub_le (a b z w : Plane) :
    |rawProjParam a b z - rawProjParam a b w| ≤
      ((|b.1 - a.1| + |b.2 - a.2|) / segLenSq a b) * dist z w := by
  unfold rawProjParam
  rw [← sub_div, abs_div, abs_of_nonneg (segLenSq_nonneg a b), div_mul_eq_mul_div]
  have hnum :
      ((z.1 - a.1) * (b.1 - a.1) + (z.2 - a.2) * (b.2 - a.2)) -
        ((w.1 - a.1) * (b.1 - a.1) + (w.2 - a.2) * (b.2 - a.2)) =
      (z.1 - w.1) * (b.1 - a.1) + (z.2 - w.2) * (b.2 - a.2) := by ring
  rw [hnum]
  have hle :
      |(z.1 - w.1) * (b.1 - a.1) + (z.2 - w.2) * (b.2 - a.2)| ≤
        (|b.1 - a.1| + |b.2 - a.2|) * dist z w := by
    calc
      |(z.1 - w.1) * (b.1 - a.1) + (z.2 - w.2) * (b.2 - a.2)|
          ≤ |(z.1 - w.1) * (b.1 - a.1)| + |(z.2 - w.2) * (b.2 - a.2)| := abs_add _ _
      _ = |z.1 - w.1| * |b.1 - a.1| + |z.2 - w.2| * |b.2 - a.2| := by
        rw [abs_mul, abs_mul]
      _ ≤ dist z w * |b.1 - a.1| + dist z w * |b.2 - a.2| :=
        add_le_add
          (mul_le_mul_of_nonneg_right (plane_fst_sub_le_dist z w) (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (plane_snd_sub_le_dist z w) (abs_nonneg _))
      _ = (|b.1 - a.1| + |b.2 - a.2|) * dist z w := by ring
  exact div_le_div_of_nonneg_right hle (segLenSq_nonneg a b)

/-- Clamped orthogonal projection parameter of `z` onto `[a, b]`. -/
noncomputable def projParam (a b z : Plane) : ℝ :=
  clamp01 (rawProjParam a b z)

theorem projParam_mem_Icc (a b z : Plane) : projParam a b z ∈ Set.Icc (0 : ℝ) 1 :=
  clamp01_mem_Icc _

theorem projParam_affinePoint {a b : Plane} (hab : a ≠ b) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    projParam a b (affinePoint a b α) = α := by
  unfold projParam
  rw [rawProjParam_affinePoint hab α, clamp01_eq_self hα]

/-- Clamped projection point on `[a, b]`. -/
noncomputable def projPoint (a b z : Plane) : Plane :=
  affinePoint a b (projParam a b z)

theorem dist_affinePoint_sub (a b : Plane) (s t : ℝ) :
    dist (affinePoint a b s) (affinePoint a b t) = |s - t| * dist a b := by
  rw [plane_dist_eq, plane_dist_eq]
  have h1 : (affinePoint a b s).1 - (affinePoint a b t).1 = -(s - t) * (a.1 - b.1) := by
    dsimp [affinePoint]; ring
  have h2 : (affinePoint a b s).2 - (affinePoint a b t).2 = -(s - t) * (a.2 - b.2) := by
    dsimp [affinePoint]; ring
  rw [h1, h2, abs_mul, abs_mul, abs_neg, ← mul_max_of_nonneg _ _ (abs_nonneg (s - t))]

theorem dist_projPoint_le_two_mul_dist (a b z w : Plane) :
    dist (projPoint a b z) (projPoint a b w) ≤ 2 * dist z w := by
  by_cases hab : a = b
  · subst hab
    have h1 : projPoint a a z = a := by ext <;> simp [projPoint, affinePoint]
    have h2 : projPoint a a w = a := by ext <;> simp [projPoint, affinePoint]
    rw [h1, h2, dist_self]
    have : 0 ≤ dist z w := dist_nonneg
    linarith
  · have hpos : 0 < segLenSq a b := segLenSq_pos_of_ne hab
    unfold projPoint
    rw [dist_affinePoint_sub]
    calc
      |projParam a b z - projParam a b w| * dist a b
          ≤ |rawProjParam a b z - rawProjParam a b w| * dist a b :=
        mul_le_mul_of_nonneg_right (abs_clamp01_sub_le _ _) dist_nonneg
      _ ≤ (((|b.1 - a.1| + |b.2 - a.2|) / segLenSq a b) * dist z w) * dist a b :=
        mul_le_mul_of_nonneg_right (abs_rawProjParam_sub_le a b z w) dist_nonneg
      _ = ((dist a b * (|b.1 - a.1| + |b.2 - a.2|)) / segLenSq a b) * dist z w := by ring
      _ ≤ ((2 * segLenSq a b) / segLenSq a b) * dist z w := by
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        exact div_le_div_of_nonneg_right (dist_mul_abs_add_le_two_mul_segLenSq a b) (le_of_lt hpos)
      _ = 2 * dist z w := by
        rw [mul_div_cancel_right₀ 2 (ne_of_gt hpos)]

end ClampedProjection

section FinsetMaxZero

variable {α : Type*} [DecidableEq α]

/-- Maximum of `0` and `{f x | x ∈ s}`. -/
def finsetMaxZero (s : Finset α) (f : α → ℝ) : ℝ :=
  s.fold max 0 f

theorem zero_le_finsetMaxZero (s : Finset α) (f : α → ℝ) :
    0 ≤ finsetMaxZero s f := by
  induction s using Finset.induction_on with
  | empty => simp [finsetMaxZero]
  | @insert a s ha ih =>
    unfold finsetMaxZero at ih ⊢
    rw [Finset.fold_insert ha]
    exact le_max_of_le_right ih

theorem le_finsetMaxZero (s : Finset α) (f : α → ℝ) {x : α} (hx : x ∈ s) :
    f x ≤ finsetMaxZero s f := by
  induction s using Finset.induction_on with
  | empty => exact False.elim (Finset.not_mem_empty x hx)
  | @insert a s ha ih =>
    unfold finsetMaxZero at ih ⊢
    rw [Finset.fold_insert ha]
    rcases Finset.mem_insert.mp hx with rfl | hxs
    · exact le_max_left _ _
    · exact le_max_of_le_right (ih hxs)

theorem finsetMaxZero_le (s : Finset α) (f : α → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ x ∈ s, f x ≤ B) :
    finsetMaxZero s f ≤ B := by
  induction s using Finset.induction_on with
  | empty => simpa [finsetMaxZero] using hB
  | @insert a s ha ih =>
    unfold finsetMaxZero at ih ⊢
    rw [Finset.fold_insert ha]
    exact max_le (hf a (Finset.mem_insert_self a s))
      (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))

theorem abs_finsetMaxZero_sub_le (s : Finset α) (f g : α → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hfg : ∀ x ∈ s, |f x - g x| ≤ C) :
    |finsetMaxZero s f - finsetMaxZero s g| ≤ C := by
  induction s using Finset.induction_on with
  | empty => simpa [finsetMaxZero] using hC
  | @insert a s ha ih =>
    unfold finsetMaxZero at ih ⊢
    rw [Finset.fold_insert ha, Finset.fold_insert ha]
    refine (abs_max_sub_max_le (f a) (s.fold max 0 f) (g a) (s.fold max 0 g)).trans ?_
    exact max_le (hfg a (Finset.mem_insert_self a s))
      (ih (fun x hx => hfg x (Finset.mem_insert_of_mem hx)))

theorem continuous_finsetMaxZero {X : Type*} [TopologicalSpace X]
    (s : Finset α) (F : α → X → ℝ) (hF : ∀ x ∈ s, Continuous (F x)) :
    Continuous (fun p => finsetMaxZero s (fun x => F x p)) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa [finsetMaxZero] using (continuous_const : Continuous (fun _ : X => (0 : ℝ)))
  | @insert a s ha ih =>
    have heq : (fun p => finsetMaxZero (insert a s) (fun x => F x p)) =
        (fun p => max (F a p) (finsetMaxZero s (fun x => F x p))) := by
      ext p
      unfold finsetMaxZero
      rw [Finset.fold_insert ha]
    rw [heq]
    exact (hF a (Finset.mem_insert_self a s)).max
      (ih (fun x hx => hF x (Finset.mem_insert_of_mem hx)))

end FinsetMaxZero

section EventGraphGeometry

variable {n : ℕ} (p : Time → Fin n → Plane) (hp : Continuous p) (hg : ∀ t, CyclicGeneric (p t))

abbrev Vtx₀ : Type := PolygonDrawing.Vertex (p start)
abbrev Ev₀ : Type := PolygonEvent (p start)

/-- Vertex position at time `u` indexed by initial drawing vertices `Vtx₀`. -/
noncomputable def vtxPos (u : Time) (v : Vtx₀ p) : Plane :=
  PolygonDrawing.vertexPoint (p u)
    (parentVertexEquiv (p start) (p u) (pathCrossingEquiv p hp hg u) v)

theorem vtxPos_inl (u : Time) (i : Fin n) :
    vtxPos p hp hg u (Sum.inl i) = p u i := rfl

theorem vtxPos_inr (u : Time) (c : PolygonCrossing (p start)) :
    vtxPos p hp hg u (Sum.inr c) = crossingPoint (p u) (pathCrossingEquiv p hp hg u c) := rfl

theorem vtxPos_start (v : Vtx₀ p) :
    vtxPos p hp hg start v = PolygonDrawing.vertexPoint (p start) v := by
  cases v with
  | inl i => rfl
  | inr c =>
    change crossingPoint (p start) (pathCrossingEquiv p hp hg start c) =
      crossingPoint (p start) c
    rw [pathCrossingEquiv_start p hp hg]
    rfl

theorem vtxPos_injective (u : Time) : Function.Injective (vtxPos p hp hg u) :=
  (PolygonDrawing.vertexPoint_injective (p u) (hg u)).comp
    (parentVertexEquiv (p start) (p u) (pathCrossingEquiv p hp hg u)).injective

theorem continuous_vtxPos (v : Vtx₀ p) :
    Continuous (fun u : Time => vtxPos p hp hg u v) := by
  cases v with
  | inl i =>
    exact (continuous_apply i).comp hp
  | inr c =>
    have heq : (fun u : Time => vtxPos p hp hg u (Sum.inr c)) =
        (fun u : Time =>
          affinePoint (p u c.val.1) (p u (cyclicSuccessor c.val.1))
            (leftParameter (p u) c.val.1 c.val.2)) := by
      funext u
      let c_u := pathCrossingEquiv p hp hg u c
      have hlab : c_u.val = c.val := pathCrossingEquiv_labels p hp hg u c
      have hD : denominator (p u) c_u.val.1 c_u.val.2 ≠ 0 :=
        DirectGLSSW.crossing_transverse (hg u).size_ge_three (p u) (hg u).g1 c_u
      have hpt := crossingPoint_eq (p u) c_u hD
      simpa only [vtxPos_inr, c_u, hlab] using hpt
    rw [heq, continuous_iff_continuousAt]
    intro u
    let c_u := pathCrossingEquiv p hp hg u c
    have hlab : c_u.val = c.val := pathCrossingEquiv_labels p hp hg u c
    have hD : denominator (p u) c.val.1 c.val.2 ≠ 0 := by
      rw [← hlab]
      exact DirectGLSSW.crossing_transverse (hg u).size_ge_three (p u) (hg u).g1 c_u
    exact (continuousAt_intersectionPoint (p u) c.val.1 c.val.2 hD).comp hp.continuousAt

/-- Source vertex in `Vtx₀` of event segment `x`. -/
def src₀ (x : Ev₀ p) : Vtx₀ p :=
  PolygonDrawing.arcSource (p start) x

/-- Target vertex in `Vtx₀` of event segment `x`. -/
noncomputable def tgt₀ (x : Ev₀ p) : Vtx₀ p :=
  PolygonDrawing.arcTarget (p start) (hg start) x

theorem src₀_ne_tgt₀ (x : Ev₀ p) : src₀ p x ≠ tgt₀ p hg x :=
  PolygonDrawing.arc_endpoints_distinct (p start) (hg start) x

theorem parentVertexEquiv_src₀ (u : Time) (x : Ev₀ p) :
    parentVertexEquiv (p start) (p u) (pathCrossingEquiv p hp hg u) (src₀ p x) =
      PolygonDrawing.arcSource (p u)
        (polygonEventMapEquiv (pathCrossingEquiv p hp hg u) x) :=
  parentVertexEquiv_eventVertex (p start) (p u) (pathCrossingEquiv p hp hg u) x

theorem smoothingPairing_empty_apply {m : ℕ} (q : Fin m → Plane) (y : PolygonEvent q) :
    smoothingPairing q ∅ y = y := by
  rw [smoothingPairing_apply]
  cases y with
  | inl e => rfl
  | inr v => simp [smoothingPairingMap]

theorem smoothingDartPermutation_empty_apply {m : ℕ} (q : Fin m → Plane)
    (hq : CyclicGeneric q) (x : PolygonEvent q) :
    smoothingDartPermutation q hq.g2 ∅ x = polygonEventSuccessor q hq.g2 x := by
  rw [smoothingDartPermutation_apply, smoothingPairing_empty_apply]

theorem parentVertexEquiv_tgt₀ (u : Time) (x : Ev₀ p) :
    parentVertexEquiv (p start) (p u) (pathCrossingEquiv p hp hg u) (tgt₀ p hg x) =
      PolygonDrawing.arcTarget (p u) (hg u)
        (polygonEventMapEquiv (pathCrossingEquiv p hp hg u) x) := by
  unfold tgt₀ PolygonDrawing.arcTarget
  rw [parentVertexEquiv_eventVertex]
  congr 1
  have hmap := smoothingDartPermutation_map (p start) (p u) (hg start) (hg u)
    (pathCrossingEquiv p hp hg u) (pathCrossingEquiv_labels p hp hg u)
    (path_eventOrder_iff p hp hg u) ∅ x
  rw [Finset.map_empty,
    smoothingDartPermutation_empty_apply (p start) (hg start) x,
    smoothingDartPermutation_empty_apply (p u) (hg u)] at hmap
  exact hmap

/-- Start point of event segment `x` at time `u`. -/
noncomputable def segStart (u : Time) (x : Ev₀ p) : Plane :=
  vtxPos p hp hg u (src₀ p x)

/-- End point of event segment `x` at time `u`. -/
noncomputable def segEnd (u : Time) (x : Ev₀ p) : Plane :=
  vtxPos p hp hg u (tgt₀ p hg x)

theorem segStart_eq_eventPoint (u : Time) (x : Ev₀ p) :
    segStart p hp hg u x =
      polygonEventPoint (p u) (polygonEventMapEquiv (pathCrossingEquiv p hp hg u) x) := by
  unfold segStart vtxPos
  rw [parentVertexEquiv_src₀]
  exact PolygonDrawing.vertexPoint_eventVertex (p u) _

theorem segEnd_eq_eventSuccessorPoint (u : Time) (x : Ev₀ p) :
    segEnd p hp hg u x =
      polygonEventPoint (p u)
        (polygonEventSuccessor (p u) (hg u).g2
          (polygonEventMapEquiv (pathCrossingEquiv p hp hg u) x)) := by
  unfold segEnd vtxPos
  rw [parentVertexEquiv_tgt₀]
  exact PolygonDrawing.vertexPoint_eventVertex (p u) _

theorem segStart_ne_segEnd (u : Time) (x : Ev₀ p) :
    segStart p hp hg u x ≠ segEnd p hp hg u x :=
  fun h => src₀_ne_tgt₀ p hg x (vtxPos_injective p hp hg u h)

theorem continuous_segStart (x : Ev₀ p) :
    Continuous (fun u : Time => segStart p hp hg u x) :=
  continuous_vtxPos p hp hg (src₀ p x)

theorem continuous_segEnd (x : Ev₀ p) :
    Continuous (fun u : Time => segEnd p hp hg u x) :=
  continuous_vtxPos p hp hg (tgt₀ p hg x)

/-- Point with parameter `α` on event segment `x` at time `u`. -/
noncomputable def segPoint (u : Time) (x : Ev₀ p) (α : ℝ) : Plane :=
  affinePoint (segStart p hp hg u x) (segEnd p hp hg u x) α

theorem segPoint_zero (u : Time) (x : Ev₀ p) :
    segPoint p hp hg u x 0 = segStart p hp hg u x :=
  affinePoint_zero _ _

theorem segPoint_one (u : Time) (x : Ev₀ p) :
    segPoint p hp hg u x 1 = segEnd p hp hg u x :=
  affinePoint_one _ _

/-- Kronecker delta indicator on `Vtx₀`. -/
def vtxIndicator (v w : Vtx₀ p) : ℝ :=
  if w = v then 1 else 0

/-- Barycentric weight of vertex `v` along event segment `x` at parameter `α`. -/
noncomputable def baryWeight (v : Vtx₀ p) (x : Ev₀ p) (α : ℝ) : ℝ :=
  (1 - α) * vtxIndicator p v (src₀ p x) + α * vtxIndicator p v (tgt₀ p hg x)

theorem vtxIndicator_nonneg (v w : Vtx₀ p) : 0 ≤ vtxIndicator p v w := by
  unfold vtxIndicator
  split_ifs <;> norm_num

theorem vtxIndicator_le_one (v w : Vtx₀ p) : vtxIndicator p v w ≤ 1 := by
  unfold vtxIndicator
  split_ifs <;> norm_num

theorem baryWeight_nonneg (v : Vtx₀ p) (x : Ev₀ p) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ baryWeight p hg v x α := by
  unfold baryWeight
  have h0 := vtxIndicator_nonneg p v (src₀ p x)
  have h1 := vtxIndicator_nonneg p v (tgt₀ p hg x)
  nlinarith [hα.1, hα.2]

theorem baryWeight_le_one (v : Vtx₀ p) (x : Ev₀ p) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    baryWeight p hg v x α ≤ 1 := by
  unfold baryWeight
  have h0 := vtxIndicator_le_one p v (src₀ p x)
  have h1 := vtxIndicator_le_one p v (tgt₀ p hg x)
  nlinarith [hα.1, hα.2]

theorem abs_baryWeight_sub_le (v : Vtx₀ p) (x : Ev₀ p) (α β : ℝ) :
    |baryWeight p hg v x α - baryWeight p hg v x β| ≤ |α - β| := by
  have heq : baryWeight p hg v x α - baryWeight p hg v x β =
      (α - β) * (vtxIndicator p v (tgt₀ p hg x) - vtxIndicator p v (src₀ p x)) := by
    dsimp [baryWeight]; ring
  rw [heq, abs_mul]
  have hdiff : |vtxIndicator p v (tgt₀ p hg x) - vtxIndicator p v (src₀ p x)| ≤ 1 := by
    rw [abs_le]
    have h0a := vtxIndicator_nonneg p v (src₀ p x)
    have h0b := vtxIndicator_le_one p v (src₀ p x)
    have h1a := vtxIndicator_nonneg p v (tgt₀ p hg x)
    have h1b := vtxIndicator_le_one p v (tgt₀ p hg x)
    constructor <;> linarith
  calc
    |α - β| * |vtxIndicator p v (tgt₀ p hg x) - vtxIndicator p v (src₀ p x)|
        ≤ |α - β| * 1 := mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
    _ = |α - β| := mul_one _

/-- Distinct event segments meet only at endpoints. -/
theorem segPoint_eq_endpoints_of_ne (u : Time) {x y : Ev₀ p} (hxy : x ≠ y)
    {α β : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (heq : segPoint p hp hg u x α = segPoint p hp hg u y β) :
    (α = 0 ∨ α = 1) ∧ (β = 0 ∨ β = 1) := by
  let E_u := pathCrossingEquiv p hp hg u
  let x_u := polygonEventMapEquiv E_u x
  let y_u := polygonEventMapEquiv E_u y
  have hxy_u : x_u ≠ y_u := fun h => hxy ((polygonEventMapEquiv E_u).injective h)
  have heq_u :
      affinePoint (PolygonDrawing.vertexPoint (p u) (PolygonDrawing.arcSource (p u) x_u))
        (PolygonDrawing.vertexPoint (p u) (PolygonDrawing.arcTarget (p u) (hg u) x_u)) α =
      affinePoint (PolygonDrawing.vertexPoint (p u) (PolygonDrawing.arcSource (p u) y_u))
        (PolygonDrawing.vertexPoint (p u) (PolygonDrawing.arcTarget (p u) (hg u) y_u)) β := by
    simpa only [segPoint, segStart, segEnd, vtxPos, parentVertexEquiv_src₀,
      parentVertexEquiv_tgt₀, x_u, y_u, E_u] using heq
  have hα_end : α = 0 ∨ α = 1 := by
    by_contra hnot
    push_neg at hnot
    have hα0 : 0 < α := lt_of_le_of_ne hα.1 (Ne.symm hnot.1)
    have hα1 : α < 1 := lt_of_le_of_ne hα.2 hnot.2
    by_cases hβ0 : β = 0
    · subst hβ0
      rw [affinePoint_zero] at heq_u
      exact PolygonDrawing.vertices_avoid_arc_interiors (p u) (hg u)
        (PolygonDrawing.arcSource (p u) y_u) x_u α hα0 hα1 heq_u.symm
    · by_cases hβ1 : β = 1
      · subst hβ1
        rw [affinePoint_one] at heq_u
        exact PolygonDrawing.vertices_avoid_arc_interiors (p u) (hg u)
          (PolygonDrawing.arcTarget (p u) (hg u) y_u) x_u α hα0 hα1 heq_u.symm
      · have hβ0' : 0 < β := lt_of_le_of_ne hβ.1 (Ne.symm hβ0)
        have hβ1' : β < 1 := lt_of_le_of_ne hβ.2 hβ1
        exact PolygonDrawing.arc_interiors_disjoint (p u) (hg u) x_u y_u hxy_u
          α β hα0 hα1 hβ0' hβ1' heq_u
  have hβ_end : β = 0 ∨ β = 1 := by
    by_contra hnot
    push_neg at hnot
    have hβ0 : 0 < β := lt_of_le_of_ne hβ.1 (Ne.symm hnot.1)
    have hβ1 : β < 1 := lt_of_le_of_ne hβ.2 hnot.2
    rcases hα_end with rfl | rfl
    · rw [affinePoint_zero] at heq_u
      exact PolygonDrawing.vertices_avoid_arc_interiors (p u) (hg u)
        (PolygonDrawing.arcSource (p u) x_u) y_u β hβ0 hβ1 heq_u
    · rw [affinePoint_one] at heq_u
      exact PolygonDrawing.vertices_avoid_arc_interiors (p u) (hg u)
        (PolygonDrawing.arcTarget (p u) (hg u) x_u) y_u β hβ0 hβ1 heq_u
  exact ⟨hα_end, hβ_end⟩

/-- Orientation-selectable endpoint and parameter helpers for half-segment analysis. -/
noncomputable def endStart (x : Ev₀ p) (b : Bool) : Vtx₀ p :=
  if b then tgt₀ p hg x else src₀ p x

noncomputable def endOther (x : Ev₀ p) (b : Bool) : Vtx₀ p :=
  if b then src₀ p x else tgt₀ p hg x

def orientedParam (b : Bool) (t : ℝ) : ℝ :=
  if b then 1 - t else t

theorem orientedParam_mem_Icc (b : Bool) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    orientedParam b t ∈ Set.Icc (0 : ℝ) 1 := by
  cases b
  · change t ∈ Set.Icc (0 : ℝ) 1
    exact ⟨ht0, by linarith⟩
  · change 1 - t ∈ Set.Icc (0 : ℝ) 1
    exact ⟨by linarith, by linarith⟩

theorem orientedParam_end_iff_zero (b : Bool) {t : ℝ} (ht1 : t ≤ 1 / 2) :
    (orientedParam b t = 0 ∨ orientedParam b t = 1) ↔ t = 0 := by
  cases b
  · change (t = 0 ∨ t = 1) ↔ t = 0
    constructor
    · rintro (h | h) <;> linarith
    · intro h; exact Or.inl h
  · change (1 - t = 0 ∨ 1 - t = 1) ↔ t = 0
    constructor
    · rintro (h | h) <;> linarith
    · intro h; right; linarith

theorem segPoint_orientedParam_eq (u : Time) (x : Ev₀ p) (b : Bool) (t : ℝ) :
    segPoint p hp hg u x (orientedParam b t) =
      affinePoint (vtxPos p hp hg u (endStart p hg x b))
        (vtxPos p hp hg u (endOther p hg x b)) t := by
  cases b
  · rfl
  · change affinePoint (vtxPos p hp hg u (src₀ p x)) (vtxPos p hp hg u (tgt₀ p hg x)) (1 - t) =
      affinePoint (vtxPos p hp hg u (tgt₀ p hg x)) (vtxPos p hp hg u (src₀ p x)) t
    exact affinePoint_reverse (vtxPos p hp hg u (tgt₀ p hg x)) (vtxPos p hp hg u (src₀ p x)) t

theorem baryWeight_orientedParam_eq (v : Vtx₀ p) (x : Ev₀ p) (b : Bool) (t : ℝ) :
    baryWeight p hg v x (orientedParam b t) =
      (1 - t) * vtxIndicator p v (endStart p hg x b) +
        t * vtxIndicator p v (endOther p hg x b) := by
  cases b
  · rfl
  · change (1 - (1 - t)) * vtxIndicator p v (src₀ p x) +
        (1 - t) * vtxIndicator p v (tgt₀ p hg x) =
      (1 - t) * vtxIndicator p v (tgt₀ p hg x) +
        t * vtxIndicator p v (src₀ p x)
    ring

abbrev HalfIcc := Set.Icc (0 : ℝ) (1 / 2)

/-- Uniform Lipschitz bound on a pair of half-segments of distinct events `x ≠ y`. -/
theorem exists_half_segment_lipschitz (v : Vtx₀ p) {x y : Ev₀ p} (hxy : x ≠ y)
    (b₁ b₂ : Bool) :
    ∃ L : ℝ, 0 < L ∧ ∀ (u : Time) (t s : ℝ),
      0 ≤ t → t ≤ 1 / 2 → 0 ≤ s → s ≤ 1 / 2 →
      |baryWeight p hg v x (orientedParam b₁ t) -
          baryWeight p hg v y (orientedParam b₂ s)| ≤
        L * dist (segPoint p hp hg u x (orientedParam b₁ t))
          (segPoint p hp hg u y (orientedParam b₂ s)) := by
  have hmeet : ∀ (u : Time) (t s : ℝ),
      0 ≤ t → t ≤ 1 / 2 → 0 ≤ s → s ≤ 1 / 2 →
      segPoint p hp hg u x (orientedParam b₁ t) =
        segPoint p hp hg u y (orientedParam b₂ s) →
      t = 0 ∧ s = 0 ∧ endStart p hg x b₁ = endStart p hg y b₂ := by
    intro u t s ht0 ht1 hs0 hs1 heq
    have hends := segPoint_eq_endpoints_of_ne p hp hg u hxy
      (orientedParam_mem_Icc b₁ ht0 ht1) (orientedParam_mem_Icc b₂ hs0 hs1) heq
    have ht_zero : t = 0 := (orientedParam_end_iff_zero b₁ ht1).mp hends.1
    have hs_zero : s = 0 := (orientedParam_end_iff_zero b₂ hs1).mp hends.2
    subst ht_zero; subst hs_zero
    rw [segPoint_orientedParam_eq, segPoint_orientedParam_eq,
      affinePoint_zero, affinePoint_zero] at heq
    exact ⟨rfl, rfl, vtxPos_injective p hp hg u heq⟩
  by_cases hend : endStart p hg x b₁ = endStart p hg y b₂
  · let F : Time × HalfIcc → ℝ := fun q =>
      dist (segPoint p hp hg q.1 x (orientedParam b₁ q.2.val))
        (segPoint p hp hg q.1 y (orientedParam b₂ (1 / 2 - q.2.val)))
    have hF_cont : Continuous F := by
      have h1 : Continuous (fun q : Time × HalfIcc =>
          segPoint p hp hg q.1 x (orientedParam b₁ q.2.val)) := by
        simp only [segPoint_orientedParam_eq, affinePoint]
        have ha : Continuous (fun q : Time × HalfIcc => vtxPos p hp hg q.1 (endStart p hg x b₁)) :=
          (continuous_vtxPos p hp hg (endStart p hg x b₁)).comp continuous_fst
        have hb : Continuous (fun q : Time × HalfIcc => vtxPos p hp hg q.1 (endOther p hg x b₁)) :=
          (continuous_vtxPos p hp hg (endOther p hg x b₁)).comp continuous_fst
        have ht : Continuous (fun q : Time × HalfIcc => q.2.val) :=
          continuous_subtype_val.comp continuous_snd
        exact (ha.fst.add (ht.mul (hb.fst.sub ha.fst))).prodMk
          (ha.snd.add (ht.mul (hb.snd.sub ha.snd)))
      have h2 : Continuous (fun q : Time × HalfIcc =>
          segPoint p hp hg q.1 y (orientedParam b₂ (1 / 2 - q.2.val))) := by
        simp only [segPoint_orientedParam_eq, affinePoint]
        have ha : Continuous (fun q : Time × HalfIcc => vtxPos p hp hg q.1 (endStart p hg y b₂)) :=
          (continuous_vtxPos p hp hg (endStart p hg y b₂)).comp continuous_fst
        have hb : Continuous (fun q : Time × HalfIcc => vtxPos p hp hg q.1 (endOther p hg y b₂)) :=
          (continuous_vtxPos p hp hg (endOther p hg y b₂)).comp continuous_fst
        have ht : Continuous (fun q : Time × HalfIcc => (1 / 2 : ℝ) - q.2.val) :=
          continuous_const.sub (continuous_subtype_val.comp continuous_snd)
        exact (ha.fst.add (ht.mul (hb.fst.sub ha.fst))).prodMk
          (ha.snd.add (ht.mul (hb.snd.sub ha.snd)))
      exact h1.dist h2
    have hF_pos : ∀ q ∈ (Set.univ : Set (Time × HalfIcc)), 0 < F q := by
      rintro ⟨u, ⟨t, ht0, ht1⟩⟩ _
      dsimp [F]
      rw [dist_pos]
      intro heq
      have hm := hmeet u t (1 / 2 - t) ht0 ht1 (by linarith) (by linarith) heq
      linarith [hm.1, hm.2.1]
    obtain ⟨δ, hδ, hδ_le⟩ := isCompact_univ.exists_forall_le' hF_cont.continuousOn hF_pos
    refine ⟨1 / (2 * δ), div_pos one_pos (by linarith), ?_⟩
    intro u t s ht0 ht1 hs0 hs1
    have hweight :
        |baryWeight p hg v x (orientedParam b₁ t) -
          baryWeight p hg v y (orientedParam b₂ s)| ≤ t + s := by
      have h0 : baryWeight p hg v x (orientedParam b₁ 0) =
          baryWeight p hg v y (orientedParam b₂ 0) := by
        rw [baryWeight_orientedParam_eq, baryWeight_orientedParam_eq, hend]
        ring
      have htri :
          |baryWeight p hg v x (orientedParam b₁ t) -
            baryWeight p hg v y (orientedParam b₂ s)| ≤
          |baryWeight p hg v x (orientedParam b₁ t) -
            baryWeight p hg v x (orientedParam b₁ 0)| +
          |baryWeight p hg v y (orientedParam b₂ 0) -
            baryWeight p hg v y (orientedParam b₂ s)| := by
        rw [h0]
        exact abs_sub_le _ _ _
      have htx : |baryWeight p hg v x (orientedParam b₁ t) -
          baryWeight p hg v x (orientedParam b₁ 0)| ≤ t := by
        refine (abs_baryWeight_sub_le p hg v x _ _).trans ?_
        cases b₁
        · change |t - 0| ≤ t
          rw [sub_zero, abs_of_nonneg ht0]
        · change |(1 - t) - (1 - 0)| ≤ t
          have : (1 - t) - (1 - 0) = -t := by ring
          rw [this, abs_neg, abs_of_nonneg ht0]
      have hsy : |baryWeight p hg v y (orientedParam b₂ 0) -
          baryWeight p hg v y (orientedParam b₂ s)| ≤ s := by
        refine (abs_baryWeight_sub_le p hg v y _ _).trans ?_
        cases b₂
        · change |0 - s| ≤ s
          rw [zero_sub, abs_neg, abs_of_nonneg hs0]
        · change |(1 - 0) - (1 - s)| ≤ s
          have : (1 - 0) - (1 - s) = s := by ring
          rw [this, abs_of_nonneg hs0]
      linarith
    by_cases hts : t + s = 0
    · have ht_z : t = 0 := by linarith
      have hs_z : s = 0 := by linarith
      have hw0 : |baryWeight p hg v x (orientedParam b₁ t) -
          baryWeight p hg v y (orientedParam b₂ s)| ≤ 0 := by linarith
      have hrhs : 0 ≤ (1 / (2 * δ)) *
          dist (segPoint p hp hg u x (orientedParam b₁ t))
            (segPoint p hp hg u y (orientedParam b₂ s)) :=
        mul_nonneg (by positivity) dist_nonneg
      linarith
    · have hts_pos : 0 < t + s := lt_of_le_of_ne (add_nonneg ht0 hs0) (Ne.symm hts)
      let r : ℝ := 2 * (t + s)
      have hr_pos : 0 < r := by dsimp [r]; linarith
      let t_hat : ℝ := t / r
      have hthat0 : 0 ≤ t_hat := div_nonneg ht0 (le_of_lt hr_pos)
      have hthat1 : t_hat ≤ 1 / 2 := by
        change t / r ≤ 1 / 2
        rw [div_le_iff₀ hr_pos]
        dsimp [r]
        linarith
      have hshat : 1 / 2 - t_hat = s / r := by
        dsimp [t_hat, r]
        field_simp [ne_of_gt hr_pos]
      have hscale :
          dist (segPoint p hp hg u x (orientedParam b₁ t))
            (segPoint p hp hg u y (orientedParam b₂ s)) =
          r * F (u, ⟨t_hat, hthat0, hthat1⟩) := by
        dsimp [F]
        simp only [segPoint_orientedParam_eq, hend]
        rw [plane_dist_eq, plane_dist_eq]
        have ht_eq : t = r * t_hat := (mul_div_cancel₀ t (ne_of_gt hr_pos)).symm
        have hs_eq : s = r * (1 / 2 - t_hat) := by
          rw [hshat]
          exact (mul_div_cancel₀ s (ne_of_gt hr_pos)).symm
        have h1 :
            (affinePoint (vtxPos p hp hg u (endStart p hg y b₂))
              (vtxPos p hp hg u (endOther p hg x b₁)) t).1 -
            (affinePoint (vtxPos p hp hg u (endStart p hg y b₂))
              (vtxPos p hp hg u (endOther p hg y b₂)) s).1 =
            r * ((affinePoint (vtxPos p hp hg u (endStart p hg y b₂))
              (vtxPos p hp hg u (endOther p hg x b₁)) t_hat).1 -
            (affinePoint (vtxPos p hp hg u (endStart p hg y b₂))
              (vtxPos p hp hg u (endOther p hg y b₂)) (1 / 2 - t_hat)).1) := by
          conv_lhs => rw [ht_eq, hs_eq]
          dsimp [affinePoint]
          ring
        have h2 :
            (affinePoint (vtxPos p hp hg u (endStart p hg y b₂))
              (vtxPos p hp hg u (endOther p hg x b₁)) t).2 -
            (affinePoint (vtxPos p hp hg u (endStart p hg y b₂))
              (vtxPos p hp hg u (endOther p hg y b₂)) s).2 =
            r * ((affinePoint (vtxPos p hp hg u (endStart p hg y b₂))
              (vtxPos p hp hg u (endOther p hg x b₁)) t_hat).2 -
            (affinePoint (vtxPos p hp hg u (endStart p hg y b₂))
              (vtxPos p hp hg u (endOther p hg y b₂)) (1 / 2 - t_hat)).2) := by
          conv_lhs => rw [ht_eq, hs_eq]
          dsimp [affinePoint]
          ring
        have hpos_r : |r| = r := abs_of_pos hr_pos
        rw [h1, h2, abs_mul r, abs_mul r, hpos_r,
          ← mul_max_of_nonneg _ _ (le_of_lt hr_pos)]
      have hlow : δ ≤ F (u, ⟨t_hat, hthat0, hthat1⟩) :=
        hδ_le (u, ⟨t_hat, hthat0, hthat1⟩) (Set.mem_univ _)
      have hdist_low : 2 * (t + s) * δ ≤
          dist (segPoint p hp hg u x (orientedParam b₁ t))
            (segPoint p hp hg u y (orientedParam b₂ s)) := by
        rw [hscale]
        exact mul_le_mul_of_nonneg_left hlow (le_of_lt hr_pos)
      calc
        |baryWeight p hg v x (orientedParam b₁ t) -
            baryWeight p hg v y (orientedParam b₂ s)|
            ≤ t + s := hweight
        _ = (1 / (2 * δ)) * (2 * (t + s) * δ) := by
          field_simp [ne_of_gt hδ]
          ring
        _ ≤ (1 / (2 * δ)) *
            dist (segPoint p hp hg u x (orientedParam b₁ t))
              (segPoint p hp hg u y (orientedParam b₂ s)) :=
          mul_le_mul_of_nonneg_left hdist_low (by positivity)
  · let G : Time × HalfIcc × HalfIcc → ℝ := fun q =>
      dist (segPoint p hp hg q.1 x (orientedParam b₁ q.2.1.val))
        (segPoint p hp hg q.1 y (orientedParam b₂ q.2.2.val))
    have hG_cont : Continuous G := by
      have h1 : Continuous (fun q : Time × HalfIcc × HalfIcc =>
          segPoint p hp hg q.1 x (orientedParam b₁ q.2.1.val)) := by
        simp only [segPoint_orientedParam_eq, affinePoint]
        have ha : Continuous (fun q : Time × HalfIcc × HalfIcc =>
            vtxPos p hp hg q.1 (endStart p hg x b₁)) :=
          (continuous_vtxPos p hp hg (endStart p hg x b₁)).comp continuous_fst
        have hb : Continuous (fun q : Time × HalfIcc × HalfIcc =>
            vtxPos p hp hg q.1 (endOther p hg x b₁)) :=
          (continuous_vtxPos p hp hg (endOther p hg x b₁)).comp continuous_fst
        have ht : Continuous (fun q : Time × HalfIcc × HalfIcc => q.2.1.val) :=
          continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
        exact (ha.fst.add (ht.mul (hb.fst.sub ha.fst))).prodMk
          (ha.snd.add (ht.mul (hb.snd.sub ha.snd)))
      have h2 : Continuous (fun q : Time × HalfIcc × HalfIcc =>
          segPoint p hp hg q.1 y (orientedParam b₂ q.2.2.val)) := by
        simp only [segPoint_orientedParam_eq, affinePoint]
        have ha : Continuous (fun q : Time × HalfIcc × HalfIcc =>
            vtxPos p hp hg q.1 (endStart p hg y b₂)) :=
          (continuous_vtxPos p hp hg (endStart p hg y b₂)).comp continuous_fst
        have hb : Continuous (fun q : Time × HalfIcc × HalfIcc =>
            vtxPos p hp hg q.1 (endOther p hg y b₂)) :=
          (continuous_vtxPos p hp hg (endOther p hg y b₂)).comp continuous_fst
        have ht : Continuous (fun q : Time × HalfIcc × HalfIcc => q.2.2.val) :=
          continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
        exact (ha.fst.add (ht.mul (hb.fst.sub ha.fst))).prodMk
          (ha.snd.add (ht.mul (hb.snd.sub ha.snd)))
      exact h1.dist h2
    have hG_pos : ∀ q ∈ (Set.univ : Set (Time × HalfIcc × HalfIcc)), 0 < G q := by
      rintro ⟨u, ⟨t, ht0, ht1⟩, ⟨s, hs0, hs1⟩⟩ _
      dsimp [G]
      rw [dist_pos]
      intro heq
      exact hend (hmeet u t s ht0 ht1 hs0 hs1 heq).2.2
    obtain ⟨δ, hδ, hδ_le⟩ := isCompact_univ.exists_forall_le' hG_cont.continuousOn hG_pos
    refine ⟨1 / δ, div_pos one_pos hδ, ?_⟩
    intro u t s ht0 ht1 hs0 hs1
    have hlow : δ ≤ dist (segPoint p hp hg u x (orientedParam b₁ t))
        (segPoint p hp hg u y (orientedParam b₂ s)) :=
      hδ_le (u, ⟨t, ht0, ht1⟩, ⟨s, hs0, hs1⟩) (Set.mem_univ _)
    have hw_le_one :
        |baryWeight p hg v x (orientedParam b₁ t) -
          baryWeight p hg v y (orientedParam b₂ s)| ≤ 1 := by
      rw [abs_le]
      have hx0 := baryWeight_nonneg p hg v x (orientedParam_mem_Icc b₁ ht0 ht1)
      have hx1 := baryWeight_le_one p hg v x (orientedParam_mem_Icc b₁ ht0 ht1)
      have hy0 := baryWeight_nonneg p hg v y (orientedParam_mem_Icc b₂ hs0 hs1)
      have hy1 := baryWeight_le_one p hg v y (orientedParam_mem_Icc b₂ hs0 hs1)
      constructor <;> linarith
    calc
      |baryWeight p hg v x (orientedParam b₁ t) -
          baryWeight p hg v y (orientedParam b₂ s)|
          ≤ 1 := hw_le_one
      _ = (1 / δ) * δ := (one_div_mul_cancel (ne_of_gt hδ)).symm
      _ ≤ (1 / δ) * dist (segPoint p hp hg u x (orientedParam b₁ t))
            (segPoint p hp hg u y (orientedParam b₂ s)) :=
        mul_le_mul_of_nonneg_left hlow (by positivity)

/-- Uniform Lipschitz bound for a pair of event segments `(x, y)` and vertex `v`. -/
theorem exists_pair_barycentric_lipschitz (v : Vtx₀ p) (x y : Ev₀ p) :
    ∃ L : ℝ, 0 < L ∧ ∀ (u : Time) (α β : ℝ),
      α ∈ Set.Icc (0 : ℝ) 1 → β ∈ Set.Icc (0 : ℝ) 1 →
      |baryWeight p hg v x α - baryWeight p hg v y β| ≤
        L * dist (segPoint p hp hg u x α) (segPoint p hp hg u y β) := by
  by_cases hxy : x = y
  · subst hxy
    let D : Time → ℝ := fun u => dist (segStart p hp hg u x) (segEnd p hp hg u x)
    have hD_cont : Continuous D :=
      (continuous_segStart p hp hg x).dist (continuous_segEnd p hp hg x)
    have hD_pos : ∀ u ∈ (Set.univ : Set Time), 0 < D u :=
      fun u _ => dist_pos.mpr (segStart_ne_segEnd p hp hg u x)
    obtain ⟨δ, hδ, hδ_le⟩ := isCompact_univ.exists_forall_le' hD_cont.continuousOn hD_pos
    refine ⟨1 / δ, div_pos one_pos hδ, ?_⟩
    intro u α β _ _
    have hlow : δ ≤ dist (segStart p hp hg u x) (segEnd p hp hg u x) :=
      hδ_le u (Set.mem_univ _)
    calc
      |baryWeight p hg v x α - baryWeight p hg v x β|
          ≤ |α - β| := abs_baryWeight_sub_le p hg v x α β
      _ = (1 / δ) * (|α - β| * δ) := by
        field_simp [ne_of_gt hδ]
      _ ≤ (1 / δ) * (|α - β| * dist (segStart p hp hg u x) (segEnd p hp hg u x)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hlow (abs_nonneg _)) (by positivity)
      _ = (1 / δ) * dist (segPoint p hp hg u x α) (segPoint p hp hg u x β) := by
        unfold segPoint
        rw [dist_affinePoint_sub]
  · obtain ⟨L₀₀, hL₀₀, h₀₀⟩ := exists_half_segment_lipschitz p hp hg v hxy false false
    obtain ⟨L₀₁, hL₀₁, h₀₁⟩ := exists_half_segment_lipschitz p hp hg v hxy false true
    obtain ⟨L₁₀, hL₁₀, h₁₀⟩ := exists_half_segment_lipschitz p hp hg v hxy true false
    obtain ⟨L₁₁, hL₁₁, h₁₁⟩ := exists_half_segment_lipschitz p hp hg v hxy true true
    let L := max (max L₀₀ L₀₁) (max L₁₀ L₁₁)
    have hL : 0 < L := lt_max_of_lt_left (lt_max_of_lt_left hL₀₀)
    have hle00 : L₀₀ ≤ L := (le_max_left L₀₀ L₀₁).trans (le_max_left _ _)
    have hle01 : L₀₁ ≤ L := (le_max_right L₀₀ L₀₁).trans (le_max_left _ _)
    have hle10 : L₁₀ ≤ L := (le_max_left L₁₀ L₁₁).trans (le_max_right _ _)
    have hle11 : L₁₁ ≤ L := (le_max_right L₁₀ L₁₁).trans (le_max_right _ _)
    refine ⟨L, hL, ?_⟩
    intro u α β hα hβ
    by_cases hα_half : α ≤ 1 / 2 <;> by_cases hβ_half : β ≤ 1 / 2
    · have h := h₀₀ u α β hα.1 hα_half hβ.1 hβ_half
      exact h.trans (mul_le_mul_of_nonneg_right hle00 dist_nonneg)
    · have h := h₀₁ u α (1 - β) hα.1 hα_half (by linarith [hβ.2]) (by linarith)
      have hβ' : orientedParam true (1 - β) = β := by change 1 - (1 - β) = β; ring
      rw [hβ'] at h
      exact h.trans (mul_le_mul_of_nonneg_right hle01 dist_nonneg)
    · have h := h₁₀ u (1 - α) β (by linarith [hα.2]) (by linarith) hβ.1 hβ_half
      have hα' : orientedParam true (1 - α) = α := by change 1 - (1 - α) = α; ring
      rw [hα'] at h
      exact h.trans (mul_le_mul_of_nonneg_right hle10 dist_nonneg)
    · have h := h₁₁ u (1 - α) (1 - β)
        (by linarith [hα.2]) (by linarith) (by linarith [hβ.2]) (by linarith)
      have hα' : orientedParam true (1 - α) = α := by change 1 - (1 - α) = α; ring
      have hβ' : orientedParam true (1 - β) = β := by change 1 - (1 - β) = β; ring
      rw [hα', hβ'] at h
      exact h.trans (mul_le_mul_of_nonneg_right hle11 dist_nonneg)

/-- Global uniform Lipschitz bound across all `u : Time`, `v : Vtx₀`, and `x, y : Ev₀`. -/
theorem exists_uniform_barycentric_lipschitz :
    ∃ L : ℝ, 0 < L ∧ ∀ (u : Time) (v : Vtx₀ p) (x y : Ev₀ p) (α β : ℝ),
      α ∈ Set.Icc (0 : ℝ) 1 → β ∈ Set.Icc (0 : ℝ) 1 →
      |baryWeight p hg v x α - baryWeight p hg v y β| ≤
        L * dist (segPoint p hp hg u x α) (segPoint p hp hg u y β) := by
  let L_pair : Vtx₀ p × Ev₀ p × Ev₀ p → ℝ := fun q =>
    Classical.choose (exists_pair_barycentric_lipschitz p hp hg q.1 q.2.1 q.2.2)
  have h_spec : ∀ q : Vtx₀ p × Ev₀ p × Ev₀ p,
      0 < L_pair q ∧ ∀ (u : Time) (α β : ℝ),
        α ∈ Set.Icc (0 : ℝ) 1 → β ∈ Set.Icc (0 : ℝ) 1 →
        |baryWeight p hg q.1 q.2.1 α - baryWeight p hg q.1 q.2.2 β| ≤
          L_pair q * dist (segPoint p hp hg u q.2.1 α) (segPoint p hp hg u q.2.2 β) :=
    fun q => Classical.choose_spec (exists_pair_barycentric_lipschitz p hp hg q.1 q.2.1 q.2.2)
  let L : ℝ := 1 + finsetMaxZero Finset.univ L_pair
  have hL_pos : 0 < L := by
    have : 0 ≤ finsetMaxZero Finset.univ L_pair := zero_le_finsetMaxZero _ _
    dsimp [L]
    linarith
  refine ⟨L, hL_pos, ?_⟩
  intro u v x y α β hα hβ
  have hle : L_pair (v, x, y) ≤ L := by
    have := le_finsetMaxZero Finset.univ L_pair (Finset.mem_univ (v, x, y))
    dsimp [L]
    linarith
  exact ((h_spec (v, x, y)).2 u α β hα hβ).trans
    (mul_le_mul_of_nonneg_right hle dist_nonneg)

end EventGraphGeometry

section McShaneTransitionAndFullGeometry

variable {n : ℕ} (p : Time → Fin n → Plane) (hp : Continuous p) (hg : ∀ t, CyclicGeneric (p t))

/-- Clamped projection parameter of `z` onto event segment `x` at time `u`. -/
noncomputable def segProjParam (u : Time) (x : Ev₀ p) (z : Plane) : ℝ :=
  projParam (segStart p hp hg u x) (segEnd p hp hg u x) z

/-- Clamped projection point of `z` onto event segment `x` at time `u`. -/
noncomputable def segProjPoint (u : Time) (x : Ev₀ p) (z : Plane) : Plane :=
  projPoint (segStart p hp hg u x) (segEnd p hp hg u x) z

theorem segProjParam_mem_Icc (u : Time) (x : Ev₀ p) (z : Plane) :
    segProjParam p hp hg u x z ∈ Set.Icc (0 : ℝ) 1 :=
  projParam_mem_Icc _ _ _

theorem segProjPoint_eq_segPoint (u : Time) (x : Ev₀ p) (z : Plane) :
    segProjPoint p hp hg u x z = segPoint p hp hg u x (segProjParam p hp hg u x z) := rfl

theorem segProjParam_segPoint (u : Time) (x : Ev₀ p) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    segProjParam p hp hg u x (segPoint p hp hg u x α) = α :=
  projParam_affinePoint (segStart_ne_segEnd p hp hg u x) hα

theorem segProjPoint_segPoint (u : Time) (x : Ev₀ p) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    segProjPoint p hp hg u x (segPoint p hp hg u x α) = segPoint p hp hg u x α := by
  rw [segProjPoint_eq_segPoint, segProjParam_segPoint p hp hg u x hα]

theorem continuous_segProjParam (x : Ev₀ p) :
    Continuous (fun q : Time × Plane => segProjParam p hp hg q.1 x q.2) := by
  unfold segProjParam projParam rawProjParam
  apply continuous_clamp01.comp
  have ha : Continuous (fun q : Time × Plane => segStart p hp hg q.1 x) :=
    (continuous_segStart p hp hg x).comp continuous_fst
  have hb : Continuous (fun q : Time × Plane => segEnd p hp hg q.1 x) :=
    (continuous_segEnd p hp hg x).comp continuous_fst
  have hz : Continuous (fun q : Time × Plane => q.2) := continuous_snd
  have hnum : Continuous (fun q : Time × Plane =>
      ((q.2.1 - (segStart p hp hg q.1 x).1) *
        ((segEnd p hp hg q.1 x).1 - (segStart p hp hg q.1 x).1) +
      (q.2.2 - (segStart p hp hg q.1 x).2) *
        ((segEnd p hp hg q.1 x).2 - (segStart p hp hg q.1 x).2))) :=
    ((hz.fst.sub ha.fst).mul (hb.fst.sub ha.fst)).add
      ((hz.snd.sub ha.snd).mul (hb.snd.sub ha.snd))
  have hden : Continuous (fun q : Time × Plane =>
      segLenSq (segStart p hp hg q.1 x) (segEnd p hp hg q.1 x)) :=
    ((hb.fst.sub ha.fst).pow 2).add ((hb.snd.sub ha.snd).pow 2)
  exact hnum.div hden (fun q => ne_of_gt (segLenSq_pos_of_ne (segStart_ne_segEnd p hp hg q.1 x)))

theorem continuous_segProjPoint (x : Ev₀ p) :
    Continuous (fun q : Time × Plane => segProjPoint p hp hg q.1 x q.2) := by
  unfold segProjPoint projPoint affinePoint
  have ha : Continuous (fun q : Time × Plane => segStart p hp hg q.1 x) :=
    (continuous_segStart p hp hg x).comp continuous_fst
  have hb : Continuous (fun q : Time × Plane => segEnd p hp hg q.1 x) :=
    (continuous_segEnd p hp hg x).comp continuous_fst
  have ht := continuous_segProjParam p hp hg x
  exact (ha.fst.add (ht.mul (hb.fst.sub ha.fst))).prodMk
    (ha.snd.add (ht.mul (hb.snd.sub ha.snd)))

/-- Single-segment branch of the McShane extension for vertex `v` and segment `x`. -/
noncomputable def mcshaneBranch (L : ℝ) (v : Vtx₀ p) (x : Ev₀ p) (u : Time) (z : Plane) : ℝ :=
  baryWeight p hg v x (segProjParam p hp hg u x z) -
    L * dist z (segProjPoint p hp hg u x z)

theorem continuous_mcshaneBranch (L : ℝ) (v : Vtx₀ p) (x : Ev₀ p) :
    Continuous (fun q : Time × Plane => mcshaneBranch p hp hg L v x q.1 q.2) := by
  unfold mcshaneBranch baryWeight
  have ht := continuous_segProjParam p hp hg x
  have hpt := continuous_segProjPoint p hp hg x
  have h1 : Continuous (fun q : Time × Plane =>
      (1 - segProjParam p hp hg q.1 x q.2) * vtxIndicator p v (src₀ p x) +
        segProjParam p hp hg q.1 x q.2 * vtxIndicator p v (tgt₀ p hg x)) :=
    ((continuous_const.sub ht).mul continuous_const).add (ht.mul continuous_const)
  exact h1.sub (continuous_const.mul (continuous_snd.dist hpt))

theorem abs_mcshaneBranch_sub_le (L : ℝ) (hL_pos : 0 ≤ L)
    (hL_lip : ∀ (u : Time) (v : Vtx₀ p) (x y : Ev₀ p) (α β : ℝ),
      α ∈ Set.Icc (0 : ℝ) 1 → β ∈ Set.Icc (0 : ℝ) 1 →
      |baryWeight p hg v x α - baryWeight p hg v y β| ≤
        L * dist (segPoint p hp hg u x α) (segPoint p hp hg u y β))
    (v : Vtx₀ p) (x : Ev₀ p) (u : Time) (z w : Plane) :
    |mcshaneBranch p hp hg L v x u z - mcshaneBranch p hp hg L v x u w| ≤
      5 * L * dist z w := by
  let α := segProjParam p hp hg u x z
  let β := segProjParam p hp hg u x w
  have hα : α ∈ Set.Icc (0 : ℝ) 1 := segProjParam_mem_Icc p hp hg u x z
  have hβ : β ∈ Set.Icc (0 : ℝ) 1 := segProjParam_mem_Icc p hp hg u x w
  have hbary : |baryWeight p hg v x α - baryWeight p hg v x β| ≤
      L * dist (segProjPoint p hp hg u x z) (segProjPoint p hp hg u x w) :=
    hL_lip u v x x α β hα hβ
  have hproj : dist (segProjPoint p hp hg u x z) (segProjPoint p hp hg u x w) ≤ 2 * dist z w :=
    dist_projPoint_le_two_mul_dist (segStart p hp hg u x) (segEnd p hp hg u x) z w
  have hdist_diff :
      |dist z (segProjPoint p hp hg u x z) - dist w (segProjPoint p hp hg u x w)| ≤
        dist z w + dist (segProjPoint p hp hg u x z) (segProjPoint p hp hg u x w) := by
    rw [abs_le]
    have h1 := dist_triangle4 z w (segProjPoint p hp hg u x w) (segProjPoint p hp hg u x z)
    have h2 := dist_triangle4 w z (segProjPoint p hp hg u x z) (segProjPoint p hp hg u x w)
    rw [dist_comm (segProjPoint p hp hg u x w) (segProjPoint p hp hg u x z)] at h1
    rw [dist_comm w z] at h2
    constructor <;> linarith
  have hsplit :
      mcshaneBranch p hp hg L v x u z - mcshaneBranch p hp hg L v x u w =
        (baryWeight p hg v x α - baryWeight p hg v x β) -
          L * (dist z (segProjPoint p hp hg u x z) - dist w (segProjPoint p hp hg u x w)) := by
    dsimp [mcshaneBranch, α, β]; ring
  calc
    |mcshaneBranch p hp hg L v x u z - mcshaneBranch p hp hg L v x u w|
        ≤ |baryWeight p hg v x α - baryWeight p hg v x β| +
            |L * (dist z (segProjPoint p hp hg u x z) - dist w (segProjPoint p hp hg u x w))| := by
          rw [hsplit]
          exact abs_sub _ _
    _ = |baryWeight p hg v x α - baryWeight p hg v x β| +
          L * |dist z (segProjPoint p hp hg u x z) - dist w (segProjPoint p hp hg u x w)| := by
        rw [abs_mul, abs_of_nonneg hL_pos]
    _ ≤ L * dist (segProjPoint p hp hg u x z) (segProjPoint p hp hg u x w) +
          L * (dist z w + dist (segProjPoint p hp hg u x z) (segProjPoint p hp hg u x w)) :=
        add_le_add hbary (mul_le_mul_of_nonneg_left hdist_diff hL_pos)
    _ ≤ 5 * L * dist z w := by nlinarith

/-- Finite-max McShane weight for vertex `v` at time `u` and plane point `z`. -/
noncomputable def mcshaneWeight (L : ℝ) (v : Vtx₀ p) (u : Time) (z : Plane) : ℝ :=
  finsetMaxZero Finset.univ (fun x : Ev₀ p => mcshaneBranch p hp hg L v x u z)

theorem continuous_mcshaneWeight (L : ℝ) (v : Vtx₀ p) :
    Continuous (fun q : Time × Plane => mcshaneWeight p hp hg L v q.1 q.2) :=
  continuous_finsetMaxZero Finset.univ
    (fun x (q : Time × Plane) => mcshaneBranch p hp hg L v x q.1 q.2)
    (fun x _ => continuous_mcshaneBranch p hp hg L v x)

theorem abs_mcshaneWeight_sub_le (L : ℝ) (hL_pos : 0 ≤ L)
    (hL_lip : ∀ (u : Time) (v : Vtx₀ p) (x y : Ev₀ p) (α β : ℝ),
      α ∈ Set.Icc (0 : ℝ) 1 → β ∈ Set.Icc (0 : ℝ) 1 →
      |baryWeight p hg v x α - baryWeight p hg v y β| ≤
        L * dist (segPoint p hp hg u x α) (segPoint p hp hg u y β))
    (v : Vtx₀ p) (u : Time) (z w : Plane) :
    |mcshaneWeight p hp hg L v u z - mcshaneWeight p hp hg L v u w| ≤
      5 * L * dist z w := by
  refine abs_finsetMaxZero_sub_le Finset.univ _ _ (by positivity) ?_
  intro x _
  exact abs_mcshaneBranch_sub_le p hp hg L hL_pos hL_lip v x u z w

theorem mcshaneWeight_segPoint (L : ℝ)
    (hL_lip : ∀ (u : Time) (v : Vtx₀ p) (x y : Ev₀ p) (α β : ℝ),
      α ∈ Set.Icc (0 : ℝ) 1 → β ∈ Set.Icc (0 : ℝ) 1 →
      |baryWeight p hg v x α - baryWeight p hg v y β| ≤
        L * dist (segPoint p hp hg u x α) (segPoint p hp hg u y β))
    (v : Vtx₀ p) (u : Time) (y : Ev₀ p) {β : ℝ} (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    mcshaneWeight p hp hg L v u (segPoint p hp hg u y β) = baryWeight p hg v y β := by
  let z := segPoint p hp hg u y β
  apply le_antisymm
  · refine finsetMaxZero_le Finset.univ _ (baryWeight_nonneg p hg v y hβ) ?_
    intro x _
    let α := segProjParam p hp hg u x z
    have hα : α ∈ Set.Icc (0 : ℝ) 1 := segProjParam_mem_Icc p hp hg u x z
    have hlip := hL_lip u v x y α β hα hβ
    have hle : baryWeight p hg v x α - baryWeight p hg v y β ≤
        L * dist z (segProjPoint p hp hg u x z) := by
      rw [dist_comm z, segProjPoint_eq_segPoint]
      exact (le_abs_self _).trans hlip
    dsimp [mcshaneBranch, z]
    linarith
  · have hself : mcshaneBranch p hp hg L v y u z = baryWeight p hg v y β := by
      dsimp [mcshaneBranch, z]
      rw [segProjParam_segPoint p hp hg u y hβ, segProjPoint_segPoint p hp hg u y hβ,
        dist_self, mul_zero, sub_zero]
    rw [← hself]
    exact le_finsetMaxZero Finset.univ
      (fun x : Ev₀ p => mcshaneBranch p hp hg L v x u z)
      (Finset.mem_univ y)

attribute [irreducible] mcshaneWeight vtxPos

/-- Transition perturbation between two time-schedules `τ₁, τ₂ : Time → Time`. -/
noncomputable def transitionPerturbation (L : ℝ) (τ₁ τ₂ : Time → Time) (t : Time) (z : Plane) :
    Plane :=
  ∑ v : Vtx₀ p,
    mcshaneWeight p hp hg L v (τ₁ t) z •
      (vtxPos p hp hg (τ₂ t) v - vtxPos p hp hg (τ₁ t) v)

theorem continuous_plane_add {X : Type*} [TopologicalSpace X]
    {f g : X → Plane} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x + g x) :=
  (hf.fst.add hg.fst).prodMk (hf.snd.add hg.snd)

theorem continuous_plane_sub {X : Type*} [TopologicalSpace X]
    {f g : X → Plane} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x - g x) :=
  (hf.fst.sub hg.fst).prodMk (hf.snd.sub hg.snd)

theorem continuous_plane_smul {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {g : X → Plane} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x • g x) :=
  (hf.mul hg.fst).prodMk (hf.mul hg.snd)

theorem continuous_plane_finset_sum {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (f : ι → X → Plane) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (continuous_const : Continuous (fun _ : X => (0 : Plane)))
  | @insert a s ha ih =>
    have heq : (fun x => ∑ i ∈ insert a s, f i x) =
        (fun x => f a x + ∑ i ∈ s, f i x) := by
      funext x
      exact Finset.sum_insert ha
    rw [heq]
    exact continuous_plane_add (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem continuous_transitionPerturbation (L : ℝ) {τ₁ τ₂ : Time → Time}
    (hτ₁ : Continuous τ₁) (hτ₂ : Continuous τ₂) :
    Continuous (fun q : Time × Plane => transitionPerturbation p hp hg L τ₁ τ₂ q.1 q.2) := by
  unfold transitionPerturbation
  exact continuous_plane_finset_sum Finset.univ
    (fun (v : Vtx₀ p) (q : Time × Plane) =>
      mcshaneWeight p hp hg L v (τ₁ q.1) q.2 •
        (vtxPos p hp hg (τ₂ q.1) v - vtxPos p hp hg (τ₁ q.1) v))
    (fun v _ => by
      have hw : Continuous (fun q : Time × Plane => mcshaneWeight p hp hg L v (τ₁ q.1) q.2) :=
        (continuous_mcshaneWeight p hp hg L v).comp ((hτ₁.comp continuous_fst).prodMk continuous_snd)
      have hv2 : Continuous (fun q : Time × Plane => vtxPos p hp hg (τ₂ q.1) v) :=
        (continuous_vtxPos p hp hg v).comp (hτ₂.comp continuous_fst)
      have hv1 : Continuous (fun q : Time × Plane => vtxPos p hp hg (τ₁ q.1) v) :=
        (continuous_vtxPos p hp hg v).comp (hτ₁.comp continuous_fst)
      exact continuous_plane_smul hw (continuous_plane_sub hv2 hv1))

theorem transitionPerturbation_eq_zero_of_eq (L : ℝ) (τ₁ τ₂ : Time → Time) (t : Time)
    (ht : τ₁ t = τ₂ t) (z : Plane) :
    transitionPerturbation p hp hg L τ₁ τ₂ t z = 0 := by
  unfold transitionPerturbation
  rw [ht]
  simp

theorem transitionPerturbation_segPoint (L : ℝ)
    (hL_lip : ∀ (u : Time) (v : Vtx₀ p) (x y : Ev₀ p) (α β : ℝ),
      α ∈ Set.Icc (0 : ℝ) 1 → β ∈ Set.Icc (0 : ℝ) 1 →
      |baryWeight p hg v x α - baryWeight p hg v y β| ≤
        L * dist (segPoint p hp hg u x α) (segPoint p hp hg u y β))
    (τ₁ τ₂ : Time → Time) (t : Time) (x : Ev₀ p) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    segPoint p hp hg (τ₁ t) x α +
        transitionPerturbation p hp hg L τ₁ τ₂ t (segPoint p hp hg (τ₁ t) x α) =
      segPoint p hp hg (τ₂ t) x α := by
  have hsum :
      transitionPerturbation p hp hg L τ₁ τ₂ t (segPoint p hp hg (τ₁ t) x α) =
        (1 - α) • (segStart p hp hg (τ₂ t) x - segStart p hp hg (τ₁ t) x) +
          α • (segEnd p hp hg (τ₂ t) x - segEnd p hp hg (τ₁ t) x) := by
    unfold transitionPerturbation
    have hcongr : ∀ v : Vtx₀ p,
        mcshaneWeight p hp hg L v (τ₁ t) (segPoint p hp hg (τ₁ t) x α) •
          (vtxPos p hp hg (τ₂ t) v - vtxPos p hp hg (τ₁ t) v) =
        ((1 - α) * vtxIndicator p v (src₀ p x)) •
          (vtxPos p hp hg (τ₂ t) v - vtxPos p hp hg (τ₁ t) v) +
        (α * vtxIndicator p v (tgt₀ p hg x)) •
          (vtxPos p hp hg (τ₂ t) v - vtxPos p hp hg (τ₁ t) v) := by
      intro v
      rw [mcshaneWeight_segPoint p hp hg L hL_lip v (τ₁ t) x hα, baryWeight, add_smul]
    simp_rw [hcongr]
    rw [Finset.sum_add_distrib]
    have h1 :
        ∑ v : Vtx₀ p,
          ((1 - α) * vtxIndicator p v (src₀ p x)) •
            (vtxPos p hp hg (τ₂ t) v - vtxPos p hp hg (τ₁ t) v) =
        (1 - α) • (segStart p hp hg (τ₂ t) x - segStart p hp hg (τ₁ t) x) := by
      have heq : ∀ v : Vtx₀ p,
          ((1 - α) * vtxIndicator p v (src₀ p x)) •
            (vtxPos p hp hg (τ₂ t) v - vtxPos p hp hg (τ₁ t) v) =
          if v = src₀ p x then
            (1 - α) • (vtxPos p hp hg (τ₂ t) v - vtxPos p hp hg (τ₁ t) v)
          else 0 := by
        intro v
        unfold vtxIndicator
        by_cases hv : src₀ p x = v
        · subst hv; simp
        · have hv' : v ≠ src₀ p x := Ne.symm hv
          simp [hv, hv']
      simp_rw [heq]
      rw [Finset.sum_ite_eq' Finset.univ (src₀ p x)]
      simp [segStart]
    have h2 :
        ∑ v : Vtx₀ p,
          (α * vtxIndicator p v (tgt₀ p hg x)) •
            (vtxPos p hp hg (τ₂ t) v - vtxPos p hp hg (τ₁ t) v) =
        α • (segEnd p hp hg (τ₂ t) x - segEnd p hp hg (τ₁ t) x) := by
      have heq : ∀ v : Vtx₀ p,
          (α * vtxIndicator p v (tgt₀ p hg x)) •
            (vtxPos p hp hg (τ₂ t) v - vtxPos p hp hg (τ₁ t) v) =
          if v = tgt₀ p hg x then
            α • (vtxPos p hp hg (τ₂ t) v - vtxPos p hp hg (τ₁ t) v)
          else 0 := by
        intro v
        unfold vtxIndicator
        by_cases hv : tgt₀ p hg x = v
        · subst hv; simp
        · have hv' : v ≠ tgt₀ p hg x := Ne.symm hv
          simp [hv, hv']
      simp_rw [heq]
      rw [Finset.sum_ite_eq' Finset.univ (tgt₀ p hg x)]
      simp [segEnd]
    rw [h1, h2]
  rw [hsum]
  ext <;> simp [segPoint, affinePoint, smul_eq_mul] <;> ring

theorem plane_dist_sum_le {ι : Type*} (s : Finset ι) (f g : ι → Plane) :
    dist (∑ i ∈ s, f i) (∑ i ∈ s, g i) ≤ ∑ i ∈ s, dist (f i) (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact (plane_dist_add_le (f a) (∑ i ∈ s, f i) (g a) (∑ i ∈ s, g i)).trans
      (add_le_add le_rfl ih)

theorem dist_transitionPerturbation_le (L : ℝ) (hL_pos : 0 ≤ L)
    (hL_lip : ∀ (u : Time) (v : Vtx₀ p) (x y : Ev₀ p) (α β : ℝ),
      α ∈ Set.Icc (0 : ℝ) 1 → β ∈ Set.Icc (0 : ℝ) 1 →
      |baryWeight p hg v x α - baryWeight p hg v y β| ≤
        L * dist (segPoint p hp hg u x α) (segPoint p hp hg u y β))
    (τ₁ τ₂ : Time → Time) (t : Time) (z w : Plane) :
    dist (transitionPerturbation p hp hg L τ₁ τ₂ t z)
        (transitionPerturbation p hp hg L τ₁ τ₂ t w) ≤
      (∑ v : Vtx₀ p, 5 * L * dist (vtxPos p hp hg (τ₂ t) v) (vtxPos p hp hg (τ₁ t) v)) *
        dist z w := by
  unfold transitionPerturbation
  refine (plane_dist_sum_le Finset.univ _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro v _
  let dv := vtxPos p hp hg (τ₂ t) v - vtxPos p hp hg (τ₁ t) v
  have hterm :
      dist (mcshaneWeight p hp hg L v (τ₁ t) z • dv)
        (mcshaneWeight p hp hg L v (τ₁ t) w • dv) =
      |mcshaneWeight p hp hg L v (τ₁ t) z - mcshaneWeight p hp hg L v (τ₁ t) w| *
        dist (vtxPos p hp hg (τ₂ t) v) (vtxPos p hp hg (τ₁ t) v) := by
    rw [plane_dist_eq, plane_dist_eq]
    have h1 :
        (mcshaneWeight p hp hg L v (τ₁ t) z • dv).1 -
          (mcshaneWeight p hp hg L v (τ₁ t) w • dv).1 =
        (mcshaneWeight p hp hg L v (τ₁ t) z - mcshaneWeight p hp hg L v (τ₁ t) w) * dv.1 := by
      dsimp [smul_eq_mul]; ring
    have h2 :
        (mcshaneWeight p hp hg L v (τ₁ t) z • dv).2 -
          (mcshaneWeight p hp hg L v (τ₁ t) w • dv).2 =
        (mcshaneWeight p hp hg L v (τ₁ t) z - mcshaneWeight p hp hg L v (τ₁ t) w) * dv.2 := by
      dsimp [smul_eq_mul]; ring
    rw [h1, h2, abs_mul, abs_mul, ← mul_max_of_nonneg _ _ (abs_nonneg _)]
    rfl
  rw [hterm]
  have hlip := abs_mcshaneWeight_sub_le p hp hg L hL_pos hL_lip v (τ₁ t) z w
  calc
    |mcshaneWeight p hp hg L v (τ₁ t) z - mcshaneWeight p hp hg L v (τ₁ t) w| *
        dist (vtxPos p hp hg (τ₂ t) v) (vtxPos p hp hg (τ₁ t) v)
        ≤ (5 * L * dist z w) * dist (vtxPos p hp hg (τ₂ t) v) (vtxPos p hp hg (τ₁ t) v) :=
      mul_le_mul_of_nonneg_right hlip dist_nonneg
    _ = 5 * L * dist (vtxPos p hp hg (τ₂ t) v) (vtxPos p hp hg (τ₁ t) v) * dist z w := by ring

/-- Single-step `AmbientPlaneIsotopy` between two time schedules `τ₁` and `τ₂`. -/
noncomputable def singleStepIsotopy (L : ℝ) (hL_pos : 0 ≤ L)
    (hL_lip : ∀ (u : Time) (v : Vtx₀ p) (x y : Ev₀ p) (α β : ℝ),
      α ∈ Set.Icc (0 : ℝ) 1 → β ∈ Set.Icc (0 : ℝ) 1 →
      |baryWeight p hg v x α - baryWeight p hg v y β| ≤
        L * dist (segPoint p hp hg u x α) (segPoint p hp hg u y β))
    (τ₁ τ₂ : Time → Time) (hτ₁ : Continuous τ₁) (hτ₂ : Continuous τ₂)
    (hstart : τ₁ start = τ₂ start)
    (hsmall : ∀ t : Time,
      ∑ v : Vtx₀ p, 5 * L * dist (vtxPos p hp hg (τ₂ t) v) (vtxPos p hp hg (τ₁ t) v) ≤ 1 / 2) :
    AmbientPlaneIsotopy :=
  AmbientPlaneIsotopy.ofContractionPerturbation
    (transitionPerturbation p hp hg L τ₁ τ₂)
    (continuous_transitionPerturbation p hp hg L hτ₁ hτ₂)
    (transitionPerturbation_eq_zero_of_eq p hp hg L τ₁ τ₂ start hstart)
    (fun t z w =>
      (dist_transitionPerturbation_le p hp hg L hL_pos hL_lip τ₁ τ₂ t z w).trans
        (mul_le_mul_of_nonneg_right (hsmall t) dist_nonneg))

theorem singleStepIsotopy_segPoint (L : ℝ) (hL_pos : 0 ≤ L)
    (hL_lip : ∀ (u : Time) (v : Vtx₀ p) (x y : Ev₀ p) (α β : ℝ),
      α ∈ Set.Icc (0 : ℝ) 1 → β ∈ Set.Icc (0 : ℝ) 1 →
      |baryWeight p hg v x α - baryWeight p hg v y β| ≤
        L * dist (segPoint p hp hg u x α) (segPoint p hp hg u y β))
    (τ₁ τ₂ : Time → Time) (hτ₁ : Continuous τ₁) (hτ₂ : Continuous τ₂)
    (hstart : τ₁ start = τ₂ start)
    (hsmall : ∀ t : Time,
      ∑ v : Vtx₀ p, 5 * L * dist (vtxPos p hp hg (τ₂ t) v) (vtxPos p hp hg (τ₁ t) v) ≤ 1 / 2)
    (t : Time) (x : Ev₀ p) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    (singleStepIsotopy p hp hg L hL_pos hL_lip τ₁ τ₂ hτ₁ hτ₂ hstart hsmall).motion t
        (segPoint p hp hg (τ₁ t) x α) =
      segPoint p hp hg (τ₂ t) x α := by
  unfold singleStepIsotopy
  rw [AmbientPlaneIsotopy.ofContractionPerturbation_apply]
  exact transitionPerturbation_segPoint p hp hg L hL_lip τ₁ τ₂ t x hα

/-- Compactness gives a positive time-step threshold `δ > 0` below which vertex displacements
have total weighted Lipschitz norm at most `1/2`. -/
theorem exists_step_delta (L : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u s : Time, dist u s < δ →
      ∑ v : Vtx₀ p, 5 * L * dist (vtxPos p hp hg s v) (vtxPos p hp hg u v) ≤ 1 / 2 := by
  let D : Time × Time → ℝ := fun q =>
    ∑ v : Vtx₀ p, 5 * L * dist (vtxPos p hp hg q.2 v) (vtxPos p hp hg q.1 v)
  have hD_cont : Continuous D := by
    apply continuous_finset_sum
    intro v _
    exact continuous_const.mul
      (((continuous_vtxPos p hp hg v).comp continuous_snd).dist
        ((continuous_vtxPos p hp hg v).comp continuous_fst))
  let K : Set (Time × Time) := {q : Time × Time | (1 / 2 : ℝ) ≤ D q}
  have hK_closed : IsClosed K := isClosed_le continuous_const hD_cont
  have hK_compact : IsCompact K := hK_closed.isCompact
  have hdist_pos : ∀ q ∈ K, 0 < dist q.1 q.2 := by
    rintro ⟨u, s⟩ hq
    dsimp
    rw [dist_pos]
    intro heq
    subst heq
    have hzero : D (u, u) = 0 := by simp [D]
    have hle : (1 / 2 : ℝ) ≤ D (u, u) := hq
    linarith
  obtain ⟨δ, hδ, hδ_le⟩ :=
    hK_compact.exists_forall_le' (continuous_fst.dist continuous_snd).continuousOn hdist_pos
  refine ⟨δ, hδ, ?_⟩
  intro u s hlt
  by_contra hnot
  have hmem : (u, s) ∈ K := by
    change (1 / 2 : ℝ) ≤ D (u, s)
    exact le_of_lt (not_le.mp hnot)
  exact (not_lt_of_ge (hδ_le (u, s) hmem)) hlt

/-- Schedule `τ(M, k, t) = clamp01 ((k / M) * t)` in `Time`. -/
noncomputable def timeStep (M k : ℕ) (t : Time) : Time :=
  ⟨clamp01 (((k : ℝ) / (M : ℝ)) * t.val), clamp01_mem_Icc _⟩

theorem continuous_timeStep (M k : ℕ) : Continuous (timeStep M k) :=
  (continuous_clamp01.comp (continuous_const.mul continuous_subtype_val)).subtype_mk _

theorem timeStep_zero (M : ℕ) (t : Time) : timeStep M 0 t = start := by
  ext
  simp [timeStep, start, clamp01]

theorem timeStep_self {M : ℕ} (hM : 0 < M) (t : Time) : timeStep M M t = t := by
  ext
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hM)
  simp [timeStep, hM', clamp01_eq_self t.property]

theorem timeStep_at_start (M k : ℕ) : timeStep M k start = start := by
  ext
  simp [timeStep, start, clamp01]

theorem dist_timeStep_succ_le {M : ℕ} (hM : 0 < M) (k : ℕ) (t : Time) :
    dist (timeStep M k t) (timeStep M (k + 1) t) ≤ 1 / (M : ℝ) := by
  have hM_pos : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  change |clamp01 (((k : ℝ) / (M : ℝ)) * t.val) -
      clamp01 ((((k + 1 : ℕ) : ℝ) / (M : ℝ)) * t.val)| ≤ 1 / (M : ℝ)
  refine (abs_clamp01_sub_le _ _).trans ?_
  have hdiff :
      ((k : ℝ) / (M : ℝ)) * t.val - (((k + 1 : ℕ) : ℝ) / (M : ℝ)) * t.val =
        -(t.val / (M : ℝ)) := by
    push_cast
    ring
  rw [hdiff, abs_neg, abs_of_nonneg (div_nonneg t.property.1 (le_of_lt hM_pos)), div_le_div_iff_of_pos_right hM_pos]
  exact t.property.2

/-- `k`-fold composition of single-step isotopies along `timeStep M 0, ..., timeStep M k`. -/
noncomputable def multiStepIsotopy (L : ℝ) (hL_pos : 0 ≤ L)
    (hL_lip : ∀ (u : Time) (v : Vtx₀ p) (x y : Ev₀ p) (α β : ℝ),
      α ∈ Set.Icc (0 : ℝ) 1 → β ∈ Set.Icc (0 : ℝ) 1 →
      |baryWeight p hg v x α - baryWeight p hg v y β| ≤
        L * dist (segPoint p hp hg u x α) (segPoint p hp hg u y β))
    (M : ℕ)
    (hsmall : ∀ (k : ℕ) (t : Time),
      ∑ v : Vtx₀ p,
        5 * L * dist (vtxPos p hp hg (timeStep M (k + 1) t) v)
          (vtxPos p hp hg (timeStep M k t) v) ≤ 1 / 2) :
    ℕ → AmbientPlaneIsotopy
  | 0 => AmbientPlaneIsotopy.refl
  | k + 1 =>
    (multiStepIsotopy L hL_pos hL_lip M hsmall k).trans
      (singleStepIsotopy p hp hg L hL_pos hL_lip
        (timeStep M k) (timeStep M (k + 1))
        (continuous_timeStep M k) (continuous_timeStep M (k + 1))
        (by rw [timeStep_at_start, timeStep_at_start])
        (hsmall k))

theorem multiStepIsotopy_segPoint (L : ℝ) (hL_pos : 0 ≤ L)
    (hL_lip : ∀ (u : Time) (v : Vtx₀ p) (x y : Ev₀ p) (α β : ℝ),
      α ∈ Set.Icc (0 : ℝ) 1 → β ∈ Set.Icc (0 : ℝ) 1 →
      |baryWeight p hg v x α - baryWeight p hg v y β| ≤
        L * dist (segPoint p hp hg u x α) (segPoint p hp hg u y β))
    (M : ℕ)
    (hsmall : ∀ (k : ℕ) (t : Time),
      ∑ v : Vtx₀ p,
        5 * L * dist (vtxPos p hp hg (timeStep M (k + 1) t) v)
          (vtxPos p hp hg (timeStep M k t) v) ≤ 1 / 2)
    (k : ℕ) (t : Time) (x : Ev₀ p) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    (multiStepIsotopy p hp hg L hL_pos hL_lip M hsmall k).motion t
        (segPoint p hp hg start x α) =
      segPoint p hp hg (timeStep M k t) x α := by
  induction k with
  | zero =>
    rw [timeStep_zero]
    rfl
  | succ k ih =>
    unfold multiStepIsotopy
    rw [AmbientPlaneIsotopy.trans_motion_apply, ih]
    exact singleStepIsotopy_segPoint p hp hg L hL_pos hL_lip
      (timeStep M k) (timeStep M (k + 1))
      (continuous_timeStep M k) (continuous_timeStep M (k + 1))
      (by rw [timeStep_at_start, timeStep_at_start])
      (hsmall k) t x hα

/-- Existence of an `AmbientPlaneIsotopy` transporting every event sub-segment
affine parameterization along `p`. -/
theorem exists_event_affinePoint_isotopy :
    ∃ I : AmbientPlaneIsotopy,
      ∀ (t : Time) (x : PolygonEvent (p start)) (α : ℝ),
        α ∈ Set.Icc (0 : ℝ) 1 →
        I.motion t (affinePoint (polygonEventPoint (p start) x)
          (polygonEventPoint (p start) (polygonEventSuccessor (p start) (hg start).g2 x)) α) =
        affinePoint
          (polygonEventPoint (p t) (polygonEventMapEquiv (pathCrossingEquiv p hp hg t) x))
          (polygonEventPoint (p t) (polygonEventSuccessor (p t) (hg t).g2
            (polygonEventMapEquiv (pathCrossingEquiv p hp hg t) x))) α := by
  obtain ⟨L, hL_pos, hL_lip⟩ := exists_uniform_barycentric_lipschitz p hp hg
  obtain ⟨δ, hδ_pos, hδ_spec⟩ := exists_step_delta p hp hg L
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ_pos
  let M := N + 1
  have hM_pos : 0 < M := Nat.succ_pos N
  have hN' : 1 / (M : ℝ) < δ := by
    dsimp [M]
    push_cast
    exact hN
  have hsmall : ∀ (k : ℕ) (t : Time),
      ∑ v : Vtx₀ p,
        5 * L * dist (vtxPos p hp hg (timeStep M (k + 1) t) v)
          (vtxPos p hp hg (timeStep M k t) v) ≤ 1 / 2 := by
    intro k t
    apply hδ_spec
    exact (dist_timeStep_succ_le hM_pos k t).trans_lt hN'
  refine ⟨multiStepIsotopy p hp hg L (le_of_lt hL_pos) hL_lip M hsmall M, ?_⟩
  intro t x α hα
  have hstep := multiStepIsotopy_segPoint p hp hg L (le_of_lt hL_pos) hL_lip M hsmall M t x hα
  rw [timeStep_self hM_pos t] at hstep
  have hstart_pt :
      segPoint p hp hg start x α =
        affinePoint (polygonEventPoint (p start) x)
          (polygonEventPoint (p start) (polygonEventSuccessor (p start) (hg start).g2 x)) α := by
    unfold segPoint segStart segEnd src₀ tgt₀ PolygonDrawing.arcSource PolygonDrawing.arcTarget
    rw [vtxPos_start, vtxPos_start,
      PolygonDrawing.vertexPoint_eventVertex, PolygonDrawing.vertexPoint_eventVertex]
  have ht_pt :
      segPoint p hp hg t x α =
        affinePoint
          (polygonEventPoint (p t) (polygonEventMapEquiv (pathCrossingEquiv p hp hg t) x))
          (polygonEventPoint (p t) (polygonEventSuccessor (p t) (hg t).g2
            (polygonEventMapEquiv (pathCrossingEquiv p hp hg t) x))) α := by
    unfold segPoint
    rw [segStart_eq_eventPoint, segEnd_eq_eventSuccessorPoint]
  rw [← hstart_pt, ← ht_pt]
  exact hstep

/-- Target 1: Full chamber geometry along every continuous path in `CyclicGeneric`. -/
theorem full_chamber_geometry {n : ℕ} (p : Time → Fin n → Plane)
    (hp : Continuous p) (hg : ∀ t, CyclicGeneric (p t)) :
    let q₀ := p start
    let h₀ : CyclicGeneric q₀ := hg start
    ∃ I : AmbientPlaneIsotopy,
      (∀ t i, I.motion t (q₀ i) = p t i) ∧
      (∀ t e, I.motion t '' originalEdge q₀ e = originalEdge (p t) e) ∧
      ∀ t, ∃ E : PolygonCrossing q₀ ≃ PolygonCrossing (p t),
        (∀ c, (E c).val = c.val) ∧
        (∃ ht : CyclicGeneric (p t),
          (∀ x y : PolygonEvent q₀,
            (polygonEventOrder q₀ h₀.g2).lt x y ↔
              (polygonEventOrder (p t) ht.g2).lt
                (polygonEventMapEquiv E x) (polygonEventMapEquiv E y)) ∧
          (∀ c, I.motion t (crossingPoint q₀ c) = crossingPoint (p t) (E c)) ∧
          leftCount q₀ = leftCount (p t) ∧
          (∀ S : Finset (PolygonCrossing q₀),
            PolygonNonalternation.polygonNonalternating q₀ h₀.g2 S ↔
              PolygonNonalternation.polygonNonalternating (p t) ht.g2
                (S.map E.toEmbedding)) ∧
          (∀ S : Finset (PolygonCrossing q₀),
            uniformDaughterSupport q₀ h₀ S ↔
              uniformDaughterSupport (p t) ht (S.map E.toEmbedding)) ∧
          ∀ (S : Finset (PolygonCrossing q₀))
            (C : Component (smoothingDartPermutation q₀ h₀.g2 S))
            (hNA : PolygonNonalternation.polygonNonalternating q₀ h₀.g2 S),
            ∃ C' : Component (smoothingDartPermutation (p t) ht.g2 (S.map E.toEmbedding)),
            ∃ hNA' : PolygonNonalternation.polygonNonalternating (p t) ht.g2
              (S.map E.toEmbedding),
            ∃ J : DiagramTransport (I.motion t)
              (sharpDaughterDiagram q₀ h₀ S C hNA)
              (sharpDaughterDiagram (p t) ht (S.map E.toEmbedding) C' hNA'),
              (∀ x : PolygonEvent q₀,
                componentOf (smoothingDartPermutation q₀ h₀.g2 S) x = C →
                componentOf (smoothingDartPermutation (p t) ht.g2 (S.map E.toEmbedding))
                  (polygonEventMapEquiv E x) = C') ∧
              (sharpDaughterDiagram q₀ h₀ S C hNA).nCrossing =
                (sharpDaughterDiagram (p t) ht (S.map E.toEmbedding) C' hNA').nCrossing ∧
              sharpDaughterRotationInteger q₀ h₀ S C hNA =
                sharpDaughterRotationInteger (p t) ht (S.map E.toEmbedding) C' hNA' ∧
              (∀ c : Fin (sharpDaughterDiagram q₀ h₀ S C hNA).nCrossing,
                oldCrossing (p t) ht (S.map E.toEmbedding) C' (J.signed.crossingEquiv c) =
                  crossingFin (p t) (E
                    ((crossingFin q₀).symm (oldCrossing q₀ h₀ S C c)))) ∧
              (∀ a : Fin (sharpDaughterDiagram q₀ h₀ S C hNA).nArc,
                oldArc (p t) ht (S.map E.toEmbedding) C' (J.signed.arcEquiv a) =
                  eventFin (p t) (polygonEventMapEquiv E
                    ((eventFin q₀).symm (oldArc q₀ h₀ S C a))))) := by
  obtain ⟨I, haff⟩ := exists_event_affinePoint_isotopy p hp hg
  exact full_chamber_geometry_of_event_affinePoint_isotopy p hp hg I haff

end McShaneTransitionAndFullGeometry

end DirectGLSSW.GeminiChamber
