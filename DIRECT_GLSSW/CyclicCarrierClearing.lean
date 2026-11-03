import OriginalOuterProperness
import UniversalCarrierTransverse

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart
open scoped BigOperators

/-- Polynomial denominator, over a general coefficient ring. -/
def slotDen {R : Type*} [CommRing R] (A B : (R × R) × R) : R :=
  planarDet A.1 B.1

/-- Polynomial intersection numerator, before division. -/
def slotNum {R : Type*} [CommRing R] (A B : (R × R) × R) : R × R :=
  (B.2*A.1.1-A.2*B.1.1, B.2*A.1.2-A.2*B.1.2)

def clearedPoints {R : Type*} [CommRing R] {s : ℕ}
    (A B : Fin s → (R × R) × R) (i : Fin s) : R × R :=
  let t := ∏ j ∈ Finset.univ.erase i, slotDen (A j) (B j)
  (t * (slotNum (A i) (B i)).1, t * (slotNum (A i) (B i)).2)

theorem clearedPoints_eq {s : ℕ} (A B : Fin s → CarrierLine)
    (hd : ∀ i, lineDenominator (A i) (B i) ≠ 0) (i : Fin s) :
    clearedPoints A B i =
      (∏ j, lineDenominator (A j) (B j)) • lineIntersection (A i) (B i) := by
  have hp := Finset.mul_prod_erase Finset.univ
    (fun j => lineDenominator (A j) (B j)) (Finset.mem_univ i)
  apply Prod.ext <;>
    simp only [clearedPoints, slotNum, slotDen, lineDenominator, lineIntersection,
      smul_eq_mul] at *
  · change _ = _ * (_ / _)
    rw [← hp]
    field_simp [hd i]
    <;> ring
  · change _ = _ * (_ / _)
    rw [← hp]
    field_simp [hd i]
    <;> ring

theorem outer_scaled (p : Fin 4 → ℝ × ℝ) (d : ℝ) :
    OriginalOuterProperness.outerNumerator (fun i => d • p i) =
      d^2 * OriginalOuterProperness.outerNumerator p := by
  simp only [OriginalOuterProperness.outerNumerator, planarDet,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  change _ = _
  dsimp at *
  ring

theorem secant_scaled (p : Fin 6 → ℝ × ℝ) (d : ℝ) :
    OriginalSecantProperness.secantNumerator (fun i => d • p i) =
      d^4 * OriginalSecantProperness.secantNumerator p := by
  simp only [OriginalSecantProperness.secantNumerator, planarDet,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  change _ = _
  dsimp at *
  ring

theorem outer_cleared (A B : Fin 4 → CarrierLine)
    (hd : ∀ i, lineDenominator (A i) (B i) ≠ 0) :
    OriginalOuterProperness.outerNumerator (clearedPoints A B) =
      (∏ j, lineDenominator (A j) (B j))^2 *
        OriginalOuterProperness.outerNumerator (fun i => lineIntersection (A i) (B i)) := by
  have he := funext (clearedPoints_eq A B hd)
  rw [he, outer_scaled]

theorem secant_cleared (A B : Fin 6 → CarrierLine)
    (hd : ∀ i, lineDenominator (A i) (B i) ≠ 0) :
    OriginalSecantProperness.secantNumerator (clearedPoints A B) =
      (∏ j, lineDenominator (A j) (B j))^4 *
        OriginalSecantProperness.secantNumerator (fun i => lineIntersection (A i) (B i)) := by
  have he := funext (clearedPoints_eq A B hd)
  rw [he, secant_scaled]

/-- An injective cyclic carrier list can realize a genuine generic polygon
with all the required four/six-label exclusions, on the original line labels. -/
theorem exists_cycle_witness {m n : ℕ} (q : Fin m → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (f : Fin m → Fin n) (hf : Function.Injective f) :
    ∃ L : Fin n → CarrierLine,
      (∀ i : Fin m, lineDenominator
        (L (f ((cyclicSuccessorPerm m)⁻¹ i))) (L (f i)) ≠ 0) ∧
      (∀ l : Fin 4 → Fin m, Function.Injective l →
        OriginalOuterProperness.outerNumerator
          ((reconstructPolygon (L ∘ f)) ∘ l) ≠ 0) ∧
      (∀ l : Fin 6 → Fin m, Function.Injective l →
        OriginalSecantProperness.secantNumerator
          ((reconstructPolygon (L ∘ f)) ∘ l) ≠ 0) := by
  obtain ⟨r, _, hr, _, h6, h4⟩ :=
    OriginalOuterProperness.exists_joint_parent_daughters q hq Set.univ isOpen_univ (Set.mem_univ q)
  let L : Fin n → CarrierLine := Function.extend f (polygonCarrierCoordinates r) (fun _ => ((0,0),0))
  have hL (i : Fin m) : L (f i) = polygonCarrierCoordinates r i := by
    exact hf.extend_apply _ _ i
  have hcomp : L ∘ f = polygonCarrierCoordinates r := funext hL
  refine ⟨L, ?_, ?_, ?_⟩
  · intro i
    simpa only [hL] using polygonCarrierDenominator_ne_zero r hr i
  · rw [hcomp, reconstructPolygon_polygonCarrierCoordinates r hr]
    exact h4
  · rw [hcomp, reconstructPolygon_polygonCarrierCoordinates r hr]
    exact h6

end DirectGLSSW.CyclicCarrierClearing







