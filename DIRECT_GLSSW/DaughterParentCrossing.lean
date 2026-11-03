import DaughterG2Inheritance
import PrimitiveEdgeGrouping
import UncutDaughterEdge

set_option autoImplicit false
namespace DirectGLSSW.DaughterParentCrossing
open DaughterFirstReturn DaughterG2Inheritance PolygonNonalternation PrimitiveEdgeGrouping
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)

include hS in
theorem crossing_carriers_ne (c : PolygonCrossing (daughterVertex P hP.g2 S root)) :
    daughterCarrier P hP.g2 S root c.val.1 ≠ daughterCarrier P hP.g2 S root c.val.2 :=
  fun h => crossing_edges_ne _ c (daughterCarrier_injective P hP.g2 S hP.size_ge_three hS root h)

/-- The exact original crossing represented by the daughter's two open subedges. -/
def parentCrossing (c : PolygonCrossing (daughterVertex P hP.g2 S root)) : PolygonCrossing P := by
  let a := daughterCarrier P hP.g2 S root c.val.1
  let b := daughterCarrier P hP.g2 S root c.val.2
  have ha := daughter_edgeInterior_subset_parent P hP.g2 S hP.size_ge_three root hroot
    c.val.1 (crossingPoint _ c) (crossingPoint_mem_left _ c)
  have hb := daughter_edgeInterior_subset_parent P hP.g2 S hP.size_ge_three root hroot
    c.val.2 (crossingPoint _ c) (crossingPoint_mem_right _ c)
  exact if h : a < b then ⟨(a,b),h,⟨crossingPoint _ c,ha,hb⟩⟩
    else ⟨(b,a),lt_of_le_of_ne (le_of_not_gt h) (crossing_carriers_ne P hP S hS root c).symm,
      ⟨crossingPoint _ c,hb,ha⟩⟩

theorem parentCrossing_labels (c : PolygonCrossing (daughterVertex P hP.g2 S root)) :
    (parentCrossing P hP S hS root hroot c).val =
      if daughterCarrier P hP.g2 S root c.val.1 < daughterCarrier P hP.g2 S root c.val.2
      then (daughterCarrier P hP.g2 S root c.val.1,daughterCarrier P hP.g2 S root c.val.2)
      else (daughterCarrier P hP.g2 S root c.val.2,daughterCarrier P hP.g2 S root c.val.1) := by
  unfold parentCrossing
  dsimp only
  split_ifs <;> rfl

theorem parentCrossing_point (c : PolygonCrossing (daughterVertex P hP.g2 S root)) :
    crossingPoint P (parentCrossing P hP S hS root hroot c) =
      crossingPoint (daughterVertex P hP.g2 S root) c := by
  symm
  apply crossingPoint_eq_of_mem hP.size_ge_three P hP.g1
  · have ha := daughter_edgeInterior_subset_parent P hP.g2 S hP.size_ge_three root hroot
      c.val.1 (crossingPoint _ c) (crossingPoint_mem_left _ c)
    have hb := daughter_edgeInterior_subset_parent P hP.g2 S hP.size_ge_three root hroot
      c.val.2 (crossingPoint _ c) (crossingPoint_mem_right _ c)
    rw [parentCrossing_labels]
    split_ifs <;> first | exact ha | exact hb
  · have ha := daughter_edgeInterior_subset_parent P hP.g2 S hP.size_ge_three root hroot
      c.val.1 (crossingPoint _ c) (crossingPoint_mem_left _ c)
    have hb := daughter_edgeInterior_subset_parent P hP.g2 S hP.size_ge_three root hroot
      c.val.2 (crossingPoint _ c) (crossingPoint_mem_right _ c)
    rw [parentCrossing_labels]
    split_ifs <;> first | exact ha | exact hb

theorem parentCrossing_injective : Function.Injective (parentCrossing P hP S hS root hroot) := by
  intro c d h
  apply crossingPoint_injective (daughterVertex P hP.g2 S root)
    (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root)
  rw [← parentCrossing_point P hP S hS root hroot c,
    ← parentCrossing_point P hP S hS root hroot d,h]

/-- Membership on a chosen daughter carrier is exactly original edge incidence. -/
theorem parentCrossing_incident_iff (i : Fin (Fintype.card (CornerCoord P hP.g2 S root)))
    (e : Fin n) (hi : daughterCarrier P hP.g2 S root i = e)
    (c : PolygonCrossing (daughterVertex P hP.g2 S root)) :
    Incident P e (parentCrossing P hP S hS root hroot c) ↔ c.val.1 = i ∨ c.val.2 = i := by
  have hinj := daughterCarrier_injective P hP.g2 S hP.size_ge_three hS root
  have h₁ : daughterCarrier P hP.g2 S root c.val.1 = e ↔ c.val.1 = i := by
    rw [← hi]
    exact hinj.eq_iff
  have h₂ : daughterCarrier P hP.g2 S root c.val.2 = e ↔ c.val.2 = i := by
    rw [← hi]
    exact hinj.eq_iff
  unfold Incident
  rw [parentCrossing_labels]
  split_ifs <;> simp only [Prod.fst,Prod.snd,h₁,h₂,or_comm]

def edgeCrossingEmbedding (i : Fin (Fintype.card (CornerCoord P hP.g2 S root)))
    (e : Fin n) (hi : daughterCarrier P hP.g2 S root i = e) :
    EdgeChord (daughterVertex P hP.g2 S root) i ↪ EdgeChord P e where
  toFun c := ⟨parentCrossing P hP S hS root hroot c.val,
    (parentCrossing_incident_iff P hP S hS root hroot i e hi c.val).mpr c.property⟩
  inj' := by
    intro c d h
    exact Subtype.ext (parentCrossing_injective P hP S hS root hroot (congrArg Subtype.val h))








end
end DirectGLSSW.DaughterParentCrossing
