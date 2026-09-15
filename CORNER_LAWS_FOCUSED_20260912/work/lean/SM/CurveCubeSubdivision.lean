import SM.UniformMeshCells
import SM.RegularScalarBoxes

/-! The source curve is subdivided into actual closed time cells lying in small
regular scalar cubes. The first and last cubes are generic, even if an inactive
control vanishes at an original endpoint. All centres and occurrence labels are
actual labelled tuples; no auxiliary path is assumed. -/

namespace SM

open Set

noncomputable section

structure CurveCubeSubdivision {n : ℕ} (γ : unitInterval → LabelledTuple n) (δ : ℝ) where
  count : ℕ
  count_pos : 0 < count
  count_ge_three : 3 ≤ count
  center : Fin count → LabelledTuple n
  radius : Fin count → ℝ
  radius_pos : ∀ i, 0 < radius i
  closure_regular : ∀ i, closure (tupleScalarBox (center i) (radius i)) ⊆ {Q | Regular Q}
  diameter_lt : ∀ i, Metric.diam (tupleCoordinates '' tupleScalarBox (center i) (radius i)) < δ
  pairwise_dist_lt : ∀ i, ∀ Q ∈ tupleScalarBox (center i) (radius i),
    ∀ R ∈ tupleScalarBox (center i) (radius i),
      dist (tupleCoordinates Q) (tupleCoordinates R) < δ
  curve_cell : ∀ i, ∀ t ∈ uniformMeshCell count count_pos i,
    γ t ∈ tupleScalarBox (center i) (radius i)
  endpoint_generic : ∀ i, (i.val = 0 ∨ i.val + 1 = count) →
    closure (tupleScalarBox (center i) (radius i)) ⊆ {Q | Generic Q}

theorem nonempty_curveCubeSubdivision {n : ℕ} (hn : 3 ≤ n)
    (γ : unitInterval → LabelledTuple n) (hγ : Continuous γ)
    (hregular : ∀ t, Regular (γ t)) (hfirst : Generic (γ 0)) (hlast : Generic (γ 1))
    (δ : ℝ) (hδ : 0 < δ) : Nonempty (CurveCubeSubdivision γ δ) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  have hboxes : ∀ t : unitInterval, ∃ r > 0,
      closure (tupleScalarBox (γ t) r) ⊆ {Q | Regular Q} ∧
      Metric.diam (tupleCoordinates '' tupleScalarBox (γ t) r) < δ ∧
      (∀ Q ∈ tupleScalarBox (γ t) r, ∀ R ∈ tupleScalarBox (γ t) r,
        dist (tupleCoordinates Q) (tupleCoordinates R) < δ) ∧
      ((t = 0 ∨ t = 1) → closure (tupleScalarBox (γ t) r) ⊆ {Q | Generic Q}) := by
    intro t
    by_cases hend : t = 0 ∨ t = 1
    · have hg : Generic (γ t) := by
        rcases hend with rfl | rfl
        · exact hfirst
        · exact hlast
      obtain ⟨r, hr, _, _, hc, hd, hp⟩ := exists_generic_tupleScalarBox hn (γ t) hg δ hδ
      exact ⟨r, hr, fun Q hQ => (hc hQ).1, hd, hp, fun _ Q hQ => (hc hQ).2⟩
    · obtain ⟨r, hr, _, _, hc, hd, hp⟩ := exists_regular_tupleScalarBox (γ t) (hregular t) δ hδ
      exact ⟨r, hr, hc, hd, hp, fun ht => (hend ht).elim⟩
  choose radius hpos hreg hdiam hpair hgen using hboxes
  let C : unitInterval → Set unitInterval := fun t => γ ⁻¹' tupleScalarBox (γ t) (radius t)
  have hOpen : ∀ t, IsOpen (C t) := fun t => (isOpen_tupleScalarBox _ _).preimage hγ
  have hCover : univ ⊆ ⋃ t, C t := by
    intro t _
    exact mem_iUnion.mpr ⟨t, tupleScalarBox_self (γ t) (radius t) (hpos t)⟩
  obtain ⟨N, hN, hN3, hcells⟩ := exists_uniformMesh_subordinate_with_endpoints C hOpen hCover 0 1
    (tupleScalarBox_self (γ 0) (radius 0) (hpos 0))
    (tupleScalarBox_self (γ 1) (radius 1) (hpos 1))
  choose selected hcell hzero hone using hcells
  refine ⟨{
    count := N
    count_pos := hN
    count_ge_three := hN3
    center := fun i => γ (selected i)
    radius := fun i => radius (selected i)
    radius_pos := fun i => hpos (selected i)
    closure_regular := fun i => hreg (selected i)
    diameter_lt := fun i => hdiam (selected i)
    pairwise_dist_lt := fun i => hpair (selected i)
    curve_cell := fun i => hcell i
    endpoint_generic := ?_ }⟩
  intro i hi
  apply hgen (selected i)
  rcases hi with hz | ho
  · exact Or.inl (hzero i hz)
  · exact Or.inr (hone i ho)

def chooseCurveCubeSubdivision {n : ℕ} (hn : 3 ≤ n)
    (γ : unitInterval → LabelledTuple n) (hγ : Continuous γ)
    (hregular : ∀ t, Regular (γ t)) (hfirst : Generic (γ 0)) (hlast : Generic (γ 1))
    (δ : ℝ) (hδ : 0 < δ) : CurveCubeSubdivision γ δ :=
  Classical.choice (nonempty_curveCubeSubdivision hn γ hγ hregular hfirst hlast δ hδ)

namespace CurveCubeSubdivision

variable {n : ℕ} {γ : unitInterval → LabelledTuple n} {δ : ℝ}
  (d : CurveCubeSubdivision γ δ)

def time (j : Fin (d.count + 1)) : unitInterval := uniformMeshPoint d.count d.count_pos j

def cell (i : Fin d.count) : Set unitInterval := uniformMeshCell d.count d.count_pos i

def cube (i : Fin d.count) : Set (LabelledTuple n) := tupleScalarBox (d.center i) (d.radius i)

theorem time_strictMono : StrictMono d.time := uniformMeshPoint_strictMono d.count d.count_pos

theorem cells_cover : ⋃ i, d.cell i = univ := iUnion_uniformMeshCell d.count d.count_pos

theorem isOpen_cube [NeZero n] (i : Fin d.count) : IsOpen (d.cube i) := isOpen_tupleScalarBox _ _

theorem curve_mem_cube (i : Fin d.count) (t : unitInterval) (ht : t ∈ d.cell i) :
    γ t ∈ d.cube i := d.curve_cell i t ht

end CurveCubeSubdivision

end

end SM
