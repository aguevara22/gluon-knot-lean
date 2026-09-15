import SM.MultivariateAvoidance
import SM.ScalarCoordinateTopology
import SM.EuclideanTuple
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Convex.Basic

/-! Prototype for the geometric subdivision phase of full thm:relgp. Outside
the audited theorem library; no original source acceptance is claimed. -/

namespace SM

open Set

noncomputable section

variable {σ : Type*}

def scalarOpenBox (x : σ → ℝ) (r : ℝ) : Set (σ → ℝ) :=
  {y | ∀ i, |y i - x i| < r}

def scalarClosedBox (x : σ → ℝ) (r : ℝ) : Set (σ → ℝ) :=
  {y | ∀ i, |y i - x i| ≤ r}

theorem isOpen_scalarOpenBox [Finite σ] (x : σ → ℝ) (r : ℝ) :
    IsOpen (scalarOpenBox x r) := by
  have he : scalarOpenBox x r = ⋂ i, {y : σ → ℝ | |y i - x i| < r} := by
    ext y
    simp [scalarOpenBox]
  rw [he]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt ((continuous_apply i).sub continuous_const).abs continuous_const

theorem isClosed_scalarClosedBox (x : σ → ℝ) (r : ℝ) :
    IsClosed (scalarClosedBox x r) := by
  have he : scalarClosedBox x r = ⋂ i, {y : σ → ℝ | |y i - x i| ≤ r} := by
    ext y
    simp [scalarClosedBox]
  rw [he]
  exact isClosed_iInter fun i =>
    isClosed_le ((continuous_apply i).sub continuous_const).abs continuous_const

theorem scalarOpenBox_subset_closed (x : σ → ℝ) (r : ℝ) :
    scalarOpenBox x r ⊆ scalarClosedBox x r := fun _ h i => (h i).le

theorem closure_scalarOpenBox_subset_closed (x : σ → ℝ) (r : ℝ) :
    closure (scalarOpenBox x r) ⊆ scalarClosedBox x r :=
  closure_minimal (scalarOpenBox_subset_closed x r) (isClosed_scalarClosedBox x r)

theorem scalarOpenBox_self (x : σ → ℝ) (r : ℝ) (hr : 0 < r) : x ∈ scalarOpenBox x r := by
  intro i
  simpa using hr

theorem scalarOpenBox_eq_pi (x : σ → ℝ) (r : ℝ) :
    scalarOpenBox x r = Set.pi Set.univ (fun i => Ioo (x i - r) (x i + r)) := by
  ext y
  constructor
  · intro h i _
    have hi := abs_lt.mp (h i)
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
  · intro h i
    have hi := h i (mem_univ i)
    exact abs_lt.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩

theorem convex_scalarOpenBox (x : σ → ℝ) (r : ℝ) : Convex ℝ (scalarOpenBox x r) := by
  rw [scalarOpenBox_eq_pi]
  exact convex_pi fun _ _ => convex_Ioo _ _

theorem scalarOpenBox_mem_of_coordinates (center x y z : σ → ℝ) (r : ℝ)
    (hx : x ∈ scalarOpenBox center r) (hy : y ∈ scalarOpenBox center r)
    (hz : ∀ i, z i = x i ∨ z i = y i) : z ∈ scalarOpenBox center r := by
  intro i
  rcases hz i with hi | hi
  · rw [hi]
    exact hx i
  · rw [hi]
    exact hy i

theorem scalarAssignmentLine_mem_box (center x y : σ → ℝ) (r t : ℝ)
    (hx : x ∈ scalarOpenBox center r) (hy : y ∈ scalarOpenBox center r)
    (ht : t ∈ Icc (0 : ℝ) 1) : scalarAssignmentLine x y t ∈ scalarOpenBox center r := by
  have he : scalarAssignmentLine x y t = (1 - t) • x + t • y := by
    funext i
    simp only [scalarAssignmentLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact convex_scalarOpenBox center r hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)

theorem exists_scalarBox_closed_subset [Fintype σ] (S : Set (σ → ℝ))
    (hS : IsOpen S) (x : σ → ℝ) (hx : x ∈ S) :
    ∃ r > 0, scalarClosedBox x r ⊆ S := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS x hx
  refine ⟨ε / 2, by positivity, ?_⟩
  intro y hy
  apply hball
  change dist y x < ε
  have hd : dist y x ≤ ε / 2 := (dist_pi_le_iff (by positivity)).mpr (by
    intro i
    simpa only [Real.dist_eq] using hy i)
  exact lt_of_le_of_lt hd (by linarith)

theorem exists_scalarBox_closure_subset [Fintype σ] (S : Set (σ → ℝ))
    (hS : IsOpen S) (x : σ → ℝ) (hx : x ∈ S) :
    ∃ r > 0, closure (scalarOpenBox x r) ⊆ S := by
  obtain ⟨r, hr, hsub⟩ := exists_scalarBox_closed_subset S hS x hx
  exact ⟨r, hr, (closure_scalarOpenBox_subset_closed x r).trans hsub⟩

def tupleScalarBox {n : ℕ} (P : LabelledTuple n) (r : ℝ) : Set (LabelledTuple n) :=
  scalarCoordinates ⁻¹' scalarOpenBox (scalarCoordinates P) r

theorem isOpen_tupleScalarBox {n : ℕ} [NeZero n] (P : LabelledTuple n) (r : ℝ) :
    IsOpen (tupleScalarBox P r) :=
  (isOpen_scalarOpenBox _ _).preimage continuous_scalarCoordinates

theorem tupleScalarBox_self {n : ℕ} (P : LabelledTuple n) (r : ℝ) (hr : 0 < r) :
    P ∈ tupleScalarBox P r := scalarOpenBox_self _ _ hr

theorem exists_tupleScalarBox_closure_diameter {n : ℕ} [NeZero n]
    (S : Set (LabelledTuple n)) (hS : IsOpen S) (P : LabelledTuple n) (hP : P ∈ S)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ r > 0, closure (tupleScalarBox P r) ⊆ S ∧
      Metric.diam (tupleCoordinates '' tupleScalarBox P r) < δ ∧
      ∀ Q ∈ tupleScalarBox P r, ∀ R ∈ tupleScalarBox P r,
        dist (tupleCoordinates Q) (tupleCoordinates R) < δ := by
  let Ψ := fun y : ScalarCoordinate n → ℝ => tupleCoordinates (tupleOfScalarCoordinates y)
  have hΨ : Continuous Ψ := continuous_tupleCoordinates.comp continuous_tupleOfScalarCoordinates
  let U := tupleOfScalarCoordinates ⁻¹' S ∩
    Ψ ⁻¹' Metric.ball (tupleCoordinates P) (δ / 4)
  have hU : IsOpen U :=
    (hS.preimage continuous_tupleOfScalarCoordinates).inter (Metric.isOpen_ball.preimage hΨ)
  have hmem : scalarCoordinates P ∈ U := by
    constructor
    · simpa only [mem_preimage, tupleOf_scalarCoordinates] using hP
    · change dist (tupleCoordinates (tupleOfScalarCoordinates (scalarCoordinates P)))
        (tupleCoordinates P) < δ / 4
      rw [tupleOf_scalarCoordinates, dist_self]
      positivity
  obtain ⟨r, hr, hsub⟩ := exists_scalarBox_closed_subset U hU (scalarCoordinates P) hmem
  have hclosure : closure (tupleScalarBox P r) ⊆
      scalarCoordinates ⁻¹' scalarClosedBox (scalarCoordinates P) r :=
    closure_minimal (fun _ hQ => scalarOpenBox_subset_closed _ _ hQ)
      ((isClosed_scalarClosedBox _ _).preimage continuous_scalarCoordinates)
  have hrad : ∀ Q ∈ tupleScalarBox P r,
      dist (tupleCoordinates Q) (tupleCoordinates P) < δ / 4 := by
    intro Q hQ
    have hu := (hsub (scalarOpenBox_subset_closed _ _ hQ)).2
    change dist (tupleCoordinates (tupleOfScalarCoordinates (scalarCoordinates Q)))
      (tupleCoordinates P) < δ / 4 at hu
    simpa only [tupleOf_scalarCoordinates] using hu
  have hpair : ∀ Q ∈ tupleScalarBox P r, ∀ R ∈ tupleScalarBox P r,
      dist (tupleCoordinates Q) (tupleCoordinates R) < δ / 2 := by
    intro Q hQ R hR
    have hq := hrad Q hQ
    have hr' : dist (tupleCoordinates P) (tupleCoordinates R) < δ / 4 := by
      rw [dist_comm]
      exact hrad R hR
    calc
      dist (tupleCoordinates Q) (tupleCoordinates R) ≤
          dist (tupleCoordinates Q) (tupleCoordinates P) +
            dist (tupleCoordinates P) (tupleCoordinates R) := dist_triangle _ _ _
      _ < δ / 2 := by linarith
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · intro Q hQ
    have hu := (hsub (hclosure hQ)).1
    simpa only [mem_preimage, tupleOf_scalarCoordinates] using hu
  · have hd : Metric.diam (tupleCoordinates '' tupleScalarBox P r) ≤ δ / 2 := by
      apply Metric.diam_le_of_forall_dist_le (by positivity)
      rintro _ ⟨Q, hQ, rfl⟩ _ ⟨R, hR, rfl⟩
      exact (hpair Q hQ R hR).le
    exact lt_of_le_of_lt hd (by linarith)
  · intro Q hQ R hR
    exact lt_trans (hpair Q hQ R hR) (by linarith)

end

end SM


set_option pp.universes false
#print SM.scalarOpenBox
#print SM.scalarClosedBox
#print SM.tupleScalarBox
#check SM.isOpen_scalarOpenBox
#print axioms SM.isOpen_scalarOpenBox
#check SM.isClosed_scalarClosedBox
#print axioms SM.isClosed_scalarClosedBox
#check SM.scalarOpenBox_subset_closed
#print axioms SM.scalarOpenBox_subset_closed
#check SM.closure_scalarOpenBox_subset_closed
#print axioms SM.closure_scalarOpenBox_subset_closed
#check SM.scalarOpenBox_self
#print axioms SM.scalarOpenBox_self
#check SM.scalarOpenBox_eq_pi
#print axioms SM.scalarOpenBox_eq_pi
#check SM.convex_scalarOpenBox
#print axioms SM.convex_scalarOpenBox
#check SM.scalarOpenBox_mem_of_coordinates
#print axioms SM.scalarOpenBox_mem_of_coordinates
#check SM.scalarAssignmentLine_mem_box
#print axioms SM.scalarAssignmentLine_mem_box
#check SM.exists_scalarBox_closed_subset
#print axioms SM.exists_scalarBox_closed_subset
#check SM.exists_scalarBox_closure_subset
#print axioms SM.exists_scalarBox_closure_subset
#check SM.isOpen_tupleScalarBox
#print axioms SM.isOpen_tupleScalarBox
#check SM.tupleScalarBox_self
#print axioms SM.tupleScalarBox_self
#check SM.exists_tupleScalarBox_closure_diameter
#print axioms SM.exists_tupleScalarBox_closure_diameter

open Set
example {n : ℕ} (P : SM.LabelledTuple n) (r : ℝ) :
    SM.scalarCoordinates '' SM.tupleScalarBox P r =
      SM.scalarOpenBox (SM.scalarCoordinates P) r := by
  ext x
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact hQ
  · intro hx
    refine ⟨SM.tupleOfScalarCoordinates x, ?_, SM.scalarCoordinates_tupleOf x⟩
    simpa only [SM.tupleScalarBox, mem_preimage, SM.scalarCoordinates_tupleOf] using hx

example {n : ℕ} (hn : 3 ≤ n) (S : Set (SM.LabelledTuple n)) (hS : IsOpen S)
    (P : SM.LabelledTuple n) (hP : P ∈ S) (δ : ℝ) (hδ : 0 < δ) :
    ∃ r > 0, P ∈ SM.tupleScalarBox P r ∧ IsOpen (SM.tupleScalarBox P r) ∧
      closure (SM.tupleScalarBox P r) ⊆ S ∧
      Metric.diam (SM.tupleCoordinates '' SM.tupleScalarBox P r) < δ := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨r, hr, hc, hd, _⟩ := SM.exists_tupleScalarBox_closure_diameter S hS P hP δ hδ
  exact ⟨r, hr, SM.tupleScalarBox_self P r hr, SM.isOpen_tupleScalarBox P r, hc, hd⟩
