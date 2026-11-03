import FiniteCriticalRootAvoidance

set_option autoImplicit false
namespace DirectGLSSW.FiniteAffineLineAvoidance
open FiniteCriticalRootAvoidance
noncomputable section
attribute [local instance] Classical.propDecidable
abbrev Point := PlanarPoint ℝ

/-- A translated parabola meets each proper affine line in the zero set of a
nonzero quadratic. Its linear/quadratic coefficients cannot both vanish. -/
def lineParabolaData (A B p : Point) : CubicData :=
  (planarDet (B-A) (p-A),planarDet (B-A) (1,0),planarDet (B-A) (0,1),0)

theorem lineParabolaData_nonzero (A B p : Point) (hAB : A ≠ B) :
    NonzeroCoefficients (lineParabolaData A B p) := by
  by_cases h1 : planarDet (B-A) (1,0) ≠ 0
  · exact Or.inr (Or.inl h1)
  by_cases h2 : planarDet (B-A) (0,1) ≠ 0
  · exact Or.inr (Or.inr (Or.inl h2))
  have h1' : planarDet (B-A) (1,0) = 0 := not_ne_iff.mp h1
  have h2' : planarDet (B-A) (0,1) = 0 := not_ne_iff.mp h2
  apply False.elim
  apply hAB
  apply Prod.ext <;> dsimp [planarDet] at h1' h2' <;> linarith

theorem lineParabolaData_value (A B p : Point) (t : ℝ) :
    cubicValue (lineParabolaData A B p) t = planarDet (B-A) (p+(t,t^2)-A) := by
  dsimp [lineParabolaData,cubicValue,planarDet]
  ring

/-- Explicit arbitrarily small perturbation avoiding any finite family of proper carriers. -/
theorem exists_near_avoiding_lines {ι : Type*} [Fintype ι]
    (A B : ι → Point) (hproper : ∀ i, A i ≠ B i) (p : Point)
    (η : ℝ) (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ t < min 1 η ∧
      |(p+(t,t^2)).1-p.1| < η ∧ |(p+(t,t^2)).2-p.2| < η ∧
      ∀ i, planarDet (B i-A i) (p+(t,t^2)-A i) ≠ 0 := by
  obtain ⟨t,ht,htb,havoid⟩ := finite_cubic_avoidance
    (fun i => lineParabolaData (A i) (B i) p)
    (fun i => lineParabolaData_nonzero _ _ _ (hproper i)) (min 1 η)
    (lt_min (by norm_num) hη)
  have ht1 : t < 1 := lt_of_lt_of_le htb (min_le_left _ _)
  have htη : t < η := lt_of_lt_of_le htb (min_le_right _ _)
  have ht2 : t^2 < η := by nlinarith
  refine ⟨t,ht,htb,?_,?_,?_⟩
  · simpa only [Prod.fst_add,add_sub_cancel_left,abs_of_pos ht] using htη
  · simpa only [Prod.snd_add,add_sub_cancel_left,abs_of_nonneg (sq_nonneg t)] using ht2
  · intro i
    rw [← lineParabolaData_value]
    exact havoid i

/-- Finset form for a sequential vertex construction; no special position of p is required. -/
theorem exists_near_avoiding_finite_lines (L : Finset (Point × Point))
    (hproper : ∀ l ∈ L, l.1 ≠ l.2) (p : Point) (η : ℝ) (hη : 0 < η) :
    ∃ q : Point, |q.1-p.1| < η ∧ |q.2-p.2| < η ∧
      ∀ l ∈ L, planarDet (l.2-l.1) (q-l.1) ≠ 0 := by
  obtain ⟨t,_,_,hx,hy,havoid⟩ := exists_near_avoiding_lines
    (fun l : L => l.val.1) (fun l : L => l.val.2)
    (fun l => hproper l.val l.property) p η hη
  exact ⟨p+(t,t^2),hx,hy,fun l hl => havoid ⟨l,hl⟩⟩






end
end DirectGLSSW.FiniteAffineLineAvoidance
