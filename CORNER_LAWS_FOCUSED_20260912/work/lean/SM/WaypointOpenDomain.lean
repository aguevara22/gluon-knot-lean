import SM.JointWaypointConstraints

/-! Finite products of prescribed open waypoint sets form one actual nonempty
open subset of the joint scalar-assignment space. The same joint choice satisfies
every central-leg condition while respecting every prescribed waypoint set. -/

namespace SM

noncomputable section

variable {κ σ : Type*}

def waypointProjection (k : κ) (W : κ × σ → ℝ) : σ → ℝ := fun z => W (k, z)

theorem continuous_waypointProjection (k : κ) : Continuous (waypointProjection (σ := σ) k) :=
  continuous_pi fun z => continuous_apply (k, z)

def waypointDomain (O : κ → Set (σ → ℝ)) : Set (κ × σ → ℝ) :=
  {W | ∀ k, waypointProjection k W ∈ O k}

theorem isOpen_waypointDomain [Finite κ] (O : κ → Set (σ → ℝ))
    (hO : ∀ k, IsOpen (O k)) : IsOpen (waypointDomain O) := by
  have he : waypointDomain O = ⋂ k, waypointProjection k ⁻¹' O k := by
    ext W
    simp [waypointDomain]
  rw [he]
  exact isOpen_iInter_of_finite fun k => (hO k).preimage (continuous_waypointProjection k)

theorem nonempty_waypointDomain (O : κ → Set (σ → ℝ))
    (hO : ∀ k, (O k).Nonempty) : (waypointDomain O).Nonempty := by
  choose W hW using hO
  refine ⟨fun x => W x.1 x.2, ?_⟩
  exact hW

theorem exists_joint_waypoint_conditions_in_domains {n : ℕ} [NeZero n]
    [Finite κ] (hn : 3 ≤ n) {ι : Type*} [Finite ι]
    (legs : ι → CoordinateWaypointLeg κ (ScalarCoordinate n))
    (O : κ → Set (ScalarCoordinate n → ℝ))
    (hOpen : ∀ k, IsOpen (O k)) (hNonempty : ∀ k, (O k).Nonempty) :
    ∃ W : κ × ScalarCoordinate n → ℝ,
      (∀ k, waypointProjection k W ∈ O k) ∧ ∀ i, JointLegConditions (legs i) W := by
  exact exists_joint_waypoint_conditions hn legs (waypointDomain O)
    (isOpen_waypointDomain O hOpen) (nonempty_waypointDomain O hNonempty)

end

end SM
