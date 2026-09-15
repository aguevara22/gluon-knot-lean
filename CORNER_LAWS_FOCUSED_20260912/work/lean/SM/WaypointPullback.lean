import SM.CoordinateIsolation

/-! Joint waypoint variables retain their scalar-coordinate name. Every hybrid
selection is therefore injective, including its restriction to precisely the
fixed coordinates of a leg. Polynomial nonvanishing survives these pullbacks. -/

namespace SM

open MvPolynomial

noncomputable section

variable {κ σ : Type*}

def waypointSelection (tag : σ → κ) (z : σ) : κ × σ := (tag z, z)

theorem waypointSelection_injective (tag : σ → κ) :
    Function.Injective (waypointSelection tag) := by
  intro z w h
  exact congrArg Prod.snd h

def waypointHybrid (tag : σ → κ) (W : κ × σ → ℝ) : σ → ℝ :=
  fun z => W (waypointSelection tag z)

def waypointPullback (tag : σ → κ) : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial (κ × σ) ℝ :=
  rename (waypointSelection tag)

theorem waypointPullback_injective (tag : σ → κ) :
    Function.Injective (waypointPullback tag) :=
  rename_injective _ (waypointSelection_injective tag)

theorem waypointPullback_ne_zero (tag : σ → κ) (p : MvPolynomial σ ℝ) (hp : p ≠ 0) :
    waypointPullback tag p ≠ 0 := by
  intro h
  apply hp
  apply waypointPullback_injective tag
  simpa only [map_zero] using h

@[simp] theorem eval_waypointPullback (tag : σ → κ) (W : κ × σ → ℝ)
    (p : MvPolynomial σ ℝ) :
    eval W (waypointPullback tag p) = eval (waypointHybrid tag W) p :=
  eval_rename (k := waypointSelection tag) W p

def remainingWaypointSelection (z : σ) (tag : σ → κ) (w : {w : σ // w ≠ z}) : κ × σ :=
  waypointSelection tag w

theorem remainingWaypointSelection_injective (z : σ) (tag : σ → κ) :
    Function.Injective (remainingWaypointSelection z tag) := by
  intro a b h
  apply Subtype.ext
  exact congrArg Prod.snd h

def remainingWaypointPullback (z : σ) (tag : σ → κ) :
    RemainingPolynomial z →ₐ[ℝ] MvPolynomial (κ × σ) ℝ :=
  rename (remainingWaypointSelection z tag)

theorem remainingWaypointPullback_injective (z : σ) (tag : σ → κ) :
    Function.Injective (remainingWaypointPullback z tag) :=
  rename_injective _ (remainingWaypointSelection_injective z tag)

theorem remainingWaypointPullback_ne_zero (z : σ) (tag : σ → κ)
    (p : RemainingPolynomial z) (hp : p ≠ 0) :
    remainingWaypointPullback z tag p ≠ 0 := by
  intro h
  apply hp
  apply remainingWaypointPullback_injective z tag
  simpa only [map_zero] using h

@[simp] theorem eval_remainingWaypointPullback (z : σ) (tag : σ → κ)
    (W : κ × σ → ℝ) (p : RemainingPolynomial z) :
    eval W (remainingWaypointPullback z tag p) =
      eval (fun w : {w : σ // w ≠ z} => waypointHybrid tag W w) p :=
  eval_rename (k := remainingWaypointSelection z tag) W p

theorem coordinateDifference_ne_zero (i j : σ) (hij : i ≠ j) :
    (X i - X j : MvPolynomial σ ℝ) ≠ 0 := by
  intro h
  exact hij (X_injective (sub_eq_zero.mp h))

theorem waypoint_coordinateDifference_ne_zero (tag : σ → κ) (i j : σ) (hij : i ≠ j) :
    waypointPullback tag (X i - X j) ≠ 0 :=
  waypointPullback_ne_zero tag _ (coordinateDifference_ne_zero i j hij)

@[simp] theorem eval_waypoint_coordinateDifference (tag : σ → κ) (W : κ × σ → ℝ)
    (i j : σ) : eval W (waypointPullback tag (X i - X j)) =
      waypointHybrid tag W i - waypointHybrid tag W j := by
  simp

end

end SM
