import SM.TurningNumber

/-! # SM cf:lem-turnlift — tangent lifts and principal turns (row 96)

Source: reference/SM/sm-3-statesum.tex:3542-3578 (proof 3579-3643). The objects (`DirectionLoop`,
`IsSeamLift`, `tw`, `ClosedC1Curve`, `tangentLoop`, `rot`) are those of the built module
`SM.TurningNumber` (row 95, cf:def-turning); the polygon rotation is the accepted `SM.rotationNumber`
with its lem:rot clauses `SM.rotation_number` (RotationTheorem.lean). Plan: work/drafts/TurnLift_PLAN.md.

Printed notion → Lean model (each documented again at its definition):
* tangent-angle lift of a direction path on an interval → `IsLiftOn u θ a b`
  (`IsSeamLift T θ ↔ IsLiftOn T θ 0 1` is `Iff.rfl`);
* orientation-preserving reparametrisation of the circle → `Reparam` (the printed increasing
  representative `φ : ℝ → ℝ`, `φ (s+1) = φ s + 1`), acting by `DirectionLoop.reparam`;
* continuous homotopy through direction loops → `DirectionHomotopy` (`H : ℝ × ℝ → Plane`, each
  `H (t, ·)` a direction loop; a printed `[0,1]`-homotopy extends to `ℝ` by `Set.projIcc`);
* regular homotopy of closed `C¹` regular curves → `RegularHomotopy` (a family `Γ (t, ·)` of closed
  `C¹` curves with jointly continuous nonvanishing derivative `Γ'`); its tangent loops form a
  `DirectionHomotopy`;
* orientation reversal → `ClosedC1Curve.reverse` (`s ↦ γ (−s)`);
* (iii) corner rounding / arc replacement / `GL⁺(2,ℝ)` paths → direction-loop level models
  (`rot_eq_rotationNumber_of_rounding`, `rot_sub_rot_of_replace`, `GLPlusPath`,
  `glplus_increment_sub_invariant`), see the docstrings there.

Method: lifts are produced by Mathlib's covering-space lifting through `Circle.exp`
(`IsCoveringMap.existsUnique_continuousMap_lifts`, `ℝ` and `ℝ × ℝ` being simply connected), and
"continuous integer-valued ⇒ constant" is `IsCoveringMap.const_of_comp`; the printed atan2
subdivision is not reproduced. The checked objects are the printed statements. -/

namespace SM

open Set

/-! ## Lifts on intervals (shared device for (i) and (iii)) -/

/-- A tangent-angle lift of the direction path `u` on the interval `[a, b]`: `θ` continuous on
`[a, b]` with `u s = (cos θ s, sin θ s)` there. The printed seam lift is the case `[0, 1]`. -/
def IsLiftOn (u : ℝ → Plane) (θ : ℝ → ℝ) (a b : ℝ) : Prop :=
  ContinuousOn θ (Icc a b) ∧ ∀ s ∈ Icc a b, u s = (Real.cos (θ s), Real.sin (θ s))

theorem isSeamLift_iff_isLiftOn (T : ℝ → Plane) (θ : ℝ → ℝ) :
    IsSeamLift T θ ↔ IsLiftOn T θ 0 1 := Iff.rfl

theorem IsLift.isLiftOn {u : ℝ → Plane} {θ : ℝ → ℝ} (h : IsLift u θ) (a b : ℝ) :
    IsLiftOn u θ a b :=
  ⟨h.1.continuousOn, fun s _ => h.2 s⟩

theorem IsLiftOn.circleExp_coe {u : ℝ → Plane} {θ : ℝ → ℝ} {a b : ℝ} (h : IsLiftOn u θ a b)
    {s : ℝ} (hs : s ∈ Icc a b) : ((Circle.exp (θ s) : Circle) : ℂ) = planeComplex (u s) := by
  rw [circleExp_planeComplex, h.2 s hs]

/-- Two lifts of the same direction path on `[a, b]` have the same increment. -/
theorem IsLiftOn.increment_eq {u : ℝ → Plane} {θ₁ θ₂ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h₁ : IsLiftOn u θ₁ a b) (h₂ : IsLiftOn u θ₂ a b) : θ₁ b - θ₁ a = θ₂ b - θ₂ a := by
  have := Circle.isCoveringMap_exp.constOn_of_comp (g := fun s => θ₁ s - θ₂ s)
    isPreconnected_Icc (h₁.1.sub h₂.1) (fun s hs s' hs' => ?_) (a := b) (a' := a)
    ⟨hab, le_rfl⟩ ⟨le_rfl, hab⟩
  · have h : θ₁ b - θ₂ b = θ₁ a - θ₂ a := this
    linarith
  · have e : ∀ x ∈ Icc a b, Circle.exp (θ₁ x) = Circle.exp (θ₂ x) := fun x hx =>
      Subtype.ext (by rw [h₁.circleExp_coe hx, h₂.circleExp_coe hx])
    show Circle.exp (θ₁ s - θ₂ s) = Circle.exp (θ₁ s' - θ₂ s')
    rw [Circle.exp_sub, Circle.exp_sub, e s hs, e s' hs', div_self', div_self']

/-- A lift of a direction path that is constant on `[a, b]` has zero increment there. -/
theorem IsLiftOn.increment_eq_zero_of_const {u : ℝ → Plane} {θ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : IsLiftOn u θ a b) {v : Plane} (hv : ∀ s ∈ Icc a b, u s = v) : θ b = θ a := by
  refine Circle.isCoveringMap_exp.constOn_of_comp isPreconnected_Icc h.1
    (fun s hs s' hs' => ?_) ⟨hab, le_rfl⟩ ⟨le_rfl, hab⟩
  exact Subtype.ext (by rw [h.circleExp_coe hs, h.circleExp_coe hs', hv s hs, hv s' hs'])

/-- Precomposing a lift with a continuous change of parameter gives a lift of the reparametrised
path: if `u s = w (ψ s)` on `[a, b]` and `θ` lifts `w` globally, then `θ ∘ ψ` lifts `u` on `[a, b]`. -/
theorem IsLift.comp_isLiftOn {w : ℝ → Plane} {θ : ℝ → ℝ} (h : IsLift w θ) {u : ℝ → Plane}
    {ψ : ℝ → ℝ} {a b : ℝ} (hψ : ContinuousOn ψ (Icc a b)) (hu : ∀ s ∈ Icc a b, u s = w (ψ s)) :
    IsLiftOn u (fun s => θ (ψ s)) a b :=
  ⟨h.1.comp_continuousOn hψ, fun s hs => by rw [hu s hs, h.2 (ψ s)]⟩

/-- Global tangent-angle lift of a continuous unit-vector map on a simply connected, locally path
connected space (used for `ℝ` and for `ℝ × ℝ`): covering-space lifting through `Circle.exp`. -/
theorem exists_lift_of_unit {α : Type*} [TopologicalSpace α] [SimplyConnectedSpace α]
    [LocallyPathConnectedSpace α] [Nonempty α] {u : α → Plane} (hu : Continuous u)
    (h1 : ∀ p, euclideanLength (u p) = 1) :
    ∃ Θ : α → ℝ, Continuous Θ ∧ ∀ p, u p = (Real.cos (Θ p), Real.sin (Θ p)) := by
  obtain ⟨a₀⟩ := ‹Nonempty α›
  let f : C(α, Circle) := ⟨fun p => unitCircle (u p) (h1 p), continuous_unitCircle hu h1⟩
  obtain ⟨θ₀, -, hθ₀⟩ := Circle.surjOn_exp_neg_pi_pi (Set.mem_univ (f a₀))
  obtain ⟨F, ⟨-, hF⟩, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f a₀ θ₀ hθ₀
  exact ⟨F, F.continuous, fun p => (circleExp_eq_unitCircle_iff (h1 p) (F p)).mp (congrFun hF p)⟩

/-- A continuous real function whose values are all multiples of `2π` (`exp (g t) = 1`) is constant
on a preconnected space: the "continuous integer-valued function is constant" step. -/
theorem const_of_circleExp_eq_one {α : Type*} [TopologicalSpace α] [PreconnectedSpace α]
    {g : α → ℝ} (hg : Continuous g) (h : ∀ a, Circle.exp (g a) = 1) (a a' : α) : g a = g a' :=
  Circle.isCoveringMap_exp.const_of_comp hg (fun x y => by rw [h x, h y]) a a'

theorem circleExp_sub_eq_one {x y : ℝ} (h : Circle.exp x = Circle.exp y) :
    Circle.exp (x - y) = 1 := by
  rw [Circle.exp_sub, h, div_self']

/-- `Circle.exp (θ p) = Circle.exp (θ' p')` whenever both lift the same plane vector. -/
theorem circleExp_eq_of_eq {u v : Plane} {x y : ℝ} (hx : u = (Real.cos x, Real.sin x))
    (hy : v = (Real.cos y, Real.sin y)) (huv : u = v) : Circle.exp x = Circle.exp y := by
  apply Subtype.ext
  rw [circleExp_planeComplex, circleExp_planeComplex, ← hx, ← hy, huv]

/-! ## (i-c) Orientation-preserving reparametrisation -/

/-- An orientation-preserving reparametrisation of the circle `ℝ/ℤ`, given by the printed
"increasing representative `φ : ℝ → ℝ` with `φ (s+1) = φ s + 1`" (sm-3:3600-3603): continuous,
strictly increasing, of degree one. (The proof of `tw_reparam` uses only continuity and the
degree-one identity.) -/
structure Reparam where
  φ : ℝ → ℝ
  continuous : Continuous φ
  strictMono : StrictMono φ
  add_one : ∀ s, φ (s + 1) = φ s + 1

/-- The reparametrised loop `s ↦ T (φ s)`. -/
def DirectionLoop.reparam (L : DirectionLoop) (φ : Reparam) : DirectionLoop where
  T := fun s => L.T (φ.φ s)
  continuous := L.continuous.comp φ.continuous
  periodic := fun s => by
    show L.T (φ.φ (s + 1)) = L.T (φ.φ s)
    rw [φ.add_one]
    exact L.periodic _
  unit := fun s => L.unit _

@[simp] theorem DirectionLoop.reparam_T (L : DirectionLoop) (φ : Reparam) (s : ℝ) :
    (L.reparam φ).T s = L.T (φ.φ s) := rfl

/-- `tw` is unchanged by an orientation-preserving reparametrisation: `θ ∘ φ` lifts `T ∘ φ`, and its
increment `θ (φ 0 + 1) − θ (φ 0)` over one period equals `θ 1 − θ 0`. -/
theorem tw_reparam (L : DirectionLoop) (φ : Reparam) : tw (L.reparam φ) = tw L := by
  have hθ : IsLift L.T L.lift := L.lift_isLift
  have hθφ : IsLift (L.reparam φ).T (fun s => L.lift (φ.φ s)) :=
    ⟨hθ.1.comp φ.continuous, fun s => hθ.2 (φ.φ s)⟩
  rw [tw_eq_of_isSeamLift (L.reparam φ) hθφ.isSeamLift]
  show (L.lift (φ.φ 1) - L.lift (φ.φ 0)) / (2 * Real.pi) = tw L
  have h1 : φ.φ 1 = φ.φ 0 + 1 := by simpa using φ.add_one 0
  rw [h1, DirectionLoop.lift_add_one_sub hθ (φ.φ 0)]
  rfl

/-! ## (i-d) Homotopies through direction loops -/

/-- A continuous homotopy through direction loops: `H : ℝ × ℝ → Plane` continuous, with every
`H (t, ·)` a direction loop (1-periodic, unit length). The homotopy parameter ranges over `ℝ`; a
printed homotopy on `0 ≤ t ≤ 1` is the case `H (t, s) = H₀ (projIcc 0 1 t, s)`. -/
structure DirectionHomotopy where
  H : ℝ × ℝ → Plane
  continuous : Continuous H
  periodic : ∀ t s, H (t, s + 1) = H (t, s)
  unit : ∀ p, euclideanLength (H p) = 1

namespace DirectionHomotopy

/-- The direction loop `H (t, ·)` at time `t`. -/
def loop (h : DirectionHomotopy) (t : ℝ) : DirectionLoop where
  T := fun s => h.H (t, s)
  continuous := h.continuous.comp (continuous_const.prodMk continuous_id)
  periodic := fun s => h.periodic t s
  unit := fun s => h.unit (t, s)

@[simp] theorem loop_T (h : DirectionHomotopy) (t s : ℝ) : (h.loop t).T s = h.H (t, s) := rfl

/-- `tw` is constant along a continuous homotopy through direction loops: lift the homotopy
globally on the simply connected `ℝ × ℝ`; the increment `Θ (t, 1) − Θ (t, 0)` is continuous in `t`
and a multiple of `2π`, hence constant. -/
theorem tw_loop_eq (h : DirectionHomotopy) (t t' : ℝ) : tw (h.loop t) = tw (h.loop t') := by
  obtain ⟨Θ, hΘc, hΘ⟩ := exists_lift_of_unit h.continuous h.unit
  have hlift : ∀ t, IsLift (h.loop t).T (fun s => Θ (t, s)) := fun t =>
    ⟨hΘc.comp (continuous_const.prodMk continuous_id), fun s => hΘ (t, s)⟩
  rw [tw_eq_of_isSeamLift _ (hlift t).isSeamLift, tw_eq_of_isSeamLift _ (hlift t').isSeamLift]
  have hg : Continuous fun t => Θ (t, 1) - Θ (t, 0) :=
    (hΘc.comp (continuous_id.prodMk continuous_const)).sub
      (hΘc.comp (continuous_id.prodMk continuous_const))
  have hone : ∀ t, Circle.exp (Θ (t, 1) - Θ (t, 0)) = 1 := fun t =>
    circleExp_sub_eq_one (circleExp_eq_of_eq (hΘ (t, 1)) (hΘ (t, 0)) (by simpa using h.periodic t 0))
  rw [const_of_circleExp_eq_one hg hone t t']

end DirectionHomotopy

/-! ## (i-e) Regular homotopies of closed `C¹` regular curves -/

/-- A regular homotopy: a family `Γ (t, ·)` of closed `C¹` regular curves, jointly continuous,
whose derivatives `Γ' (t, s)` (in `s`) are jointly continuous and never vanish. Its normalised
tangents form a continuous homotopy through direction loops (`tangentHomotopy`). -/
structure RegularHomotopy where
  Γ : ℝ × ℝ → Plane
  Γ' : ℝ × ℝ → Plane
  continuous : Continuous Γ
  hasDerivAt : ∀ t s, HasDerivAt (fun s => Γ (t, s)) (Γ' (t, s)) s
  continuous_deriv : Continuous Γ'
  regular : ∀ p, Γ' p ≠ 0
  periodic : ∀ t s, Γ (t, s + 1) = Γ (t, s)

namespace RegularHomotopy

/-- The closed `C¹` regular curve at time `t`. -/
def curve (h : RegularHomotopy) (t : ℝ) : ClosedC1Curve where
  γ := fun s => h.Γ (t, s)
  γ' := fun s => h.Γ' (t, s)
  hasDerivAt := h.hasDerivAt t
  continuous_deriv := h.continuous_deriv.comp (continuous_const.prodMk continuous_id)
  regular := fun s => h.regular (t, s)
  periodic := fun s => h.periodic t s

/-- The homotopy of normalised tangents `T_{Γ(t,·)}`. -/
noncomputable def tangentHomotopy (h : RegularHomotopy) : DirectionHomotopy where
  H := fun p => normalize (h.Γ' p)
  continuous := continuous_normalize_comp h.continuous_deriv h.regular
  periodic := fun t s => congrArg normalize ((h.curve t).deriv_periodic s)
  unit := fun p => euclideanLength_normalize (h.regular p)

theorem tangentHomotopy_loop (h : RegularHomotopy) (t : ℝ) :
    h.tangentHomotopy.loop t = (h.curve t).tangentLoop := rfl

/-- The rotation of a closed `C¹` regular curve is invariant under regular homotopy. -/
theorem rot_curve_eq (h : RegularHomotopy) (t t' : ℝ) : (h.curve t).rot = (h.curve t').rot := by
  show tw (h.curve t).tangentLoop = tw (h.curve t').tangentLoop
  rw [← tangentHomotopy_loop, ← tangentHomotopy_loop]
  exact h.tangentHomotopy.tw_loop_eq t t'

end RegularHomotopy

/-! ## (i-f) Orientation reversal -/

theorem normalize_neg (v : Plane) : normalize (-v) = -normalize v := by
  rw [normalize, normalize, euclideanLength_neg, smul_neg]

namespace ClosedC1Curve

/-- The oppositely oriented curve `s ↦ γ (−s)`, with derivative `−γ' (−s)`. -/
noncomputable def reverse (c : ClosedC1Curve) : ClosedC1Curve where
  γ := fun s => c.γ (-s)
  γ' := fun s => -c.γ' (-s)
  hasDerivAt := fun t => by
    have := (c.hasDerivAt (-t)).scomp t (hasDerivAt_neg t)
    simpa [Function.comp_def] using this
  continuous_deriv := (c.continuous_deriv.comp continuous_neg).neg
  regular := fun t => neg_ne_zero.mpr (c.regular (-t))
  periodic := fun s => by
    show c.γ (-(s + 1)) = c.γ (-s)
    have := c.periodic (-(s + 1))
    rw [show -(s + 1) + 1 = -s by ring] at this
    exact this.symm

@[simp] theorem reverse_γ (c : ClosedC1Curve) (s : ℝ) : c.reverse.γ s = c.γ (-s) := rfl
@[simp] theorem reverse_γ' (c : ClosedC1Curve) (s : ℝ) : c.reverse.γ' s = -c.γ' (-s) := rfl

theorem reverse_tangentLoop_T (c : ClosedC1Curve) (s : ℝ) :
    c.reverse.tangentLoop.T s = -c.tangentLoop.T (-s) := by
  show normalize (-c.γ' (-s)) = -normalize (c.γ' (-s))
  exact normalize_neg _

/-- Reversing the orientation negates the rotation: `θ (−s) + π` lifts the reversed tangent loop
`−T_γ (−s)`, and its increment over `[0, 1]` is `θ (−1) − θ 0 = −(θ 1 − θ 0)`. -/
theorem rot_reverse (c : ClosedC1Curve) : c.reverse.rot = -c.rot := by
  set θ := c.tangentLoop.lift with hθdef
  have hθ : IsLift c.tangentLoop.T θ := c.tangentLoop.lift_isLift
  have hrev : IsLift c.reverse.tangentLoop.T (fun s => θ (-s) + Real.pi) := by
    refine ⟨(hθ.1.comp continuous_neg).add continuous_const, fun s => ?_⟩
    rw [reverse_tangentLoop_T, hθ.2 (-s), Real.cos_add_pi, Real.sin_add_pi]
    rfl
  show tw c.reverse.tangentLoop = -tw c.tangentLoop
  rw [tw_eq_of_isSeamLift _ hrev.isSeamLift]
  have h := DirectionLoop.lift_add_one_sub hθ (-1)
  rw [show (-1 : ℝ) + 1 = 0 by norm_num] at h
  show (θ (-1) + Real.pi - (θ (-0) + Real.pi)) / (2 * Real.pi) = -((θ 1 - θ 0) / (2 * Real.pi))
  rw [neg_zero, ← neg_div]
  congr 1
  linarith

end ClosedC1Curve

/-! ## (ii) Polygons: the accepted lem:rot bundle `SM.rotation_number` -/

/-- `2π rot(L) = Σ ϑ_i` for a regular polygon: the accepted definition
`rotationNumber P = (Σ principalTurn P i) / 2π` (RotationNumber.lean). -/
theorem two_pi_mul_rotationNumber {n : ℕ} [NeZero n] (P : LabelledTuple n) :
    2 * Real.pi * rotationNumber P = ∑ i : ZMod n, principalTurn P i := by
  unfold rotationNumber
  exact mul_div_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))

/-! ## (iii-a) Corner rounding -/

/-- Reindexing a sum over `range n` by the natural cast `ℕ → ZMod n`. -/
theorem sum_range_natCast_eq_sum_zmod {n : ℕ} [NeZero n] (f : ZMod n → ℝ) :
    ∑ k ∈ Finset.range n, f (k : ZMod n) = ∑ i : ZMod n, f i := by
  refine Finset.sum_nbij' (fun k : ℕ => (k : ZMod n)) (fun i : ZMod n => i.val) ?_ ?_ ?_ ?_ ?_
  · intro k _
    exact Finset.mem_univ _
  · intro i _
    exact Finset.mem_range.mpr (ZMod.val_lt i)
  · intro k hk
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hk)
  · intro i _
    exact ZMod.natCast_zmod_val i
  · intro k _
    rfl

/-- (iii-a) Corner rounding, direction-loop reading of "a closed `C¹` regular curve obtained from
`L` by replacing every corner by a regular arc whose compatible tangent-angle lift has increment
`ϑ_i`" (sm-3:3561-3563, proof 3625-3628). The curve `γ` is subdivided by
`0 = a 0 ≤ b 0 ≤ a 1 ≤ b 1 ≤ ⋯ ≤ b (n-1) ≤ a n = 1`: on `[a k, b k]` runs the arc rounding the
corner at vertex `k` (between edges `k−1` and `k`), whose tangent direction admits a lift on that
interval of increment `principalTurn L k` (the compatible lift: any lift on the arc, since all lifts
on an interval have the same increment); on `[b k, a (k+1)]` the curve runs straight along edge `k`,
so its tangent direction is the constant `edge L k / |edge L k|`. Then `rot γ = rot L`: the global
lift increments telescope to `Σ ϑ_k`, which is `2π · rotationNumber L` by definition. -/
theorem rot_eq_rotationNumber_of_rounding {n : ℕ} [NeZero n] (L : LabelledTuple n)
    (γ : ClosedC1Curve) (a b : ℕ → ℝ) (ha0 : a 0 = 0) (han : a n = 1)
    (hab : ∀ k < n, a k ≤ b k) (hba : ∀ k < n, b k ≤ a (k + 1))
    (hcorner : ∀ k < n, ∃ θ : ℝ → ℝ, IsLiftOn γ.tangentLoop.T θ (a k) (b k) ∧
      θ (b k) - θ (a k) = principalTurn L (k : ZMod n))
    (hstraight : ∀ k < n, ∀ s ∈ Icc (b k) (a (k + 1)),
      γ.tangentLoop.T s = normalize (edge L (k : ZMod n))) :
    γ.rot = rotationNumber L := by
  have hΘ : IsLift γ.tangentLoop.T γ.tangentLoop.lift := γ.tangentLoop.lift_isLift
  have hpiece : ∀ k < n, γ.tangentLoop.lift (a (k + 1)) - γ.tangentLoop.lift (a k) =
      principalTurn L (k : ZMod n) := by
    intro k hk
    obtain ⟨θ, hθ, hinc⟩ := hcorner k hk
    have h1 : γ.tangentLoop.lift (b k) - γ.tangentLoop.lift (a k) = principalTurn L (k : ZMod n) := by
      rw [IsLiftOn.increment_eq (hab k hk) (hΘ.isLiftOn _ _) hθ]
      exact hinc
    have h2 : γ.tangentLoop.lift (a (k + 1)) = γ.tangentLoop.lift (b k) :=
      IsLiftOn.increment_eq_zero_of_const (hba k hk) (hΘ.isLiftOn _ _) (hstraight k hk)
    linarith
  have hsum : γ.tangentLoop.lift 1 - γ.tangentLoop.lift 0 = ∑ i : ZMod n, principalTurn L i := by
    have h01 : γ.tangentLoop.lift 1 - γ.tangentLoop.lift 0 =
        γ.tangentLoop.lift (a n) - γ.tangentLoop.lift (a 0) := by rw [ha0, han]
    rw [h01, ← Finset.sum_range_sub (fun k => γ.tangentLoop.lift (a k)) n,
      ← sum_range_natCast_eq_sum_zmod]
    exact Finset.sum_congr rfl (fun k hk => hpiece k (Finset.mem_range.mp hk))
  show tw γ.tangentLoop = rotationNumber L
  unfold tw rotationNumber
  rw [hsum]

/-! ## (iii-b) Arc replacement -/

/-- (iii-b) Arc replacement, direction-loop reading (sm-3:3565-3573, proof 3630-3634). The closed
`C¹` regular curves `Fb = a ∪ b` and `Fc = a ∪ c` are parametrised (after a seam shift, which does
not change `rot`: `tw_shift`) so that the arc `b` occupies `[0, λ]` of `Fb` and the arc `c` occupies
`[0, μ]` of `Fc`; the common complementary arc `a` is traversed by both, `Fb` on `[λ, 1]` and `Fc` on
`[μ, 1]`, up to a continuous change of parameter `ψ` with `ψ λ = μ`, `ψ 1 = 1` and
`T_{Fb} s = T_{Fc} (ψ s)` (the same oriented tangents along `a`). "Same endpoints and same oriented
tangent rays at both endpoints of `b`, `c`" is what makes `Fb`, `Fc` closed `C¹` regular curves and
is carried by those hypotheses. `θb`, `θc` are tangent-angle lifts on the arcs with increments
`Δb = θb λ − θb 0`, `Δc = θc μ − θc 0` (any lifts: increments are lift-independent, and the printed
normalisation "equal initial values" is not needed). Then `rot Fc − rot Fb = (Δc − Δb) / 2π`. -/
theorem rot_sub_rot_of_replace (Fb Fc : ClosedC1Curve) {lam mu : ℝ} (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (hmu0 : 0 ≤ mu) {ψ : ℝ → ℝ} (hψ : ContinuousOn ψ (Icc lam 1))
    (hψlam : ψ lam = mu) (hψ1 : ψ 1 = 1)
    (hcompl : ∀ s ∈ Icc lam 1, Fb.tangentLoop.T s = Fc.tangentLoop.T (ψ s))
    {θb θc : ℝ → ℝ} (hθb : IsLiftOn Fb.tangentLoop.T θb 0 lam)
    (hθc : IsLiftOn Fc.tangentLoop.T θc 0 mu) :
    Fc.rot - Fb.rot = ((θc mu - θc 0) - (θb lam - θb 0)) / (2 * Real.pi) := by
  have hΘb : IsLift Fb.tangentLoop.T Fb.tangentLoop.lift := Fb.tangentLoop.lift_isLift
  have hΘc : IsLift Fc.tangentLoop.T Fc.tangentLoop.lift := Fc.tangentLoop.lift_isLift
  have hb : Fb.tangentLoop.lift lam - Fb.tangentLoop.lift 0 = θb lam - θb 0 :=
    IsLiftOn.increment_eq hlam0 (hΘb.isLiftOn _ _) hθb
  have hc : Fc.tangentLoop.lift mu - Fc.tangentLoop.lift 0 = θc mu - θc 0 :=
    IsLiftOn.increment_eq hmu0 (hΘc.isLiftOn _ _) hθc
  have hcomp : Fb.tangentLoop.lift 1 - Fb.tangentLoop.lift lam =
      Fc.tangentLoop.lift 1 - Fc.tangentLoop.lift mu := by
    have := IsLiftOn.increment_eq hlam1 (hΘb.isLiftOn lam 1) (hΘc.comp_isLiftOn hψ hcompl)
    rwa [hψ1, hψlam] at this
  show tw Fc.tangentLoop - tw Fb.tangentLoop = _
  unfold tw
  rw [← sub_div]
  congr 1
  linarith

/-! ## (iii-c) Paths in `GL⁺(2, ℝ)` -/

theorem euclideanLength_smul (r : ℝ) (v : Plane) :
    euclideanLength (r • v) = |r| * euclideanLength v := by
  simp only [euclideanLength, planeComplex_smul, norm_smul, Real.norm_eq_abs]

/-- Normalisation forgets positive scalars: `r • v` and `v` span the same oriented ray. -/
theorem normalize_smul_of_pos {r : ℝ} (hr : 0 < r) (v : Plane) : normalize (r • v) = normalize v := by
  unfold normalize
  rw [euclideanLength_smul, abs_of_pos hr, smul_smul, mul_inv, mul_comm r⁻¹, mul_assoc,
    inv_mul_cancel₀ hr.ne', mul_one]

/-- Curve-level source of the hypothesis `T_{Fb} s = T_{Fc} (ψ s)` of `rot_sub_rot_of_replace`:
if `Fb.γ = Fc.γ ∘ ψ` near `s` and the change of parameter `ψ` is differentiable at `s` with
positive derivative (an orientation-preserving `C¹` reparametrisation of the common arc), the unit
tangents agree, by the chain rule and `normalize_smul_of_pos`. -/
theorem ClosedC1Curve.tangentLoop_T_eq_of_eventuallyEq (Fb Fc : ClosedC1Curve) {ψ : ℝ → ℝ}
    {ψ' s : ℝ} (hψ : HasDerivAt ψ ψ' s) (hpos : 0 < ψ')
    (hγ : ∀ᶠ x in nhds s, Fb.γ x = Fc.γ (ψ x)) :
    Fb.tangentLoop.T s = Fc.tangentLoop.T (ψ s) := by
  have h1 : HasDerivAt (fun x => Fc.γ (ψ x)) (ψ' • Fc.γ' (ψ s)) s := by
    have := (Fc.hasDerivAt (ψ s)).scomp s hψ
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt Fb.γ (ψ' • Fc.γ' (ψ s)) s := h1.congr_of_eventuallyEq hγ
  have h3 : Fb.γ' s = ψ' • Fc.γ' (ψ s) := (Fb.hasDerivAt s).unique h2
  show normalize (Fb.γ' s) = normalize (Fc.γ' (ψ s))
  rw [h3, normalize_smul_of_pos hpos]

/-- A continuous path `A_t` (`t ∈ ℝ`) in `GL⁺(2, ℝ)` with `A_0 = I`, given by its four continuous
matrix entries `[[a, b], [c, d]]` of positive determinant. The printed path on `0 ≤ t ≤ 1` is the
case of entries composed with `Set.projIcc 0 1`; `A = A_1`. -/
structure GLPlusPath where
  a : ℝ → ℝ
  b : ℝ → ℝ
  c : ℝ → ℝ
  d : ℝ → ℝ
  continuous_a : Continuous a
  continuous_b : Continuous b
  continuous_c : Continuous c
  continuous_d : Continuous d
  det_pos : ∀ t, 0 < a t * d t - b t * c t
  a_zero : a 0 = 1
  b_zero : b 0 = 0
  c_zero : c 0 = 0
  d_zero : d 0 = 1

namespace GLPlusPath

/-- The matrix `A_t` applied to the vector `z`. -/
def apply (A : GLPlusPath) (t : ℝ) (z : Plane) : Plane :=
  (A.a t * z.1 + A.b t * z.2, A.c t * z.1 + A.d t * z.2)

theorem apply_zero (A : GLPlusPath) (z : Plane) : A.apply 0 z = z := by
  simp [apply, A.a_zero, A.b_zero, A.c_zero, A.d_zero]

theorem apply_smul (A : GLPlusPath) (t r : ℝ) (z : Plane) :
    A.apply t (r • z) = r • A.apply t z := by
  simp only [apply, Prod.smul_mk, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  exact Prod.ext (by ring) (by ring)

/-- `A_t` is invertible (positive determinant), so it maps nonzero vectors to nonzero vectors. -/
theorem apply_ne_zero (A : GLPlusPath) (t : ℝ) {z : Plane} (hz : z ≠ 0) : A.apply t z ≠ 0 := by
  intro h
  have h1 : A.a t * z.1 + A.b t * z.2 = 0 := congrArg Prod.fst h
  have h2 : A.c t * z.1 + A.d t * z.2 = 0 := congrArg Prod.snd h
  have hdet := A.det_pos t
  apply hz
  have hx : (A.a t * A.d t - A.b t * A.c t) * z.1 = 0 := by
    linear_combination A.d t * h1 - A.b t * h2
  have hy : (A.a t * A.d t - A.b t * A.c t) * z.2 = 0 := by
    linear_combination A.a t * h2 - A.c t * h1
  exact Prod.ext ((mul_eq_zero.mp hx).resolve_left hdet.ne')
    ((mul_eq_zero.mp hy).resolve_left hdet.ne')

theorem continuous_apply_comp (A : GLPlusPath) {v : ℝ → Plane} (hv : Continuous v) :
    Continuous (fun p : ℝ × ℝ => A.apply p.1 (v p.2)) := by
  have ha := A.continuous_a
  have hb := A.continuous_b
  have hc := A.continuous_c
  have hd := A.continuous_d
  unfold apply
  fun_prop

end GLPlusPath

/-- Two homotopies of direction paths `U V : ℝ × ℝ → Plane` (continuous, unit length) that agree
at the ends `s = 0` and `s = 1` for every `t` have `incr U (t, ·) − incr V (t, ·)` independent of
`t`. This is clause (i-d) for the closed direction loop "`U (t, ·)`, then `V (t, ·)` backwards"
(sm-3:3636-3643), stated without constructing the concatenation: lift both homotopies on `ℝ × ℝ`;
the difference of increments is continuous in `t` and a multiple of `2π`. -/
theorem pair_increment_sub_const {U V : ℝ × ℝ → Plane} (hU : Continuous U) (hV : Continuous V)
    (hU1 : ∀ p, euclideanLength (U p) = 1) (hV1 : ∀ p, euclideanLength (V p) = 1)
    (h0 : ∀ t, U (t, 0) = V (t, 0)) (h1 : ∀ t, U (t, 1) = V (t, 1))
    {t t' : ℝ} {θU θV θU' θV' : ℝ → ℝ}
    (hθU : IsLiftOn (fun s => U (t, s)) θU 0 1) (hθV : IsLiftOn (fun s => V (t, s)) θV 0 1)
    (hθU' : IsLiftOn (fun s => U (t', s)) θU' 0 1) (hθV' : IsLiftOn (fun s => V (t', s)) θV' 0 1) :
    (θU 1 - θU 0) - (θV 1 - θV 0) = (θU' 1 - θU' 0) - (θV' 1 - θV' 0) := by
  obtain ⟨ΘU, hΘUc, hΘU⟩ := exists_lift_of_unit hU hU1
  obtain ⟨ΘV, hΘVc, hΘV⟩ := exists_lift_of_unit hV hV1
  have hliftU : ∀ t, IsLiftOn (fun s => U (t, s)) (fun s => ΘU (t, s)) 0 1 := fun t =>
    IsLift.isLiftOn ⟨hΘUc.comp (continuous_const.prodMk continuous_id), fun s => hΘU (t, s)⟩ 0 1
  have hliftV : ∀ t, IsLiftOn (fun s => V (t, s)) (fun s => ΘV (t, s)) 0 1 := fun t =>
    IsLift.isLiftOn ⟨hΘVc.comp (continuous_const.prodMk continuous_id), fun s => hΘV (t, s)⟩ 0 1
  have hg : Continuous fun t => (ΘU (t, 1) - ΘU (t, 0)) - (ΘV (t, 1) - ΘV (t, 0)) := by
    fun_prop
  have hone : ∀ t, Circle.exp ((ΘU (t, 1) - ΘU (t, 0)) - (ΘV (t, 1) - ΘV (t, 0))) = 1 := by
    intro t
    have e1 : Circle.exp (ΘU (t, 1)) = Circle.exp (ΘV (t, 1)) :=
      circleExp_eq_of_eq (hΘU (t, 1)) (hΘV (t, 1)) (h1 t)
    have e0 : Circle.exp (ΘU (t, 0)) = Circle.exp (ΘV (t, 0)) :=
      circleExp_eq_of_eq (hΘU (t, 0)) (hΘV (t, 0)) (h0 t)
    rw [Circle.exp_sub, Circle.exp_sub, Circle.exp_sub, e1, e0, div_self']
  have hc := const_of_circleExp_eq_one hg hone t t'
  rw [IsLiftOn.increment_eq zero_le_one hθU (hliftU t),
    IsLiftOn.increment_eq zero_le_one hθV (hliftV t),
    IsLiftOn.increment_eq zero_le_one hθU' (hliftU t'),
    IsLiftOn.increment_eq zero_le_one hθV' (hliftV t')]
  exact hc

/-- (iii-c) Applying a supplied path `A_t` in `GL⁺(2, ℝ)`, `A_0 = I`, `A_1 = A`, to both arcs leaves
`Δc − Δb` unchanged (sm-3:3574-3577, proof 3636-3643). Model: the regular oriented arcs `b`, `c` are
given by their (continuous, nonvanishing) tangent vector paths `vb vc : ℝ → Plane` on `[0, 1]`, with
the same oriented tangent rays at both endpoints (`vc 0 = r • vb 0`, `vc 1 = r' • vb 1`, `r, r' > 0`);
`A` acts on an arc by acting on its tangent vectors. `θb, θc` are tangent-angle lifts of the
normalised tangents of `b`, `c` on `[0, 1]` with increments `Δb, Δc`, and `θb', θc'` those of the
transformed arcs `A_1 b`, `A_1 c`. The homotopy `ν_t (z) = A_t z / |A_t z|` of both tangent paths
keeps the difference of increments constant (`pair_increment_sub_const`). -/
theorem glplus_increment_sub_invariant (A : GLPlusPath) {vb vc : ℝ → Plane} (hvb : Continuous vb)
    (hvc : Continuous vc) (hb0 : ∀ s, vb s ≠ 0) (hc0 : ∀ s, vc s ≠ 0)
    (hray0 : ∃ r : ℝ, 0 < r ∧ vc 0 = r • vb 0) (hray1 : ∃ r : ℝ, 0 < r ∧ vc 1 = r • vb 1)
    {θb θc θb' θc' : ℝ → ℝ}
    (hθb : IsLiftOn (fun s => normalize (vb s)) θb 0 1)
    (hθc : IsLiftOn (fun s => normalize (vc s)) θc 0 1)
    (hθb' : IsLiftOn (fun s => normalize (A.apply 1 (vb s))) θb' 0 1)
    (hθc' : IsLiftOn (fun s => normalize (A.apply 1 (vc s))) θc' 0 1) :
    (θc' 1 - θc' 0) - (θb' 1 - θb' 0) = (θc 1 - θc 0) - (θb 1 - θb 0) := by
  have hU : Continuous fun p : ℝ × ℝ => normalize (A.apply p.1 (vc p.2)) :=
    continuous_normalize_comp (A.continuous_apply_comp hvc)
      (fun p => A.apply_ne_zero p.1 (hc0 p.2))
  have hV : Continuous fun p : ℝ × ℝ => normalize (A.apply p.1 (vb p.2)) :=
    continuous_normalize_comp (A.continuous_apply_comp hvb)
      (fun p => A.apply_ne_zero p.1 (hb0 p.2))
  have hU1 : ∀ p : ℝ × ℝ, euclideanLength (normalize (A.apply p.1 (vc p.2))) = 1 := fun p =>
    euclideanLength_normalize (A.apply_ne_zero _ (hc0 _))
  have hV1 : ∀ p : ℝ × ℝ, euclideanLength (normalize (A.apply p.1 (vb p.2))) = 1 := fun p =>
    euclideanLength_normalize (A.apply_ne_zero _ (hb0 _))
  have h0 : ∀ t, normalize (A.apply t (vc 0)) = normalize (A.apply t (vb 0)) := by
    intro t
    obtain ⟨r, hr, hrv⟩ := hray0
    rw [hrv, A.apply_smul, normalize_smul_of_pos hr]
  have h1 : ∀ t, normalize (A.apply t (vc 1)) = normalize (A.apply t (vb 1)) := by
    intro t
    obtain ⟨r, hr, hrv⟩ := hray1
    rw [hrv, A.apply_smul, normalize_smul_of_pos hr]
  have hθc0 : IsLiftOn (fun s => normalize (A.apply 0 (vc s))) θc 0 1 := by
    have : (fun s => normalize (A.apply 0 (vc s))) = fun s => normalize (vc s) :=
      funext fun s => by rw [A.apply_zero]
    rw [this]
    exact hθc
  have hθb0 : IsLiftOn (fun s => normalize (A.apply 0 (vb s))) θb 0 1 := by
    have : (fun s => normalize (A.apply 0 (vb s))) = fun s => normalize (vb s) :=
      funext fun s => by rw [A.apply_zero]
    rw [this]
    exact hθb
  exact pair_increment_sub_const hU hV hU1 hV1 h0 h1 hθc' hθb' hθc0 hθb0

/-! ## The lemma row: one field per printed clause of cf:lem-turnlift (sm-3:3542-3578) -/

/-- cf:lem-turnlift. Clause (i): fields `exists_tangent_angle_lift` … `rot_reverse`; clause (ii):
fields `polygon_two_pi_rot` … `polygon_triangle` (the accepted `SM.rotation_number`, not
re-proved); clause (iii): fields `rounding`, `replacement`, `glplus_invariance`. Models: `Reparam`,
`DirectionHomotopy`, `RegularHomotopy`, `ClosedC1Curve.reverse`, `IsLiftOn`, `GLPlusPath`. -/
structure TurnLiftData : Prop where
  /-- (i) Every continuous direction loop has a tangent-angle lift (at the seam `[0,1]`). -/
  exists_tangent_angle_lift : ∀ L : DirectionLoop, ∃ θ : ℝ → ℝ, IsSeamLift L.T θ
  /-- (i) "The integer `tw(T)`": `tw` is an integer. -/
  tw_integer : ∀ L : DirectionLoop, ∃ k : ℤ, tw L = (k : ℝ)
  /-- (i) `tw(T)` is independent of the lift: every seam lift gives the printed quotient. -/
  tw_lift_independent : ∀ (L : DirectionLoop) (θ : ℝ → ℝ), IsSeamLift L.T θ →
    tw L = (θ 1 - θ 0) / (2 * Real.pi)
  /-- (i) `tw(T)` is independent of the seam. -/
  tw_seam_independent : ∀ (L : DirectionLoop) (a : ℝ), tw (L.shift a) = tw L
  /-- (i) `tw(T)` is unchanged by an orientation-preserving reparametrisation `φ`
  (continuous, strictly increasing, `φ (s+1) = φ s + 1`). -/
  tw_reparam : ∀ (L : DirectionLoop) (φ : Reparam), tw (L.reparam φ) = tw L
  /-- (i) `tw` is constant under a continuous homotopy through direction loops. -/
  tw_homotopy : ∀ (h : DirectionHomotopy) (t t' : ℝ), tw (h.loop t) = tw (h.loop t')
  /-- (i) Consequently the rotation of a closed `C¹` regular curve is invariant under regular
  homotopy. -/
  rot_regular_homotopy : ∀ (h : RegularHomotopy) (t t' : ℝ), (h.curve t).rot = (h.curve t').rot
  /-- (i) Reversing the orientation of a closed `C¹` regular curve negates its rotation. -/
  rot_reverse : ∀ c : ClosedC1Curve, c.reverse.rot = -c.rot
  /-- (ii) `2π rot(L) = Σ ϑ_i` for `L` in the regular locus. -/
  polygon_two_pi_rot : ∀ {n : ℕ} [NeZero n], 3 ≤ n → ∀ P : LabelledTuple n, Regular P →
    2 * Real.pi * rotationNumber P = ∑ i : ZMod n, principalTurn P i
  /-- (ii) Rotation is constant along every path in the regular locus (`SM.rotation_number`). -/
  polygon_path_constant : ∀ {n : ℕ} [NeZero n], 3 ≤ n → ∀ P : LabelledTuple n, Regular P →
    ∀ Q : LabelledTuple n, ∀ γ : Path P Q, (∀ u, Regular (γ u)) →
      ∀ s t : unitInterval, rotationNumber (γ s) = rotationNumber (γ t)
  /-- (ii) Rotation is unchanged by a positive flat subdivision: inserting a vertex in the interior
  of any edge keeps the polygon regular and keeps its rotation (`SM.rotation_number`). -/
  polygon_subdivision : ∀ {n : ℕ} [NeZero n], 3 ≤ n → ∀ P : LabelledTuple n, Regular P →
    ∀ (i : ZMod n) (t : ℝ), 0 < t → t < 1 →
      insertVertex P i t (insertedIndex n) ∈ edgeInterior P i ∧
      Regular (insertVertex P i t) ∧ rotationNumber (insertVertex P i t) = rotationNumber P
  /-- (ii) Rotation is negated by orientation reversal (`SM.rotation_number`). -/
  polygon_reversal : ∀ {n : ℕ} [NeZero n], 3 ≤ n → ∀ P : LabelledTuple n, Regular P →
    Regular (reversal P) ∧ rotationNumber (reversal P) = -rotationNumber P
  /-- (ii) Every regular three-corner polygon has rotation `+1` or `−1` according to the common
  sign of its three turns (`SM.rotation_number`). -/
  polygon_triangle : ∀ {n : ℕ} [NeZero n], 3 ≤ n → ∀ P : LabelledTuple n, Regular P → n = 3 →
    (∀ i : ZMod n, rotationNumber P = (turn P i : ℝ)) ∧
      (rotationNumber P = 1 ∨ rotationNumber P = -1)
  /-- (iii) Corner rounding: a closed `C¹` regular curve obtained from the regular polygon `L` by
  replacing every corner by a regular arc whose compatible tangent-angle lift has increment `ϑ_k`
  (subdivision `0 = a 0 ≤ b 0 ≤ a 1 ≤ ⋯ ≤ a n = 1`, corner arc at vertex `k` on `[a k, b k]`,
  straight piece along edge `k` on `[b k, a (k+1)]`; see `rot_eq_rotationNumber_of_rounding`) has
  rotation `rot(L)`. -/
  rounding : ∀ {n : ℕ} [NeZero n], 3 ≤ n → ∀ L : LabelledTuple n, Regular L →
    ∀ (γ : ClosedC1Curve) (a b : ℕ → ℝ), a 0 = 0 → a n = 1 →
      (∀ k < n, a k ≤ b k) → (∀ k < n, b k ≤ a (k + 1)) →
      (∀ k < n, ∃ θ : ℝ → ℝ, IsLiftOn γ.tangentLoop.T θ (a k) (b k) ∧
        θ (b k) - θ (a k) = principalTurn L (k : ZMod n)) →
      (∀ k < n, ∀ s ∈ Icc (b k) (a (k + 1)),
        γ.tangentLoop.T s = normalize (edge L (k : ZMod n))) →
      γ.rot = rotationNumber L
  /-- (iii) Arc replacement: `Fb`, `Fc` closed `C¹` regular, the arc `b` on `[0, λ]` of `Fb`, the arc
  `c` on `[0, μ]` of `Fc`, the common complementary arc traversed by `Fb` on `[λ, 1]` and by `Fc` on
  `[μ, 1]` up to a monotone continuous change of parameter `ψ` (see `rot_sub_rot_of_replace`);
  compatible tangent lifts `θb`, `θc` on the arcs with equal initial values and increments
  `Δb`, `Δc`. Then `rot Fc − rot Fb = (Δc − Δb) / 2π`. -/
  replacement : ∀ (Fb Fc : ClosedC1Curve) (lam mu : ℝ), lam ∈ Icc (0 : ℝ) 1 → mu ∈ Icc (0 : ℝ) 1 →
    ∀ ψ : ℝ → ℝ, ContinuousOn ψ (Icc lam 1) → MonotoneOn ψ (Icc lam 1) → ψ lam = mu → ψ 1 = 1 →
      (∀ s ∈ Icc lam 1, Fb.tangentLoop.T s = Fc.tangentLoop.T (ψ s)) →
      ∀ θb θc : ℝ → ℝ, IsLiftOn Fb.tangentLoop.T θb 0 lam → IsLiftOn Fc.tangentLoop.T θc 0 mu →
        θb 0 = θc 0 →
        Fc.rot - Fb.rot = ((θc mu - θc 0) - (θb lam - θb 0)) / (2 * Real.pi)
  /-- (iii) A supplied continuous path `A_t` in `GL⁺(2, ℝ)` with `A_0 = I`, `A_1 = A`, applied to
  both arcs (given by their nonvanishing tangent paths with common oriented end rays), leaves
  `Δc − Δb` unchanged (see `glplus_increment_sub_invariant`). -/
  glplus_invariance : ∀ (A : GLPlusPath) (vb vc : ℝ → Plane), Continuous vb → Continuous vc →
    (∀ s, vb s ≠ 0) → (∀ s, vc s ≠ 0) →
    (∃ r : ℝ, 0 < r ∧ vc 0 = r • vb 0) → (∃ r : ℝ, 0 < r ∧ vc 1 = r • vb 1) →
    ∀ θb θc θb' θc' : ℝ → ℝ,
      IsLiftOn (fun s => normalize (vb s)) θb 0 1 →
      IsLiftOn (fun s => normalize (vc s)) θc 0 1 →
      IsLiftOn (fun s => normalize (A.apply 1 (vb s))) θb' 0 1 →
      IsLiftOn (fun s => normalize (A.apply 1 (vc s))) θc' 0 1 →
      (θc' 1 - θc' 0) - (θb' 1 - θb' 0) = (θc 1 - θc 0) - (θb 1 - θb 0)

theorem turnlift : TurnLiftData where
  exists_tangent_angle_lift := DirectionLoop.exists_seamLift
  tw_integer := tw_int
  tw_lift_independent := fun L _ h => tw_eq_of_isSeamLift L h
  tw_seam_independent := tw_shift
  tw_reparam := tw_reparam
  tw_homotopy := DirectionHomotopy.tw_loop_eq
  rot_regular_homotopy := RegularHomotopy.rot_curve_eq
  rot_reverse := ClosedC1Curve.rot_reverse
  polygon_two_pi_rot := fun _ P _ => two_pi_mul_rotationNumber P
  polygon_path_constant := fun hn P h => (rotation_number hn P h).2.2.1
  polygon_subdivision := fun hn P h i t ht0 ht1 =>
    ((rotation_number hn P h).2.2.2.1 i t ht0 ht1).2.2
  polygon_reversal := fun hn P h =>
    ⟨(rotation_number hn P h).2.2.2.2.1, (rotation_number hn P h).2.2.2.2.2.1⟩
  polygon_triangle := fun hn P h h3 =>
    ⟨((rotation_number hn P h).2.2.2.2.2.2.1 h3).1, ((rotation_number hn P h).2.2.2.2.2.2.1 h3).2.1⟩
  rounding := fun _ L _ γ a b ha0 han hab hba hcorner hstraight =>
    rot_eq_rotationNumber_of_rounding L γ a b ha0 han hab hba hcorner hstraight
  replacement := fun Fb Fc _ _ hlam hmu _ hψ _ hψlam hψ1 hcompl _ _ hθb hθc _ =>
    rot_sub_rot_of_replace Fb Fc hlam.1 hlam.2 hmu.1 hψ hψlam hψ1 hcompl hθb hθc
  glplus_invariance := fun A _ _ hvb hvc hb0 hc0 hray0 hray1 _ _ _ _ hθb hθc hθb' hθc' =>
    glplus_increment_sub_invariant A hvb hvc hb0 hc0 hray0 hray1 hθb hθc hθb' hθc'

end SM

#print axioms SM.turnlift
