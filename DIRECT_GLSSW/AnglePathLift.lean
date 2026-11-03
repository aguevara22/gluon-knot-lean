import PositionalAngleLiftUniqueness
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex

/-- Local real sections cover the actual angle quotient. -/
theorem angle_local_charts (y : Real.Angle) :
    ∃ q : PartialHomeomorph ℝ Real.Angle,
      y ∈ q.target ∧ ((↑) : ℝ → Real.Angle) = q := by
  refine Real.Angle.induction_on y ?_
  intro x
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  obtain ⟨q,hx,hq⟩ := AddCircle.isLocalHomeomorph_coe (2 * Real.pi) x
  refine ⟨q, ?_, hq⟩
  change (QuotientAddGroup.mk x : AddCircle (2 * Real.pi)) ∈ q.target
  rw [hq]
  exact q.map_source hx

/-- Finite subdivision and additive chart corrections give path lifting without
assuming the as-yet-unexported covering-map theorem for the angle quotient. -/
theorem angle_path_lift_exists (γ : C(I, Real.Angle)) (e : ℝ)
    (hstart : γ 0 = (e : Real.Angle)) :
    ∃ Γ : C(I, ℝ), (∀ u, (Γ u : Real.Angle) = γ u) ∧ Γ 0 = e := by
  classical
  choose q mem_target hq using angle_local_charts
  obtain ⟨t, t_0, t_mono, ⟨n_max, h_max⟩, t_sub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun x => (q x).open_target.preimage γ.continuous)
      (fun u _ => Set.mem_iUnion.mpr ⟨γ u, mem_target _⟩)
  suffices ∀ n, ∃ Γ : I → ℝ, ContinuousOn Γ (Set.Icc 0 (t n)) ∧
      (∀ u ∈ Set.Icc 0 (t n), (Γ u : Real.Angle) = γ u) ∧ Γ 0 = e by
    obtain ⟨Γ, cont, heq, hzero⟩ := this n_max
    rw [h_max _ le_rfl] at cont heq
    refine ⟨⟨Γ, continuous_iff_continuousOn_univ.mpr ?_⟩,
      fun u => heq u ⟨bot_le,le_top⟩, hzero⟩
    convert cont
    rw [eq_comm, Set.eq_univ_iff_forall]
    exact fun u => ⟨bot_le,le_top⟩
  intro n
  induction n with
  | zero =>
    refine ⟨fun _ => e, continuous_const.continuousOn, ?_, rfl⟩
    intro u hu
    rw [t_0, Set.Icc_self, Set.mem_singleton_iff] at hu
    subst u
    exact hstart.symm
  | succ n ih =>
    obtain ⟨Γ, cont, heq, hzero⟩ := ih
    obtain ⟨x, hsub⟩ := t_sub n
    have htn : γ (t n) ∈ (q x).target := hsub ⟨le_rfl,t_mono n.le_succ⟩
    have hsection (u : I) (hu : γ u ∈ (q x).target) :
        (((q x).symm (γ u) : ℝ) : Real.Angle) = γ u := by
      change ((↑) : ℝ → Real.Angle) ((q x).symm (γ u)) = γ u
      rw [hq x]
      exact (q x).right_inv hu
    have hΓtn : (Γ (t n) : Real.Angle) = γ (t n) :=
      heq _ ⟨t_0 ▸ t_mono n.zero_le,le_rfl⟩
    let c : ℝ := Γ (t n) - (q x).symm (γ (t n))
    have hc : (c : Real.Angle) = 0 := by
      change (Γ (t n) : Real.Angle) - ((q x).symm (γ (t n)) : Real.Angle) = 0
      rw [hΓtn, hsection _ htn, sub_self]
    refine ⟨fun u => if u ≤ t n then Γ u else (q x).symm (γ u) + c,
      .if (fun u hu => ?_) (cont.mono fun u hu => ?_) ?_, ?_, ?_⟩
    · cases frontier_Iic_subset _ hu.2
      dsimp [c]
      ring
    · rw [closure_le_eq continuous_id' continuous_const] at hu
      exact ⟨hu.1.1,hu.2⟩
    · apply ContinuousOn.add _ continuousOn_const
      apply (q x).continuousOn_symm.comp γ.continuous.continuousOn
      intro u hu
      simp_rw [not_le] at hu
      exact hsub ⟨closure_lt_subset_le continuous_const continuous_subtype_val hu.2,hu.1.2⟩
    · intro u hu
      dsimp only
      split_ifs with h
      · exact heq _ ⟨hu.1,h⟩
      · change ((q x).symm (γ u) : Real.Angle) + (c : Real.Angle) = γ u
        rw [hc, add_zero, hsection _ (hsub ⟨le_of_not_le h,hu.2⟩)]
    · dsimp only
      rwa [if_pos (t_0 ▸ t_mono n.zero_le)]

/-- Normalization removes the sole additive ambiguity of a real angle lift. -/
theorem angle_path_lift_unique (γ : C(I, Real.Angle)) (e : ℝ)
    (Γ Λ : C(I, ℝ))
    (hΓ : Γ 0 = e ∧ ∀ u, (Γ u : Real.Angle) = γ u)
    (hΛ : Λ 0 = e ∧ ∀ u, (Λ u : Real.Angle) = γ u) : Γ = Λ := by
  apply DFunLike.ext'
  apply (T2Space.isSeparatedMap ((↑) : ℝ → Real.Angle)).eq_of_comp_eq
    angle_coe_locally_injective Γ.continuous Λ.continuous (a := (0 : I))
  · funext u
    exact (hΓ.2 u).trans (hΛ.2 u).symm
  · exact hΓ.1.trans hΛ.1.symm

/-- Existence and uniqueness precede every normalized lift or index definition. -/
theorem existsUnique_angle_path_lift (γ : C(I, Real.Angle)) (e : ℝ)
    (hstart : γ 0 = (e : Real.Angle)) :
    ∃! Γ : C(I, ℝ), Γ 0 = e ∧ ∀ u, (Γ u : Real.Angle) = γ u := by
  obtain ⟨Γ, hΓ, hzero⟩ := angle_path_lift_exists γ e hstart
  exact ⟨Γ, ⟨hzero,hΓ⟩, fun Λ hΛ => angle_path_lift_unique γ e Λ Γ hΛ ⟨hzero,hΓ⟩⟩

end DirectGLSSW.HOMFLY.PositionalIndex




