import SM.CrossingEquiv
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.GroupWithZero

/-! Developing continuity inputs for source lem:wall-segment-stability.
These auxiliaries do not by themselves establish that complete source lemma. -/

namespace SM

variable {α : Type*} [TopologicalSpace α] {t₀ : α}

theorem continuousAt_det {u v : α → Plane}
    (hu : ContinuousAt u t₀) (hv : ContinuousAt v t₀) :
    ContinuousAt (fun t => det (u t) (v t)) t₀ :=
  (hu.fst.mul hv.snd).sub (hu.snd.mul hv.fst)

noncomputable def cramerFirst (a b u v : Plane) : ℝ := det (b - a) v / det u v
noncomputable def cramerSecond (a b u v : Plane) : ℝ := det (b - a) u / det u v

theorem continuousAt_cramerFirst {a b u v : α → Plane}
    (ha : ContinuousAt a t₀) (hb : ContinuousAt b t₀)
    (hu : ContinuousAt u t₀) (hv : ContinuousAt v t₀) (hd : det (u t₀) (v t₀) ≠ 0) :
    ContinuousAt (fun t => cramerFirst (a t) (b t) (u t) (v t)) t₀ :=
  (continuousAt_det (hb.sub ha) hv).div (continuousAt_det hu hv) hd

theorem continuousAt_cramerSecond {a b u v : α → Plane}
    (ha : ContinuousAt a t₀) (hb : ContinuousAt b t₀)
    (hu : ContinuousAt u t₀) (hv : ContinuousAt v t₀) (hd : det (u t₀) (v t₀) ≠ 0) :
    ContinuousAt (fun t => cramerSecond (a t) (b t) (u t) (v t)) t₀ :=
  (continuousAt_det (hb.sub ha) hu).div (continuousAt_det hu hv) hd

open Filter Topology

theorem continuousAt_preserves_unit_interval {f : α → ℝ}
    (hf : ContinuousAt f t₀) (h0 : 0 < f t₀) (h1 : f t₀ < 1) :
    ∀ᶠ t in 𝓝 t₀, 0 < f t ∧ f t < 1 :=
  hf.eventually (isOpen_Ioo.mem_nhds ⟨h0, h1⟩)

theorem continuousAt_preserves_strict_order {f g : α → ℝ}
    (hf : ContinuousAt f t₀) (hg : ContinuousAt g t₀) (h : f t₀ < g t₀) :
    ∀ᶠ t in 𝓝 t₀, f t < g t := by
  have hd := (hg.sub hf).eventually (isOpen_Ioi.mem_nhds (sub_pos.mpr h))
  exact hd.mono (fun _ hx => sub_pos.mp hx)

theorem continuousAt_preserves_transversality {u v : α → Plane}
    (hu : ContinuousAt u t₀) (hv : ContinuousAt v t₀) (hd : det (u t₀) (v t₀) ≠ 0) :
    ∀ᶠ t in 𝓝 t₀, det (u t) (v t) ≠ 0 :=
  (continuousAt_det hu hv).eventually (isOpen_compl_singleton.mem_nhds hd)

theorem transverse_intersection_persists {a b u v : α → Plane}
    (ha : ContinuousAt a t₀) (hb : ContinuousAt b t₀)
    (hu : ContinuousAt u t₀) (hv : ContinuousAt v t₀) (hd : det (u t₀) (v t₀) ≠ 0)
    {s₀ r₀ : ℝ} (hs0 : 0 < s₀) (hs1 : s₀ < 1) (hr0 : 0 < r₀) (hr1 : r₀ < 1)
    (heq : a t₀ + s₀ • u t₀ = b t₀ + r₀ • v t₀) :
    ∀ᶠ t in 𝓝 t₀, ∃ s r : ℝ, 0 < s ∧ s < 1 ∧ 0 < r ∧ r < 1 ∧
      a t + s • u t = b t + r • v t ∧ det (u t) (v t) ≠ 0 := by
  have hs : cramerFirst (a t₀) (b t₀) (u t₀) (v t₀) = s₀ :=
    (div_eq_iff hd).mpr (intersection_parameter_identity heq)
  have hr : cramerSecond (a t₀) (b t₀) (u t₀) (v t₀) = r₀ :=
    (div_eq_iff hd).mpr (intersection_second_parameter_identity heq)
  have hse := continuousAt_preserves_unit_interval (continuousAt_cramerFirst ha hb hu hv hd)
    (by rwa [hs]) (by rwa [hs])
  have hre := continuousAt_preserves_unit_interval (continuousAt_cramerSecond ha hb hu hv hd)
    (by rwa [hr]) (by rwa [hr])
  have hde := continuousAt_preserves_transversality hu hv hd
  filter_upwards [hse, hre, hde] with t hst hrt hdt
  exact ⟨_, _, hst.1, hst.2, hrt.1, hrt.2,
    cramer_intersection (a t) (b t) (u t) (v t) hdt, hdt⟩

end SM
