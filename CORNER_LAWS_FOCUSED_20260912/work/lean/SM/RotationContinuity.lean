import SM.RotationNumber
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Path

/-! Continuity on the actual regular domain and constancy in continuous
regular families. Integrality is proved in RotationNumber, not assumed. -/

namespace SM

variable {n : ℕ} {α : Type*} [TopologicalSpace α]

theorem continuous_planeComplex : Continuous planeComplex := by
  have he : planeComplex = fun u : Plane => (u.1 : ℂ) + (u.2 : ℂ) * Complex.I := by
    funext u
    apply Complex.ext <;> simp [planeComplex]
  rw [he]
  exact (Complex.continuous_ofReal.comp continuous_fst).add
    ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)

theorem continuousAt_principalAngle {u v : α → Plane} {t : α}
    (hu : ContinuousAt u t) (hv : ContinuousAt v t) (h : RegularPair (u t) (v t)) :
    ContinuousAt (fun s => principalAngle (u s) (v s)) t := by
  have hc : ContinuousAt (fun s => cornerRotor (u s) (v s)) t :=
    (continuous_planeComplex.continuousAt.comp hu).star.mul
      (continuous_planeComplex.continuousAt.comp hv)
  change ContinuousAt (Complex.arg ∘ (fun s => cornerRotor (u s) (v s))) t
  exact ContinuousAt.comp (f := fun s => cornerRotor (u s) (v s)) (x := t) (g := Complex.arg)
    (Complex.continuousAt_arg (regularPair_slitPlane h)) hc

theorem continuous_principalTurn_family {f : α → LabelledTuple n}
    (hf : Continuous f) (hr : ∀ t, Regular (f t)) (i : ZMod n) :
    Continuous (fun t => principalTurn (f t) i) := by
  have he (j : ZMod n) : Continuous (fun t => edge (f t) j) :=
    ((continuous_apply (j + 1)).comp hf).sub ((continuous_apply j).comp hf)
  rw [continuous_iff_continuousAt]
  intro t
  exact continuousAt_principalAngle (he (i - 1)).continuousAt (he i).continuousAt (hr t i)

theorem continuous_rotationNumber_family [NeZero n] {f : α → LabelledTuple n}
    (hf : Continuous f) (hr : ∀ t, Regular (f t)) :
    Continuous (fun t => rotationNumber (f t)) := by
  apply Continuous.div_const
  exact continuous_finsetSum _ (fun i _ => continuous_principalTurn_family hf hr i)

theorem rotationNumber_family_constant [NeZero n] [PreconnectedSpace α]
    {f : α → LabelledTuple n} (hf : Continuous f) (hr : ∀ t, Regular (f t)) (s t : α) :
    rotationNumber (f s) = rotationNumber (f t) := by
  have hm : Set.MapsTo (fun u => rotationNumber (f u)) Set.univ
      (Set.range ((↑) : ℤ → ℝ)) := by
    intro u _
    obtain ⟨k, hk⟩ := rotationNumber_integer (hr u)
    exact ⟨k, hk.symm⟩
  exact isPreconnected_univ.constant_of_mapsTo
    Real.isClosedEmbedding_intCast.isEmbedding.isDiscrete_range
    (continuous_rotationNumber_family hf hr).continuousOn hm
    (Set.mem_univ s) (Set.mem_univ t)

theorem rotationNumber_path_constant [NeZero n] {P Q : LabelledTuple n}
    (γ : Path P Q) (hr : ∀ t, Regular (γ t)) : rotationNumber P = rotationNumber Q := by
  have he := rotationNumber_family_constant γ.continuous hr (0 : unitInterval) 1
  simpa using he

end SM
