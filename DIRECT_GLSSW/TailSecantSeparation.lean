import ParallelSecantAvoidance
import ShiftFirstPair
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CursorWallTransport
open EndpointEventGeometry

theorem core_distinct_triple (W : ℕ → PlanarPoint ℝ) (N : ℕ)
    (h : ShortEdgeSignStability.CoreHGeneric W N)
    (i j k : ℕ) (hi : i≤N) (hj : j≤N) (hk : k≤N)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    planarDet (W i-W j) (W k-W j)≠0 := by
  intro hz
  rcases lt_or_gt_of_ne hij with hij|hji
  · by_cases hki : k < i
    · exact h k i j hki hij hj hz
    · have hik : i < k := by omega
      by_cases hkj : k < j
      · apply h i k j hik hkj hj
        dsimp [polygonHDet,planarDet] at *
        nlinarith
      · have hjk : j < k := by omega
        apply h i j k hij hjk hk
        dsimp [polygonHDet,planarDet] at *
        nlinarith
  · by_cases hkj : k < j
    · apply h k j i hkj hji hi
      dsimp [polygonHDet,planarDet] at *
      nlinarith
    · have hjk : j < k := by omega
      by_cases hki : k < i
      · apply h j k i hjk hki hi
        dsimp [polygonHDet,planarDet] at *
        nlinarith
      · have hik : i < k := by omega
        apply h j i k hji hik hk
        dsimp [polygonHDet,planarDet] at *
        nlinarith

/-- Ordered fixed-tail secants (the two translated vertices are excluded). -/
abbrev TailSecant (N : ℕ) := {ij : Fin (N+1) × Fin (N+1) // 1 < ij.1.val ∧ ij.1.val < ij.2.val}

def tailSlope (W : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) {N : ℕ} (s : TailSecant N) : ℝ :=
  planarDet (W s.val.1-W s.val.2) v

def tailIntercept (W : ℕ → PlanarPoint ℝ) (p : PlanarPoint ℝ) {N : ℕ} (s : TailSecant N) : ℝ :=
  planarDet (W s.val.1-W s.val.2) (p-W s.val.2)

/-- Every pair of different transverse tail secants has a proper affine
collision polynomial, derived from actual triple noncollinearity. -/
theorem tail_collision_proper (W : ℕ → PlanarPoint ℝ) (v w p : PlanarPoint ℝ) (N : ℕ)
    (hcore : ShortEdgeSignStability.CoreHGeneric W N) (hbasis : planarDet v w≠0)
    (s t : TailSecant N) (hne : s≠t) (ht : tailSlope W v t≠0) :
    tailSlope W w s*tailSlope W v t-tailSlope W w t*tailSlope W v s≠0 ∨
      tailIntercept W p s*tailSlope W v t-tailIntercept W p t*tailSlope W v s≠0 := by
  have hslt := s.property.2
  have htlt := t.property.2
  have hoff (z : Fin (N+1)) (hz0 : z≠s.val.1) (hz1 : z≠s.val.2) :
      planarDet (W s.val.1-W s.val.2) (W z-W s.val.2)≠0 := by
    apply core_distinct_triple W N hcore s.val.1 s.val.2 z (by omega) (by omega) (by omega) (by omega)
    · intro hh; exact hz0 (Fin.ext hh.symm)
    · intro hh; exact hz1 (Fin.ext hh.symm)
  by_cases ht0 : t.val.1=s.val.1 ∨ t.val.1=s.val.2
  · have ht1a : t.val.2≠s.val.1 := by
      intro hh
      rcases ht0 with hh0|hh0  <;> have hv := congrArg Fin.val hh0  <;> have hu := congrArg Fin.val hh  <;> omega
    have ht1b : t.val.2≠s.val.2 := by
      intro hh
      rcases ht0 with hh0|hh0
      · apply hne
        apply Subtype.ext
        exact Prod.ext hh0.symm hh.symm
      · have hv := congrArg Fin.val hh0
        have hu := congrArg Fin.val hh
        omega
    have hp := secant_collision_affine_proper p v w (W s.val.1) (W s.val.2)
      (W t.val.2) (W t.val.1) hbasis (by
        have he : planarDet (W t.val.2-W t.val.1) v= -tailSlope W v t := by
          dsimp [tailSlope,planarDet]
          ring
        rw [he]
        exact neg_ne_zero.mpr ht) (hoff _ ht1a ht1b)
    dsimp [tailSlope,tailIntercept] at *
    have hs (P : PlanarPoint ℝ) : planarDet (W t.val.2-W t.val.1) P =
        -planarDet (W t.val.1-W t.val.2) P := by dsimp [planarDet];ring
    have hb : planarDet (W t.val.2-W t.val.1) (p-W t.val.1) =
        -planarDet (W t.val.1-W t.val.2) (p-W t.val.2) := by dsimp [planarDet];ring
    rw [hs v,hs w,hb] at hp
    rcases hp with hp|hp
    · exact Or.inl (by intro hz; apply hp; nlinarith [hz])
    · exact Or.inr (by intro hz; apply hp; nlinarith [hz])
  · push_neg at ht0
    exact secant_collision_affine_proper p v w (W s.val.1) (W s.val.2)
      (W t.val.1) (W t.val.2) hbasis ht (hoff _ ht0.1 ht0.2)

/-- An arbitrarily small parallel-line translation separates all transverse
fixed-tail secant parameters simultaneously. -/
theorem exists_small_tail_secant_separation (W : ℕ → PlanarPoint ℝ) (v w p : PlanarPoint ℝ) (N : ℕ)
    (hcore : ShortEdgeSignStability.CoreHGeneric W N) (hbasis : planarDet v w≠0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η < ε ∧ ∀ s t : TailSecant N, s≠t →
      tailSlope W v s≠0 → tailSlope W v t≠0 →
      tailIntercept W (p+η • w) s*tailSlope W v t-
        tailIntercept W (p+η • w) t*tailSlope W v s≠0 := by
  classical
  let I := {st : TailSecant N × TailSecant N // st.1≠st.2 ∧ tailSlope W v st.2≠0}
  let A : I → ℝ := fun st => tailSlope W w st.val.1*tailSlope W v st.val.2-
    tailSlope W w st.val.2*tailSlope W v st.val.1
  let B : I → ℝ := fun st => tailIntercept W p st.val.1*tailSlope W v st.val.2-
    tailIntercept W p st.val.2*tailSlope W v st.val.1
  obtain ⟨η,hη,hηε,hh⟩ := exists_small_affine_avoidance A B
    (fun st => tail_collision_proper W v w p N hcore hbasis st.val.1 st.val.2 st.property.1 st.property.2) ε hε
  refine ⟨η,hη,hηε,?_⟩
  intro s t hst hs ht
  have hz := hh ⟨(s,t),hst,ht⟩
  have he : tailIntercept W (p+η • w) s*tailSlope W v t-
      tailIntercept W (p+η • w) t*tailSlope W v s = A ⟨(s,t),hst,ht⟩*η+B ⟨(s,t),hst,ht⟩ := by
    dsimp [tailIntercept,tailSlope,A,B,planarDet]
    ring
  rw [he]
  exact hz

end DirectGLSSW.CursorWallTransport
