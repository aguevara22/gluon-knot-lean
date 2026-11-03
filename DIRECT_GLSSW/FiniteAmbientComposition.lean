import DescendingHeightArcs
import Mathlib.Topology.Homeomorph.Defs

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.DescendingSpatial

/-- Compose finitely many ambient isotopies whose height supports are pairwise
disjoint. The result agrees with each local isotopy on its support and is fixed
off their union. -/
theorem exists_finite_disjoint_height_supported_ambient :
    ∀ (n : ℕ)
      (F : Fin n → unitInterval → ((ℂ × ℝ) ≃ₜ (ℂ × ℝ)))
      (S : Fin n → Set ℝ),
      Pairwise (fun i j => Disjoint (S i) (S j)) →
      (∀ i, F i 0 = Homeomorph.refl (ℂ × ℝ)) →
      (∀ i, Continuous (fun p : unitInterval × (ℂ × ℝ) => F i p.1 p.2)) →
      (∀ i, Continuous (fun p : unitInterval × (ℂ × ℝ) => (F i p.1).symm p.2)) →
      (∀ i s x, (F i s x).2 = x.2) →
      (∀ i s x, x.2 ∉ S i → F i s x = x) →
      ∃ Φ : unitInterval → ((ℂ × ℝ) ≃ₜ (ℂ × ℝ)),
        Φ 0 = Homeomorph.refl (ℂ × ℝ) ∧
        Continuous (fun p : unitInterval × (ℂ × ℝ) => Φ p.1 p.2) ∧
        Continuous (fun p : unitInterval × (ℂ × ℝ) => (Φ p.1).symm p.2) ∧
        (∀ s x, (Φ s x).2 = x.2) ∧
        (∀ i s x, x.2 ∈ S i → Φ s x = F i s x) ∧
        (∀ s x, (∀ i, x.2 ∉ S i) → Φ s x = x) := by
  intro n
  induction n with
  | zero =>
      intro F S hdisj hzero hforward hinverse hheight hfixed
      let Φ : unitInterval → ((ℂ × ℝ) ≃ₜ (ℂ × ℝ)) := fun _ =>
        Homeomorph.refl (ℂ × ℝ)
      refine ⟨Φ, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · change Continuous (fun p : unitInterval × (ℂ × ℝ) => p.2)
        fun_prop
      · change Continuous (fun p : unitInterval × (ℂ × ℝ) => p.2)
        fun_prop
      · intro s x
        rfl
      · intro i
        exact Fin.elim0 i
      · intro s x _
        rfl
  | succ n ih =>
      intro F S hdisj hzero hforward hinverse hheight hfixed
      let F' : Fin n → unitInterval → ((ℂ × ℝ) ≃ₜ (ℂ × ℝ)) :=
        fun i => F i.succ
      let S' : Fin n → Set ℝ := fun i => S i.succ
      have hdisj' : Pairwise (fun i j : Fin n => Disjoint (S' i) (S' j)) := by
        intro i j hij
        apply hdisj
        intro heq
        apply hij
        apply Fin.ext
        exact Nat.succ.inj (congrArg Fin.val heq)
      obtain ⟨Ψ,hΨzero,hΨforward,hΨinverse,hΨheight,hΨsupport,hΨfixed⟩ :=
        ih F' S' hdisj'
          (fun i => hzero i.succ)
          (fun i => hforward i.succ)
          (fun i => hinverse i.succ)
          (fun i s x => hheight i.succ s x)
          (fun i s x hx => hfixed i.succ s x hx)
      let Φ : unitInterval → ((ℂ × ℝ) ≃ₜ (ℂ × ℝ)) := fun s =>
        (F 0 s).trans (Ψ s)
      have hΦapply (s : unitInterval) (x : ℂ × ℝ) :
          Φ s x = Ψ s (F 0 s x) := rfl
      have hΦinverse (s : unitInterval) (x : ℂ × ℝ) :
          (Φ s).symm x = (F 0 s).symm ((Ψ s).symm x) := rfl
      have hzero0 : F 0 0 = Homeomorph.refl (ℂ × ℝ) := hzero 0
      have hΦzero : Φ 0 = Homeomorph.refl (ℂ × ℝ) := by
        apply Homeomorph.ext
        intro x
        change Ψ 0 (F 0 0 x) = x
        calc
          Ψ 0 (F 0 0 x) = Ψ 0 x := by rw [hzero0]; rfl
          _ = x := by rw [hΨzero]; rfl
      have hΦforward :
          Continuous (fun p : unitInterval × (ℂ × ℝ) => Φ p.1 p.2) := by
        change Continuous (fun p : unitInterval × (ℂ × ℝ) => Ψ p.1 (F 0 p.1 p.2))
        have hinput : Continuous (fun p : unitInterval × (ℂ × ℝ) =>
            (p.1, F 0 p.1 p.2)) := continuous_fst.prod_mk (hforward 0)
        exact hΨforward.comp hinput
      have hΦinverseContinuous :
          Continuous (fun p : unitInterval × (ℂ × ℝ) => (Φ p.1).symm p.2) := by
        change Continuous (fun p : unitInterval × (ℂ × ℝ) =>
          (F 0 p.1).symm ((Ψ p.1).symm p.2))
        have hinput : Continuous (fun p : unitInterval × (ℂ × ℝ) =>
            (p.1, (Ψ p.1).symm p.2)) := continuous_fst.prod_mk hΨinverse
        exact (hinverse 0).comp hinput
      have hΦheight : ∀ s x, (Φ s x).2 = x.2 := by
        intro s x
        rw [hΦapply, hΨheight]
        exact hheight 0 s x
      have hΦsupport : ∀ i s x, x.2 ∈ S i → Φ s x = F i s x := by
        intro i s x
        refine Fin.cases ?_ (fun j => ?_) i
        · intro hx
          have hnotTail : ∀ j : Fin n, (F 0 s x).2 ∉ S' j := by
            intro j hj
            have hne : (0 : Fin (n+1)) ≠ j.succ := by
              intro heq
              have hv := congrArg Fin.val heq
              simp at hv
            have hd : Disjoint (S 0) (S j.succ) := hdisj hne
            have hmem0 : (F 0 s x).2 ∈ S 0 := by rw [hheight 0 s x]; exact hx
            exact (Set.disjoint_left.mp hd) hmem0 (by simpa [S'] using hj)
          have htail : Ψ s (F 0 s x) = F 0 s x := hΨfixed s (F 0 s x) hnotTail
          calc
            Φ s x = Ψ s (F 0 s x) := hΦapply s x
            _ = F 0 s x := htail
        · intro hx
          have hx0 : x.2 ∉ S 0 := by
            intro hmem
            have hne : (0 : Fin (n+1)) ≠ j.succ := by
              intro heq
              have hv := congrArg Fin.val heq
              simp at hv
            have hd : Disjoint (S 0) (S j.succ) := hdisj hne
            exact (Set.disjoint_left.mp hd) hmem hx
          have hfirst : F 0 s x = x := hfixed 0 s x hx0
          calc
            Φ s x = Ψ s (F 0 s x) := hΦapply s x
            _ = Ψ s x := by rw [hfirst]
            _ = F j.succ s x := by simpa [F',S'] using hΨsupport j s x (by simpa [S'] using hx)
      have hΦfixed : ∀ s x, (∀ i, x.2 ∉ S i) → Φ s x = x := by
        intro s x hnone
        have hfirst : F 0 s x = x := hfixed 0 s x (hnone 0)
        have htail : ∀ j : Fin n, x.2 ∉ S' j := by
          intro j
          exact hnone j.succ
        calc
          Φ s x = Ψ s (F 0 s x) := hΦapply s x
          _ = Ψ s x := by rw [hfirst]
          _ = x := hΨfixed s x htail
      exact ⟨Φ,hΦzero,hΦforward,hΦinverseContinuous,hΦheight,hΦsupport,hΦfixed⟩

end DirectGLSSW.DescendingSpatial


