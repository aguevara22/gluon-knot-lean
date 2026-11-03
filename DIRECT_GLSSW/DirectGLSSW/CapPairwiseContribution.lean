import DirectGLSSW.CapGlobalTelescope
import DirectGLSSW.CapCrossingVectors

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DirectGLSSW.CapPairwiseContribution

open DirectGLSSW
open DirectGLSSW.CapCrossingEvent
open DirectGLSSW.CapCriticalTimes
open DirectGLSSW.CapCriticalEventGeometry
open DirectGLSSW.CapGlobalEventJump
open DirectGLSSW.CapCriticalGlobalJump
open DirectGLSSW.CapGlobalTelescope
open DirectGLSSW.CapCrossingVectors
open DirectGLSSW.GlobalCapAlgebra
open DirectGLSSW.GlobalCapEntry
open DirectGLSSW.GlobalCapIntertwining

private theorem exists_isolating_radius (T : Finset ℝ) (t : ℝ) (ht : t ∈ T) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u, u ∈ T → u ≠ t → ρ < |u - t| := by
  classical
  let gaps := (T.erase t).image (fun u => |u - t|)
  by_cases hne : gaps.Nonempty
  · let ρ := gaps.min' hne / 2
    have hminpos : 0 < gaps.min' hne := by
      have hx : gaps.min' hne ∈ gaps := gaps.min'_mem hne
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hx
      have hut : u ≠ t := (Finset.mem_erase.mp hu).1
      rw [← heq]
      exact abs_pos.mpr (sub_ne_zero.mpr hut)
    refine ⟨ρ, ?_, ?_⟩
    · dsimp [ρ]
      linarith
    · intro u hu hut
      have huerase : u ∈ T.erase t := Finset.mem_erase.mpr ⟨hut, hu⟩
      have hgap : |u - t| ∈ gaps := Finset.mem_image.mpr ⟨u, huerase, rfl⟩
      have hmin : gaps.min' hne ≤ |u - t| := gaps.min'_le _ hgap
      dsimp [ρ]
      linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro u hu hut
    have huerase : u ∈ T.erase t := Finset.mem_erase.mpr ⟨hut, hu⟩
    have hgap : |u - t| ∈ gaps := Finset.mem_image.mpr ⟨u, huerase, rfl⟩
    exact (hne ⟨|u - t|, hgap⟩).elim

private theorem crossing_isolation_disjunction
    (q : ℕ → PlanarPoint ℝ) (n k j : ℕ)
    (htriples : ∀ i a b, i < a → a < b → b ≤ n → (i, a, b) ≠ (0, k, j) →
      polygonHDet q i a b ≠ 0) :
    ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) → polygonHDet q a b c ≠ 0 := by
  intro a b c hab hbc hcn hcase
  apply htriples a b c hab hbc hcn
  intro heq
  have heq' : a = 0 ∧ b = k ∧ c = j := by
    simpa only [Prod.mk.injEq] using heq
  rcases heq' with ⟨ha, hb, hc⟩
  rcases hcase with hbad | hbad | hbad
  · exact hbad ha
  · exact hbad hb
  · exact hbad hc

private def sandwich (n : ℕ) (vc ud : Fin n → ℚ)
    (M : Matrix (Fin n) (Fin n) ℚ) : ℚ :=
  ∑ i : Fin n, vc i * ∑ j : Fin n, M i j * ud j

private theorem sandwich_rankOne_left_zero
    (n : ℕ) (vc u v ud : Fin n → ℚ) (a : ℚ)
    (hleft : (∑ i : Fin n, vc i * u i) = 0) :
    sandwich n vc ud (fun i j => 2 * a * u i * v j) = 0 := by
  classical
  unfold sandwich
  calc
    (∑ i : Fin n, vc i * ∑ j : Fin n, (2 * a * u i * v j) * ud j) =
        ∑ i : Fin n, vc i * ((2 * a * u i) * ∑ j : Fin n, v j * ud j) := by
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          calc
            (∑ j : Fin n, (2 * a * u i * v j) * ud j) =
                ∑ j : Fin n, (2 * a * u i) * (v j * ud j) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ = (2 * a * u i) * ∑ j : Fin n, v j * ud j := by rw [Finset.mul_sum]
    _ = 0 := by
          have hfactor :
              (∑ i : Fin n, vc i * ((2 * a * u i) * ∑ j : Fin n, v j * ud j)) =
                (2 * a * (∑ j : Fin n, v j * ud j)) * (∑ i : Fin n, vc i * u i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          rw [hfactor, hleft]
          ring

private theorem sandwich_rankOne_right_zero
    (n : ℕ) (vc u v ud : Fin n → ℚ) (a : ℚ)
    (hright : (∑ j : Fin n, v j * ud j) = 0) :
    sandwich n vc ud (fun i j => 2 * a * u i * v j) = 0 := by
  classical
  unfold sandwich
  calc
    (∑ i : Fin n, vc i * ∑ j : Fin n, (2 * a * u i * v j) * ud j) =
        ∑ i : Fin n, vc i * ((2 * a * u i) * ∑ j : Fin n, v j * ud j) := by
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          calc
            (∑ j : Fin n, (2 * a * u i * v j) * ud j) =
                ∑ j : Fin n, (2 * a * u i) * (v j * ud j) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ = (2 * a * u i) * ∑ j : Fin n, v j * ud j := by rw [Finset.mul_sum]
    _ = 0 := by rw [hright]; simp

private theorem sandwich_sum
    {α : Type} [DecidableEq α] (n : ℕ) (vc ud : Fin n → ℚ)
    (S : Finset α) (M : α → Matrix (Fin n) (Fin n) ℚ) :
    sandwich n vc ud (∑ a ∈ S, M a) = ∑ a ∈ S, sandwich n vc ud (M a) := by
  classical
  unfold sandwich
  simp only [Matrix.sum_apply]
  calc
    (∑ i : Fin n, vc i * ∑ j : Fin n, (∑ a ∈ S, M a i j) * ud j) =
        ∑ i : Fin n, vc i * ∑ j : Fin n, ∑ a ∈ S, M a i j * ud j := by
          apply Finset.sum_congr rfl
          intro i hi
          apply congrArg (fun z : ℚ => vc i * z)
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_mul]
    _ = ∑ i : Fin n, vc i * ∑ a ∈ S, ∑ j : Fin n, M a i j * ud j := by
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          rw [Finset.sum_comm]
    _ = ∑ i : Fin n, ∑ a ∈ S, vc i * ∑ j : Fin n, M a i j * ud j := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ = ∑ a ∈ S, ∑ i : Fin n, vc i * ∑ j : Fin n, M a i j * ud j := by
          rw [Finset.sum_comm]

private theorem sandwich_sub (n : ℕ) (vc ud : Fin n → ℚ)
    (A B : Matrix (Fin n) (Fin n) ℚ) :
    sandwich n vc ud (A - B) = sandwich n vc ud A - sandwich n vc ud B := by
  classical
  unfold sandwich
  calc
    (∑ i : Fin n, vc i * ∑ j : Fin n, (A - B) i j * ud j) =
        ∑ i : Fin n, vc i * ((∑ j : Fin n, A i j * ud j) -
          ∑ j : Fin n, B i j * ud j) := by
            apply Finset.sum_congr rfl
            intro i hi
            congr 1
            calc
              (∑ j : Fin n, (A - B) i j * ud j) =
                  ∑ j : Fin n, ((A i j * ud j) - (B i j * ud j)) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [Matrix.sub_apply]
                    ring
              _ = (∑ j : Fin n, A i j * ud j) -
                  ∑ j : Fin n, B i j * ud j := Finset.sum_sub_distrib
    _ = (∑ i : Fin n, vc i * ∑ j : Fin n, A i j * ud j) -
        ∑ i : Fin n, vc i * ∑ j : Fin n, B i j * ud j := by
          calc
            (∑ i : Fin n, vc i * ((∑ j : Fin n, A i j * ud j) -
              ∑ j : Fin n, B i j * ud j)) =
                ∑ i : Fin n, (vc i * ∑ j : Fin n, A i j * ud j -
                  vc i * ∑ j : Fin n, B i j * ud j) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
            _ = _ := Finset.sum_sub_distrib

theorem actual_pairwise_contribution_identity
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n k l : ℕ)
    (hzero : (q 0).2 = 0)
    (hoff : ∀ a, 0 < a → a ≤ n → (q a).2 ≠ 0)
    (hdistinct : ∀ a b, 0 < a → a ≤ n → 0 < b → b ≤ n → a ≠ b → q a ≠ q b)
    (hpositive : ∀ i a b, 0 < i → i < a → a < b → b ≤ n → polygonHDet q i a b ≠ 0)
    (hroots : ∀ p r, p ∈ criticalPairs q n → r ∈ criticalPairs q n →
      criticalRoot q p = criticalRoot q r → p = r)
    (hk : 0 < k) (hkn : k < n)
    (hl : 0 < l) (hln : l < n)
    (hsK : planarDet (q k - q (k+1)) (1, 0) ≠ 0)
    (hsL : planarDet (q l - q (l+1)) (1, 0) ≠ 0)
    (hτc : (q k).2 / (q (k+1)).2 < 0)
    (hτd : (q l).2 / (q (l+1)).2 < 0)
    (hcd : criticalRoot q (k, k+1) < criticalRoot q (l, l+1))
    (hlocalCaps : ∀ t, t ∈ criticalTimes q n →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
        ∀ a b : Fin n, a.val < b.val →
          CyclicGeneric (lineCapCore (horizontalMove q (t+s)) a b)) :
    let c := criticalRoot q (k, k+1)
    let d := criticalRoot q (l, l+1)
    let vc : Fin n → ℚ := fun i => lineCapF (horizontalMove q c) n ⟨k, hkn⟩ i
    let ud : Fin n → ℚ := fun j => lineCapU (horizontalMove q d) n j ⟨l-1, by omega⟩
    let sc := scalarSignValue (q (k+1)).2
    let sd := scalarSignValue (q (l+1)).2
    (sc + sd) * (∑ i : Fin n, vc i * ud i) +
      ∑ t ∈ (criticalTimes q n).filter (fun t => c < t ∧ t < d),
        ∑ i : Fin n, ∑ j : Fin n,
          vc i * contributionAt q n t i j * ud j = 0 := by
  classical
  let c : ℝ := criticalRoot q (k, k+1)
  let d : ℝ := criticalRoot q (l, l+1)
  let τc : ℝ := (q k).2 / (q (k+1)).2
  let τd : ℝ := (q l).2 / (q (l+1)).2
  let qc : ℕ → PlanarPoint ℝ := horizontalMove q c
  let qd : ℕ → PlanarPoint ℝ := horizontalMove q d
  let vc : Fin n → ℚ := fun i => lineCapF qc n ⟨k, hkn⟩ i
  let vd : Fin n → ℚ := fun i => lineCapF qd n ⟨l, hln⟩ i
  let uc : Fin n → ℚ := fun i => lineCapU qc n i ⟨k-1, by omega⟩
  let ud : Fin n → ℚ := fun i => lineCapU qd n i ⟨l-1, by omega⟩
  let sc : ℚ := scalarSignValue (q (k+1)).2
  let sd : ℚ := scalarSignValue (q (l+1)).2
  let T := criticalTimes q n
  have hcT : c ∈ T := by
    apply (mem_criticalTimes_iff q n c).2
    refine ⟨k, k+1, hk, by omega, by omega, hsK, ?_⟩
    simp [c, criticalRoot]
  have hdT : d ∈ T := by
    apply (mem_criticalTimes_iff q n d).2
    refine ⟨l, l+1, hl, by omega, by omega, hsL, ?_⟩
    simp [d, criticalRoot]
  obtain ⟨ρcIso, hρcIso, hnoOtherC⟩ := exists_isolating_radius T c hcT
  obtain ⟨ρdIso, hρdIso, hnoOtherD⟩ := exists_isolating_radius T d hdT
  obtain ⟨δc, hδc, hcapsC⟩ := hlocalCaps c hcT
  obtain ⟨δd, hδd, hcapsD⟩ := hlocalCaps d hdT
  have hgeomC := critical_event_geometry q n k (k+1) hzero hoff hdistinct
    hpositive hroots hk (by omega) (by omega) hsK
  have hgeomD := critical_event_geometry q n l (l+1) hzero hoff hdistinct
    hpositive hroots hl (by omega) (by omega) hsL
  rcases hgeomC with ⟨hτcne, hτcne1, hcolC, hisCraw⟩
  rcases hgeomD with ⟨hτdne, hτdne1, hcolD, hisDraw⟩
  have hzeroC : (qc 0).2 = 0 := by
    change (horizontalMove q c 0).2 = 0
    rw [CapGlobalEventJump.horizontalMove_y]
    exact hzero
  have hzeroD : (qd 0).2 = 0 := by
    change (horizontalMove q d 0).2 = 0
    rw [CapGlobalEventJump.horizontalMove_y]
    exact hzero
  have hoffC : ∀ a, 0 < a → a ≤ n → (qc a).2 ≠ 0 := by
    intro a ha han
    change (horizontalMove q c a).2 ≠ 0
    rw [CapGlobalEventJump.horizontalMove_y]
    exact hoff a ha han
  have hoffD : ∀ a, 0 < a → a ≤ n → (qd a).2 ≠ 0 := by
    intro a ha han
    change (horizontalMove q d a).2 ≠ 0
    rw [CapGlobalEventJump.horizontalMove_y]
    exact hoff a ha han
  have hlastC : (qc (k+1)).2 ≠ 0 := hoffC (k+1) (by omega) (by omega)
  have hlastD : (qd (l+1)).2 ≠ 0 := hoffD (l+1) (by omega) (by omega)
  have hisC := crossing_isolation_disjunction qc n k (k+1) hisCraw
  have hisD := crossing_isolation_disjunction qd n l (l+1) hisDraw
  obtain ⟨ρcEig, hρcEig, heigC⟩ := exists_lineCap_crossing_side_eigenidentities
    hRI qc n k hk hkn τc hτc hzeroC hcolC hlastC hoffC hisC
  obtain ⟨ρdEig, hρdEig, heigD⟩ := exists_lineCap_crossing_side_eigenidentities
    hRI qd n l hl hln τd hτd hzeroD hcolD hlastD hoffD hisD
  let Rc := min ρcIso (min δc ρcEig)
  let Rd := min ρdIso (min δd ρdEig)
  let R := min Rc (min Rd ((d-c)/3))
  let ε := R / 2
  have hRc : 0 < Rc := lt_min hρcIso (lt_min hδc hρcEig)
  have hRd : 0 < Rd := lt_min hρdIso (lt_min hδd hρdEig)
  have hgap : 0 < d-c := sub_pos.mpr hcd
  have hR : 0 < R := lt_min hRc (lt_min hRd (by linarith))
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hRρc : R ≤ ρcIso := by dsimp [R, Rc]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hRδc : R ≤ δc := by dsimp [R, Rc]; exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hRσc : R ≤ ρcEig := by dsimp [R, Rc]; exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hRρd : R ≤ ρdIso := by dsimp [R, Rd]; exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hRδd : R ≤ δd := by dsimp [R, Rd]; exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hRσd : R ≤ ρdEig := by dsimp [R, Rd]; exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hRgap : R ≤ (d-c)/3 := by dsimp [R]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hεcIso : ε < ρcIso := by dsimp [ε]; linarith
  have hεdIso : ε < ρdIso := by dsimp [ε]; linarith
  have hεcCaps : ε < δc := by dsimp [ε]; linarith
  have hεdCaps : ε < δd := by dsimp [ε]; linarith
  have hεcEig : ε < ρcEig := by dsimp [ε]; linarith
  have hεdEig : ε < ρdEig := by dsimp [ε]; linarith
  have h2εgap : 2*ε < d-c := by dsimp [ε]; linarith
  have hxc : c-ε ∉ T := by
    intro hmem
    have hne : c-ε ≠ c := by intro heq; linarith
    have hb := hnoOtherC (c-ε) hmem hne
    have habs : |(c-ε)-c| = ε := by rw [show (c-ε)-c = -ε by ring, abs_neg, abs_of_pos hε]
    rw [habs] at hb
    linarith
  have hyd : d+ε ∉ T := by
    intro hmem
    have hne : d+ε ≠ d := by intro heq; linarith
    have hb := hnoOtherD (d+ε) hmem hne
    have habs : |(d+ε)-d| = ε := by rw [show (d+ε)-d = ε by ring, abs_of_pos hε]
    rw [habs] at hb
    linarith
  have hxy : c-ε < d+ε := by linarith
  have htel := lineCapJ_criticalTimes_telescope hRI q n hxy hzero hoff hdistinct
    hpositive hroots hxc hyd hlocalCaps
  have hcapCPlus : ∀ a b : Fin n, a.val < b.val →
      CyclicGeneric (lineCapCore (horizontalMove qc ε) a b) := by
    intro a b hab
    have h := hcapsC ε (by rw [abs_of_pos hε]; exact hε) (by rw [abs_of_pos hε]; exact hεcCaps) a b hab
    rw [CapGlobalEventJump.horizontalMove_add q c ε]
    exact h
  have hcapCMinus : ∀ a b : Fin n, a.val < b.val →
      CyclicGeneric (lineCapCore (horizontalMove qc (-ε)) a b) := by
    intro a b hab
    have h := hcapsC (-ε) (by rw [abs_neg, abs_of_pos hε]; exact hε)
      (by rw [abs_neg, abs_of_pos hε]; exact hεcCaps) a b hab
    rw [CapGlobalEventJump.horizontalMove_add q c (-ε)]
    exact h
  have hcapDPlus : ∀ a b : Fin n, a.val < b.val →
      CyclicGeneric (lineCapCore (horizontalMove qd ε) a b) := by
    intro a b hab
    have h := hcapsD ε (by rw [abs_of_pos hε]; exact hε)
      (by rw [abs_of_pos hε]; exact hεdCaps) a b hab
    rw [CapGlobalEventJump.horizontalMove_add q d ε]
    exact h
  have hcapDMinus : ∀ a b : Fin n, a.val < b.val →
      CyclicGeneric (lineCapCore (horizontalMove qd (-ε)) a b) := by
    intro a b hab
    have h := hcapsD (-ε) (by rw [abs_neg, abs_of_pos hε]; exact hε)
      (by rw [abs_neg, abs_of_pos hε]; exact hεdCaps) a b hab
    rw [CapGlobalEventJump.horizontalMove_add q d (-ε)]
    exact h
  have hsideC := heigC ε hε hεcEig hcapCPlus hcapCMinus
  have hsideD := heigD ε hε hεdEig hcapDPlus hcapDMinus
  let x := c-ε
  let y := d+ε
  let I := T.filter (fun t => c < t ∧ t < d)
  have hcNotI : c ∉ I := by simp [I]
  have hdNotI : d ∉ I := by simp [I, le_of_lt hcd]
  have hfilter : T.filter (fun t => x < t ∧ t < y) = insert c (insert d I) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_insert, I, T]
    constructor
    · rintro ⟨ht, hxt, hty⟩
      rcases lt_trichotomy t c with htc | htc | htc
      · have hne : t ≠ c := ne_of_lt htc
        have hbound := hnoOtherC t ht hne
        dsimp [x] at hxt
        have habs : |t-c| = c-t := by rw [abs_of_neg (sub_neg.mpr htc)]; ring
        have hsmall : c-t < ε := by linarith
        have hεsmall := lt_trans hεcIso hbound
        rw [habs] at hbound
        linarith
      · subst t
        exact Or.inl rfl
      · rcases lt_trichotomy t d with htd | htd | htd
        · exact Or.inr (Or.inr ⟨ht, htc, htd⟩)
        · subst t
          exact Or.inr (Or.inl rfl)
        · have hne : t ≠ d := ne_of_gt htd
          have hbound := hnoOtherD t ht hne
          dsimp [y] at hty
          have habs : |t-d| = t-d := by rw [abs_of_pos (sub_pos.mpr htd)]
          have hsmall : t-d < ε := by linarith
          have hεsmall := lt_trans hεdIso hbound
          rw [habs] at hbound
          linarith
    · intro ht
      rcases ht with ht | ht | ht
      · subst t
        exact ⟨hcT, by dsimp [x]; linarith, by dsimp [y]; linarith⟩
      · subst t
        exact ⟨hdT, by dsimp [x]; linarith, by dsimp [y]; linarith⟩
      · rcases ht with ⟨ht, hct, htd⟩
        exact ⟨ht, by dsimp [x]; linarith, by dsimp [y]; linarith⟩
  have htel' := htel
  rw [hfilter] at htel'
  let sandwichCD := sandwich n vc ud
  have hSandTel := congrArg sandwichCD htel'
  have hcEndpoint : contributionAt q n c =
      eventContribution qc n k (k+1) hk (by omega) (by omega) τc := by
    exact contributionAt_eq_eventContribution q n k (k+1) hroots hk (by omega) (by omega) hsK
  have hdEndpoint : contributionAt q n d =
      eventContribution qd n l (l+1) hl (by omega) (by omega) τd := by
    exact contributionAt_eq_eventContribution q n l (l+1) hroots hl (by omega) (by omega) hsL
  have hcRank : eventContribution qc n k (k+1) hk (by omega) (by omega) τc =
      fun i j => 2 * sc * uc i * vc j := by
    have hcond : τc < 0 ∧ k+1 = k+1 := ⟨by simpa [τc] using hτc, rfl⟩
    change (if τc < 0 ∧ k+1 = k+1 then
      fun i j => 2 * scalarSignValue (qc (k+1)).2 * uc i * vc j else 0) = _
    rw [if_pos hcond]
    funext i j
    simp [sc, uc, vc, qc, CapGlobalEventJump.horizontalMove_y]
  have hdRank : eventContribution qd n l (l+1) hl (by omega) (by omega) τd =
      fun i j => 2 * sd * ud i * vd j := by
    have hcond : τd < 0 ∧ l+1 = l+1 := ⟨by simpa [τd] using hτd, rfl⟩
    change (if τd < 0 ∧ l+1 = l+1 then
      fun i j => 2 * scalarSignValue (qd (l+1)).2 * ud i * vd j else 0) = _
    rw [if_pos hcond]
    funext i j
    simp [sd, ud, vd, qd, CapGlobalEventJump.horizontalMove_y]
  have hbelowC : (∑ i : Fin n, vc i * uc i) = 0 := by
    simpa [vc, uc, qc] using lineCap_FU_entry_below qc n k hk hkn
  have hbelowD : (∑ i : Fin n, vd i * ud i) = 0 := by
    simpa [vd, ud, qd] using lineCap_FU_entry_below qd n l hl hln
  have hSandC : sandwichCD (contributionAt q n c) = 0 := by
    rw [hcEndpoint, hcRank]
    exact sandwich_rankOne_left_zero n vc uc vc ud sc hbelowC
  have hSandD : sandwichCD (contributionAt q n d) = 0 := by
    rw [hdEndpoint, hdRank]
    exact sandwich_rankOne_right_zero n vc ud vd ud sd hbelowD
  have hrowC : ∀ j : Fin n,
      (∑ i : Fin n, vc i * lineCapJ (horizontalMove qc (-ε)) n i j) = sc * vc j := by
    intro j
    exact (hsideC.1 j).2
  have hcolD : ∀ i : Fin n,
      (∑ j : Fin n, lineCapJ (horizontalMove qd ε) n i j * ud j) = -sd * ud i := by
    intro i
    exact (hsideD.2 i).1
  have hSandLeft : sandwichCD (lineCapJ (horizontalMove qd ε) n) = -sd *
      (∑ i : Fin n, vc i * ud i) := by
    unfold sandwichCD sandwich
    calc
      (∑ i : Fin n, vc i * ∑ j : Fin n,
          lineCapJ (horizontalMove qd ε) n i j * ud j) =
        ∑ i : Fin n, vc i * (-sd * ud i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hcolD i]
      _ = -sd * (∑ i : Fin n, vc i * ud i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
  have hSandRight : sandwichCD (lineCapJ (horizontalMove qc (-ε)) n) = sc *
      (∑ i : Fin n, vc i * ud i) := by
    unfold sandwichCD sandwich
    calc
      (∑ i : Fin n, vc i * ∑ j : Fin n,
          lineCapJ (horizontalMove qc (-ε)) n i j * ud j) =
        ∑ i : Fin n, ∑ j : Fin n,
          (vc i * lineCapJ (horizontalMove qc (-ε)) n i j) * ud j := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = ∑ j : Fin n, (∑ i : Fin n,
          vc i * lineCapJ (horizontalMove qc (-ε)) n i j) * ud j := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.sum_mul]
      _ = ∑ j : Fin n, (sc * vc j) * ud j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hrowC j]
      _ = sc * (∑ j : Fin n, vc j * ud j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
  have hSandMiddle : sandwichCD
      (∑ t ∈ I, contributionAt q n t) =
      ∑ t ∈ I, ∑ i : Fin n, ∑ j : Fin n,
        vc i * contributionAt q n t i j * ud j := by
    change sandwich n vc ud (∑ t ∈ I, contributionAt q n t) = _
    rw [sandwich_sum]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro i hi
    calc
      vc i * ∑ j : Fin n, contributionAt q n t i j * ud j =
          ∑ j : Fin n, vc i * (contributionAt q n t i j * ud j) := by
            rw [Finset.mul_sum]
      _ = ∑ j : Fin n, vc i * contributionAt q n t i j * ud j := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
  have hSandExpand : sandwichCD (∑ t ∈ insert c (insert d I), contributionAt q n t) =
      sandwichCD (contributionAt q n c) + sandwichCD (contributionAt q n d) +
        sandwichCD (∑ t ∈ I, contributionAt q n t) := by
    change sandwich n vc ud (∑ t ∈ insert c (insert d I), contributionAt q n t) = _
    rw [sandwich_sum]
    change (∑ t ∈ insert c (insert d I), sandwich n vc ud (contributionAt q n t)) = _
    have hcinsert : c ∉ insert d I := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨ne_of_lt hcd, hcNotI⟩
    rw [Finset.sum_insert hcinsert]
    rw [Finset.sum_insert hdNotI]
    change sandwichCD (contributionAt q n c) +
      (sandwichCD (contributionAt q n d) +
        (∑ t ∈ I, sandwich n vc ud (contributionAt q n t))) = _
    have hsumI : (∑ t ∈ I, sandwich n vc ud (contributionAt q n t)) =
        sandwich n vc ud (∑ t ∈ I, contributionAt q n t) :=
      (sandwich_sum n vc ud I (fun t => contributionAt q n t)).symm
    rw [hsumI]
    ring

  have hSandLeft' : sandwichCD (lineCapJ (horizontalMove q (d+ε)) n) =
      -sd * (∑ i : Fin n, vc i * ud i) := by
    simpa [qd, CapGlobalEventJump.horizontalMove_add] using hSandLeft
  have hSandRight' : sandwichCD (lineCapJ (horizontalMove q (c-ε)) n) =
      sc * (∑ i : Fin n, vc i * ud i) := by
    simpa [qc, sub_eq_add_neg, CapGlobalEventJump.horizontalMove_add] using hSandRight
  have hSandTelSub := hSandTel
  rw [show sandwichCD (lineCapJ (horizontalMove q (d+ε)) n -
      lineCapJ (horizontalMove q (c-ε)) n) =
      sandwichCD (lineCapJ (horizontalMove q (d+ε)) n) -
      sandwichCD (lineCapJ (horizontalMove q (c-ε)) n) by
        exact sandwich_sub n vc ud _ _] at hSandTelSub
  rw [hSandExpand, hSandC, hSandD, hSandMiddle, hSandLeft', hSandRight'] at hSandTelSub
  have hmatrixIdentity :
      -(sc + sd) * (∑ i : Fin n, vc i * ud i) =
        ∑ t ∈ I, ∑ i : Fin n, ∑ j : Fin n,
          vc i * contributionAt q n t i j * ud j := by
    convert hSandTelSub using 1 <;> ring
  change (sc + sd) * (∑ i : Fin n, vc i * ud i) +
    ∑ t ∈ I, ∑ i : Fin n, ∑ j : Fin n,
      vc i * contributionAt q n t i j * ud j = 0
  linarith [hmatrixIdentity]









end DirectGLSSW.CapPairwiseContribution
