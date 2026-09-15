namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- Collapse the new occurrence to its attachment label; every old label
is recovered from the proved exhaustive old/new decomposition. -/
def softCollapseIndex (j : ZMod n) (a : ZMod (n + 1)) : ZMod n :=
  if h : a = softNewIndex j then j else
    Classical.choose ((soft_indices_exhaust j a).resolve_left h)

theorem softCollapseIndex_new (j : ZMod n) :
    softCollapseIndex j (softNewIndex j) = j := by
  simp [softCollapseIndex]

theorem softCollapseIndex_old (j k : ZMod n) :
    softCollapseIndex j (softOldIndex j k) = k := by
  unfold softCollapseIndex
  rw [dif_neg (softOldIndex_ne_new j k)]
  apply softOldIndex_injective j
  exact (Classical.choose_spec ((soft_indices_exhaust j (softOldIndex j k)).resolve_left
    (softOldIndex_ne_new j k))).symm

/-- The source's exceptional far sign, defined on all core labels.
Its value at j is unused; admissibility makes every other value nonzero. -/
def softFarSign (P : LabelledTuple n) (j : ZMod n) (q : Plane) (k : ZMod n) : SignType :=
  -SignType.sign (det q (P k - P j))

theorem softFarSign_ne_zero {P : LabelledTuple n} {j : ZMod n} {q : Plane}
    (hq : SoftAdmissible P j q) {k : ZMod n} (hk : k ≠ j) :
    softFarSign P j q k ≠ 0 := by
  intro h
  exact (sign_ne_zero.mpr (hq.2.2 k hk)) (SignType.neg_eq_zero_iff.mp h)

/-- These are exactly the reversed triple orders read by the far gates
of (X,A,B) and (A,B,X). They hold for every positive parameter. -/
theorem softFarSign_exceptional (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (ε : ℝ) (hε : 0 < ε) (k : ZMod n) :
    chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j j) (softOldIndex j k) =
      softFarSign P j q k ∧
    chi (softInsertion P j q ε) (softOldIndex j k) (softNewIndex j) (softOldIndex j j) =
      softFarSign P j q k := by
  have h := chi_softInsertion_new_attachment P j k q ε hε
  refine ⟨h, ?_⟩
  exact (chi_cyclic (softInsertion P j q ε) (softOldIndex j k)
    (softNewIndex j) (softOldIndex j j)).symm.trans h

/-- The neighbors are cyclic core neighbors, including the physical wrap.
Their exceptional far values are precisely the two source attachments. -/
theorem softFarSign_neighbors (P : LabelledTuple n) (j : ZMod n) (q : Plane) :
    softFarSign P j q (j - 1) = softAttachmentMinus P j q ∧
    softFarSign P j q (j + 1) = softAttachmentPlus P j q := by
  have hs := softInsertion_attachment_signs P j q 1 (by norm_num)
  exact ⟨(softFarSign_exceptional P j q 1 (by norm_num) (j - 1)).1.symm.trans hs.1,
    (softFarSign_exceptional P j q 1 (by norm_num) (j + 1)).1.symm.trans hs.2⟩

/-- Each ordered distinct child triple avoiding the pair of attachment
occurrences has the same sign as its collapsed core triple near zero.
Old/new exhaustion and alternation cover every order of the new label. -/
theorem soft_chi_pullback_eventually {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) (a b c : ZMod (n + 1))
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (havoid : ¬ (softOldIndex j j ∈ ({a, b, c} : Finset (ZMod (n + 1))) ∧
      softNewIndex j ∈ ({a, b, c} : Finset (ZMod (n + 1))))) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), chi (softInsertion P j q ε) a b c =
      chi P (softCollapseIndex j a) (softCollapseIndex j b) (softCollapseIndex j c) := by
  rcases soft_indices_exhaust j a with rfl | ⟨i, rfl⟩
  · rcases soft_indices_exhaust j b with rfl | ⟨k, rfl⟩
    · exact (hab rfl).elim
    · rcases soft_indices_exhaust j c with rfl | ⟨l, rfl⟩
      · exact (hac rfl).elim
      · have hkj : k ≠ j := by
          intro h; subst k
          exact havoid ⟨by simp, by simp⟩
        have hlj : l ≠ j := by
          intro h; subst l
          exact havoid ⟨by simp, by simp⟩
        have hkl : k ≠ l := fun h => hbc (congrArg (softOldIndex j) h)
        simpa only [softCollapseIndex_new, softCollapseIndex_old] using
          soft_new_nonattachment_chi_persists hP j k l q hkj hlj hkl
  · rcases soft_indices_exhaust j b with rfl | ⟨k, rfl⟩
    · rcases soft_indices_exhaust j c with rfl | ⟨l, rfl⟩
      · exact (hbc rfl).elim
      · have hij : i ≠ j := by
          intro h; subst i
          exact havoid ⟨by simp, by simp⟩
        have hlj : l ≠ j := by
          intro h; subst l
          exact havoid ⟨by simp, by simp⟩
        have hil : i ≠ l := fun h => hac (congrArg (softOldIndex j) h)
        filter_upwards [soft_new_nonattachment_chi_persists hP j i l q hij hlj hil] with ε hε
        simp only [softCollapseIndex_old, softCollapseIndex_new]
        calc
          chi (softInsertion P j q ε) (softOldIndex j i) (softNewIndex j) (softOldIndex j l) =
              -chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j i)
                (softOldIndex j l) := chi_swap_first _ _ _ _
          _ = -chi P j i l := congrArg (fun s : SignType => -s) hε
          _ = chi P i j l := (chi_swap_first P j i l).symm
    · rcases soft_indices_exhaust j c with rfl | ⟨l, rfl⟩
      · have hij : i ≠ j := by
          intro h; subst i
          exact havoid ⟨by simp, by simp⟩
        have hkj : k ≠ j := by
          intro h; subst k
          exact havoid ⟨by simp, by simp⟩
        have hik : i ≠ k := fun h => hab (congrArg (softOldIndex j) h)
        filter_upwards [soft_new_nonattachment_chi_persists hP j i k q hij hkj hik] with ε hε
        simp only [softCollapseIndex_old, softCollapseIndex_new]
        calc
          chi (softInsertion P j q ε) (softOldIndex j i) (softOldIndex j k) (softNewIndex j) =
              chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j i)
                (softOldIndex j k) := chi_cyclic _ _ _ _
          _ = chi P j i k := hε
          _ = chi P i k j := (chi_cyclic P j i k).symm
      · exact Eventually.of_forall (fun ε => by
          simp only [chi_softInsertion_old, softCollapseIndex_old])

/-- Finiteness of the actual child label set supplies a common neighborhood
for every allowed ordered triple, not one radius chosen per triple. -/
theorem soft_all_chi_pullback_eventually {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ∀ a b c : ZMod (n + 1),
      a ≠ b → b ≠ c → a ≠ c →
      ¬ (softOldIndex j j ∈ ({a, b, c} : Finset (ZMod (n + 1))) ∧
        softNewIndex j ∈ ({a, b, c} : Finset (ZMod (n + 1)))) →
      chi (softInsertion P j q ε) a b c =
        chi P (softCollapseIndex j a) (softCollapseIndex j b) (softCollapseIndex j c) := by
  apply eventually_all.mpr
  intro a
  apply eventually_all.mpr
  intro b
  apply eventually_all.mpr
  intro c
  by_cases h : a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      ¬ (softOldIndex j j ∈ ({a, b, c} : Finset (ZMod (n + 1))) ∧
        softNewIndex j ∈ ({a, b, c} : Finset (ZMod (n + 1))))
  · exact (soft_chi_pullback_eventually hP j q a b c h.1 h.2.1 h.2.2.1 h.2.2.2).mono
      (fun _ he _ _ _ _ => he)
  · exact Eventually.of_forall (fun _ hab hbc hac ha => (h ⟨hab, hbc, hac, ha⟩).elim)

/-- Root-independent geometric far data for the duplication proof. G1 and
admissibility suffice. The single positive radius supplies child G1 and
all nonexceptional pullbacks; exceptional signs and cyclic neighbor values
are exact. No boundary-word correspondence or child Generic at zero is assumed. -/
theorem soft_far_sign_family (_hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      G1 (softInsertion P j q ε) ∧
      (∀ a b c : ZMod (n + 1), a ≠ b → b ≠ c → a ≠ c →
        ¬ (softOldIndex j j ∈ ({a, b, c} : Finset (ZMod (n + 1))) ∧
          softNewIndex j ∈ ({a, b, c} : Finset (ZMod (n + 1)))) →
        chi (softInsertion P j q ε) a b c =
          chi P (softCollapseIndex j a) (softCollapseIndex j b) (softCollapseIndex j c)) ∧
      (∀ k : ZMod n, k ≠ j → softFarSign P j q k ≠ 0 ∧
        chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j j) (softOldIndex j k) =
          softFarSign P j q k ∧
        chi (softInsertion P j q ε) (softOldIndex j k) (softNewIndex j) (softOldIndex j j) =
          softFarSign P j q k) ∧
      softFarSign P j q (j - 1) = softAttachmentMinus P j q ∧
      softFarSign P j q (j + 1) = softAttachmentPlus P j q := by
  obtain ⟨δp, hδp, hp⟩ := Metric.eventually_nhds_iff.mp (soft_all_chi_pullback_eventually hP j q)
  obtain ⟨δg, hδg, hg⟩ := softInsertion_small_G1 hP j q hq
  refine ⟨min δp δg, lt_min hδp hδg, ?_⟩
  intro ε hε hεδ
  have hεp : dist ε (0 : ℝ) < δp := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hε] using
      (lt_of_lt_of_le hεδ (min_le_left δp δg))
  refine ⟨hg ε hε (lt_of_lt_of_le hεδ (min_le_right δp δg)), hp hεp, ?_,
    (softFarSign_neighbors P j q).1, (softFarSign_neighbors P j q).2⟩
  intro k hk
  exact ⟨softFarSign_ne_zero hq hk, softFarSign_exceptional P j q ε hε k⟩

end
end SM
