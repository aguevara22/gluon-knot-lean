import ReversalContract.Contract

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW

open DirectGLSSW.GeminiReversalContract

/-- Edge index correspondence under orientation reversal: edge `i` (between `q i` and
`q (cyclicSuccessor i)`) corresponds to edge `(cyclicSuccessor i).rev` of `reversePolygon q`. -/
def edgeRev {n : ℕ} (i : Fin n) : Fin n :=
  (cyclicSuccessor i).rev

theorem cyclicSuccessor_edgeRev {n : ℕ} (i : Fin n) :
    cyclicSuccessor (edgeRev i) = i.rev := by
  have hn : 0 < n := i.pos
  apply Fin.ext
  simp only [edgeRev, cyclicSuccessor, cyclicVertexIndex_val _ hn, Fin.val_rev]
  split_ifs <;> omega

@[simp] theorem edgeRev_edgeRev {n : ℕ} (i : Fin n) :
    edgeRev (edgeRev i) = i := by
  rw [edgeRev, cyclicSuccessor_edgeRev, Fin.rev_rev]

theorem edgeRev_involutive (n : ℕ) : Function.Involutive (edgeRev (n := n)) :=
  edgeRev_edgeRev

def edgeRevEquiv (n : ℕ) : Equiv.Perm (Fin n) where
  toFun := edgeRev
  invFun := edgeRev
  left_inv := edgeRev_edgeRev
  right_inv := edgeRev_edgeRev

@[simp] theorem edgeRevEquiv_apply {n : ℕ} (i : Fin n) :
    edgeRevEquiv n i = edgeRev i := rfl

@[simp] theorem edgeRevEquiv_symm_apply {n : ℕ} (i : Fin n) :
    (edgeRevEquiv n).symm i = edgeRev i := rfl

theorem edgeRev_injective {n : ℕ} : Function.Injective (edgeRev (n := n)) :=
  (edgeRev_involutive n).injective

@[simp] theorem cyclicSuccessor_edgeRev_cyclicSuccessor {n : ℕ} (j : Fin n) :
    cyclicSuccessor (edgeRev (cyclicSuccessor j)) = edgeRev j := by
  rw [cyclicSuccessor_edgeRev]
  rfl

@[simp] theorem edgeRev_cyclicSuccessor_edgeRev_cyclicSuccessor {n : ℕ} (j : Fin n) :
    edgeRev (cyclicSuccessor (edgeRev (cyclicSuccessor j))) = j := by
  rw [cyclicSuccessor_edgeRev_cyclicSuccessor, edgeRev_edgeRev]

theorem cyclicSuccessorPerm_symm_edgeRev {n : ℕ} (i : Fin n) :
    (cyclicSuccessorPerm n)⁻¹ (edgeRev i) = edgeRev (cyclicSuccessor i) := by
  apply (cyclicSuccessorPerm n).injective
  rw [Equiv.Perm.apply_inv_self, cyclicSuccessorPerm_apply, cyclicSuccessor_edgeRev_cyclicSuccessor]

@[simp] theorem reversePolygon_apply {n : ℕ} (q : Fin n → PlanarPoint ℝ) (i : Fin n) :
    reversePolygon q i = q i.rev := rfl

@[simp] theorem reversePolygon_rev {n : ℕ} (q : Fin n → PlanarPoint ℝ) (i : Fin n) :
    reversePolygon q i.rev = q i := by
  simp [reversePolygon]

@[simp] theorem reversePolygon_reversePolygon {n : ℕ} (q : Fin n → PlanarPoint ℝ) :
    reversePolygon (reversePolygon q) = q := by
  funext i
  simp [reversePolygon]

theorem reversePolygon_edgeRev {n : ℕ} (q : Fin n → PlanarPoint ℝ) (i : Fin n) :
    reversePolygon q (edgeRev i) = q (cyclicSuccessor i) := by
  simp [reversePolygon, edgeRev]

theorem reversePolygon_cyclicSuccessor_edgeRev {n : ℕ} (q : Fin n → PlanarPoint ℝ) (i : Fin n) :
    reversePolygon q (cyclicSuccessor (edgeRev i)) = q i := by
  rw [cyclicSuccessor_edgeRev, reversePolygon_rev]

theorem cyclicTangent_reversePolygon_edgeRev {n : ℕ} (q : Fin n → PlanarPoint ℝ) (i : Fin n) :
    cyclicTangent (reversePolygon q) (edgeRev i) = - cyclicTangent q i := by
  simp only [cyclicTangent, reversePolygon_cyclicSuccessor_edgeRev, reversePolygon_edgeRev]
  abel

theorem cyclicTangent_reversePolygon {n : ℕ} (q : Fin n → PlanarPoint ℝ) (e : Fin n) :
    cyclicTangent (reversePolygon q) e = - cyclicTangent q (edgeRev e) := by
  simpa using cyclicTangent_reversePolygon_edgeRev q (edgeRev e)

theorem turnDet_reversePolygon_edgeRev {n : ℕ} (q : Fin n → PlanarPoint ℝ) (i : Fin n) :
    planarDet (cyclicTangent (reversePolygon q) (edgeRev (cyclicSuccessor i)))
      (cyclicTangent (reversePolygon q) (edgeRev i)) =
      - planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)) := by
  rw [cyclicTangent_reversePolygon_edgeRev, cyclicTangent_reversePolygon_edgeRev]
  simp only [planarDet, Prod.fst_neg, Prod.snd_neg]
  ring

theorem turnDet_reversePolygon {n : ℕ} (q : Fin n → PlanarPoint ℝ) (j : Fin n) :
    planarDet (cyclicTangent (reversePolygon q) j)
      (cyclicTangent (reversePolygon q) (cyclicSuccessor j)) =
      - planarDet (cyclicTangent q (edgeRev (cyclicSuccessor j)))
          (cyclicTangent q (cyclicSuccessor (edgeRev (cyclicSuccessor j)))) := by
  have h := turnDet_reversePolygon_edgeRev q (edgeRev (cyclicSuccessor j))
  simpa only [edgeRev_cyclicSuccessor_edgeRev_cyclicSuccessor, edgeRev_edgeRev] using h

theorem edgeInterior_reversePolygon_edgeRev {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (i : Fin n) (x : PlanarPoint ℝ) :
    edgeInterior (reversePolygon q) (edgeRev i) x ↔ edgeInterior q i x := by
  unfold edgeInterior
  rw [reversePolygon_edgeRev, reversePolygon_cyclicSuccessor_edgeRev]
  exact ⟨onOpenSegment_symm, onOpenSegment_symm⟩

theorem edgeInterior_reversePolygon {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (e : Fin n) (x : PlanarPoint ℝ) :
    edgeInterior (reversePolygon q) e x ↔ edgeInterior q (edgeRev e) x := by
  simpa using edgeInterior_reversePolygon_edgeRev q (edgeRev e) x

theorem cyclicNoncollinear_reversePolygon {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (h1 : cyclicNoncollinear q) :
    cyclicNoncollinear (reversePolygon q) := by
  intro i j k hij hjk hik
  exact h1 i.rev j.rev k.rev
    (Fin.rev_injective.ne hij) (Fin.rev_injective.ne hjk) (Fin.rev_injective.ne hik)

theorem cyclicNoTripleIntersections_reversePolygon {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (h2 : cyclicNoTripleIntersections q) :
    cyclicNoTripleIntersections (reversePolygon q) := by
  intro e f g x hef hfg heg ⟨he, hf, hg⟩
  exact h2 (edgeRev e) (edgeRev f) (edgeRev g) x
    (edgeRev_injective.ne hef) (edgeRev_injective.ne hfg) (edgeRev_injective.ne heg)
    ⟨(edgeInterior_reversePolygon q e x).mp he,
     (edgeInterior_reversePolygon q f x).mp hf,
     (edgeInterior_reversePolygon q g x).mp hg⟩

theorem cyclicGeneric_reversePolygon {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) :
    CyclicGeneric (reversePolygon q) :=
  ⟨hq.size_ge_three,
   cyclicNoncollinear_reversePolygon q hq.g1,
   cyclicNoTripleIntersections_reversePolygon q hq.g2⟩

theorem strictLeft_reversePolygon_iff {n : ℕ} (q : Fin n → PlanarPoint ℝ) :
    StrictLeft (reversePolygon q) ↔ StrictRight q := by
  constructor
  · intro h i
    have hi := h (edgeRev (cyclicSuccessor i))
    rw [cyclicSuccessor_edgeRev_cyclicSuccessor, turnDet_reversePolygon_edgeRev] at hi
    linarith
  · intro h j
    have hj := h (edgeRev (cyclicSuccessor j))
    rw [turnDet_reversePolygon]
    linarith

theorem strictRight_reversePolygon_iff {n : ℕ} (q : Fin n → PlanarPoint ℝ) :
    StrictRight (reversePolygon q) ↔ StrictLeft q := by
  have h := strictLeft_reversePolygon_iff (reversePolygon q)
  rw [reversePolygon_reversePolygon] at h
  exact h.symm

theorem leftCount_eq_filter_succ {n : ℕ} (q : Fin n → PlanarPoint ℝ) :
    leftCount q =
      (Finset.univ.filter fun i : Fin n =>
        0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i))).card := by
  classical
  unfold leftCount
  rw [← Finset.card_map (cyclicSuccessorPerm n).symm.toEmbedding]
  congr 1
  ext i
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.toEmbedding_apply, Equiv.Perm.inv_def]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hsucc : cyclicSuccessor ((cyclicSuccessorPerm n).symm j) = j :=
      (cyclicSuccessorPerm n).apply_symm_apply j
    simpa [hsucc] using hj
  · intro hi
    refine ⟨cyclicSuccessor i, ?_, (cyclicSuccessorPerm n).symm_apply_apply i⟩
    have hprev : (cyclicSuccessorPerm n).symm (cyclicSuccessor i) = i :=
      (cyclicSuccessorPerm n).symm_apply_apply i
    simpa [hprev] using hi

theorem leftCount_reversePolygon {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) :
    leftCount (reversePolygon q) = n - leftCount q := by
  classical
  rw [leftCount_eq_filter_succ q]
  unfold leftCount
  let P : Fin n → Prop := fun i =>
    0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i))
  have hmap :
      (Finset.univ.filter fun j : Fin n =>
        0 < planarDet (cyclicTangent (reversePolygon q) ((cyclicSuccessorPerm n)⁻¹ j))
          (cyclicTangent (reversePolygon q) j)) =
      (Finset.univ.filter fun i : Fin n => ¬ P i).map (edgeRevEquiv n).toEmbedding := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.toEmbedding_apply, edgeRevEquiv_apply]
    refine ⟨?_, ?_⟩
    · intro hj
      refine ⟨edgeRev j, ?_, edgeRev_edgeRev j⟩
      have hj' : 0 < planarDet
          (cyclicTangent (reversePolygon q) ((cyclicSuccessorPerm n)⁻¹ (edgeRev (edgeRev j))))
          (cyclicTangent (reversePolygon q) (edgeRev (edgeRev j))) := by
        simpa only [edgeRev_edgeRev] using hj
      rw [cyclicSuccessorPerm_symm_edgeRev, turnDet_reversePolygon_edgeRev] at hj'
      dsimp [P]
      linarith
    · rintro ⟨i, hi, rfl⟩
      have hdet := cyclic_turn_det_ne_zero hq.size_ge_three q hq.g1 i
      have hneg : planarDet (cyclicTangent q i)
          (cyclicTangent q (cyclicSuccessor i)) < 0 := by
        dsimp [P] at hi
        cases lt_or_gt_of_ne hdet with
        | inl hlt => exact hlt
        | inr hgt => exact False.elim (hi hgt)
      rw [cyclicSuccessorPerm_symm_edgeRev, turnDet_reversePolygon_edgeRev]
      linarith
  have hcard :
      (Finset.univ.filter fun j : Fin n =>
        0 < planarDet (cyclicTangent (reversePolygon q) ((cyclicSuccessorPerm n)⁻¹ j))
          (cyclicTangent (reversePolygon q) j)).card =
      (Finset.univ.filter fun i : Fin n => ¬ P i).card := by
    rw [hmap, Finset.card_map]
  rw [hcard, Finset.filter_not, Finset.card_sdiff (Finset.filter_subset _ _),
    Finset.card_univ, Fintype.card_fin]

theorem cyclicGeneric_reversal_thm :
    ∀ {n : ℕ} (q : Fin n → PlanarPoint ℝ) (_hq : CyclicGeneric q),
      CyclicGeneric (reversePolygon q) ∧
        (StrictLeft (reversePolygon q) ↔ StrictRight q) ∧
        (StrictRight (reversePolygon q) ↔ StrictLeft q) := by
  intro n q hq
  exact ⟨cyclicGeneric_reversePolygon q hq,
    strictLeft_reversePolygon_iff q,
    strictRight_reversePolygon_iff q⟩

end DirectGLSSW
