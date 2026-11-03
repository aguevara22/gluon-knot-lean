import DirectGLSSW.ShortEdgeEndpointPhi
import DirectGLSSW.ShortEdgeRightEndpointPhi
import DirectGLSSW.ShortEdgeSpanningPhi
import DirectGLSSW.NearData

namespace DirectGLSSW.ShortEdgeWeighted.CurrentTableImpl

theorem parentTable_phi_ordinary
    (a : ℕ) (ha : 0 < a) (t : ℕ → Sign)
    (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign)
    {i j : ℕ} (hij : i < j) :
    phi (D1 a t D) (H1 a t H)
      (parentTable a ha t (ordinaryCurrent (D0 a t D) (H0 H))) i j =
        source i j := by
  let U := ordinaryCurrent (D0 a t D) (H0 H)
  have hphi :
      phi (D1 a t D) (H1 a t H) (parentTable a ha t U) i j = source i j := by
    by_cases hbefore : j ≤ a
    · have hci : collapseAfter a i = i :=
        ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega)
      have hcj : collapseAfter a j = j :=
        ShortEdgeCutFibers.collapseAfter_eq_of_le a j hbefore
      have hp := awayPhi a ha t U Sign.neg D H hij (Or.inl hbefore)
      calc
        phi (D1 a t D) (H1 a t H) (parentTable a ha t U) i j =
            phi (D0 a t D) (H0 H) U i j := by
              simpa [PhiEta, Sign.value, hci, hcj] using hp
        _ = source i j := ordinaryCurrent_phi (D0 a t D) (H0 H) hij
    · by_cases hafter : a + 1 ≤ i
      · have hci : collapseAfter a i = i - 1 :=
          ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a i (by omega)
        have hcj : collapseAfter a j = j - 1 :=
          ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)
        have hcore : i - 1 < j - 1 := by omega
        have hp := awayPhi a ha t U Sign.neg D H hij (Or.inr hafter)
        calc
          phi (D1 a t D) (H1 a t H) (parentTable a ha t U) i j =
              phi (D0 a t D) (H0 H) U (i - 1) (j - 1) := by
                simpa [PhiEta, Sign.value, hci, hcj] using hp
          _ = source (i - 1) (j - 1) :=
            ordinaryCurrent_phi (D0 a t D) (H0 H) hcore
          _ = source i j := by
            by_cases heq : j = i + 1 <;> simp [source, heq] <;> omega
      · by_cases hshort : i = a ∧ j = a + 1
        · rcases hshort with ⟨rfl, rfl⟩
          simpa [source, PhiEta, Sign.value] using shortpairPhi1 i ha t U Sign.neg D H
        · by_cases hleft : i = a
          · subst i
            have hBj : a + 1 < j := by omega
            simpa [U] using
              EndpointPhiImpl.leftEndpoint_ordinary_source a j ha hBj t D H
          · by_cases hright : j = a + 1
            · subst j
              have hiA : i < a := by omega
              exact RightEndpointPhiImpl.rightEndpoint_ordinary_source
                a i ha hiA t D H
            · have hiA : i < a := by omega
              have hBj : a + 1 < j := by omega
              exact SpanningPhiImpl.spanning_ordinary_source
                a i j ha hiA hBj t D H
  simpa [U] using hphi

theorem parentTable_eq_ordinaryCurrent
    (a : ℕ) (ha : 0 < a) (t : ℕ → Sign)
    (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign)
    {i j : ℕ} (hij : i < j) :
    parentTable a ha t (ordinaryCurrent (D0 a t D) (H0 H)) i j =
      ordinaryCurrent (D1 a t D) (H1 a t H) i j := by
  apply (ordinaryCurrent_unique (D1 a t D) (H1 a t H)
    (parentTable a ha t (ordinaryCurrent (D0 a t D) (H0 H))) ?_ hij)
  intro x y hxy
  exact parentTable_phi_ordinary a ha t D H hxy

theorem shortEdge_markedAmplitude
    (a i j : ℕ) (ha : 0 < a) (hiA : i < a) (hBj : a + 1 < j)
    (t : ℕ → Sign) (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign) :
    markedAmplitude (D1 a t D) (H1 a t H) i j =
      kappa a ha t * markedAmplitude (D0 a t D) (H0 H) i (collapseAfter a j) := by
  have hij : i < j := by omega
  let U := ordinaryCurrent (D0 a t D) (H0 H)
  let Up := ordinaryCurrent (D1 a t D) (H1 a t H)
  have htab : ∀ x y, x < y →
      Up x y = parentTable a ha t U x y := by
    intro x y hxy
    exact (parentTable_eq_ordinaryCurrent a ha t D H hxy).symm
  have hcongr := phi_congr_upper (D1 a t D) (fun x k y => -H1 a t H x k y)
    (X := Up) (Y := parentTable a ha t U) htab hij
  calc
    markedAmplitude (D1 a t D) (H1 a t H) i j =
        phi (D1 a t D) (fun x k y => -H1 a t H x k y) Up i j := rfl
    _ = phi (D1 a t D) (fun x k y => -H1 a t H x k y)
          (parentTable a ha t U) i j := hcongr
    _ = kappa a ha t *
          phi (D0 a t D) (fun x k y => -H0 H x k y) U i (collapseAfter a j) := by
        simpa [PhiEta, Sign.value] using
          SpanningPhiImpl.spanningPhi a i j ha hiA hBj t U Sign.pos D H
    _ = kappa a ha t *
          markedAmplitude (D0 a t D) (H0 H) i (collapseAfter a j) := rfl

theorem shortEdge_markedAmplitude_near_free
    (a i j : ℕ) (ha : 0 < a) (hiA : i < a) (hBj : a + 1 < j)
    (t : ℕ → Sign) (DParent DCore : TripleArray) (H : ℕ → ℕ → ℕ → Sign) :
    markedAmplitude DParent (H1 a t H) i j =
      kappa a ha t * markedAmplitude DCore (H0 H) i (collapseAfter a j) := by
  have hcore : i < collapseAfter a j := by
    change i < ShortEdgeCutFibers.collapseAfter a j
    rw [ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)]
    omega
  calc
    markedAmplitude DParent (H1 a t H) i j =
        markedAmplitude (D1 a t DParent) (H1 a t H) i j :=
          markedAmplitude_near_independent DParent (D1 a t DParent) (H1 a t H) (by omega)
    _ = kappa a ha t * markedAmplitude (D0 a t DParent) (H0 H)
          i (collapseAfter a j) :=
        shortEdge_markedAmplitude a i j ha hiA hBj t DParent H
    _ = kappa a ha t * markedAmplitude DCore (H0 H) i (collapseAfter a j) := by
        rw [markedAmplitude_near_independent (D0 a t DParent) DCore (H0 H) hcore]

end DirectGLSSW.ShortEdgeWeighted.CurrentTableImpl
