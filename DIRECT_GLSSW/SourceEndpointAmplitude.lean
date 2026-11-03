import DirectGLSSW.EndpointMarkedCap
import DirectGLSSW.RealPolygons
import EndpointEventSourceAdapter

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceEndpointAmplitude
open DirectGLSSW EndpointCurrent EndpointMarkedCap GlobalCapEntry EndpointEventGeometry

/-- The actual moving-endpoint prefix has the independent GLSSW amplitude,
for every nontrivial prefix. Near data are arbitrary and disappear by the
proved marked-output independence. -/
theorem prefix_marked_eq_amplitude
    (hRI : GLSSWRootIndependence) (d : ℕ → ℚ)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (a b : Fin n) (hab : a.val < b.val)
    (hcap : CyclicGeneric (lineCapCore q a b)) :
    endpointMarked d (polygonSignArray q) a.val b.val =
      polygonAmplitude (lineCapCore q a b) hcap :=
  endpointMarked_lineCapCore hRI d q a b hab hcap

/-- The source one-edge marked prefix is the unit source, not a two-vertex
polygon amplitude. -/
theorem prefix_one_edge_unit (d : ℕ → ℚ) (q : ℕ → PlanarPoint ℝ) (a : ℕ) :
    endpointMarked d (polygonSignArray q) a a = 1 :=
  endpointMarked_diagonal d (polygonSignArray q) a

/-- Replace only the formal endpoint slot 0 by the first fixed suffix vertex.
The rest of the finite word remains the actual fixed polygonal arc. -/
def suffixAnchoredWord (q : ℕ → PlanarPoint ℝ) (k : ℕ) : ℕ → PlanarPoint ℝ :=
  fun x => if x = 0 then q k else q x

@[simp] theorem suffixAnchoredWord_zero (q : ℕ → PlanarPoint ℝ) (k : ℕ) :
    suffixAnchoredWord q k 0 = q k := by simp [suffixAnchoredWord]

@[simp] theorem suffixAnchoredWord_positive (q : ℕ → PlanarPoint ℝ) (k x : ℕ)
    (hx : 0 < x) : suffixAnchoredWord q k x = q x := by
  simp [suffixAnchoredWord, ne_of_gt hx]

/-- For a suffix with at least two physical edges, the marked source on
q_k,...,q_j is exactly the independent amplitude of that literal closed
polygon. `hcap` is the source's explicit auxiliary cap genericity, not a
consequence of CoreHGeneric. -/
theorem suffix_marked_eq_amplitude
    (hRI : GLSSWRootIndependence) (d : ℕ → ℚ)
    (q : ℕ → PlanarPoint ℝ) (k j : ℕ)
    (hk : 0 < k) (hkj : k + 1 < j)
    (hcap : CyclicGeneric
      (lineCapCore (suffixAnchoredWord q k)
        (⟨k, by omega⟩ : Fin (j + 1))
        (⟨j - 1, by omega⟩ : Fin (j + 1)))) :
    markedAmplitude (fun _ l _ => d l) (polygonSignArray q) k j =
      polygonAmplitude
        (lineCapCore (suffixAnchoredWord q k)
          (⟨k, by omega⟩ : Fin (j + 1))
          (⟨j - 1, by omega⟩ : Fin (j + 1))) hcap := by
  let a : Fin (j + 1) := ⟨k, by omega⟩
  let b : Fin (j + 1) := ⟨j - 1, by omega⟩
  have hab : a.val < b.val := by dsimp [a, b]; omega
  have hbridge := endpointMarked_lineCapCore hRI d
    (suffixAnchoredWord q k) a b hab hcap
  have hlocal : markedAmplitude (fun _ l _ => d l) (polygonSignArray q) k j =
      endpointMarked d (polygonSignArray (suffixAnchoredWord q k)) k (j - 1) := by
    rw [endpointMarked, if_pos (by omega : k ≤ j - 1)]
    have hj : j - 1 + 1 = j := by omega
    rw [hj]
    apply markedAmplitude_congr_interval
    · omega
    · intro x y z hx hxy hyz hz
      by_cases hxk : x = k
      · subst x
        simp [EndpointCurrent.endpointFar, suffixAnchoredWord,
          polygonSignArray, polygonHDet, ne_of_gt (by omega : 0 < y),
          ne_of_gt (by omega : 0 < z)]
      · have hx0 : 0 < x := by omega
        simp [EndpointCurrent.endpointFar, hxk, suffixAnchoredWord,
          polygonSignArray, polygonHDet, ne_of_gt hx0,
          ne_of_gt (by omega : 0 < y), ne_of_gt (by omega : 0 < z)]
  exact hlocal.trans (by simpa [a, b] using hbridge)

/-- The source suffix with one physical edge is the unit marked output. -/
theorem suffix_one_edge_unit (d : ℕ → ℚ)
    (q : ℕ → PlanarPoint ℝ) (k : ℕ) :
    markedAmplitude (fun _ l _ => d l) (polygonSignArray q) k (k + 1) = 1 := by
  unfold markedAmplitude
  rw [phi_eq_unary_add]
  have hIoo : Finset.Ioo k (k + 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    rcases Finset.mem_Ioo.mp hx with ⟨hax, hxsucc⟩
    omega
  simp [nonUnary, hIoo, ordinaryCurrent_adjacent]

/-- Full source-A endpoint event, with the three literal regimes. Genericity
of the particular finite prefix/suffix caps is explicit on the source
auxiliary locus; it is not inferred from the current-level CoreHGeneric. -/
theorem exists_endpoint_event_amplitude_all_regimes
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (d : ℕ → ℚ) (n : ℕ)
    {k j : ℕ} (hk : 0 < k) (hkj : k < j) (hjn : j ≤ n) (τ : ℝ)
    (hqDistinct : ∀ a b, a ≤ n → b ≤ n → a ≠ b → q a ≠ q b)
    (hcollinear : q k = q 0 + τ • (q j - q 0))
    (htransverse : planarDet (q k - q j) v ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) → polygonHDet q a b c ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      let Q := moveEndpoint q v (-ε)
      ∀ (hprefix : ∀ a : Fin n, a.val < k - 1 →
          CyclicGeneric (lineCapCore Q a (⟨k - 1, by omega⟩ : Fin n)))
        (hsuffix : k + 1 < j →
          CyclicGeneric (lineCapCore (suffixAnchoredWord Q k)
            (⟨k, by omega⟩ : Fin (j + 1))
            (⟨j - 1, by omega⟩ : Fin (j + 1))))
        (a i : Fin n),
      endpointCurrent d (polygonSignArray (moveEndpoint q v ε)) a.val i.val -
        endpointCurrent d (polygonSignArray Q) a.val i.val =
      if τ < 0 then
        scalarSignValue (planarDet (q k - q j) v) *
          (if ha : a.val < k - 1 then
            polygonAmplitude (lineCapCore Q a (⟨k - 1, by omega⟩ : Fin n))
              (hprefix a ha)
           else if a.val = k - 1 then 1 else 0) *
          source k j * endpointCurrent d (polygonSignArray Q) (j - 1) i.val
      else if 1 < τ then
        scalarSignValue (planarDet (q k - q j) v) * source a.val k *
          (if hs : k + 1 < j then
            polygonAmplitude (lineCapCore (suffixAnchoredWord Q k)
              (⟨k, by omega⟩ : Fin (j + 1))
              (⟨j - 1, by omega⟩ : Fin (j + 1))) (hsuffix hs)
           else 1) * endpointCurrent d (polygonSignArray Q) (j - 1) i.val
      else
        scalarSignValue (planarDet (q k - q j) v) * source a.val k * source k j *
          endpointCurrent d (polygonSignArray Q) (j - 1) i.val := by
  obtain ⟨ρ, hρ, hcurrent⟩ :=
    EndpointEventSourceAdapter.exists_endpoint_event_matrix_all_regimes
      q v d n hk hkj hjn τ hqDistinct hcollinear htransverse hisolated
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ
  dsimp only
  intro hprefix hsuffix a i
  let Q := moveEndpoint q v (-ε)
  have hP : endpointMarked d (polygonSignArray Q) a.val (k - 1) =
      if ha : a.val < k - 1 then
        polygonAmplitude (lineCapCore Q a (⟨k - 1, by omega⟩ : Fin n)) (hprefix a ha)
      else if a.val = k - 1 then 1 else 0 := by
    by_cases ha : a.val < k - 1
    · rw [dif_pos ha]
      exact prefix_marked_eq_amplitude hRI d Q n a ⟨k - 1, by omega⟩ ha (hprefix a ha)
    · rw [dif_neg ha]
      by_cases heq : a.val = k - 1
      · rw [if_pos heq]
        simpa [heq] using prefix_one_edge_unit d Q a.val
      · rw [if_neg heq]
        have hnot : ¬ a.val ≤ k - 1 := by omega
        simp [endpointMarked, hnot]
  have hS : markedAmplitude (fun _ l _ => d l) (polygonSignArray Q) k j =
      if hs : k + 1 < j then
        polygonAmplitude (lineCapCore (suffixAnchoredWord Q k)
          (⟨k, by omega⟩ : Fin (j + 1))
          (⟨j - 1, by omega⟩ : Fin (j + 1))) (hsuffix hs)
      else 1 := by
    by_cases hs : k + 1 < j
    · rw [dif_pos hs]
      exact suffix_marked_eq_amplitude hRI d Q k j hk hs (hsuffix hs)
    · rw [dif_neg hs]
      have hj : j = k + 1 := by omega
      subst j
      exact suffix_one_edge_unit d Q k
  obtain ⟨_, _, hjump⟩ := hcurrent ε hε hερ
  have h := hjump a i
  rw [hP, hS] at h
  exact h

end DirectGLSSW.SourceEndpointAmplitude





