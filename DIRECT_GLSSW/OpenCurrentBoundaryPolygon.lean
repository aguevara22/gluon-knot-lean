import AdjacentEventLimit
import ParentReindex
import DirectGLSSW.RealPolygons

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW
open EndpointEventGeometry EndpointCurrent

/-- The finite prefix marked current is the amplitude of its literal closed
polygon, using root independence only to choose the last root. -/
theorem markedAmplitude_prefix_polygon (hRI : GLSSWRootIndependence)
    (W : ℕ → PlanarPoint ℝ) (k : ℕ)
    (hQ : CyclicGeneric (fun i : Fin (k+1) => W i.val)) :
    markedAmplitude (fun _ _ _ : ℕ => -1) (polygonSignArray W) 0 k =
      polygonAmplitude (fun i : Fin (k+1) => W i.val) hQ := by
  let Q : Fin (k+1) → PlanarPoint ℝ := fun i => W i.val
  let last : Fin (k+1) := ⟨k,by omega⟩
  let R := rootedPolygonWord Q last
  have hsize := hQ.size_ge_three
  have hk : 0<k := by omega
  have hw (i : ℕ) (hi : i≤k) : R i = W i := by
    change W ((k+1+i)%(k+1)) = W i
    congr 1
    rw [Nat.add_comm (k+1) i,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  have hroot : polygonAmplitude Q hQ =
      markedAmplitude (polygonSignArray R) (polygonSignArray R) 0 k := by
    rw [polygonAmplitude_eq_rootedSpinorAmplitude hRI Q hQ last,
      rootedSpinorAmplitude_eq_markedTreeSum hsize Q hQ.g1 last]
    simpa only [Nat.add_sub_cancel] using
      (markedTreeSum_eq_markedAmplitude (polygonSignArray R) (polygonSignArray R) hk)
  rw [hroot]
  apply markedAmplitude_congr_interval _ _ _ _ hk
  intro x y z _ hxy hyz hzk
  simp only [polygonSignArray,polygonHDet,hw x (by omega),hw y (by omega),hw z hzk]

/-- Isolated adjacent endpoint transport with the literal closed-prefix A
and reindexed parent M. The event-chart and closed-prefix genericity inputs
are explicit; physical support factorization is a separate consumer. -/
theorem exists_isolated_boundary_polygon_jump
    (hRI : GLSSWRootIndependence) (W : ℕ → PlanarPoint ℝ)
    (v : PlanarPoint ℝ) (N k : ℕ) (hKN : k<N) (τ : ℝ)
    (hcol : W k=W 0+τ • (W (k+1)-W 0))
    (htrans : planarDet (W k-W (k+1)) v≠0)
    (hisolated : ∀ a b d, a<b → b<d → d≤N →
      (a≠0 ∨ b≠k ∨ d≠k+1) → polygonHDet W a b d≠0)
    (hτ : τ<0) (hQ : CyclicGeneric (fun i : Fin (k+1) => W i.val)) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ ε : ℝ, 0<ε → ε<ρ →
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v ε) N ∧
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v (-ε)) N ∧
      OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v ε)) 0 N -
        OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v (-ε))) 0 N =
      scalarSignValue (planarDet v (W (k+1)-W k)) *
        polygonAmplitude (fun i : Fin (k+1) => W i.val) hQ *
        OpenMarkedCurrent.entry
          (polygonSignArray (fun i => if i=0 then W 0 else W (k+i))) 0 (N-k) := by
  have hsize := hQ.size_ge_three
  have hk : 0<k := by omega
  obtain ⟨ρ,hρ,hjump⟩ := exists_openMarkedCurrent_adjacent_negative_event_limit
    W v N k hk (by omega) τ hcol htrans hisolated hτ
  refine ⟨ρ,hρ,?_⟩
  intro ε he her
  obtain ⟨hp,hm,hvalue⟩ := hjump ε he her
  refine ⟨hp,hm,?_⟩
  have hdet : planarDet (W k-W (k+1)) v = planarDet v (W (k+1)-W k) := by
    simp only [planarDet,Prod.fst_sub,Prod.snd_sub]
    ring
  rw [markedAmplitude_prefix_polygon hRI W k hQ,
    OpenMarkedCurrent.endpointFar_entry_reindexed W k N hKN,hdet] at hvalue
  exact hvalue



end DirectGLSSW
