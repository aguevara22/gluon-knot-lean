import DirectGLSSW.EndpointGeometricMatrix
import DirectGLSSW.OpenMarkedCurrent
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CursorWallTransport
open EndpointEventGeometry EndpointCurrent

private theorem endpointCurrent_zero_eq (d : ℕ → ℚ) (H : TripleArray)
    (b : ℕ) (hb : 0 < b) :
    endpointCurrent d H 0 (b-1) = ordinaryCurrent (fun _ k _ => d k) H 0 b := by
  rw [endpointCurrent,if_pos (Nat.zero_le _),Nat.sub_add_cancel (by omega)]
  have hfar : endpointFar 0 H = H := by
    funext x y z
    by_cases hx : x = 0 <;> simp [endpointFar,hx]
  rw [hfar]

/-- A transverse isolated secant wall away from every actual later side has
zero open-current jump. First-side parallelism eliminates the other sources. -/
theorem isolated_virtual_wall_openCurrent_eq
    (W : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (N k j : ℕ)
    (hk : 0<k) (hkj : k<j) (hjn : j≤N)
    (hfirst : planarDet (W 1-W 0) v=0) (hfirstne : W 1≠W 0)
    (hno : ∀ r, 0<r → r<N → ∀ u : ℝ, 0<u → u<1 →
      W 0≠affinePoint (W r) (W (r+1)) u)
    (τ : ℝ) (hcol : W k=W 0+τ • (W j-W 0))
    (htrans : planarDet (W k-W j) v≠0)
    (hisolated : ∀ a b d, a<b → b<d → d≤N →
      (a≠0 ∨ b≠k ∨ d≠j) → polygonHDet W a b d≠0) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ ε : ℝ, 0<ε → ε<ρ →
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v ε) N ∧
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v (-ε)) N ∧
      OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v ε)) 0 N =
        OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v (-ε))) 0 N := by
  have hN : 0<N := by omega
  have ht0 : τ≠0 := by
    intro ht
    have heq : W k=W 0 := by simpa only [ht,zero_smul,add_zero] using hcol
    by_cases hk1 : k=1
    · exact hfirstne (hk1 ▸ heq)
    · have hh := hisolated 0 1 k (by omega) (by omega) (by omega) (Or.inr (Or.inl (Ne.symm hk1)))
      apply hh
      simp only [polygonHDet,heq,sub_self,planarDet,Prod.fst_zero,Prod.snd_zero,mul_zero,zero_mul,sub_zero]
  have hk1 : k≠1 := by
    intro he
    subst k
    have hrel : planarDet (W 1-W 0) v=τ*planarDet (W j-W 0) v := by
      rw [hcol]
      dsimp [planarDet]
      ring
    have hzj : planarDet (W j-W 0) v=0 := (mul_eq_zero.mp (hrel.symm.trans hfirst)).resolve_left ht0
    apply htrans
    calc
      _ = planarDet (W 1-W 0) v-planarDet (W j-W 0) v := by
        simp only [planarDet,Prod.fst_sub,Prod.snd_sub]
        ring
      _ = 0 := by rw [hfirst,hzj,sub_self]
  have ht1 : τ≠1 := by
    intro ht
    have hp : W k=W j := by simpa [ht] using hcol
    apply htrans
    rw [hp,sub_self]
    simp [planarDet]
  have hgap (ht : τ<0) : j≠k+1 := by
    intro hadj
    subst j
    have hd : 0<1-τ := by linarith
    have hu0 : 0 < -τ/(1-τ) := div_pos (neg_pos.mpr ht) hd
    have hu1 : -τ/(1-τ)<1 := (div_lt_one hd).mpr (by linarith)
    apply hno k hk (by omega) (-τ/(1-τ)) hu0 hu1
    have hx := congrArg Prod.fst hcol
    have hy := congrArg Prod.snd hcol
    change (W k).1=(W 0).1+τ*((W (k+1)).1-(W 0).1) at hx
    change (W k).2=(W 0).2+τ*((W (k+1)).2-(W 0).2) at hy
    apply Prod.ext
    · simp only [affinePoint]
      field_simp
      nlinarith [hx]
    · simp only [affinePoint]
      field_simp
      nlinarith [hy]
  have hs0 : source 0 k=0 := by simp [source,hk1]
  have hrow : ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v ε) N ∧
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v (-ε)) N ∧
      ∀ i : Fin N,
        endpointCurrent (fun _ => -1) (polygonSignArray (moveEndpoint W v ε)) 0 i.val -
        endpointCurrent (fun _ => -1) (polygonSignArray (moveEndpoint W v (-ε))) 0 i.val = 0 := by
    rcases lt_or_gt_of_ne ht0 with ht | ht
    · have hgap := hgap ht
      have hs : source k j = 0 := by simp [source,hgap]
      obtain ⟨ρ,hρ,hdata⟩ := exists_endpoint_current_matrix_event_negative_positive
        W v (fun _ => -1) N hk hkj hjn τ hcol htrans hisolated ht
      refine ⟨ρ,hρ,?_⟩
      intro ε hε hερ
      obtain ⟨hg1,hg0,hmat⟩ := hdata ε hε hερ
      refine ⟨hg1,hg0,?_⟩
      intro i
      simpa [hs] using hmat ⟨0,hN⟩ i
    · rcases lt_or_gt_of_ne ht1 with hlt | hgt
      · obtain ⟨ρ,hρ,hdata⟩ := exists_endpoint_current_matrix_event_positive_positive
          W v (fun _ => -1) N hk hkj hjn τ hcol htrans hisolated ht (by linarith)
        refine ⟨ρ,hρ,?_⟩
        intro ε hε hερ
        obtain ⟨hg1,hg0,hmat⟩ := hdata ε hε hερ
        refine ⟨hg1,hg0,?_⟩
        intro i
        simpa [hs0] using hmat ⟨0,hN⟩ i
      · obtain ⟨ρ,hρ,hdata⟩ := exists_endpoint_current_matrix_event_positive_negative
          W v (fun _ => -1) N hk hkj hjn τ hcol htrans hisolated hgt
        refine ⟨ρ,hρ,?_⟩
        intro ε hε hερ
        obtain ⟨hg1,hg0,hmat⟩ := hdata ε hε hερ
        refine ⟨hg1,hg0,?_⟩
        intro i
        simpa [hs0] using hmat ⟨0,hN⟩ i
  obtain ⟨ρ,hρ,hdata⟩ := hrow
  refine ⟨ρ,hρ,?_⟩
  intro ε hε hερ
  obtain ⟨hg1,hg0,hrow⟩ := hdata ε hε hερ
  refine ⟨hg1,hg0,?_⟩
  change OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v ε)) 0 N =
    OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v (-ε))) 0 N
  unfold OpenMarkedCurrent.entry
  apply weightedCutSum_congr_of_branch_eq _ hN
  intro a b ha hab hbN
  by_cases ha0 : a = 0
  · subst a
    have he := hrow ⟨b-1,by omega⟩
    change endpointCurrent (fun _ => -1) (polygonSignArray (moveEndpoint W v ε)) 0 (b-1) -
      endpointCurrent (fun _ => -1) (polygonSignArray (moveEndpoint W v (-ε))) 0 (b-1) = 0 at he
    rw [endpointCurrent_zero_eq _ _ b hab,endpointCurrent_zero_eq _ _ b hab] at he
    exact sub_eq_zero.mp he
  · apply ordinaryCurrent_congr_interval_fixed_near _ _ _ hab
    intro x y z hax hxy hyz hzb
    have hx : x ≠ 0 := by omega
    have hy : y ≠ 0 := by omega
    have hz : z ≠ 0 := by omega
    simp only [polygonSignArray,polygonHDet,moveEndpoint,if_neg hx,if_neg hy,if_neg hz]

end DirectGLSSW.CursorWallTransport
