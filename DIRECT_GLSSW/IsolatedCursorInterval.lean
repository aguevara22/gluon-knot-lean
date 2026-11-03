import EndpointAffineWalls
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CursorWallTransport
open EndpointEventGeometry

theorem collinear_parameter (P A B : PlanarPoint ℝ)
    (hB : B≠P) (hd : planarDet (A-B) (P-B)=0) :
    ∃ τ : ℝ, A=P+τ • (B-P) := by
  have hh : (A.1-P.1)*(B.2-P.2)-(A.2-P.2)*(B.1-P.1)=0 := by
    simp only [planarDet,Prod.fst_sub,Prod.snd_sub] at hd
    nlinarith
  by_cases hx : B.1-P.1=0
  · have hy : B.2-P.2≠0 := by
      intro hy
      apply hB
      apply Prod.ext <;> linarith
    refine ⟨(A.2-P.2)/(B.2-P.2),?_⟩
    apply Prod.ext
    · change A.1=P.1+(A.2-P.2)/(B.2-P.2)*(B.1-P.1)
      rw [hx,mul_zero,add_zero]
      have ha : (A.1-P.1)*(B.2-P.2)=0 := by simpa only [hx,mul_zero,sub_zero] using hh
      have he := (mul_eq_zero.mp ha).resolve_right hy
      linarith
    · change A.2=P.2+(A.2-P.2)/(B.2-P.2)*(B.2-P.2)
      rw [div_mul_cancel₀ _ hy]
      ring
  · refine ⟨(A.1-P.1)/(B.1-P.1),?_⟩
    apply Prod.ext
    · change A.1=P.1+(A.1-P.1)/(B.1-P.1)*(B.1-P.1)
      rw [div_mul_cancel₀ _ hx]
      ring
    · change A.2=P.2+(A.1-P.1)/(B.1-P.1)*(B.2-P.2)
      field_simp
      nlinarith [hh]

theorem moveEndpoint_add (W : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (s t : ℝ) :
    moveEndpoint (moveEndpoint W v s) v t=moveEndpoint W v (s+t) := by
  funext i
  by_cases hi : i=0
  · subst i
    simp only [moveEndpoint,if_pos rfl,add_smul]
    exact add_assoc _ _ _
  · simp only [moveEndpoint,if_neg hi]

/-- Finite isolated-wall transport for the literal open current.  All auxiliary
conditions are geometric determinant statements; no current equality is input.
The secant-separation condition will be removed by parallel-line perturbation. -/
theorem isolated_interval_openCurrent_eq
    (W : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (N : ℕ) (hN : 0<N)
    (a b : ℝ) (hab : a≤b)
    (ha : ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v a) N)
    (hb : ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v b) N)
    (hfirst : planarDet (W 1-W 0) v=0)
    (hno : ∀ t : ℝ, a≤t → t≤b → ∀ r : ℕ, 0<r → r<N →
      ∀ u : ℝ, 0≤u → u≤1 → W 0+t • v≠affinePoint (W r) (W (r+1)) u)
    (hsep : ∀ t : ℝ, a<t → t<b → ∀ k j : ℕ, 0<k → k<j → j≤N →
      polygonHDet (moveEndpoint W v t) 0 k j=0 →
      ∀ l m : ℕ, 0<l → l<m → m≤N → (l≠k ∨ m≠j) →
        polygonHDet (moveEndpoint W v t) 0 l m≠0) :
    OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v a)) 0 N =
      OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v b)) 0 N := by
  apply finite_wall_gluing (endpointWallSet W v N)
    (fun t => OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v t)) 0 N) a b hab
    ((core_iff_not_endpointWallSet W v N a ha a).mp ha)
    ((core_iff_not_endpointWallSet W v N a ha b).mp hb)
  · intro x y hax hxy hyb hx hy hn
    exact endpoint_chamber_openCurrent_eq W v N hN a ha x y hxy hx hy hn
  · intro t ht hat htb
    obtain ⟨k,j,hk,hkj,hjN,htrans,hzero⟩ := (mem_endpointWallSet W v N t).mp ht
    have hj0 : j≠0 := by omega
    have hk0 : k≠0 := by omega
    have h1 : 1<N := by omega
    have hBp : W j≠W 0+t • v := by
      intro hp
      have hh := hno t (le_of_lt hat) (le_of_lt htb) (j-1) (by omega) (by omega) 1 (by norm_num) (by norm_num)
      rw [Nat.sub_add_cancel (by omega),affinePoint_one] at hh
      exact hh hp.symm
    have hfirst' : planarDet (moveEndpoint W v t 1-moveEndpoint W v t 0) v=0 := by
      simp only [moveEndpoint,if_pos rfl,if_neg (by omega : (1 : ℕ)≠0)]
      have hid : planarDet (W 1-(W 0+t • v)) v=planarDet (W 1-W 0) v := by
        dsimp [planarDet]
        ring
      exact hid.trans hfirst
    have hfirstne : moveEndpoint W v t 1≠moveEndpoint W v t 0 := by
      intro hp
      have hh := hno t (le_of_lt hat) (le_of_lt htb) 1 (by omega) h1 0 le_rfl zero_le_one
      rw [affinePoint_zero] at hh
      apply hh
      simpa only [moveEndpoint,if_pos rfl,if_neg (by omega : (1 : ℕ)≠0)] using hp.symm
    obtain ⟨τ,hcol⟩ := collinear_parameter (W 0+t • v) (W k) (W j) hBp (by
      simpa only [polygonHDet,moveEndpoint,if_pos rfl,if_neg hk0,if_neg hj0] using hzero)
    have hiso : ∀ i l m, i<l → l<m → m≤N → (i≠0 ∨ l≠k ∨ m≠j) →
        polygonHDet (moveEndpoint W v t) i l m≠0 := by
      intro i l m hil hlm hm hother
      by_cases hi : i=0
      · subst i
        exact hsep t hat htb k j hk hkj hjN hzero l m hil hlm hm (hother.resolve_left (not_ne_iff.mpr rfl))
      · have hl0 : l≠0 := by omega
        have hm0 : m≠0 := by omega
        simpa only [polygonHDet,moveEndpoint,if_neg hi,if_neg hl0,if_neg hm0] using ha i l m hil hlm hm
    obtain ⟨ρ,hρ,hjump⟩ := isolated_virtual_wall_openCurrent_eq (moveEndpoint W v t) v N k j hk hkj hjN
      hfirst' hfirstne (by
        intro r hr hrN u hu0 hu1
        simpa only [moveEndpoint,if_pos rfl,if_neg (by omega : r≠0),if_neg (by omega : r+1≠0)] using
          hno t (le_of_lt hat) (le_of_lt htb) r hr hrN u (le_of_lt hu0) (le_of_lt hu1))
      τ (by simpa only [moveEndpoint,if_pos rfl,if_neg hk0,if_neg hj0] using hcol)
      (by simpa only [moveEndpoint,if_neg hk0,if_neg hj0] using htrans) hiso
    refine ⟨ρ,hρ,?_⟩
    intro ε hε hερ
    have hh := (hjump ε hε hερ).2.2
    rw [moveEndpoint_add,moveEndpoint_add] at hh
    simpa only [sub_eq_add_neg] using hh.symm

end DirectGLSSW.CursorWallTransport
