import IsolatedCursorInterval
import TailSecantSeparation
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CursorWallTransport
open EndpointEventGeometry

/-- The first retained vertex cannot participate in a transverse cursor event
while the cursor remains outside the actual closed later sides. -/
theorem transverse_secant_not_first (W : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ)
    (t : ℝ) (j : ℕ) (hj : 1<j)
    (hfirst : planarDet (W 1-W 0) v=0)
    (hne1 : W 1≠W 0+t • v) (hnej : W j≠W 0+t • v)
    (htrans : planarDet (W 1-W j) v≠0) :
    polygonHDet (moveEndpoint W v t) 0 1 j≠0 := by
  intro hz
  obtain ⟨τ,hcol⟩ := collinear_parameter (W 0+t • v) (W 1) (W j) hnej (by
    simpa only [polygonHDet,moveEndpoint,if_pos rfl,if_neg (by omega : (1:ℕ)≠0),if_neg (by omega : j≠0)] using hz)
  have hf : planarDet (W 1-(W 0+t • v)) v=0 := by
    have he : planarDet (W 1-(W 0+t • v)) v=planarDet (W 1-W 0) v := by dsimp [planarDet];ring
    exact he.trans hfirst
  have ht : planarDet (W j-(W 0+t • v)) v≠0 := by
    intro hh
    apply htrans
    have he : planarDet (W 1-W j) v=planarDet (W 1-(W 0+t • v)) v-planarDet (W j-(W 0+t • v)) v := by
      dsimp [planarDet]
      ring
    rw [he,hf,hh,sub_self]
  have hm : τ*planarDet (W j-(W 0+t • v)) v=0 := by
    rw [hcol] at hf
    have he : planarDet (W 0+t • v+τ • (W j-(W 0+t • v))-(W 0+t • v)) v =
        τ*planarDet (W j-(W 0+t • v)) v := by dsimp [planarDet];ring
    exact he.symm.trans hf
  have hτ : τ=0 := (mul_eq_zero.mp hm).resolve_right ht
  apply hne1
  simpa only [hτ,zero_smul,add_zero] using hcol

/-- The finite fixed-tail collision exclusions imply the full isolated event
condition. First-vertex pairs are ruled out geometrically, not postulated. -/
theorem shifted_secants_isolated (W : ℕ → PlanarPoint ℝ) (v w : PlanarPoint ℝ)
    (η : ℝ) (N : ℕ) (a b : ℝ)
    (ha : ShortEdgeSignStability.CoreHGeneric (moveEndpoint (shiftFirstPair W w η) v a) N)
    (hfirst : planarDet (W 1-W 0) v=0)
    (hno : ∀ t : ℝ, a≤t → t≤b → ∀ r : ℕ, 0<r → r<N →
      ∀ u : ℝ, 0≤u → u≤1 →
      shiftFirstPair W w η 0+t • v≠affinePoint (shiftFirstPair W w η r) (shiftFirstPair W w η (r+1)) u)
    (hsep : ∀ s t : TailSecant N, s≠t → tailSlope W v s≠0 → tailSlope W v t≠0 →
      tailIntercept W (W 0+η • w) s*tailSlope W v t-
        tailIntercept W (W 0+η • w) t*tailSlope W v s≠0) :
    ∀ t : ℝ, a<t → t<b → ∀ k j : ℕ, 0<k → k<j → j≤N →
      polygonHDet (moveEndpoint (shiftFirstPair W w η) v t) 0 k j=0 →
      ∀ l m : ℕ, 0<l → l<m → m≤N → (l≠k ∨ m≠j) →
        polygonHDet (moveEndpoint (shiftFirstPair W w η) v t) 0 l m≠0 := by
  let Q := shiftFirstPair W w η
  have hfirstQ : planarDet (Q 1-Q 0) v=0 := by
    have he : planarDet (Q 1-Q 0) v=planarDet (W 1-W 0) v := by
      dsimp [Q,shiftFirstPair,planarDet]
      ring
    exact he.trans hfirst
  intro t hat htb k j hk hkj hjN hz l m hl hlm hmN hother hz'
  have bound (i j : ℕ) (hi : 0 < i) (hij : i<j) (hj : j≤N)
      (hzero : polygonHDet (moveEndpoint Q v t) 0 i j=0) :
      1 < i ∧ planarDet (Q i-Q j) v≠0 := by
    have hs : planarDet (Q i-Q j) v≠0 := by
      intro hh
      have haa := ha 0 i j hi hij hj
      rw [moveEndpoint_farDet Q v hi hij,hh,mul_zero,add_zero] at haa hzero
      exact haa hzero
    refine ⟨?_,hs⟩
    by_contra hnot
    have hi1 : i=1 := by omega
    subst i
    have hneq1 : Q 1≠Q 0+t • v := by
      intro hp
      have hh := hno t (le_of_lt hat) (le_of_lt htb) 1 (by omega) (by omega) 0 le_rfl zero_le_one
      rw [affinePoint_zero] at hh
      exact hh hp.symm
    have hneqj : Q j≠Q 0+t • v := by
      intro hp
      have hh := hno t (le_of_lt hat) (le_of_lt htb) (j-1) (by omega) (by omega) 1 zero_le_one le_rfl
      rw [Nat.sub_add_cancel (by omega),affinePoint_one] at hh
      exact hh hp.symm
    exact transverse_secant_not_first Q v t j hij hfirstQ hneq1 hneqj hs hzero
  obtain ⟨hk1,hsk⟩ := bound k j hk hkj hjN hz
  obtain ⟨hl1,hsl⟩ := bound l m hl hlm hmN hz'
  let s : TailSecant N := ⟨(⟨k,by omega⟩,⟨j,by omega⟩),hk1,hkj⟩
  let z : TailSecant N := ⟨(⟨l,by omega⟩,⟨m,by omega⟩),hl1,hlm⟩
  have hsz : s≠z := by
    intro he
    have h0 := congrArg (fun z : TailSecant N => z.val.1.val) he
    have h1 := congrArg (fun z : TailSecant N => z.val.2.val) he
    rcases hother with hh|hh
    · exact hh h0.symm
    · exact hh h1.symm
  have hs : tailSlope W v s≠0 := by
    simpa only [Q,shiftFirstPair,if_neg (by omega : ¬(k=0 ∨ k=1)),if_neg (by omega : ¬(j=0 ∨ j=1))] using hsk
  have hzv : tailSlope W v z≠0 := by
    simpa only [Q,shiftFirstPair,if_neg (by omega : ¬(l=0 ∨ l=1)),if_neg (by omega : ¬(m=0 ∨ m=1))] using hsl
  have Hs : tailIntercept W (W 0+η • w) s+t*tailSlope W v s=0 := by
    rw [moveEndpoint_farDet Q v hk hkj] at hz
    simpa only [polygonHDet,Q,shiftFirstPair,if_pos (Or.inl rfl),
      if_neg (by omega : ¬(k=0 ∨ k=1)),if_neg (by omega : ¬(j=0 ∨ j=1))] using hz
  have Hz : tailIntercept W (W 0+η • w) z+t*tailSlope W v z=0 := by
    rw [moveEndpoint_farDet Q v hl hlm] at hz'
    simpa only [polygonHDet,Q,shiftFirstPair,if_pos (Or.inl rfl),
      if_neg (by omega : ¬(l=0 ∨ l=1)),if_neg (by omega : ¬(m=0 ∨ m=1))] using hz'
  apply hsep s z hsz hs hzv
  have Hs' : tailIntercept W (W 0+η • w) s= -t*tailSlope W v s := by linarith
  have Hz' : tailIntercept W (W 0+η • w) z= -t*tailSlope W v z := by linarith
  rw [Hs',Hz']
  ring

end DirectGLSSW.CursorWallTransport
