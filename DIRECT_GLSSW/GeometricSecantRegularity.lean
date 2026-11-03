import ExtendedArcCriticalData

set_option autoImplicit false
namespace DirectGLSSW.GeometricSecantRegularity
open ExtendedReturnArcGeometry FiniteCriticalRootAvoidance ExtendedArcCriticalData
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- The two secants use four disjoint strict-interior vertex labels. -/
def InteriorSecantsSeparated (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) : Prop :=
  ∀ a b c d : Fin n,
    0 < a.val → a.val+1 < n → 0 < b.val → b.val+1 < n →
    0 < c.val → c.val+1 < n → 0 < d.val → d.val+1 < n →
    a.val < b.val → c.val < d.val →
    a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    planarDet (P a-P b) (1,0) ≠ 0 → planarDet (P c-P d) (1,0) ≠ 0 →
    -planarDet (P a-P b) (P (zeroIndex hn)-P b) / planarDet (P a-P b) (1,0) ≠
    -planarDet (P c-P d) (P (zeroIndex hn)-P d) / planarDet (P c-P d) (1,0)

/-- Equal neighbor heights make the outer secant permanently horizontal;
otherwise nonparallel endpoint return edges prevent its persistent coincidences. -/
def OuterSecantRegular (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) : Prop :=
  (P (firstIndex hn)).2 = (P (penultimateIndex hn)).2 ∨
    planarDet (P (firstIndex hn)-P (zeroIndex hn))
      (P (penultimateIndex hn)-P (lastIndex hn)) ≠ 0

def secantCross (u A B C D : PlanarPoint ℝ) : ℝ :=
  planarDet (A-B) (u-B) * planarDet (C-D) (1,0) -
    planarDet (C-D) (u-D) * planarDet (A-B) (1,0)

def leftIndex (p : SecantLabel n) : Fin n := ⟨p.val.1.val-1,by
  have := p.property.1; have := p.val.1.isLt; omega⟩
def rightIndex (p : SecantLabel n) : Fin n := ⟨p.val.2.val-1,by
  have := p.property.1; have := p.property.2; have := p.val.2.isLt; omega⟩

private theorem indices_lt (p : SecantLabel n) : (leftIndex p).val < (rightIndex p).val := by
  have := p.property.1; have := p.property.2
  dsimp [leftIndex,rightIndex]
  omega

private theorem indices_injective (p r : SecantLabel n)
    (h1 : leftIndex p = leftIndex r) (h2 : rightIndex p = rightIndex r) : p = r := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · have h := congrArg Fin.val h1
    have := p.property.1; have := r.property.1
    dsimp [leftIndex] at h
    omega
  · have h := congrArg Fin.val h2
    have := p.property.1; have := p.property.2
    have := r.property.1; have := r.property.2
    dsimp [rightIndex] at h
    omega

private theorem pair_points (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ)
    (p : SecantLabel n) (ε : ℝ) :
    extendedArc hn P ε (labelNat p).1 = extendedWord hn P ε (leftIndex p) ∧
    extendedArc hn P ε (labelNat p).2 = extendedWord hn P ε (rightIndex p) := by
  have hk := p.property.1
  have hj : 0 < p.val.2.val := lt_trans hk p.property.2
  have hkn : p.val.1.val ≤ n := by have := p.val.1.isLt; omega
  have hjn : p.val.2.val ≤ n := by have := p.val.2.isLt; omega
  simp [extendedArc,arcFromWord,labelNat,hk,hj,hkn,hjn,leftIndex,rightIndex]

private theorem collision_value (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ)
    (p r : SecantLabel n) (ε : ℝ) :
    cubicValue (collisionData (baseData hn P p) (baseData hn P r)
      (slopeData hn P p) (slopeData hn P r)) ε =
    secantCross (P (zeroIndex hn)) (extendedWord hn P ε (leftIndex p))
      (extendedWord hn P ε (rightIndex p)) (extendedWord hn P ε (leftIndex r))
      (extendedWord hn P ε (rightIndex r)) := by
  rw [collisionData_value,baseData_eval,baseData_eval,slopeData_eval,slopeData_eval]
  simp only [polygonHDet,extendedArc_zero,(pair_points hn P p ε).1,(pair_points hn P p ε).2,
    (pair_points hn P r ε).1,(pair_points hn P r ε).2,secantCross]

private theorem coefficients_of_value_ne_zero (C : CubicData) (ε : ℝ)
    (h : cubicValue C ε ≠ 0) : NonzeroCoefficients C := by
  by_contra hc
  simp only [NonzeroCoefficients,not_or,not_not] at hc
  apply h
  simp [cubicValue,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

private theorem collision_zero_value (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ)
    (p r : SecantLabel n) :
    cubicValue (collisionData (baseData hn P p) (baseData hn P r)
      (slopeData hn P p) (slopeData hn P r)) 0 =
    secantCross (P (zeroIndex hn)) (P (leftIndex p)) (P (rightIndex p))
      (P (leftIndex r)) (P (rightIndex r)) := by
  rw [collision_value]
  simp [extendedWord,affineWord]

private theorem pair_data (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (p : SecantLabel n) :
    let A := P (leftIndex p)
    let B := P (rightIndex p)
    let U := P (zeroIndex hn)
    let V := endpointVelocity hn P (leftIndex p)
    let W := endpointVelocity hn P (rightIndex p)
    baseData hn P p = (planarDet (A-B) (U-B),
      planarDet (V-W) (U-B)+planarDet (A-B) (-W),planarDet (V-W) (-W)) ∧
    slopeData hn P p = (planarDet (A-B) (1,0),planarDet (V-W) (1,0)) := by
  have hk := p.property.1
  have hj : 0 < p.val.2.val := lt_trans hk p.property.2
  have hkn : p.val.1.val ≤ n := by have := p.val.1.isLt; omega
  have hjn : p.val.2.val ≤ n := by have := p.val.2.isLt; omega
  simp [baseData,slopeData,arcBase,arcVelocity,labelNat,hk,hj,hkn,hjn,leftIndex,rightIndex]

private theorem interior_data (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (p : SecantLabel n)
    (ha0 : 0 < (leftIndex p).val) (haL : (leftIndex p).val+1 < n)
    (hb0 : 0 < (rightIndex p).val) (hbL : (rightIndex p).val+1 < n) :
    baseData hn P p = (planarDet (P (leftIndex p)-P (rightIndex p))
      (P (zeroIndex hn)-P (rightIndex p)),0,0) ∧
    slopeData hn P p = (planarDet (P (leftIndex p)-P (rightIndex p)) (1,0),0) := by
  obtain ⟨hB,hD⟩ := pair_data hn P p
  simp only [endpointVelocity,ne_of_gt ha0,ne_of_lt haL,ne_of_gt hb0,ne_of_lt hbL,if_false] at hB hD
  simpa [planarDet] using And.intro hB hD

private theorem cross_swap_first (u A B C D : PlanarPoint ℝ) :
    secantCross u B A C D = -secantCross u A B C D := by
  dsimp [secantCross,planarDet]; ring
private theorem cross_swap_second (u A B C D : PlanarPoint ℝ) :
    secantCross u A B D C = -secantCross u A B C D := by
  dsimp [secantCross,planarDet]; ring
private theorem cross_swap_pairs (u A B C D : PlanarPoint ℝ) :
    secantCross u C D A B = -secantCross u A B C D := by
  dsimp [secantCross]; ring

private theorem shared_first_ne_zero (E : Fin n → PlanarPoint ℝ)
    (hE : cyclicNoncollinear E) (hoff : ∀ i, (E i).2 ≠ 0)
    (u : PlanarPoint ℝ) (hu : u.2 = 0) (a b d : Fin n)
    (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) :
    secantCross u (E a) (E b) (E a) (E d) ≠ 0 := by
  have hid : secantCross u (E a) (E b) (E a) (E d) =
      -(E a).2 * planarDet (E b-E d) (E a-E d) := by
    dsimp [secantCross,planarDet]; rw [hu]; ring
  rw [hid]
  exact mul_ne_zero (neg_ne_zero.mpr (hoff a)) (hE a b d hab hbd had)

private theorem shared_cross_ne_zero (E : Fin n → PlanarPoint ℝ)
    (hE : cyclicNoncollinear E) (hoff : ∀ i, (E i).2 ≠ 0)
    (u : PlanarPoint ℝ) (hu : u.2 = 0) (a b c d : Fin n)
    (hab : a.val < b.val) (hcd : c.val < d.val)
    (hne : (a,b) ≠ (c,d)) (hshare : a = c ∨ a = d ∨ b = c ∨ b = d) :
    secantCross u (E a) (E b) (E c) (E d) ≠ 0 := by
  rcases hshare with h | h | h | h
  · subst c
    apply shared_first_ne_zero E hE hoff u hu a b d
    · exact ne_of_lt hab
    · intro h; exact hne (by rw [h])
    · exact ne_of_lt hcd
  · subst d
    rw [cross_swap_second u (E a) (E b) (E a) (E c)]
    apply neg_ne_zero.mpr
    apply shared_first_ne_zero E hE hoff u hu a b c
    · exact ne_of_lt hab
    · exact ne_of_gt (lt_trans hcd hab)
    · exact ne_of_gt hcd
  · subst c
    rw [cross_swap_first u (E b) (E a) (E b) (E d)]
    apply neg_ne_zero.mpr
    apply shared_first_ne_zero E hE hoff u hu b a d
    · exact ne_of_gt hab
    · exact ne_of_lt (lt_trans hab hcd)
    · exact ne_of_lt hcd
  · subst d
    rw [cross_swap_first u (E b) (E a) (E c) (E b),
      cross_swap_second u (E b) (E a) (E b) (E c),neg_neg]
    apply shared_first_ne_zero E hE hoff u hu b a c
    · exact ne_of_gt hab
    · intro h; exact hne (by rw [h])
    · exact ne_of_gt hcd

private theorem shared_coefficients (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ)
    (hP : cyclicNoncollinear P) (hU : (P (zeroIndex hn)).2 = 0)
    (hV : (P (lastIndex hn)).2 = 0) (p r : SecantLabel n) (hpr : p ≠ r)
    (hshare : leftIndex p = leftIndex r ∨ leftIndex p = rightIndex r ∨
      rightIndex p = leftIndex r ∨ rightIndex p = rightIndex r) :
    NonzeroCoefficients (collisionData (baseData hn P p) (baseData hn P r)
      (slopeData hn P p) (slopeData hn P r)) := by
  let ε := geometricRadius hn P/2
  have hrad := geometricRadius_pos hn P hP
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hbound : ε < geometricRadius hn P := by dsimp [ε]; linarith
  have hE : cyclicNoncollinear (extendedWord hn P ε) :=
    affineWord_G1 P _ hP ε hε.le (lt_of_lt_of_le hbound (min_le_left _ _))
  apply coefficients_of_value_ne_zero _ ε
  rw [collision_value]
  apply shared_cross_ne_zero _ hE (extendedWord_off_line hn P hP hU hV ε hε)
    (P (zeroIndex hn)) hU _ _ _ _ (indices_lt p) (indices_lt r) _ hshare
  intro h
  exact hpr (indices_injective p r (congrArg Prod.fst h) (congrArg Prod.snd h))

private theorem collision_nonzero_symm (B B' : QuadraticData) (D D' : LinearData)
    (h : NonzeroCoefficients (collisionData B' B D' D)) :
    NonzeroCoefficients (collisionData B B' D D') := by
  have hid : collisionData B B' D D' =
      (-(collisionData B' B D' D).1,-(collisionData B' B D' D).2.1,
       -(collisionData B' B D' D).2.2.1,-(collisionData B' B D' D).2.2.2) := by
    ext <;> dsimp [collisionData] <;> ring
  simpa [hid,NonzeroCoefficients] using h


private theorem velocity_zero (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) :
    endpointVelocity hn P (zeroIndex hn) = P (zeroIndex hn)-P (firstIndex hn) := by
  simp [endpointVelocity,zeroIndex]
private theorem velocity_last (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) :
    endpointVelocity hn P (lastIndex hn) = P (lastIndex hn)-P (penultimateIndex hn) := by
  have h0 : n-1 ≠ 0 := by omega
  have hL : n-1+1=n := by omega
  simp [endpointVelocity,lastIndex,h0,hL]

private theorem outer_data (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ)
    (hU : (P (zeroIndex hn)).2 = 0) (hV : (P (lastIndex hn)).2 = 0)
    (p : SecantLabel n) (ha : leftIndex p = zeroIndex hn) (hb : rightIndex p = lastIndex hn) :
    slopeData hn P p = (0,(P (firstIndex hn)).2-(P (penultimateIndex hn)).2) ∧
    (baseData hn P p).2.2 = -planarDet (P (firstIndex hn)-P (zeroIndex hn))
      (P (penultimateIndex hn)-P (lastIndex hn)) := by
  obtain ⟨hB,hD⟩ := pair_data hn P p
  rw [ha,hb,velocity_zero,velocity_last] at hB hD
  constructor
  · rw [hD]
    ext <;> dsimp [planarDet] <;> rw [hU,hV] <;> ring
  · rw [hB]
    dsimp [planarDet]
    ring

private theorem outer_case (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ)
    (hU : (P (zeroIndex hn)).2 = 0) (hV : (P (lastIndex hn)).2 = 0)
    (hOuter : OuterSecantRegular hn P) (p r : SecantLabel n)
    (ha : leftIndex p = zeroIndex hn) (hb : rightIndex p = lastIndex hn)
    (hc0 : 0 < (leftIndex r).val) (hcL : (leftIndex r).val+1 < n)
    (hd0 : 0 < (rightIndex r).val) (hdL : (rightIndex r).val+1 < n) :
    ZeroSlope (slopeData hn P p) ∨ ZeroSlope (slopeData hn P r) ∨
    NonzeroCoefficients (collisionData (baseData hn P p) (baseData hn P r)
      (slopeData hn P p) (slopeData hn P r)) := by
  obtain ⟨hD,hB2⟩ := outer_data hn P hU hV p ha hb
  rcases hOuter with heq | hnon
  · left
    simp [ZeroSlope,hD,heq]
  · by_cases hr : ZeroSlope (slopeData hn P r)
    · exact Or.inr (Or.inl hr)
    · obtain ⟨hBr,hDr⟩ := interior_data hn P r hc0 hcL hd0 hdL
      have hDr0 : planarDet (P (leftIndex r)-P (rightIndex r)) (1,0) ≠ 0 := by
        intro h
        apply hr
        simp [ZeroSlope,hDr,h]
      right; right; right; right; left
      have hid : (collisionData (baseData hn P p) (baseData hn P r)
          (slopeData hn P p) (slopeData hn P r)).2.2.1 =
          -planarDet (P (firstIndex hn)-P (zeroIndex hn))
            (P (penultimateIndex hn)-P (lastIndex hn)) *
              planarDet (P (leftIndex r)-P (rightIndex r)) (1,0) := by
        simp only [collisionData,hBr,hDr,mul_zero,zero_mul,zero_add,sub_zero]
        rw [hB2]
      rw [hid]
      exact mul_ne_zero (neg_ne_zero.mpr hnon) hDr0

private theorem interior_case (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ)
    (hInterior : InteriorSecantsSeparated hn P) (p r : SecantLabel n)
    (ha0 : 0 < (leftIndex p).val) (haL : (leftIndex p).val+1 < n)
    (hb0 : 0 < (rightIndex p).val) (hbL : (rightIndex p).val+1 < n)
    (hc0 : 0 < (leftIndex r).val) (hcL : (leftIndex r).val+1 < n)
    (hd0 : 0 < (rightIndex r).val) (hdL : (rightIndex r).val+1 < n)
    (hac : leftIndex p ≠ leftIndex r) (had : leftIndex p ≠ rightIndex r)
    (hbc : rightIndex p ≠ leftIndex r) (hbd : rightIndex p ≠ rightIndex r) :
    ZeroSlope (slopeData hn P p) ∨ ZeroSlope (slopeData hn P r) ∨
    NonzeroCoefficients (collisionData (baseData hn P p) (baseData hn P r)
      (slopeData hn P p) (slopeData hn P r)) := by
  by_cases hp : ZeroSlope (slopeData hn P p)
  · exact Or.inl hp
  by_cases hr : ZeroSlope (slopeData hn P r)
  · exact Or.inr (Or.inl hr)
  obtain ⟨_,hDp⟩ := interior_data hn P p ha0 haL hb0 hbL
  obtain ⟨_,hDr⟩ := interior_data hn P r hc0 hcL hd0 hdL
  have hp0 : planarDet (P (leftIndex p)-P (rightIndex p)) (1,0) ≠ 0 := by
    intro h; apply hp; simp [ZeroSlope,hDp,h]
  have hr0 : planarDet (P (leftIndex r)-P (rightIndex r)) (1,0) ≠ 0 := by
    intro h; apply hr; simp [ZeroSlope,hDr,h]
  right; right
  apply coefficients_of_value_ne_zero _ 0
  rw [collision_zero_value]
  intro hzero
  have hsep := hInterior _ _ _ _ ha0 haL hb0 hbL hc0 hcL hd0 hdL
    (indices_lt p) (indices_lt r) hac had hbc hbd hp0 hr0
  apply hsep
  apply (div_eq_div_iff hp0 hr0).mpr
  dsimp [secantCross] at hzero
  have hcross := sub_eq_zero.mp hzero
  simpa only [neg_mul,neg_inj] using hcross

private theorem first_endpoint_cross (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ)
    (hP : cyclicNoncollinear P) (hU : (P (zeroIndex hn)).2 = 0)
    (hV : (P (lastIndex hn)).2 = 0) (b c d : Fin n)
    (hb0 : 0 < b.val) (hbL : b.val+1 < n)
    (hUc : zeroIndex hn ≠ c) (hUd : zeroIndex hn ≠ d) (hcd : c ≠ d) :
    secantCross (P (zeroIndex hn)) (P (zeroIndex hn)) (P b) (P c) (P d) ≠ 0 := by
  have hid : secantCross (P (zeroIndex hn)) (P (zeroIndex hn)) (P b) (P c) (P d) =
      -planarDet (P c-P d) (P (zeroIndex hn)-P d) * (P b).2 := by
    dsimp [secantCross,planarDet]; rw [hU]; ring
  rw [hid]
  exact mul_ne_zero (neg_ne_zero.mpr (hP _ _ _ hUc hcd hUd))
    (original_interior_off_line hn P hP hU hV b hb0 hbL)

private theorem last_endpoint_cross (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ)
    (hP : cyclicNoncollinear P) (hU : (P (zeroIndex hn)).2 = 0)
    (hV : (P (lastIndex hn)).2 = 0) (a c d : Fin n)
    (ha0 : 0 < a.val) (haL : a.val+1 < n)
    (hVc : lastIndex hn ≠ c) (hVd : lastIndex hn ≠ d) (hcd : c ≠ d) :
    secantCross (P (zeroIndex hn)) (P a) (P (lastIndex hn)) (P c) (P d) ≠ 0 := by
  have hid : secantCross (P (zeroIndex hn)) (P a) (P (lastIndex hn)) (P c) (P d) =
      (P a).2 * planarDet (P c-P d) (P (lastIndex hn)-P d) := by
    dsimp [secantCross,planarDet]; rw [hU,hV]; ring
  rw [hid]
  exact mul_ne_zero (original_interior_off_line hn P hP hU hV a ha0 haL)
    (hP _ _ _ hVc hcd hVd)


private theorem index_positive (hn : 3 ≤ n) (i : Fin n) (h : i ≠ zeroIndex hn) :
    0 < i.val := by
  have h0 : i.val ≠ 0 := by intro h0; exact h (Fin.ext h0)
  omega
private theorem index_before_last (hn : 3 ≤ n) (i : Fin n) (h : i ≠ lastIndex hn) :
    i.val+1 < n := by
  have hi := i.isLt
  by_contra hn'
  apply h
  apply Fin.ext
  change i.val = n-1
  omega

/-- Concrete original-vertex geometric exclusions suffice for the full secant
coefficient criterion. Shared vertices and endpoint incidences need no exclusion.
This proves no density statement and imposes no new condition on the closing endpoints. -/
theorem extendedSecantRegular_of_geometric (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ)
    (hP : cyclicNoncollinear P) (hU : (P (zeroIndex hn)).2 = 0)
    (hV : (P (lastIndex hn)).2 = 0)
    (_hleft : (P (zeroIndex hn)).1 < (P (lastIndex hn)).1)
    (hInterior : InteriorSecantsSeparated hn P) (hOuter : OuterSecantRegular hn P) :
    ExtendedSecantRegular hn P := by
  intro p r hpr
  by_cases hshare : leftIndex p = leftIndex r ∨ leftIndex p = rightIndex r ∨
      rightIndex p = leftIndex r ∨ rightIndex p = rightIndex r
  · exact Or.inr (Or.inr (shared_coefficients hn P hP hU hV p r hpr hshare))
  push_neg at hshare
  obtain ⟨hac,had,hbc,hbd⟩ := hshare
  have hpL : (leftIndex p).val+1 < n := by
    have := indices_lt p; have := (rightIndex p).isLt; omega
  have hpR : 0 < (rightIndex p).val := by have := indices_lt p; omega
  have hrL : (leftIndex r).val+1 < n := by
    have := indices_lt r; have := (rightIndex r).isLt; omega
  have hrR : 0 < (rightIndex r).val := by have := indices_lt r; omega
  by_cases hpOuter : leftIndex p = zeroIndex hn ∧ rightIndex p = lastIndex hn
  · exact outer_case hn P hU hV hOuter p r hpOuter.1 hpOuter.2
      (index_positive hn _ (by intro h; exact hac (hpOuter.1.trans h.symm))) hrL hrR
      (index_before_last hn _ (by intro h; exact hbd (hpOuter.2.trans h.symm)))
  by_cases hrOuter : leftIndex r = zeroIndex hn ∧ rightIndex r = lastIndex hn
  · have h := outer_case hn P hU hV hOuter r p hrOuter.1 hrOuter.2
      (index_positive hn _ (by intro h; exact hac (h.trans hrOuter.1.symm))) hpL hpR
      (index_before_last hn _ (by intro h; exact hbd (h.trans hrOuter.2.symm)))
    rcases h with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (collision_nonzero_symm _ _ _ _ h))
  by_cases ha0 : leftIndex p = zeroIndex hn
  · right; right
    apply coefficients_of_value_ne_zero _ 0
    rw [collision_zero_value,ha0]
    exact first_endpoint_cross hn P hP hU hV _ _ _ hpR
      (index_before_last hn _ (fun h => hpOuter ⟨ha0,h⟩))
      (by simpa only [ha0] using hac) (by simpa only [ha0] using had) (ne_of_lt (indices_lt r))
  by_cases hbL : rightIndex p = lastIndex hn
  · right; right
    apply coefficients_of_value_ne_zero _ 0
    rw [collision_zero_value,hbL]
    exact last_endpoint_cross hn P hP hU hV _ _ _ (index_positive hn _ ha0) hpL
      (by simpa only [hbL] using hbc) (by simpa only [hbL] using hbd) (ne_of_lt (indices_lt r))
  by_cases hc0 : leftIndex r = zeroIndex hn
  · right; right
    apply coefficients_of_value_ne_zero _ 0
    rw [collision_zero_value,cross_swap_pairs _ (P (leftIndex r)) (P (rightIndex r)),hc0]
    apply neg_ne_zero.mpr
    exact first_endpoint_cross hn P hP hU hV _ _ _ hrR
      (index_before_last hn _ (fun h => hrOuter ⟨hc0,h⟩))
      (by simpa only [hc0] using hac.symm) (by simpa only [hc0] using hbc.symm)
      (ne_of_lt (indices_lt p))
  by_cases hdL : rightIndex r = lastIndex hn
  · right; right
    apply coefficients_of_value_ne_zero _ 0
    rw [collision_zero_value,cross_swap_pairs _ (P (leftIndex r)) (P (rightIndex r)),hdL]
    apply neg_ne_zero.mpr
    exact last_endpoint_cross hn P hP hU hV _ _ _ (index_positive hn _ hc0) hrL
      (by simpa only [hdL] using had.symm) (by simpa only [hdL] using hbd.symm)
      (ne_of_lt (indices_lt p))
  exact interior_case hn P hInterior p r (index_positive hn _ ha0) hpL hpR
    (index_before_last hn _ hbL) (index_positive hn _ hc0) hrL hrR
    (index_before_last hn _ hdL) hac had hbc hbd

/-- The geometric exclusions supply an actual small extension with all critical
roots distinct. The exclusions are explicit auxiliary conditions, not consequences of G1-G2. -/
theorem exists_extendedArc_injective_of_geometric (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ)
    (hP : cyclicNoncollinear P) (hU : (P (zeroIndex hn)).2 = 0)
    (hV : (P (lastIndex hn)).2 = 0)
    (hleft : (P (zeroIndex hn)).1 < (P (lastIndex hn)).1)
    (hInterior : InteriorSecantsSeparated hn P) (hOuter : OuterSecantRegular hn P) :
    ∃ ε : ℝ, 0 < ε ∧ ε < geometricRadius hn P ∧
      Set.InjOn (CapCriticalEventGeometry.criticalRoot (extendedArc hn P ε))
        ↑(CapCriticalTimes.criticalPairs (extendedArc hn P ε) n) :=
  exists_extendedArc_injective hn P hP
    (extendedSecantRegular_of_geometric hn P hP hU hV hleft hInterior hOuter)

































end
end DirectGLSSW.GeometricSecantRegularity
