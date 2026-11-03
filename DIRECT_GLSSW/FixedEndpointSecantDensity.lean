import SequentialSecantChoice
import GeometricSecantRegularity

set_option autoImplicit false
namespace DirectGLSSW.FixedEndpointSecantDensity
open SequentialSecantChoice SecantLineExtension GeometricSecantRegularity
open ExtendedReturnArcGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
abbrev Point := PlanarPoint ℝ

theorem prefix_noncollinear (u v : Point) (R : ℕ → Point) (k : ℕ)
    (hR : PrefixGood u v R k) (a b c : ℕ)
    (ha : a < k+2) (hb : b < k+2) (hc : c < k+2)
    (hab : a≠b) (hbc : b≠c) (hac : a≠c) :
    planarDet (R b-R c) (R a-R c)≠0 := by
  by_cases hAC : a < c
  · by_cases hBC : b < c
    · have hh := hR.triangle a b c hAC hBC hab (by omega) hc
      have he : planarDet (R b-R c) (R a-R c) =
          -planarDet (R b-R a) (R c-R a) := by dsimp [planarDet]; ring
      rw [he]; exact neg_ne_zero.mpr hh
    · have hCB : c < b := by omega
      have hh := hR.triangle c a b (by omega) (by omega) (Ne.symm hac) (by omega) hb
      have he : planarDet (R b-R c) (R a-R c) =
          -planarDet (R a-R c) (R b-R c) := by dsimp [planarDet]; ring
      rw [he]; exact neg_ne_zero.mpr hh
  · have hCA : c < a := by omega
    by_cases hBA : b < a
    · exact hR.triangle c b a hCA hBA (Ne.symm hbc) (by omega) ha
    · have hAB : a < b := by omega
      have hh := hR.triangle c a b (by omega) hAB (Ne.symm hac) (by omega) hb
      have he : planarDet (R b-R c) (R a-R c) =
          -planarDet (R a-R c) (R b-R c) := by dsimp [planarDet]; ring
      rw [he]; exact neg_ne_zero.mpr hh

/-- Put the fixed closing endpoints first, followed by the interior vertices. -/
def openLabel {n : ℕ} (i : Fin n) : ℕ :=
  if i.val=0 then 0 else if i.val+1=n then 1 else i.val+1

theorem openLabel_lt {n : ℕ} (hn : 3 ≤ n) (i : Fin n) : openLabel i < n := by
  dsimp [openLabel]; split_ifs  <;> omega

theorem openLabel_injective {n : ℕ} : Function.Injective (@openLabel n) := by
  intro a b he
  apply Fin.ext
  dsimp [openLabel] at he
  split_ifs at he  <;> omega

theorem openLabel_zero {n : ℕ} (hn : 3 ≤ n) : openLabel (zeroIndex hn)=0 := by
  simp [openLabel,zeroIndex]
theorem openLabel_last {n : ℕ} (hn : 3 ≤ n) : openLabel (lastIndex hn)=1 := by
  simp [openLabel,lastIndex,show n-1≠0 by omega,show n-1+1=n by omega]
theorem openLabel_interior {n : ℕ} (i : Fin n) (hi : 0 < i.val) (hi' : i.val+1 < n) :
    openLabel i=i.val+1 := by simp [openLabel,show i.val≠0 by omega,show i.val+1≠n by omega]

theorem prefix_geometric_predicates {n : ℕ} (hn : 3 ≤ n) (u v : Point)
    (R : ℕ → Point) (hR : PrefixGood u v R (n-2)) :
    cyclicNoncollinear (fun i : Fin n => R (openLabel i)) ∧
    InteriorSecantsSeparated hn (fun i : Fin n => R (openLabel i)) ∧
    OuterSecantRegular hn (fun i : Fin n => R (openLabel i)) := by
  have hn2 : n-2+2=n := by omega
  constructor
  · intro a b c hab hbc hac
    apply prefix_noncollinear u v R (n-2) hR (openLabel a) (openLabel b) (openLabel c)
    · rw [hn2]; exact openLabel_lt hn a
    · rw [hn2]; exact openLabel_lt hn b
    · rw [hn2]; exact openLabel_lt hn c
    · exact fun he => hab (openLabel_injective he)
    · exact fun he => hbc (openLabel_injective he)
    · exact fun he => hac (openLabel_injective he)
  constructor
  · intro a b c d ha ha' hb hb' hc hc' hd hd' hab hcd hac had hbc hbd hs ht
    have hA := openLabel_interior a ha ha'
    have hB := openLabel_interior b hb hb'
    have hC := openLabel_interior c hc hc'
    have hD := openLabel_interior d hd hd'
    have h0 := openLabel_zero hn
    dsimp only
    change rootOffset (R (openLabel (zeroIndex hn))) (R (openLabel a)) (R (openLabel b)) ≠
      rootOffset (R (openLabel (zeroIndex hn))) (R (openLabel c)) (R (openLabel d))
    rw [h0,hR.zero,hA,hB,hC,hD]
    dsimp only at hs ht
    rw [hA,hB] at hs
    rw [hC,hD] at ht
    have hbd' : b.val≠d.val := fun he => hbd (Fin.ext he)
    by_cases hBD : b.val < d.val
    · have hh := hR.secant (a.val+1) (b.val+1) (c.val+1) (d.val+1)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hs
      have hswap : planarDet (R (d.val+1)-R (c.val+1)) (1,0) ≠ 0 := by
        have he : planarDet (R (d.val+1)-R (c.val+1)) (1,0) =
            -planarDet (R (c.val+1)-R (d.val+1)) (1,0) := by dsimp [planarDet]; ring
        rw [he]; exact neg_ne_zero.mpr ht
      have hne := rootOffset_ne_of_avoidance u (R (c.val+1)) (R (d.val+1))
        (R (a.val+1)) (R (b.val+1)) hswap hh
      rw [rootOffset_swap u (R (d.val+1)) (R (c.val+1))] at hne
      exact Ne.symm hne
    · have hDB : d.val < b.val := by omega
      have hh := hR.secant (c.val+1) (d.val+1) (a.val+1) (b.val+1)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ht
      have hswap : planarDet (R (b.val+1)-R (a.val+1)) (1,0) ≠ 0 := by
        have he : planarDet (R (b.val+1)-R (a.val+1)) (1,0) =
            -planarDet (R (a.val+1)-R (b.val+1)) (1,0) := by dsimp [planarDet]; ring
        rw [he]; exact neg_ne_zero.mpr hs
      have hne := rootOffset_ne_of_avoidance u (R (a.val+1)) (R (b.val+1))
        (R (c.val+1)) (R (d.val+1)) hswap hh
      rw [rootOffset_swap u (R (b.val+1)) (R (a.val+1))] at hne
      exact hne
  · apply Or.inr
    have hf : openLabel (firstIndex hn)=2 := by
      apply openLabel_interior  <;> dsimp [firstIndex]  <;> omega
    have hp : openLabel (penultimateIndex hn)=n-1 := by
      have hh := openLabel_interior (penultimateIndex hn) (by dsimp [penultimateIndex]; omega)
        (by dsimp [penultimateIndex]; omega)
      dsimp [penultimateIndex] at hh
      rw [hh]; omega
    dsimp only
    rw [openLabel_zero hn,openLabel_last hn,hf,hp,hR.zero,hR.one]
    by_cases he : n=3
    · subst n
      norm_num
      have hh := hR.triangle 0 1 2 (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hR.zero,hR.one] at hh
      have hid : planarDet (R 2-u) (R 2-v) = planarDet (v-u) (R 2-u) := by
        dsimp [planarDet]; ring
      rw [hid]; exact hh
    · exact hR.outer 2 (n-1) (by omega) (by omega) (by omega)

/-- Density with fixed distinct horizontal endpoints, in coordinatewise neighborhoods.
This theorem does not assert G2/chamber openness or daughter genericity. -/
theorem exists_near_geometric_secant_regular {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hU : (P (zeroIndex hn)).2=0) (hV : (P (lastIndex hn)).2=0)
    (hleft : (P (zeroIndex hn)).1  <  (P (lastIndex hn)).1)
    (η : ℝ) (hη : 0 < η) :
    ∃ Q : (Fin n → Point), Q (zeroIndex hn)=P (zeroIndex hn) ∧
      Q (lastIndex hn)=P (lastIndex hn) ∧
      (∀ i, |(Q i).1-(P i).1| < η ∧ |(Q i).2-(P i).2| < η) ∧
      cyclicNoncollinear Q ∧ InteriorSecantsSeparated hn Q ∧ OuterSecantRegular hn Q := by
  let target : ℕ → Point := fun j => if hj : 0 < j ∧ j ≤ n then P ⟨j-1,by omega⟩ else P (zeroIndex hn)
  have huv : P (zeroIndex hn)≠P (lastIndex hn) := by
    intro he; have hx := congrArg Prod.fst he; linarith
  obtain ⟨R,hR,hnear⟩ := exists_good_prefix (P (zeroIndex hn)) (P (lastIndex hn)) hU hV
    huv target η hη (n-2)
  let Q : Fin n → Point := fun i => R (openLabel i)
  have hQ0 : Q (zeroIndex hn)=P (zeroIndex hn) := by dsimp [Q]; rw [openLabel_zero,hR.zero]
  have hQn : Q (lastIndex hn)=P (lastIndex hn) := by dsimp [Q]; rw [openLabel_last,hR.one]
  refine ⟨Q,hQ0,hQn,?_,prefix_geometric_predicates hn _ _ R hR⟩
  intro i
  by_cases hi0 : i.val=0
  · have hi : i=zeroIndex hn := Fin.ext hi0
    rw [hi,hQ0]
    simpa using And.intro hη hη
  by_cases hin : i.val+1=n
  · have hi : i=lastIndex hn := Fin.ext (by dsimp [lastIndex]; omega)
    rw [hi,hQn]
    simpa using And.intro hη hη
  have hi : 0 < i.val := by omega
  have hi' : i.val+1 < n := by omega
  have hn2 : n-2+2=n := by omega
  have hh := hnear (i.val+1) (by omega) (by omega)
  have ht : target (i.val+1)=P i := by
    simp [target,show 0 < i.val+1 ∧ i.val+1 ≤ n by omega]
  rw [ht] at hh
  dsimp [Q]
  rw [openLabel_interior i hi hi']
  exact hh

/-- The geometric exclusions give an actual small extended arc with distinct
critical roots. No G2/chamber preservation is asserted by this approximation. -/
theorem exists_near_with_extendedArc_injective {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hU : (P (zeroIndex hn)).2=0) (hV : (P (lastIndex hn)).2=0)
    (hleft : (P (zeroIndex hn)).1 < (P (lastIndex hn)).1)
    (η : ℝ) (hη : 0 < η) :
    ∃ Q : (Fin n → Point), ∃ ε : ℝ,
      Q (zeroIndex hn)=P (zeroIndex hn) ∧ Q (lastIndex hn)=P (lastIndex hn) ∧
      (∀ i, |(Q i).1-(P i).1| < η ∧ |(Q i).2-(P i).2| < η) ∧
      cyclicNoncollinear Q ∧ 0 < ε ∧ ε < geometricRadius hn Q ∧
      Set.InjOn (CapCriticalEventGeometry.criticalRoot (extendedArc hn Q ε))
        ↑(CapCriticalTimes.criticalPairs (extendedArc hn Q ε) n) := by
  obtain ⟨Q,hQ0,hQn,hnear,hG1,hInterior,hOuter⟩ :=
    exists_near_geometric_secant_regular hn P hU hV hleft η hη
  obtain ⟨ε,hε,hbound,hroots⟩ := exists_extendedArc_injective_of_geometric hn Q hG1
    (by rw [hQ0]; exact hU) (by rw [hQn]; exact hV)
    (by rw [hQ0,hQn]; exact hleft) hInterior hOuter
  exact ⟨Q,ε,hQ0,hQn,hnear,hG1,hε,hbound,hroots⟩











end
end DirectGLSSW.FixedEndpointSecantDensity
