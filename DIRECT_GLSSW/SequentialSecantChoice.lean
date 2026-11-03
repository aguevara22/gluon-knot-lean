import SecantLineExtension

set_option autoImplicit false
namespace DirectGLSSW.SequentialSecantChoice
open SecantLineExtension
noncomputable section
attribute [local instance] Classical.propDecidable
abbrev Point := PlanarPoint ℝ

/-- Labels 0 and 1 are fixed endpoints. Labels 2,...,k+1 are interior vertices
chosen so far. The history records only finite affine-line exclusions. -/
structure PrefixGood (u v : Point) (R : ℕ → Point) (k : ℕ) : Prop where
  zero : R 0=u
  one : R 1=v
  injective : ∀ a b, a<k+2 → b<k+2 → R a=R b → a=b
  off_line : ∀ a, 2≤a → a<k+2 → (R a).2≠0
  triangle : ∀ a b c, a<c → b<c → a≠b → 2≤c → c<k+2 →
    planarDet (R b-R a) (R c-R a)≠0
  secant : ∀ a b c d, 2≤a → 2≤b → 2≤c →
    a<d → b<d → c<d → d<k+2 →
    planarDet (R a-R b) (1,0)≠0 →
    planarDet (baselineRoot u (R a) (R b)-R c) (R d-R c)≠0
  outer : ∀ a d, 2≤a → a<d → d<k+2 →
    planarDet (R a-u) (R d-v)≠0

theorem prefixGood_zero (u v : Point) (huv : u≠v) :
    PrefixGood u v (fun i => if i=0 then u else v) 0 := by
  constructor
  · simp
  · simp
  · intro a b ha hb he
    have ha' : a=0 ∨ a=1 := by omega
    have hb' : b=0 ∨ b=1 := by omega
    rcases ha' with rfl|rfl <;> rcases hb' with rfl|rfl <;> simp_all
  · intro a ha hb; omega
  · intro a b c ha hb hab hc hd; omega
  · intro a b c d ha hb hc had hbd hcd hd; omega
  · intro a d ha had hd; omega

theorem prefixGood_extend (u v : Point) (hu : u.2=0) (hv : v.2=0)
    (R : ℕ → Point) (k : ℕ) (hR : PrefixGood u v R k)
    (p : Point) (η : ℝ) (hη : 0<η) :
    ∃ X : Point, |X.1-p.1|<η ∧ |X.2-p.2|<η ∧
      PrefixGood u v (Function.update R (k+2) X) (k+1) := by
  let r : Fin (k+2) → Point := fun i => R i.val
  have hr : Function.Injective r := by
    intro a b he
    exact Fin.ext (hR.injective a.val b.val a.isLt b.isLt he)
  have hu' : (r ⟨0,by omega⟩).2=0 := by dsimp [r]; rw [hR.zero]; exact hu
  have hv' : (r ⟨1,by omega⟩).2=0 := by dsimp [r]; rw [hR.one]; exact hv
  obtain ⟨X,hx,hy,hXy,hXne,htri,hsec,hout⟩ :=
    exists_next_vertex (by omega : 2≤k+2) r hr hu' hv'
      (fun i hi => hR.off_line i.val hi i.isLt) p η hη
  have hold (a : ℕ) (ha : a<k+2) : Function.update R (k+2) X a=R a :=
    Function.update_of_ne (by omega) _ _
  have hnew : Function.update R (k+2) X (k+2)=X := Function.update_same _ _ _
  refine ⟨X,hx,hy,?_⟩
  constructor
  · rw [hold 0 (by omega)]; exact hR.zero
  · rw [hold 1 (by omega)]; exact hR.one
  · intro a b ha hb he
    by_cases hA : a=k+2
    · by_cases hB : b=k+2
      · omega
      · have hb' : b<k+2 := by omega
        rw [hA,hnew,hold b hb'] at he
        exact False.elim (hXne ⟨b,hb'⟩ he)
    · have ha' : a<k+2 := by omega
      by_cases hB : b=k+2
      · rw [hB,hnew,hold a ha'] at he
        exact False.elim (hXne ⟨a,ha'⟩ he.symm)
      · have hb' : b<k+2 := by omega
        rw [hold a ha',hold b hb'] at he
        exact hR.injective a b ha' hb' he
  · intro a ha hb
    by_cases hA : a=k+2
    · rw [hA,hnew]; exact hXy
    · have ha' : a<k+2 := by omega
      rw [hold a ha']; exact hR.off_line a ha ha'
  · intro a b c hac hbc hab hc hc'
    have ha' : a<k+2 := by omega
    have hb' : b<k+2 := by omega
    rw [hold a ha',hold b hb']
    by_cases hC : c=k+2
    · rw [hC,hnew]
      exact htri ⟨a,ha'⟩ ⟨b,hb'⟩ (by intro he; exact hab (congrArg Fin.val he))
    · have hc'' : c<k+2 := by omega
      rw [hold c hc'']; exact hR.triangle a b c hac hbc hab hc hc''
  · intro a b c d ha hb hc had hbd hcd hd hs
    have ha' : a<k+2 := by omega
    have hb' : b<k+2 := by omega
    have hc' : c<k+2 := by omega
    rw [hold a ha',hold b hb'] at hs
    rw [hold a ha',hold b hb',hold c hc']
    by_cases hD : d=k+2
    · rw [hD,hnew]
      have hh := hsec ⟨a,ha'⟩ ⟨b,hb'⟩ ⟨c,hc'⟩ ha hb hc hs
      dsimp [r] at hh
      rw [hR.zero] at hh
      exact hh
    · have hd' : d<k+2 := by omega
      rw [hold d hd']; exact hR.secant a b c d ha hb hc had hbd hcd hd' hs
  · intro a d ha had hd
    have ha' : a<k+2 := by omega
    rw [hold a ha']
    by_cases hD : d=k+2
    · rw [hD,hnew]
      have hh := hout ⟨a,ha'⟩ ha
      dsimp [r] at hh
      rw [hR.zero,hR.one] at hh
      exact hh
    · have hd' : d<k+2 := by omega
      rw [hold d hd']; exact hR.outer a d ha had hd'

theorem exists_good_prefix (u v : Point) (hu : u.2=0) (hv : v.2=0)
    (huv : u≠v) (P : ℕ → Point) (η : ℝ) (hη : 0<η) (k : ℕ) :
    ∃ R : (ℕ → Point), PrefixGood u v R k ∧
      (∀ i : ℕ, 2 ≤ i → i < k+2 → |(R i).1-(P i).1| < η ∧ |(R i).2-(P i).2| < η) := by
  induction k with
  | zero =>
    refine ⟨fun i => if i=0 then u else v,prefixGood_zero u v huv,?_⟩
    intro i hi hj; omega
  | succ k ih =>
    obtain ⟨R,hR,hnear⟩ := ih
    obtain ⟨X,hx,hy,hgood⟩ := prefixGood_extend u v hu hv R k hR (P (k+2)) η hη
    refine ⟨Function.update R (k+2) X,hgood,?_⟩
    intro i hi hj
    by_cases he : i=k+2
    · subst i
      simpa only [Function.update_same] using And.intro hx hy
    · rw [Function.update_of_ne he]
      exact hnear i hi (by omega)





end
end DirectGLSSW.SequentialSecantChoice
