import SM.PolynomialControlFamily

/-! Reordering source triples changes the actual polynomial only by sign.
Every raw source control is covered by its unique unordered name. -/

namespace SM

open MvPolynomial

noncomputable section

theorem triple_value_eq_or_neg {α β : Type*} [DecidableEq α] [Neg β]
    (F : α → α → α → β) (hcyc : ∀ a b c, F a b c = F b c a)
    (hswap : ∀ a b c, F a c b = -F a b c)
    (a b c i j k : α) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hs : ({i, j, k} : Finset α) = {a, b, c}) :
    F i j k = F a b c ∨ F i j k = -F a b c := by
  have hi : i = a ∨ i = b ∨ i = c := by
    have hm : i ∈ ({a, b, c} : Finset α) := hs ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hj : j = a ∨ j = b ∨ j = c := by
    have hm : j ∈ ({a, b, c} : Finset α) := hs ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hk : k = a ∨ k = b ∨ k = c := by
    have hm : k ∈ ({a, b, c} : Finset α) := hs ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have h₁ := (hcyc a b c).symm
  have h₂ := (hcyc b c a).symm.trans h₁
  have h₃ := hswap a b c
  have h₄ := (hcyc a c b).symm.trans h₃
  have h₅ := (hcyc c b a).symm.trans h₄
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inl h₁
    | exact Or.inl h₂
    | exact Or.inr h₃
    | exact Or.inr h₄
    | exact Or.inr h₅
    | exact (hij rfl).elim
    | exact (hik rfl).elim
    | exact (hjk rfl).elim

variable {n : ℕ}

theorem areaPolynomial_swap_last (i j k : ZMod n) :
    areaPolynomial i k j = -areaPolynomial i j k := by
  dsimp [areaPolynomial]
  ring

theorem concurrencePolynomial_swap_last (e f g : ZMod n) :
    concurrencePolynomial e g f = -concurrencePolynomial e f g := by
  simp only [concurrencePolynomial_formula]
  ring

def vertexControlNameOf (i j k : ZMod n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    VertexControlName n :=
  ⟨{i, j, k}, Finset.card_triple_eq_three_iff.mpr ⟨hij, hik, hjk⟩⟩

def edgeControlNameOf (e f g : ZMod n)
    (hef : remote e f) (heg : remote e g) (hfg : remote f g) : EdgeControlName n := by
  classical
  have hef' : e ≠ f := (remote_endpoints e f hef).1.symm
  have heg' : e ≠ g := (remote_endpoints e g heg).1.symm
  have hfg' : f ≠ g := (remote_endpoints f g hfg).1.symm
  refine ⟨{e, f, g}, Finset.card_triple_eq_three_iff.mpr ⟨hef', heg', hfg'⟩, ?_⟩
  intro a ha b hb hne
  change a ∈ ({e, f, g} : Finset (ZMod n)) at ha
  change b ∈ ({e, f, g} : Finset (ZMod n)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals first | assumption | exact remote_symm hef | exact remote_symm heg |
    exact remote_symm hfg | exact (hne rfl).elim

theorem vertexControlNameOf_coverage (i j k : ZMod n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    let name : PolynomialControlName n := .inl (vertexControlNameOf i j k hij hik hjk)
    areaPolynomial i j k = namedControlPolynomial name ∨
      areaPolynomial i j k = -namedControlPolynomial name := by
  dsimp only
  let v := vertexControlNameOf i j k hij hik hjk
  let r := vertexRepresentative v
  exact triple_value_eq_or_neg areaPolynomial areaPolynomial_cyclic areaPolynomial_swap_last
    r.first r.second r.third i j k hij hik hjk r.support_eq

theorem edgeControlNameOf_coverage (e f g : ZMod n)
    (hef : remote e f) (heg : remote e g) (hfg : remote f g) :
    let name : PolynomialControlName n := .inr (edgeControlNameOf e f g hef heg hfg)
    concurrencePolynomial e f g = namedControlPolynomial name ∨
      concurrencePolynomial e f g = -namedControlPolynomial name := by
  dsimp only
  let v := edgeControlNameOf e f g hef heg hfg
  let r := edgeRepresentative v
  exact triple_value_eq_or_neg concurrencePolynomial concurrencePolynomial_cyclic
    concurrencePolynomial_swap_last r.first r.second r.third e f g
    (remote_endpoints e f hef).1.symm (remote_endpoints e g heg).1.symm
    (remote_endpoints f g hfg).1.symm r.support_eq

end

end SM
