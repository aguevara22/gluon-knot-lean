import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange

/-!
# Generic finite permutation components (staged prerequisite)

Statement transcription: `STATEMENTS.md`, written before this source.
Source motivation: frozen note lines 131–139 and 724–756. This module does
not claim the geometric smoothing, nonalternation, or refinement theorems.
Every orbit is retained, including fixed points. No cycle-factor counting.
-/

set_option autoImplicit false

namespace DirectGLSSW.PermutationOrbits

open Equiv

universe u
variable {α : Type u}

/-- Components are the full orbit quotient, including singleton orbits. -/
def Component (p : Perm α) : Type u := Quotient (Perm.SameCycle.setoid p)

/-- The component containing an underlying point. -/
def componentOf (p : Perm α) (x : α) : Component p := Quotient.mk _ x

@[simp] theorem componentOf_eq_iff (p : Perm α) (x y : α) :
    componentOf p x = componentOf p y ↔ p.SameCycle x y :=
  Quotient.eq

@[simp] theorem componentOf_apply (p : Perm α) (x : α) :
    componentOf p (p x) = componentOf p x := by
  apply (componentOf_eq_iff _ _ _).2
  simpa using Perm.SameCycle.refl p x

@[simp] theorem componentOf_pow_apply (p : Perm α) (i : ℕ) (x : α) :
    componentOf p ((p ^ i) x) = componentOf p x := by
  apply (componentOf_eq_iff _ _ _).2
  simpa using Perm.SameCycle.refl p x

noncomputable instance componentFintype [Fintype α] (p : Perm α) :
    Fintype (Component p) := by
  classical
  exact Quotient.fintype _

/-- Counts the whole orbit quotient. In particular identity has `card α` components. -/
noncomputable def componentCount [Fintype α] (p : Perm α) : ℕ :=
  Fintype.card (Component p)

/-- Explicit transport of orbit classes under conjugacy; the representative map is `g`. -/
def conjugacyEquiv (p g : Perm α) : Component p ≃ Component (g * p * g⁻¹) :=
  Quotient.congr g fun x y => by
    change p.SameCycle x y ↔ (g * p * g⁻¹).SameCycle (g x) (g y)
    simp

@[simp] theorem conjugacyEquiv_componentOf (p g : Perm α) (x : α) :
    conjugacyEquiv p g (componentOf p x) = componentOf (g * p * g⁻¹) (g x) := rfl

/-- The incoming-event permutation `p*q` and outgoing-dart permutation `q*p`
have explicitly equivalent components, with representative map `q`. -/
def productOrderEquiv (p q : Perm α) : Component (p * q) ≃ Component (q * p) :=
  Quotient.congr q fun x y => by
    change (p * q).SameCycle x y ↔ (q * p).SameCycle (q x) (q y)
    have h := (Perm.sameCycle_conj (f := p * q) (g := q) (x := q x) (y := q y))
    simpa [mul_assoc] using h.symm

@[simp] theorem productOrderEquiv_componentOf (p q : Perm α) (x : α) :
    productOrderEquiv p q (componentOf (p * q) x) = componentOf (q * p) (q x) := rfl

theorem componentCount_conjugate [Fintype α] (p g : Perm α) :
    componentCount (g * p * g⁻¹) = componentCount p :=
  (Fintype.card_congr (conjugacyEquiv p g)).symm

theorem componentCount_product_order [Fintype α] (p q : Perm α) :
    componentCount (p * q) = componentCount (q * p) :=
  Fintype.card_congr (productOrderEquiv p q)

/-- Identity components are the original points, including every fixed point. -/
def identityEquiv : Component (1 : Perm α) ≃ α where
  toFun := Quotient.lift id fun x y h => Perm.sameCycle_one.mp h
  invFun := componentOf 1
  left_inv := by intro c; exact Quotient.inductionOn c fun _ => rfl
  right_inv := fun _ => rfl

@[simp] theorem identityEquiv_componentOf (x : α) :
    identityEquiv (componentOf (1 : Perm α) x) = x := rfl

@[simp] theorem componentCount_one [Fintype α] :
    componentCount (1 : Perm α) = Fintype.card α :=
  Fintype.card_congr identityEquiv

theorem componentOf_fixed_iff (p : Perm α) (x : α) (hx : p x = x) (y : α) :
    componentOf p x = componentOf p y ↔ x = y := by
  rw [componentOf_eq_iff]
  exact ⟨fun h => h.eq_of_left hx, fun h => h.sameCycle p⟩

/-- A transitive nonempty permutation has one component, even on a singleton. -/
theorem componentCount_eq_one [Fintype α] [Nonempty α] (p : Perm α)
    (hp : p.IsCycleOn Set.univ) : componentCount p = 1 := by
  letI : Nonempty (Component p) := Nonempty.map (componentOf p) inferInstance
  letI : Subsingleton (Component p) := ⟨by
    intro c d
    induction c using Quotient.inductionOn with | h x =>
      induction d using Quotient.inductionOn with | h y =>
        exact (componentOf_eq_iff p x y).2 (hp.2 (Set.mem_univ x) (Set.mem_univ y))⟩
  letI : Unique (Component p) := Classical.choice (nonempty_unique (Component p))
  exact Fintype.card_unique

/-- The actual point fibre of a quotient component. -/
def Fibre (p : Perm α) (c : Component p) : Type u :=
  {x : α // componentOf p x = c}

noncomputable instance fibreFintype [Fintype α] (p : Perm α) (c : Component p) :
    Fintype (Fibre p c) := by
  classical
  unfold Fibre
  infer_instance

instance fibreNonempty (p : Perm α) (c : Component p) : Nonempty (Fibre p c) := by
  induction c using Quotient.inductionOn with | h x => exact ⟨⟨x, rfl⟩⟩

/-- Restriction of the actual successor to one full orbit fibre. -/
def fibrePerm (p : Perm α) (c : Component p) : Perm (Fibre p c) :=
  p.subtypePerm fun _ => by simp

@[simp] theorem fibrePerm_apply_val (p : Perm α) (c : Component p) (x : Fibre p c) :
    (fibrePerm p c x).val = p x.val := rfl

@[simp] theorem fibrePerm_pow_apply_val (p : Perm α) (c : Component p)
    (i : ℕ) (x : Fibre p c) : ((fibrePerm p c ^ i) x).val = (p ^ i) x.val := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp only [pow_succ', Perm.mul_apply, fibrePerm_apply_val, ih]

/-- Every fibre restriction is transitive on its entire domain. -/
theorem fibrePerm_isCycleOn (p : Perm α) (c : Component p) :
    (fibrePerm p c).IsCycleOn Set.univ := by
  refine ⟨(fibrePerm p c).bijOn (fun _ => Iff.rfl), ?_⟩
  intro x _ y _
  apply Perm.sameCycle_subtypePerm.mpr
  exact (componentOf_eq_iff p x.val y.val).mp (x.property.trans y.property.symm)

/-- The point set is exactly the disjoint union of its actual component fibres. -/
def fibresEquiv (p : Perm α) : (Σ c : Component p, Fibre p c) ≃ α where
  toFun z := z.2.val
  invFun x := ⟨componentOf p x, ⟨x, rfl⟩⟩
  left_inv := by rintro ⟨c, x, hx⟩; cases hx; rfl
  right_inv := fun _ => rfl

/-- A fixed point's fibre has exactly one point. -/
def fixedFibreEquiv (p : Perm α) (x : α) (hx : p x = x) :
    Fibre p (componentOf p x) ≃ PUnit.{u + 1} where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => ⟨x, rfl⟩
  left_inv := by
    intro y
    apply Subtype.ext
    exact ((componentOf_fixed_iff p x hx y.val).mp y.property.symm)
  right_inv := by intro y; cases y; rfl

theorem fixedFibre_card [Fintype α] (p : Perm α) (x : α) (hx : p x = x) :
    Fintype.card (Fibre p (componentOf p x)) = 1 := by
  simpa using Fintype.card_congr (fixedFibreEquiv p x hx)

/-- Finite successor enumeration rooted at `x`. Unlike `Perm.toList`, this
has one entry when `x` is fixed. -/
noncomputable def orbitEnumeration [Fintype α] (p : Perm α) (x : α) :
    Fin (Fintype.card (Fibre p (componentOf p x))) ≃ Fibre p (componentOf p x) := by
  classical
  let q := fibrePerm p (componentOf p x)
  let x₀ : Fibre p (componentOf p x) := ⟨x, rfl⟩
  have hq : q.IsCycleOn (Finset.univ : Finset (Fibre p (componentOf p x))) := by
    simpa using fibrePerm_isCycleOn p (componentOf p x)
  refine Equiv.ofBijective (fun i => (q ^ (i : ℕ)) x₀) ⟨?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    have hm := (hq.pow_apply_eq_pow_apply (Finset.mem_univ x₀)).mp hij
    simpa only [Finset.card_univ, Nat.ModEq, Nat.mod_eq_of_lt i.isLt,
      Nat.mod_eq_of_lt j.isLt] using hm
  · intro y
    obtain ⟨i, hi, he⟩ := hq.exists_pow_eq (Finset.mem_univ x₀) (Finset.mem_univ y)
    exact ⟨⟨i, by simpa using hi⟩, he⟩

@[simp] theorem orbitEnumeration_apply_val [Fintype α] (p : Perm α) (x : α)
    (i : Fin (Fintype.card (Fibre p (componentOf p x)))) :
    (orbitEnumeration p x i).val = (p ^ (i : ℕ)) x := by
  simp [orbitEnumeration]

/-- A concrete nonempty orbit word retaining singleton fixed-point orbits. -/
noncomputable def orbitWord [Fintype α] (p : Perm α) (x : α) : List α :=
  List.ofFn fun i => (orbitEnumeration p x i).val

@[simp] theorem orbitWord_length [Fintype α] (p : Perm α) (x : α) :
    (orbitWord p x).length = Fintype.card (Fibre p (componentOf p x)) := by
  simp [orbitWord]

theorem orbitWord_nodup [Fintype α] (p : Perm α) (x : α) :
    (orbitWord p x).Nodup := by
  apply List.nodup_ofFn_ofInjective
  exact Subtype.val_injective.comp (orbitEnumeration p x).injective

@[simp] theorem mem_orbitWord_iff [Fintype α] (p : Perm α) (x y : α) :
    y ∈ orbitWord p x ↔ p.SameCycle x y := by
  constructor
  · intro hy
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hy
    have hc := (orbitEnumeration p x i).property
    rw [hi] at hc
    exact (componentOf_eq_iff p x y).mp hc.symm
  · intro hy
    let y₀ : Fibre p (componentOf p x) :=
      ⟨y, ((componentOf_eq_iff p x y).mpr hy).symm⟩
    obtain ⟨i, hi⟩ := (orbitEnumeration p x).surjective y₀
    apply List.mem_ofFn.mpr
    exact ⟨i, congrArg Subtype.val hi⟩

theorem orbitWord_nonempty [Fintype α] (p : Perm α) (x : α) : orbitWord p x ≠ [] := by
  intro h
  have hx := (mem_orbitWord_iff p x x).mpr (Perm.SameCycle.refl p x)
  simp [h] at hx

/-- The word of a fixed point is literally a singleton, not an empty word. -/
theorem orbitWord_fixed [Fintype α] (p : Perm α) (x : α) (hx : p x = x) :
    orbitWord p x = [x] := by
  have hlen : (orbitWord p x).length = 1 :=
    (orbitWord_length p x).trans (fixedFibre_card p x hx)
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp hlen
  have hmem : y ∈ orbitWord p x := by simp [hy]
  have hyx : y = x := ((mem_orbitWord_iff p x y).mp hmem).eq_of_left hx |>.symm
  simpa [hyx] using hy

/-- Right multiplication swaps the two selected outgoing successors. -/
theorem mul_swap_apply_left [DecidableEq α] (p : Perm α) (a b : α) :
    (p * Equiv.swap a b) a = p b := by simp

theorem mul_swap_apply_right [DecidableEq α] (p : Perm α) (a b : α) :
    (p * Equiv.swap a b) b = p a := by simp

theorem mul_swap_apply_of_ne [DecidableEq α] (p : Perm α) {a b x : α}
    (ha : x ≠ a) (hb : x ≠ b) : (p * Equiv.swap a b) x = p x := by
  simp [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- A swap does not alter the forward traversal of an old orbit avoiding both endpoints. -/
theorem pow_mul_swap_apply_of_avoids [DecidableEq α] (p : Perm α) {a b x : α}
    (ha : ¬p.SameCycle x a) (hb : ¬p.SameCycle x b) (i : ℕ) :
    ((p * Equiv.swap a b) ^ i) x = (p ^ i) x := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [pow_succ', Perm.mul_apply, ih, pow_succ', Perm.mul_apply]
      apply mul_swap_apply_of_ne p
      · intro he
        apply ha
        exact ⟨(i : ℤ), by simpa using he⟩
      · intro he
        apply hb
        exact ⟨(i : ℤ), by simpa using he⟩

/-- Every old orbit avoiding the two endpoints is exactly unchanged by the swap. -/
theorem sameCycle_mul_swap_iff_of_avoids [Fintype α] [DecidableEq α]
    (p : Perm α) {a b x y : α} (ha : ¬p.SameCycle x a) (hb : ¬p.SameCycle x b) :
    (p * Equiv.swap a b).SameCycle x y ↔ p.SameCycle x y := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h.exists_nat_pow_eq
    rw [pow_mul_swap_apply_of_avoids p ha hb] at hi
    exact ⟨(i : ℤ), by simpa using hi⟩
  · intro h
    obtain ⟨i, hi⟩ := h.exists_nat_pow_eq
    refine ⟨(i : ℤ), ?_⟩
    simpa [pow_mul_swap_apply_of_avoids p ha hb] using hi

/-- An unaffected old fibre and the corresponding new fibre are equivalent
by the identity on ambient points. -/
def unaffectedFibreEquiv [Fintype α] [DecidableEq α] (p : Perm α) {a b x : α}
    (ha : ¬p.SameCycle x a) (hb : ¬p.SameCycle x b) :
    Fibre (p * Equiv.swap a b) (componentOf (p * Equiv.swap a b) x) ≃
      Fibre p (componentOf p x) :=
  (Equiv.refl α).subtypeEquiv fun y => by
    change componentOf (p * Equiv.swap a b) y = componentOf (p * Equiv.swap a b) x ↔
      componentOf p y = componentOf p x
    rw [componentOf_eq_iff, componentOf_eq_iff]
    rw [Perm.sameCycle_comm (f := p * Equiv.swap a b), Perm.sameCycle_comm (f := p)]
    exact sameCycle_mul_swap_iff_of_avoids p ha hb

@[simp] theorem unaffectedFibreEquiv_apply_val [Fintype α] [DecidableEq α]
    (p : Perm α) {a b x : α} (ha : ¬p.SameCycle x a) (hb : ¬p.SameCycle x b)
    (y : Fibre (p * Equiv.swap a b) (componentOf (p * Equiv.swap a b) x)) :
    (unaffectedFibreEquiv p ha hb y).val = y.val := rfl

/-- Adjacent abstract cut endpoints can create a singleton component. -/
theorem mul_swap_fixed_left [DecidableEq α] (p : Perm α) (a b : α) (h : p b = a) :
    (p * Equiv.swap a b) a = a := by simpa using h

theorem mul_swap_singleton_fibre [Fintype α] [DecidableEq α]
    (p : Perm α) (a b : α) (h : p b = a) :
    Fintype.card (Fibre (p * Equiv.swap a b) (componentOf (p * Equiv.swap a b) a)) = 1 :=
  fixedFibre_card _ a (mul_swap_fixed_left p a b h)

end DirectGLSSW.PermutationOrbits

