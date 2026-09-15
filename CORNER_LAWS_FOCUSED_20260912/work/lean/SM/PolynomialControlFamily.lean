import SM.ConcurrenceNonassociation
import SM.ConcurrenceAffinity

/-! One chosen ordered representative per unordered source control. Names are
exactly the vertex triples and pairwise-remote edge triples of the source. -/

namespace SM

open MvPolynomial

noncomputable section

variable {n : ℕ}

structure TripleRepresentative (s : Finset (ZMod n)) where
  first : ZMod n
  second : ZMod n
  third : ZMod n
  first_ne_second : first ≠ second
  first_ne_third : first ≠ third
  second_ne_third : second ≠ third
  support_eq : s = {first, second, third}

def selectThree (s : Finset (ZMod n)) (h : s.card = 3) : TripleRepresentative s :=
  Classical.choice (by
    classical
    obtain ⟨i, j, k, hij, hik, hjk, hs⟩ := Finset.card_eq_three.mp h
    exact ⟨⟨i, j, k, hij, hik, hjk, hs⟩⟩)

abbrev VertexControlName (n : ℕ) := {s : Finset (ZMod n) // s.card = 3}
abbrev EdgeControlName (n : ℕ) :=
  {s : Finset (ZMod n) // s.card = 3 ∧ (s : Set (ZMod n)).Pairwise remote}
abbrev PolynomialControlName (n : ℕ) := VertexControlName n ⊕ EdgeControlName n

instance polynomialControlNameFintype [NeZero n] : Fintype (PolynomialControlName n) :=
  Fintype.ofFinite _

def vertexRepresentative (v : VertexControlName n) : TripleRepresentative v.val :=
  selectThree v.val v.property

def edgeRepresentative (e : EdgeControlName n) : TripleRepresentative e.val :=
  selectThree e.val e.property.1

theorem edgeRepresentative_remote (e : EdgeControlName n) :
    remote (edgeRepresentative e).first (edgeRepresentative e).second ∧
    remote (edgeRepresentative e).first (edgeRepresentative e).third ∧
    remote (edgeRepresentative e).second (edgeRepresentative e).third := by
  classical
  let r := edgeRepresentative e
  have hi : r.first ∈ e.val :=
    Eq.mpr (congrArg (fun s : Finset (ZMod n) => r.first ∈ s) r.support_eq) (by simp)
  have hj : r.second ∈ e.val :=
    Eq.mpr (congrArg (fun s : Finset (ZMod n) => r.second ∈ s) r.support_eq) (by simp)
  have hk : r.third ∈ e.val :=
    Eq.mpr (congrArg (fun s : Finset (ZMod n) => r.third ∈ s) r.support_eq) (by simp)
  exact ⟨e.property.2 hi hj r.first_ne_second,
    e.property.2 hi hk r.first_ne_third, e.property.2 hj hk r.second_ne_third⟩

def namedControlPolynomial (name : PolynomialControlName n) : CoordinatePolynomial n :=
  match name with
  | .inl v => areaPolynomial (vertexRepresentative v).first
      (vertexRepresentative v).second (vertexRepresentative v).third
  | .inr e => concurrencePolynomial (edgeRepresentative e).first
      (edgeRepresentative e).second (edgeRepresentative e).third

def polynomialControlFamily (n : ℕ) [NeZero n] : Finset (CoordinatePolynomial n) :=
  Finset.univ.image namedControlPolynomial

theorem mem_polynomialControlFamily [NeZero n] (p : CoordinatePolynomial n) :
    p ∈ polynomialControlFamily n ↔ ∃ name : PolynomialControlName n,
      namedControlPolynomial name = p := by
  classical
  simp [polynomialControlFamily]

theorem namedControlPolynomial_irreducible (hn : 3 ≤ n) (name : PolynomialControlName n) :
    Irreducible (namedControlPolynomial name) := by
  rcases name with v | e
  · let r := vertexRepresentative v
    exact areaPolynomial_irreducible r.first r.second r.third
      r.first_ne_second r.first_ne_third r.second_ne_third
  · let r := edgeRepresentative e
    obtain ⟨hij, hik, hjk⟩ := edgeRepresentative_remote e
    exact concurrencePolynomial_irreducible hn r.first r.second r.third hij hik hjk

theorem namedControlPolynomial_ne_zero (hn : 3 ≤ n) (name : PolynomialControlName n) :
    namedControlPolynomial name ≠ 0 := (namedControlPolynomial_irreducible hn name).ne_zero

theorem namedControlPolynomial_affine (name : PolynomialControlName n) (z : ScalarCoordinate n) :
    (namedControlPolynomial name).degreeOf z ≤ 1 := by
  rcases name with v | e
  · exact areaPolynomial_affine z _ _ _
  · obtain ⟨hij, hik, hjk⟩ := edgeRepresentative_remote e
    exact concurrencePolynomial_affine z _ _ _ hij hik hjk

theorem namedControlPolynomial_not_associated (hn : 3 ≤ n)
    (u v : PolynomialControlName n) (hne : u ≠ v) :
    ¬ Associated (namedControlPolynomial u) (namedControlPolynomial v) := by
  classical
  rcases u with u | u <;> rcases v with v | v
  · let r := vertexRepresentative u
    let s := vertexRepresentative v
    apply areaPolynomial_not_associated_of_support_ne r.first r.second r.third
      s.first s.second s.third r.first_ne_second r.first_ne_third r.second_ne_third
      s.first_ne_second s.first_ne_third s.second_ne_third
    intro h
    apply hne
    congr 1
    apply Subtype.ext
    exact r.support_eq.trans (h.trans s.support_eq.symm)
  · let r := vertexRepresentative u
    let s := edgeRepresentative v
    obtain ⟨hij, hik, hjk⟩ := edgeRepresentative_remote v
    exact area_concurrence_not_associated hn r.first r.second r.third s.first s.second s.third
      r.first_ne_second r.first_ne_third r.second_ne_third hij hik hjk
  · let r := edgeRepresentative u
    let s := vertexRepresentative v
    obtain ⟨hij, hik, hjk⟩ := edgeRepresentative_remote u
    intro h
    exact area_concurrence_not_associated hn s.first s.second s.third r.first r.second r.third
      s.first_ne_second s.first_ne_third s.second_ne_third hij hik hjk h.symm
  · let r := edgeRepresentative u
    let s := edgeRepresentative v
    obtain ⟨hij, hik, hjk⟩ := edgeRepresentative_remote u
    obtain ⟨hab, hac, hbc⟩ := edgeRepresentative_remote v
    apply concurrence_not_associated_of_tail_sets_ne hn r.first r.second r.third
      s.first s.second s.third hij hik hjk hab hac hbc
    intro h
    apply hne
    congr 1
    apply Subtype.ext
    exact r.support_eq.trans (h.trans s.support_eq.symm)

theorem namedControlPolynomial_injective (hn : 3 ≤ n) :
    Function.Injective (namedControlPolynomial (n := n)) := by
  intro u v h
  by_contra hne
  apply namedControlPolynomial_not_associated hn u v hne
  rw [h]

theorem polynomialControlFamily_card [NeZero n] (hn : 3 ≤ n) :
    (polynomialControlFamily n).card = Fintype.card (PolynomialControlName n) := by
  classical
  rw [polynomialControlFamily, Finset.card_image_of_injective _ (namedControlPolynomial_injective hn)]
  simp

end

end SM
