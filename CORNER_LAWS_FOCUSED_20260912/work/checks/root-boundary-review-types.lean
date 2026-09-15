import SM.Generic
import Mathlib.Tactic

/-! Development of source def:root. Work with labelled representatives and
prove the stipulated simultaneous shift of tuple and root. Composition lengths
are unbounded natural numbers in the definition; their finite bound is derived
from strict monotonicity, so no extra restriction is hidden in the domain. -/

namespace SM

variable {n : ℕ} [NeZero n]

def boundaryIndex (g : ZMod n) (k : Fin n) : ZMod n :=
  g + (k.val : ZMod n) + 1

def boundaryWord (P : LabelledTuple n) (g : ZMod n) (k : Fin n) : Plane :=
  P (boundaryIndex g k)

theorem boundaryIndex_injective (g : ZMod n) : Function.Injective (boundaryIndex g) := by
  intro i j he
  have hc : (i.val : ZMod n) = (j.val : ZMod n) :=
    add_left_cancel (add_right_cancel he)
  apply Fin.ext
  have hv := congrArg ZMod.val hc
  simpa only [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt] using hv

theorem boundaryWord_shift (P : LabelledTuple n) (g a : ZMod n) :
    boundaryWord (shift a P) (g - a) = boundaryWord P g := by
  funext k
  change P (g - a + (k.val : ZMod n) + 1 + a) = P (g + (k.val : ZMod n) + 1)
  congr 1
  ring

theorem boundaryWord_first (P : LabelledTuple n) (g : ZMod n) (hn : 0 < n) :
    boundaryWord P g ⟨0, hn⟩ = P (g + 1) := by
  simp [boundaryWord, boundaryIndex]

theorem boundaryWord_last (P : LabelledTuple n) (g : ZMod n) (hn : 0 < n) :
    boundaryWord P g ⟨n - 1, by omega⟩ = P g := by
  have hsum : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
    calc
      ((n - 1 : ℕ) : ZMod n) + 1 = (((n - 1) + 1 : ℕ) : ZMod n) := by simp
      _ = (n : ZMod n) := congrArg (fun t : ℕ => (t : ZMod n)) (Nat.sub_add_cancel hn)
      _ = 0 := ZMod.natCast_self n
  simp [boundaryWord, boundaryIndex, add_assoc, hsum]

theorem boundaryWord_leaf_edge (P : LabelledTuple n) (g : ZMod n)
    (k : ℕ) (hk : k + 1 < n) :
    boundaryWord P g ⟨k + 1, hk⟩ - boundaryWord P g ⟨k, by omega⟩ =
      edge P (g + (k + 1 : ℕ)) := by
  simp [boundaryWord, boundaryIndex, edge, Nat.cast_add, Nat.cast_one, add_assoc]

structure BoundaryInterval (n : ℕ) where
  left : Fin n
  right : Fin n
  increasing : left < right

namespace BoundaryInterval

def leaves (I : BoundaryInterval n) : ℕ := I.right.val - I.left.val

theorem leaves_pos (I : BoundaryInterval n) : 0 < I.leaves :=
  Nat.sub_pos_of_lt I.increasing

end BoundaryInterval

structure IntervalComposition (I : BoundaryInterval n) where
  parts : ℕ
  parts_pos : 0 < parts
  cut : Fin (parts + 1) → Fin n
  strict : StrictMono cut
  first : cut 0 = I.left
  last : cut (Fin.last parts) = I.right

namespace IntervalComposition

variable {I : BoundaryInterval n}

theorem parts_lt (π : IntervalComposition I) : π.parts < n := by
  have hc := Fintype.card_le_of_injective π.cut π.strict.injective
  simp only [Fintype.card_fin] at hc
  omega

def part (π : IntervalComposition I) (k : Fin π.parts) : BoundaryInterval n where
  left := π.cut k.castSucc
  right := π.cut k.succ
  increasing := π.strict (by simp)

def single (I : BoundaryInterval n) : IntervalComposition I where
  parts := 1
  parts_pos := by decide
  cut := ![I.left, I.right]
  strict := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [I.increasing]
  first := rfl
  last := rfl

end IntervalComposition

/-- The exact representative-based root/boundary/interval/composition data;
`boundaryWord_shift` supplies descent under the source's allowed reading. -/
def rootData (n : ℕ) [NeZero n] (_hn : 3 ≤ n) :=
  (ZMod n, edge (n := n), boundaryWord (n := n), BoundaryInterval n,
    BoundaryInterval.leaves (n := n),
    (fun I : BoundaryInterval n => IntervalComposition I),
    fun (I : BoundaryInterval n) (π : IntervalComposition I) => π.part)

end SM

set_option pp.fullNames true
set_option pp.universes false
#check SM.boundaryIndex
#print axioms SM.boundaryIndex
#check SM.boundaryWord
#print axioms SM.boundaryWord
#check SM.boundaryIndex_injective
#print axioms SM.boundaryIndex_injective
#check SM.boundaryWord_shift
#print axioms SM.boundaryWord_shift
#check SM.boundaryWord_first
#print axioms SM.boundaryWord_first
#check SM.boundaryWord_last
#print axioms SM.boundaryWord_last
#check SM.boundaryWord_leaf_edge
#print axioms SM.boundaryWord_leaf_edge
#check SM.BoundaryInterval
#print axioms SM.BoundaryInterval
#check SM.BoundaryInterval.leaves
#print axioms SM.BoundaryInterval.leaves
#check SM.BoundaryInterval.leaves_pos
#print axioms SM.BoundaryInterval.leaves_pos
#check SM.IntervalComposition
#print axioms SM.IntervalComposition
#check SM.IntervalComposition.parts_lt
#print axioms SM.IntervalComposition.parts_lt
#check SM.IntervalComposition.part
#print axioms SM.IntervalComposition.part
#check SM.IntervalComposition.single
#print axioms SM.IntervalComposition.single
#check SM.rootData
#print axioms SM.rootData
#print SM.rootData
#print SM.boundaryIndex
#print SM.boundaryWord
#print SM.BoundaryInterval
#print SM.IntervalComposition
#print SM.IntervalComposition.part
namespace RootBoundaryIndependentReview
open SM

-- Relabelling retains the same actual physical root vector and boundary word.
theorem simultaneous_root_shift {n : ℕ} [NeZero n]
    (P : LabelledTuple n) (g a : ZMod n) :
    edge (shift a P) (g - a) = edge P g ∧
      boundaryWord (shift a P) (g - a) = boundaryWord P g := by
  constructor
  · rw [edge_shift]
    simp
  · exact boundaryWord_shift P g a

-- Exactly the n-1 nonroot occurrence labels are traversed, including wraparound.
theorem leaf_index_exhaustion {n : ℕ} [NeZero n] (g : ZMod n) :
    (∀ k : Fin (n - 1), g + ((k.val + 1 : ℕ) : ZMod n) ≠ g) ∧
    ∀ e : ZMod n, e ≠ g → ∃ k : Fin (n - 1), g + ((k.val + 1 : ℕ) : ZMod n) = e := by
  have hn := NeZero.pos n
  constructor
  · intro k he
    have hz : ((k.val + 1 : ℕ) : ZMod n) = 0 := add_left_cancel (he.trans (add_zero g).symm)
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
    omega
  · intro e he
    have hp : 0 < (e - g).val := Nat.pos_of_ne_zero (fun hz => he (sub_eq_zero.mp ((ZMod.val_eq_zero _).mp hz)))
    have hlt := (e - g).val_lt
    let k : Fin (n - 1) := ⟨(e - g).val - 1, by omega⟩
    refine ⟨k, ?_⟩
    have hk : k.val + 1 = (e - g).val := by dsimp [k]; omega
    rw [hk, ZMod.natCast_zmod_val]
    abel

-- The order positions are distinct actual labels; under G1 they are distinct
-- vertices. No G2 premise is used or supplied.
theorem boundary_vertices_distinct {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    Function.Injective (boundaryWord P g) :=
  (g1_vertices_injective hn hP).comp (boundaryIndex_injective g)

-- All cuts belong to the printed interval; each positive part is an interval.
theorem cut_containment {n : ℕ} (I : BoundaryInterval n) (π : IntervalComposition I) :
    (∀ k, I.left ≤ π.cut k ∧ π.cut k ≤ I.right) ∧
      ∀ k : Fin π.parts, 0 < (π.part k).leaves := by
  letI : NeZero n := ⟨by have := I.left.isLt; omega⟩
  refine ⟨?_, fun k => (π.part k).leaves_pos⟩
  intro k
  constructor
  · rw [← π.first]
    exact π.strict.monotone (Fin.zero_le k)
  · rw [← π.last]
    exact π.strict.monotone (Fin.le_last k)

-- The representation admits EVERY source natural strictly increasing list:
-- the Fin n cut bounds follow from its last cut, not from an extra hypothesis.
theorem raw_composition_admitted {n : ℕ} (I : BoundaryInterval n)
    (s : ℕ) (hs : 0 < s) (r : Fin (s + 1) → ℕ) (hr : StrictMono r)
    (hfirst : r 0 = I.left.val) (hlast : r (Fin.last s) = I.right.val) :
    let cuts : Fin (s + 1) → Fin n := fun k => ⟨r k,
      lt_of_le_of_lt (by rw [← hlast]; exact hr.monotone (Fin.le_last k)) I.right.isLt⟩
    ∃ π : IntervalComposition I, π.parts = s ∧ HEq π.cut cuts := by
  dsimp only
  let π : IntervalComposition I := {
    parts := s
    parts_pos := hs
    cut := fun k => ⟨r k, lt_of_le_of_lt (by rw [← hlast]; exact hr.monotone (Fin.le_last k)) I.right.isLt⟩
    strict := fun a b h => hr h
    first := Fin.ext hfirst
    last := Fin.ext hlast }
  exact ⟨π, rfl, HEq.rfl⟩

-- Finiteness of the ENTIRE arbitrary-natural-part-count type is derived by
-- embedding it into bounded part counts and finite functions, with no truncation.
theorem all_compositions_finite {n : ℕ} (I : BoundaryInterval n) :
    Finite (IntervalComposition I) := by
  letI : NeZero n := ⟨by have := I.left.isLt; omega⟩
  let f : IntervalComposition I → (Σ s : Fin n, Fin (s.val + 1) → Fin n) :=
    fun π => ⟨⟨π.parts, π.parts_lt⟩, π.cut⟩
  apply Finite.of_injective f
  rintro ⟨s, hs, c, hc, hc0, hc1⟩ ⟨t, ht, d, hd, hd0, hd1⟩ he
  have hst : s = t := congrArg (fun q => q.1.val) he
  subst t
  have hcd : c = d := eq_of_heq (Sigma.mk.inj he).2
  subst d
  rfl

-- A nonempty one-part composition exists for every valid source interval.
theorem one_part_exists {n : ℕ} (I : BoundaryInterval n) :
    ∃ π : IntervalComposition I, π.parts = 1 ∧ π.part ⟨0, π.parts_pos⟩ = I := by
  refine ⟨IntervalComposition.single I, rfl, ?_⟩
  cases I
  rfl

-- The root denotes the actual placed segment and both placed endpoints,
-- not only an edge vector shared by possibly different geometric edges.
theorem root_segment_and_endpoints_shift {n : ℕ} [NeZero n]
    (P : LabelledTuple n) (g a : ZMod n) :
    edgeSegment (shift a P) (g - a) = edgeSegment P g ∧
      (shift a P) (g - a) = P g ∧
      (shift a P) (g - a + 1) = P (g + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [edgeSegment_shift]
    simp
  · simp [shift]
  · change P (g - a + 1 + a) = P (g + 1)
    congr 1
    ring

end RootBoundaryIndependentReview

#print axioms RootBoundaryIndependentReview.simultaneous_root_shift
#print axioms RootBoundaryIndependentReview.leaf_index_exhaustion
#print axioms RootBoundaryIndependentReview.boundary_vertices_distinct
#print axioms RootBoundaryIndependentReview.cut_containment
#print axioms RootBoundaryIndependentReview.raw_composition_admitted
#print axioms RootBoundaryIndependentReview.all_compositions_finite
#print axioms RootBoundaryIndependentReview.one_part_exists
#print axioms RootBoundaryIndependentReview.root_segment_and_endpoints_shift
