import SM.TreeCoefficient
import SM.GenericReversal

/-! Reversal and shift covariance of the tree coefficient (towards prop:A-reversal,
reference/SM/sm-2-amplitude.tex:1508). Written 2026-09-13 by a Claude Code prover subagent of the
pod executor (workflow prove-A-reversal, attempt B), checked with `lake env lean`; ported verbatim.
Contents: `BoundaryInterval.rev`, `IntervalComposition.revTo`/`rev`/`revEquiv`, the sign-twisted
transport lemmas `openTreeRec_rev`/`rootedTreeRec_rev` for arbitrary weights, the boundary-word
reversal identity, the negation of near and far signs under reversal, and
`treeCoefficient_shift_one`, `openTreeSum_reversal`, `treeCoefficient_reversal`. -/


/-! Source prop:A-reversal: the tree coefficient under the unit cyclic shift and
under traversal reversal. Reversal of boundary intervals and of interval
compositions is set up as an explicit bijection; every near and far sign is
negated, so every gate factor is negated, and the two tree recursions transport
with the sign (-1)^(leaves - 1). -/

namespace SM

variable {n : ℕ}

/-! ### Reversal of intervals -/

namespace BoundaryInterval

theorem ext' {I J : BoundaryInterval n} (hl : I.left = J.left) (hr : I.right = J.right) :
    I = J := by
  cases I; cases J
  simp only at hl hr
  subst hl; subst hr
  rfl

/-- The reflected interval `[N - j, N - i]` of `[i, j]`, `N = n - 1`. -/
def rev (I : BoundaryInterval n) : BoundaryInterval n where
  left := Fin.rev I.right
  right := Fin.rev I.left
  increasing := Fin.rev_lt_rev.mpr I.increasing

@[simp] theorem rev_left (I : BoundaryInterval n) : I.rev.left = Fin.rev I.right := rfl
@[simp] theorem rev_right (I : BoundaryInterval n) : I.rev.right = Fin.rev I.left := rfl

@[simp] theorem rev_rev (I : BoundaryInterval n) : I.rev.rev = I :=
  ext' (Fin.rev_rev _) (Fin.rev_rev _)

@[simp] theorem leaves_rev (I : BoundaryInterval n) : I.rev.leaves = I.leaves := by
  have h := I.increasing
  rw [Fin.lt_def] at h
  have hl := I.left.isLt
  have hr := I.right.isLt
  simp only [leaves, rev_left, rev_right, Fin.val_rev]
  omega

end BoundaryInterval

/-! ### Reversal of compositions -/

namespace IntervalComposition

variable {I : BoundaryInterval n}

theorem ext' {π ρ : IntervalComposition I} (hp : π.parts = ρ.parts)
    (hc : ∀ (k : ℕ) (hk : k < π.parts + 1) (hk' : k < ρ.parts + 1),
      π.cut ⟨k, hk⟩ = ρ.cut ⟨k, hk'⟩) : π = ρ := by
  obtain ⟨p, hp0, c, hc0, cf, cl⟩ := π
  obtain ⟨q, hq0, d, hd0, df, dl⟩ := ρ
  simp only at hp
  subst hp
  have hcd : c = d := by
    funext k
    exact hc k.val k.isLt k.isLt
  subst hcd
  rfl

/-- The reflected cut list `(N - r_s < ⋯ < N - r_0)` on any interval `J` whose
endpoints are the reflected endpoints of `I`. -/
def revTo (π : IntervalComposition I) (J : BoundaryInterval n)
    (hl : J.left = Fin.rev I.right) (hr : J.right = Fin.rev I.left) :
    IntervalComposition J where
  parts := π.parts
  parts_pos := π.parts_pos
  cut := fun k => Fin.rev (π.cut (Fin.rev k))
  strict := by
    intro a b hab
    exact Fin.rev_lt_rev.mpr (π.strict (Fin.rev_lt_rev.mpr hab))
  first := by
    simp only [Fin.rev_zero, π.last, hl]
  last := by
    simp only [Fin.rev_last, π.first, hr]

/-- The reflected composition on the reflected interval. -/
def rev (π : IntervalComposition I) : IntervalComposition I.rev :=
  π.revTo I.rev rfl rfl

@[simp] theorem rev_parts (π : IntervalComposition I) : π.rev.parts = π.parts := rfl

theorem rev_cut (π : IntervalComposition I) (k : Fin (π.parts + 1)) :
    π.rev.cut k = Fin.rev (π.cut (Fin.rev k)) := rfl

/-- Reversal is a bijection between the compositions of `I` and of `I.rev`. -/
def revEquiv (I : BoundaryInterval n) : IntervalComposition I ≃ IntervalComposition I.rev where
  toFun := rev
  invFun := fun ρ => ρ.revTo I (by simp) (by simp)
  left_inv := by
    intro π
    refine ext' ?_ ?_
    · rfl
    · intro k hk hk'
      simp only [rev, revTo, Fin.rev_rev]
  right_inv := by
    intro ρ
    refine ext' ?_ ?_
    · rfl
    · intro k hk hk'
      simp only [rev, revTo, Fin.rev_rev]

@[simp] theorem revEquiv_apply (I : BoundaryInterval n) (π : IntervalComposition I) :
    revEquiv I π = π.rev := rfl

/-- The parts of the reflected composition are the reflected parts in reversed order. -/
theorem part_rev (π : IntervalComposition I) (k : Fin π.parts) :
    π.rev.part k = (π.part (Fin.rev k)).rev := by
  apply BoundaryInterval.ext'
  · show Fin.rev (π.cut (Fin.rev (Fin.castSucc k))) = Fin.rev (π.cut (Fin.succ (Fin.rev k)))
    exact congrArg _ (congrArg _ (Fin.rev_castSucc k))
  · show Fin.rev (π.cut (Fin.rev (Fin.succ k))) = Fin.rev (π.cut (Fin.castSucc (Fin.rev k)))
    exact congrArg _ (congrArg _ (Fin.rev_succ k))

/-- Telescoping: the leaves of the parts add up to the leaves of the interval. -/
theorem sum_part_leaves (π : IntervalComposition I) :
    ∑ k : Fin π.parts, (π.part k).leaves = I.leaves := by
  let f : ℕ → ℕ := fun i => (π.cut ⟨min i π.parts, by omega⟩).val
  have hf : Monotone f := by
    intro a b hab
    apply π.strict.monotone
    rw [Fin.le_def]
    simp only
    omega
  have hterm : ∀ k : Fin π.parts, (π.part k).leaves = f (k.val + 1) - f k.val := by
    intro k
    have hk := k.isLt
    simp only [BoundaryInterval.leaves, part, f]
    congr 2
    · apply congrArg
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    · apply congrArg
      apply Fin.ext
      simp only [Fin.val_castSucc]
      omega
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Fin.sum_univ_eq_sum_range (fun i => f (i + 1) - f i) π.parts, Finset.sum_range_tsub hf]
  have h1 : f π.parts = I.right.val := by
    simp only [f, min_self]
    rw [← π.last]
    rfl
  have h0 : f 0 = I.left.val := by
    simp only [f, Nat.zero_min]
    rw [← π.first]
    rfl
  rw [h1, h0]
  rfl

theorem parts_le_leaves (π : IntervalComposition I) : π.parts ≤ I.leaves := by
  rw [← π.sum_part_leaves]
  calc π.parts = ∑ _k : Fin π.parts, 1 := by simp
    _ ≤ ∑ k : Fin π.parts, (π.part k).leaves :=
      Finset.sum_le_sum (fun k _ => Nat.sub_pos_of_lt (π.part k).increasing)

end IntervalComposition

/-! ### Sign-twisted transport of the tree recursions -/

section Transport

variable [NeZero n] {R : Type*} [CommRing R]

open IntervalComposition in
/-- The product over the reflected parts, given the transport of every part. -/
theorem prod_part_rev (w w' : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    {I : BoundaryInterval n} (π : IntervalComposition I)
    (hpart : ∀ k : Fin π.parts, openTreeRec w' (π.part k).rev =
      (-1) ^ ((π.part k).leaves - 1) * openTreeRec w (π.part k)) :
    ∏ k : Fin π.rev.parts, openTreeRec w' (π.rev.part k) =
      (-1) ^ (I.leaves - π.parts) * ∏ k : Fin π.parts, openTreeRec w (π.part k) := by
  have h1 : ∏ k : Fin π.rev.parts, openTreeRec w' (π.rev.part k) =
      ∏ k : Fin π.parts, openTreeRec w' (π.part (Fin.rev k)).rev :=
    Finset.prod_congr rfl (fun k _ => by rw [π.part_rev k])
  have h2 : ∏ k : Fin π.parts, openTreeRec w' (π.part (Fin.rev k)).rev =
      ∏ k : Fin π.parts, openTreeRec w' (π.part k).rev :=
    Equiv.prod_comp Fin.revPerm (fun k => openTreeRec w' (π.part k).rev)
  have hsum : ∑ k : Fin π.parts, ((π.part k).leaves - 1) = I.leaves - π.parts := by
    have h := π.sum_part_leaves
    have h3 : ∑ k : Fin π.parts, ((π.part k).leaves - 1 + 1) =
        ∑ k : Fin π.parts, (π.part k).leaves :=
      Finset.sum_congr rfl (fun k _ => Nat.sub_add_cancel (Nat.sub_pos_of_lt (π.part k).increasing))
    rw [Finset.sum_add_distrib] at h3
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h3
    omega
  rw [h1, h2, Finset.prod_congr rfl (fun k _ => hpart k), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hsum]

/-- Abstract sign-twisted transport of the open recursion: if every weight of the
reflected composition is `(-1)^(parts - 1)` times the original weight, the open sum of the
reflected interval is `(-1)^(leaves - 1)` times the original open sum. -/
theorem openTreeRec_rev (w w' : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (hw : ∀ (I : BoundaryInterval n) (π : IntervalComposition I),
      w' I.rev π.rev = (-1) ^ (π.parts - 1) * w I π) :
    ∀ (m : ℕ) (I : BoundaryInterval n), I.leaves = m →
      openTreeRec w' I.rev = (-1) ^ (I.leaves - 1) * openTreeRec w I := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro I hI
  by_cases h1 : I.leaves = 1
  · rw [openTreeRec_one w' I.rev (by rw [BoundaryInterval.leaves_rev]; exact h1),
      openTreeRec_one w I h1, h1]
    simp
  · have h2 : 2 ≤ I.leaves := by
      have h0 : 0 < I.leaves := Nat.sub_pos_of_lt I.increasing
      omega
    rw [openTreeRec_many w' I.rev (by rw [BoundaryInterval.leaves_rev]; exact h2),
      openTreeRec_many w I h2, mul_neg, Finset.mul_sum]
    congr 1
    symm
    apply Fintype.sum_equiv
      (Equiv.subtypeEquiv (p := fun π : IntervalComposition I => 2 ≤ π.parts)
        (q := fun π : IntervalComposition I.rev => 2 ≤ π.parts)
        (IntervalComposition.revEquiv I) (fun π => Iff.rfl))
    intro π
    show (-1) ^ (I.leaves - 1) * (w I π.val * ∏ k : Fin π.val.parts, openTreeRec w (π.val.part k)) =
      w' I.rev π.val.rev * ∏ k : Fin π.val.rev.parts, openTreeRec w' (π.val.rev.part k)
    rw [hw I π.val, prod_part_rev w w' π.val
      (fun k => ih _ (by rw [← hI]; exact π.val.part_leaves_lt π.property k) _ rfl)]
    have hp1 := π.val.parts_pos
    have hp2 := π.val.parts_le_leaves
    have hpow : (-1 : R) ^ (π.val.parts - 1) * (-1) ^ (I.leaves - π.val.parts) =
        (-1) ^ (I.leaves - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [← hpow]
    ring

/-- Abstract sign-twisted transport of the rooted recursion. -/
theorem rootedTreeRec_rev (w w' r r' : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (hw : ∀ (I : BoundaryInterval n) (π : IntervalComposition I),
      w' I.rev π.rev = (-1) ^ (π.parts - 1) * w I π)
    (hr : ∀ (I : BoundaryInterval n) (π : IntervalComposition I),
      r' I.rev π.rev = (-1) ^ (π.parts - 1) * r I π)
    (I : BoundaryInterval n) :
    rootedTreeRec w' r' I.rev = (-1) ^ (I.leaves - 1) * rootedTreeRec w r I := by
  unfold rootedTreeRec
  rw [Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (IntervalComposition.revEquiv I)
  intro π
  show (-1) ^ (I.leaves - 1) * (r I π * ∏ k : Fin π.parts, openTreeRec w (π.part k)) =
    r' I.rev π.rev * ∏ k : Fin π.rev.parts, openTreeRec w' (π.rev.part k)
  rw [hr I π, prod_part_rev w w' π (fun k => openTreeRec_rev w w' hw _ (π.part k) rfl)]
  have hp1 := π.parts_pos
  have hp2 := π.parts_le_leaves
  have hpow : (-1 : R) ^ (π.parts - 1) * (-1) ^ (I.leaves - π.parts) =
      (-1) ^ (I.leaves - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [← hpow]
  ring

end Transport

/-! ### The geometric weights of the reversed polygon at the reversed root -/

section Geometric

theorem natCast_rev_val (k : Fin n) :
    (((Fin.rev k).val : ℕ) : ZMod n) = -(k.val : ZMod n) - 1 := by
  have hk : k.val + 1 ≤ n := k.isLt
  rw [Fin.val_rev, Nat.cast_sub hk, ZMod.natCast_self]
  push_cast
  ring

/-- Source eq. arpr:boundary: the reversed polygon at root `1 - g` reads the boundary
word of `(P, g)` backwards, position `k ↦ N - k`. -/
theorem two_sub_boundaryIndex_rev (g : ZMod n) (k : Fin n) :
    2 - boundaryIndex (1 - g) (Fin.rev k) = boundaryIndex g k := by
  unfold boundaryIndex
  rw [natCast_rev_val]
  ring

theorem boundaryWord_reversal (P : LabelledTuple n) (g : ZMod n) (k : Fin n) :
    boundaryWord (reversal P) (1 - g) k = boundaryWord P g (Fin.rev k) := by
  unfold boundaryWord
  rw [reversal_apply]
  congr 1
  conv_lhs => rw [← Fin.rev_rev k]
  exact two_sub_boundaryIndex_rev g (Fin.rev k)

theorem chi_reversal_boundaryIndex (P : LabelledTuple n) (g : ZMod n) (a b c : Fin n) :
    chi (reversal P) (boundaryIndex (1 - g) (Fin.rev a)) (boundaryIndex (1 - g) (Fin.rev b))
      (boundaryIndex (1 - g) (Fin.rev c)) =
    chi P (boundaryIndex g a) (boundaryIndex g b) (boundaryIndex g c) := by
  rw [chi_reversal, two_sub_boundaryIndex_rev, two_sub_boundaryIndex_rev,
    two_sub_boundaryIndex_rev]

variable [NeZero n]

theorem signType_neg_ne_zero {d : SignType} (hd : d ≠ 0) : -d ≠ 0 :=
  fun h => hd (SignType.neg_eq_zero_iff.mp h)

/-- Source eq. arpr:gate for the ordinary gate: negating both signs negates the gate. -/
theorem ordinaryGate_neg (d h : SignType) (hd : d ≠ 0) (hh : h ≠ 0) (hd' : -d ≠ 0)
    (hh' : -h ≠ 0) : ordinaryGate (-d) (-h) hd' hh' = -ordinaryGate d h hd hh := by
  cases d <;> cases h <;> first | exact (hd rfl).elim | exact (hh rfl).elim | rfl

/-- Source eq. arpr:gate for the root gate. -/
theorem rootGate_neg (d h : SignType) (hd : d ≠ 0) (hh : h ≠ 0) (hd' : -d ≠ 0)
    (hh' : -h ≠ 0) : rootGate (-d) (-h) hd' hh' = -rootGate d h hd hh := by
  cases d <;> cases h <;> first | exact (hd rfl).elim | exact (hh rfl).elim | rfl

namespace IntervalComposition

variable {I : BoundaryInterval n} (π : IntervalComposition I)

omit [NeZero n] in
/-- The near sign at the reflected cut is the negated near sign at the original cut
(the ordered near triple is read backwards). -/
theorem nearSign_rev (P : LabelledTuple n) (g : ZMod n) (k : Fin (π.parts - 1)) :
    π.rev.nearSign (reversal P) (1 - g) k = -π.nearSign P g (Fin.rev k) := by
  have hk := k.isLt
  have e2 : (Fin.rev ⟨k.val + 2, by omega⟩ : Fin (π.parts + 1)) =
      ⟨(Fin.rev k).val, by simp only [Fin.val_rev]; omega⟩ := by
    ext; simp only [Fin.val_rev]; omega
  have e1 : (Fin.rev ⟨k.val + 1, by omega⟩ : Fin (π.parts + 1)) =
      ⟨(Fin.rev k).val + 1, by simp only [Fin.val_rev]; omega⟩ := by
    ext; simp only [Fin.val_rev]; omega
  have e0 : (Fin.rev ⟨k.val, by omega⟩ : Fin (π.parts + 1)) =
      ⟨(Fin.rev k).val + 2, by simp only [Fin.val_rev]; omega⟩ := by
    ext; simp only [Fin.val_rev]; omega
  unfold nearSign
  rw [← chi_swap_outer]
  show chi (reversal P)
      (boundaryIndex (1 - g) (Fin.rev (π.cut (Fin.rev ⟨k.val + 2, by omega⟩))))
      (boundaryIndex (1 - g) (Fin.rev (π.cut (Fin.rev ⟨k.val + 1, by omega⟩))))
      (boundaryIndex (1 - g) (Fin.rev (π.cut (Fin.rev ⟨k.val, by omega⟩)))) = _
  rw [chi_reversal_boundaryIndex, e2, e1, e0]

omit [NeZero n] in
/-- The far sign at the reflected cut is the negated far sign at the original cut. -/
theorem farSign_rev (P : LabelledTuple n) (g : ZMod n) (k : Fin (π.parts - 1)) :
    π.rev.farSign (reversal P) (1 - g) k = -π.farSign P g (Fin.rev k) := by
  have hk := k.isLt
  have e1 : (Fin.rev ⟨k.val + 1, by omega⟩ : Fin (π.parts + 1)) =
      ⟨(Fin.rev k).val + 1, by simp only [Fin.val_rev]; omega⟩ := by
    ext; simp only [Fin.val_rev]; omega
  unfold farSign
  rw [← chi_swap_outer]
  show chi (reversal P)
      (boundaryIndex (1 - g) (Fin.rev I.left))
      (boundaryIndex (1 - g) (Fin.rev (π.cut (Fin.rev ⟨k.val + 1, by omega⟩))))
      (boundaryIndex (1 - g) (Fin.rev I.right)) = _
  rw [chi_reversal_boundaryIndex, e1]

/-- Each of the `parts - 1` ordinary gates is negated: `V⁺(π') = (-1)^(s-1) V⁺(π)`. -/
theorem ordinaryWeight_rev (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    π.rev.ordinaryWeight (reversal P) (g1_reversal_forward hP) (1 - g) =
      (-1) ^ (π.parts - 1) * π.ordinaryWeight P hP g := by
  unfold ordinaryWeight
  show ∏ k : Fin (π.parts - 1),
      ordinaryGate (π.rev.nearSign (reversal P) (1 - g) k) (π.rev.farSign (reversal P) (1 - g) k)
        (π.rev.nearSign_ne_zero (g1_reversal_forward hP) (1 - g) k)
        (π.rev.farSign_ne_zero (g1_reversal_forward hP) (1 - g) k) =
    (-1) ^ (π.parts - 1) * ∏ k : Fin (π.parts - 1),
      ordinaryGate (π.nearSign P g k) (π.farSign P g k)
        (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k)
  have h : ∀ k : Fin (π.parts - 1),
      ordinaryGate (π.rev.nearSign (reversal P) (1 - g) k) (π.rev.farSign (reversal P) (1 - g) k)
        (π.rev.nearSign_ne_zero (g1_reversal_forward hP) (1 - g) k)
        (π.rev.farSign_ne_zero (g1_reversal_forward hP) (1 - g) k) =
      -ordinaryGate (π.nearSign P g (Fin.rev k)) (π.farSign P g (Fin.rev k))
        (π.nearSign_ne_zero hP g (Fin.rev k)) (π.farSign_ne_zero hP g (Fin.rev k)) := by
    intro k
    rw [ordinaryGate_congr (π.nearSign_rev P g k) (π.farSign_rev P g k) _ _
      (signType_neg_ne_zero (π.nearSign_ne_zero hP g (Fin.rev k)))
      (signType_neg_ne_zero (π.farSign_ne_zero hP g (Fin.rev k)))]
    exact ordinaryGate_neg _ _ _ _ _ _
  refine (Finset.prod_congr rfl (fun k _ => h k)).trans ?_
  rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
  congr 1
  exact Equiv.prod_comp Fin.revPerm (fun k => ordinaryGate (π.nearSign P g k) (π.farSign P g k)
    (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k))

/-- Each of the `parts - 1` root gates is negated: `V⁻(π') = (-1)^(s-1) V⁻(π)`. -/
theorem rootWeight_rev (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    π.rev.rootWeight (reversal P) (g1_reversal_forward hP) (1 - g) =
      (-1) ^ (π.parts - 1) * π.rootWeight P hP g := by
  unfold rootWeight
  show ∏ k : Fin (π.parts - 1),
      rootGate (π.rev.nearSign (reversal P) (1 - g) k) (π.rev.farSign (reversal P) (1 - g) k)
        (π.rev.nearSign_ne_zero (g1_reversal_forward hP) (1 - g) k)
        (π.rev.farSign_ne_zero (g1_reversal_forward hP) (1 - g) k) =
    (-1) ^ (π.parts - 1) * ∏ k : Fin (π.parts - 1),
      rootGate (π.nearSign P g k) (π.farSign P g k)
        (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k)
  have h : ∀ k : Fin (π.parts - 1),
      rootGate (π.rev.nearSign (reversal P) (1 - g) k) (π.rev.farSign (reversal P) (1 - g) k)
        (π.rev.nearSign_ne_zero (g1_reversal_forward hP) (1 - g) k)
        (π.rev.farSign_ne_zero (g1_reversal_forward hP) (1 - g) k) =
      -rootGate (π.nearSign P g (Fin.rev k)) (π.farSign P g (Fin.rev k))
        (π.nearSign_ne_zero hP g (Fin.rev k)) (π.farSign_ne_zero hP g (Fin.rev k)) := by
    intro k
    rw [rootGate_congr (π.nearSign_rev P g k) (π.farSign_rev P g k) _ _
      (signType_neg_ne_zero (π.nearSign_ne_zero hP g (Fin.rev k)))
      (signType_neg_ne_zero (π.farSign_ne_zero hP g (Fin.rev k)))]
    exact rootGate_neg _ _ _ _ _ _
  refine (Finset.prod_congr rfl (fun k _ => h k)).trans ?_
  rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
  congr 1
  exact Equiv.prod_comp Fin.revPerm (fun k => rootGate (π.nearSign P g k) (π.farSign P g k)
    (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k))

end IntervalComposition

/-- The open sums of the reversed polygon at the reversed root, on the reflected interval. -/
theorem openTreeSum_reversal (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (I : BoundaryInterval n) :
    openTreeSum (reversal P) (g1_reversal_forward hP) (1 - g) I.rev =
      (-1) ^ (I.leaves - 1) * openTreeSum P hP g I :=
  openTreeRec_rev (fun _ π => π.ordinaryWeight P hP g)
    (fun _ π => π.ordinaryWeight (reversal P) (g1_reversal_forward hP) (1 - g))
    (fun _ π => π.ordinaryWeight_rev P hP g) _ I rfl

omit [NeZero n] in
theorem fullBoundaryInterval_rev (hn : 3 ≤ n) :
    (fullBoundaryInterval hn).rev = fullBoundaryInterval hn := by
  apply BoundaryInterval.ext'
  · apply Fin.ext
    rw [BoundaryInterval.rev_left, Fin.val_rev]
    change n - (n - 1 + 1) = 0
    omega
  · apply Fin.ext
    rw [BoundaryInterval.rev_right, Fin.val_rev]
    change n - (0 + 1) = n - 1
    omega

omit [NeZero n] in
theorem fullBoundaryInterval_leaves (hn : 3 ≤ n) :
    (fullBoundaryInterval hn).leaves = n - 1 := by
  simp only [BoundaryInterval.leaves, fullBoundaryInterval]
  omega

/-! ### Source prop:A-reversal -/

/-- prop:A-reversal (i): `A_g(σP) = A_{g+1}(P)`. -/
theorem treeCoefficient_shift_one (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient (shift 1 P) (g1_shift_forward 1 hP) g hn = treeCoefficient P hP (g + 1) hn := by
  simpa only [add_sub_cancel_right] using treeCoefficient_shift P hP (g + 1) 1 hn

/-- prop:A-reversal (ii): `A_{1-g}(P̄) = (-1)^n A_g(P)`. -/
theorem treeCoefficient_reversal (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient (reversal P) (g1_reversal_forward hP) (1 - g) hn =
      (-1) ^ n * treeCoefficient P hP g hn := by
  unfold treeCoefficient
  have h := rootedTreeRec_rev (fun _ π => π.ordinaryWeight P hP g)
    (fun _ π => π.ordinaryWeight (reversal P) (g1_reversal_forward hP) (1 - g))
    (fun _ π => π.rootWeight P hP g)
    (fun _ π => π.rootWeight (reversal P) (g1_reversal_forward hP) (1 - g))
    (fun _ π => π.ordinaryWeight_rev P hP g) (fun _ π => π.rootWeight_rev P hP g)
    (fullBoundaryInterval hn)
  rw [fullBoundaryInterval_rev, fullBoundaryInterval_leaves] at h
  rw [h]
  congr 1
  have hn' : n = (n - 1 - 1) + 2 := by omega
  conv_rhs => rw [hn', pow_add]
  norm_num

end Geometric

end SM
