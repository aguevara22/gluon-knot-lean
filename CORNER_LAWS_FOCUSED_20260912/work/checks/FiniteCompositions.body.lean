namespace SM.IntervalComposition

variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- A finite encoding of the unchanged raw source composition. The cut count
bound is proved from strict monotonicity, not inserted as a source premise. -/
def finiteCode (π : IntervalComposition I) : Σ s : Fin n, Fin (s.val + 1) → Fin n :=
  ⟨⟨π.parts, π.parts_lt⟩, π.cut⟩

theorem finiteCode_injective : Function.Injective (finiteCode (I := I)) := by
  intro π ρ he
  have hp := congrArg (fun s : Σ s : Fin n, Fin (s.val + 1) → Fin n => s.1.val) he
  cases π with
  | mk p hp0 c hc cf cl =>
    cases ρ with
    | mk q hq0 d hd df dl =>
      change p = q at hp
      subst q
      have hcd : c = d := eq_of_heq (Sigma.mk.inj he).2
      cases hcd
      rfl

instance finite : Finite (IntervalComposition I) :=
  Finite.of_injective finiteCode finiteCode_injective

noncomputable instance fintype : Fintype (IntervalComposition I) := Fintype.ofFinite _

/-- Every child of a composition with at least two parts has strictly fewer
leaves. This is the actual termination measure of the source tree recursion. -/
theorem part_leaves_lt (π : IntervalComposition I) (hp : 2 ≤ π.parts)
    (k : Fin π.parts) : (π.part k).leaves < I.leaves := by
  have hleft := π.strict.monotone (show (0 : Fin (π.parts + 1)) ≤ k.castSucc by simp)
  have hright := π.strict.monotone (show k.succ ≤ Fin.last π.parts by exact Fin.le_last _)
  rw [π.first] at hleft
  rw [π.last] at hright
  change I.left.val ≤ (π.cut k.castSucc).val at hleft
  change (π.cut k.succ).val ≤ I.right.val at hright
  change (π.cut k.succ).val - (π.cut k.castSucc).val < I.right.val - I.left.val
  by_cases hk : k.val = 0
  · have he : k.succ < Fin.last π.parts := by
      change k.val + 1 < π.parts
      omega
    have ht := π.strict he
    rw [π.last] at ht
    change (π.cut k.succ).val < I.right.val at ht
    have hc := π.strict (show k.castSucc < k.succ by simp)
    change (π.cut k.castSucc).val < (π.cut k.succ).val at hc
    omega
  · have he : (0 : Fin (π.parts + 1)) < k.castSucc := by
      change 0 < k.val
      omega
    have ht := π.strict he
    rw [π.first] at ht
    change I.left.val < (π.cut k.castSucc).val at ht
    have hc := π.strict (show k.castSucc < k.succ by simp)
    change (π.cut k.castSucc).val < (π.cut k.succ).val at hc
    omega

end SM.IntervalComposition
