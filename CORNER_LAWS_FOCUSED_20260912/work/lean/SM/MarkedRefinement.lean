import SM.NestedCutSets

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- Select any subset of a refined composition's actual interior cut positions. -/
abbrev MarkedCuts (S : BoundaryCutSet I) :=
  {m : Finset (Fin n) // m ⊆ S.interior.val}

namespace BoundaryCutSet

theorem cuts_subset_iff_interior_subset (S T : BoundaryCutSet I) :
    S.cuts ⊆ T.cuts ↔ S.interior.val ⊆ T.interior.val := by
  constructor
  · intro h x hx
    simp only [interior, Finset.mem_erase] at hx ⊢
    exact ⟨hx.1, hx.2.1, h hx.2.2⟩
  · intro h x hx
    by_cases hl : x = I.left
    · rw [hl]; exact T.left_mem
    · by_cases hr : x = I.right
      · rw [hr]; exact T.right_mem
      · have hs : x ∈ S.interior.val := by
          simp only [interior, Finset.mem_erase]
          exact ⟨hr, hl, hx⟩
        have ht := h hs
        simp only [interior, Finset.mem_erase] at ht
        exact ht.2.2

/-- Marked positions become outer cuts by adjoining the fixed endpoints. -/
def outerFromMarks (T : BoundaryCutSet I) (m : MarkedCuts T) : BoundaryCutSet I :=
  ofInterior ⟨m.val, fun x hx => T.interior.property x (m.property hx)⟩

theorem outerFromMarks_subset (T : BoundaryCutSet I) (m : MarkedCuts T) :
    (T.outerFromMarks m).cuts ⊆ T.cuts := by
  rw [cuts_subset_iff_interior_subset]
  change (ofInterior ⟨m.val, _⟩).interior.val ⊆ T.interior.val
  rw [interior_ofInterior]
  exact m.property

/-- Outer cut sets contained in the refinement are exactly all choices of
marked interior cuts, including no marks and all marks. -/
def outerMarkedEquiv (T : BoundaryCutSet I) :
    {S : BoundaryCutSet I // S.cuts ⊆ T.cuts} ≃ MarkedCuts T where
  toFun S := ⟨S.val.interior.val, (cuts_subset_iff_interior_subset S.val T).mp S.property⟩
  invFun m := ⟨T.outerFromMarks m, T.outerFromMarks_subset m⟩
  left_inv := by
    intro S
    apply Subtype.ext
    exact ofInterior_interior S.val
  right_inv := by
    intro m
    apply Subtype.ext
    change (T.outerFromMarks m).interior.val = m.val
    exact congrArg (fun s : InteriorCutSet I => s.val) (interior_ofInterior
      (⟨m.val, fun x hx => T.interior.property x (m.property hx)⟩ : InteriorCutSet I))

end BoundaryCutSet

/-- Exchange which cut set is recorded first while retaining the same
containment certificate. This is only a finite indexing rearrangement. -/
def swapSigmaSubtype {A B : Type*} (rel : A → B → Prop) :
    (Σ a : A, {b : B // rel a b}) ≃ (Σ b : B, {a : A // rel a b}) where
  toFun x := ⟨x.2.val, ⟨x.1, x.2.property⟩⟩
  invFun x := ⟨x.2.val, ⟨x.1, x.2.property⟩⟩
  left_inv := by rintro ⟨a, b, h⟩; rfl
  right_inv := by rintro ⟨b, a, h⟩; rfl

namespace IntervalComposition

/-- The actual raw outer compositions whose cuts lie in T correspond to
all marked interior subsets of T. -/
def outerCompositionMarkedEquiv (T : BoundaryCutSet I) :
    {π : IntervalComposition I // π.cutSet.cuts ⊆ T.cuts} ≃ MarkedCuts T :=
  (Equiv.subtypeEquiv (cutSetEquiv I) (fun _ => Iff.rfl)).trans T.outerMarkedEquiv

/-- Full source refinement bijection: an outer composition and one raw
inner composition per outer part correspond to a refined composition with
any selected subset of its interior cuts. Unary parts, empty marks and all
marks are retained by the component equivalences. -/
def nestedMarkedCutEquiv (I : BoundaryInterval n) :
    (Σ π : IntervalComposition I, ∀ k : Fin π.parts, IntervalComposition (π.part k)) ≃
      Σ ρ : IntervalComposition I, MarkedCuts ρ.cutSet :=
  (Equiv.sigmaCongrRight (fun π => π.nestedCompositionEquiv)).trans
    ((swapSigmaSubtype (fun (π : IntervalComposition I) (T : BoundaryCutSet I) =>
        π.cutSet.cuts ⊆ T.cuts)).trans
      ((Equiv.sigmaCongrRight (fun T => outerCompositionMarkedEquiv T)).trans
        (Equiv.sigmaCongrLeft (β := fun T : BoundaryCutSet I => MarkedCuts T)
          (cutSetEquiv I)).symm))

end IntervalComposition

end
end SM
