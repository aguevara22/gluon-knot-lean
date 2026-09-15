import SM.ZeroTriples
import SM.CrossingEquiv

/-! Exact cyclic transport of actual unordered zero and concurrence triples,
valid at arbitrary tuples, including nongeneric germ centres. -/

namespace SM

variable {n : ℕ}

theorem translateSupport_card (a : ZMod n) (s : Finset (ZMod n)) :
    (translateSupport a s).card = s.card :=
  Finset.card_image_of_injective s (Equiv.addRight a).injective

theorem pointZeroTriple_shift (a : ZMod n) (P : LabelledTuple n) (s : Finset (ZMod n)) :
    PointZeroTriple (shift a P) s ↔ PointZeroTriple P (translateSupport a s) := by
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨by rw [translateSupport_card]; exact hc, ?_⟩
    intro i hi j hj k hk
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hk
    simpa only [chi_shift] using h i' hi' j' hj' k' hk'
  · rintro ⟨hc, h⟩
    refine ⟨by simpa only [translateSupport_card] using hc, ?_⟩
    intro i hi j hj k hk
    rw [chi_shift]
    exact h _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩) _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)

theorem concurrenceTriple_shift (a : ZMod n) (P : LabelledTuple n) (s : Finset (ZMod n)) :
    ConcurrenceTriple (shift a P) s ↔ ConcurrenceTriple P (translateSupport a s) := by
  constructor
  · rintro ⟨hc, hr, x, hx⟩
    refine ⟨by rw [translateSupport_card]; exact hc, ?_, x, ?_⟩
    · intro i hi j hj hij
      obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
      exact (remote_add a i' j').mpr (hr hi' hj' (fun he => hij (congrArg (fun k => k + a) he)))
    · intro i hi
      obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
      simpa only [edgeInterior_shift] using hx i' hi'
  · rintro ⟨hc, hr, x, hx⟩
    refine ⟨by simpa only [translateSupport_card] using hc, ?_, x, ?_⟩
    · intro i hi j hj hij
      exact (remote_add a i j).mp (hr (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
        (Finset.mem_image.mpr ⟨j, hj, rfl⟩) (fun he => hij (add_right_cancel he)))
    · intro i hi
      simpa only [edgeInterior_shift] using hx (i + a) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

theorem pointZeroTriples_shift [NeZero n] (a : ZMod n) (P : LabelledTuple n) :
    pointZeroTriples (shift a P) = (pointZeroTriples P).image (translateSupport (-a)) := by
  ext s
  constructor
  · intro hs
    refine Finset.mem_image.mpr ⟨translateSupport a s,
      (mem_pointZeroTriples P _).mpr ((pointZeroTriple_shift a P s).mp
        ((mem_pointZeroTriples (shift a P) s).mp hs)), ?_⟩
    simpa only [neg_neg] using translateSupport_cancel (-a) s
  · intro hs
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    apply (mem_pointZeroTriples _ _).mpr
    apply (pointZeroTriple_shift a P _).mpr
    rw [translateSupport_cancel]
    exact (mem_pointZeroTriples P s').mp hs'

theorem concurrenceTriples_shift [NeZero n] (a : ZMod n) (P : LabelledTuple n) :
    concurrenceTriples (shift a P) = (concurrenceTriples P).image (translateSupport (-a)) := by
  ext s
  constructor
  · intro hs
    refine Finset.mem_image.mpr ⟨translateSupport a s,
      (mem_concurrenceTriples P _).mpr ((concurrenceTriple_shift a P s).mp
        ((mem_concurrenceTriples (shift a P) s).mp hs)), ?_⟩
    simpa only [neg_neg] using translateSupport_cancel (-a) s
  · intro hs
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    apply (mem_concurrenceTriples _ _).mpr
    apply (concurrenceTriple_shift a P _).mpr
    rw [translateSupport_cancel]
    exact (mem_concurrenceTriples P s').mp hs'

end SM
