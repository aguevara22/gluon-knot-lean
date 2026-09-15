import SM.GaussFamily
import SM.CycleMaps

/-! The actual visible triple. Its Gauss letters are embedded as their
unordered edge supports in a common alphabet, with injectivity and exact
letter inventory proved. This only removes proof-carrying dependent typing. -/

namespace SM

variable {n : ℕ}

abbrev VisibleSignatureData (n : ℕ) :=
  (ZMod n → SignType) × Finset (Finset (ZMod n)) × Cycle (Finset (ZMod n))

noncomputable def gaussSupportWord (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    Cycle (Finset (ZMod n)) := (gaussWord hn hP).map (fun c : Crossing P => c.val)

theorem gaussSupportEmbedding_injective (P : LabelledTuple n) :
    Function.Injective (fun w : Cycle (Crossing P) => w.map (fun c => c.val)) :=
  cycle_map_injective _ Subtype.val_injective

theorem mem_gaussWord (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (c : Crossing P) : c ∈ gaussWord hn hP := by
  obtain ⟨i, _, _⟩ := crossing_visits_exist c
  apply Cycle.mem_map.mpr
  refine ⟨⟨c, i⟩, ?_, rfl⟩
  exact Cycle.mem_coe_iff.mpr (mem_gaussList hn hP ⟨c, i⟩)

theorem mem_gaussSupportWord (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (s : Finset (ZMod n)) : s ∈ gaussSupportWord hn hP ↔ IsCrossing P s := by
  change s ∈ (gaussWord hn hP).map (fun c : Crossing P => c.val) ↔ _
  rw [Cycle.mem_map]
  constructor
  · rintro ⟨c, _, he⟩
    exact he ▸ c.property
  · intro hs
    exact ⟨⟨s, hs⟩, mem_gaussWord hn hP ⟨s, hs⟩, rfl⟩

theorem gaussSupportWord_length (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    (gaussSupportWord hn hP).length = 2 * Nat.card (Crossing P) := by
  rw [gaussSupportWord, cycle_map_length, gaussWord_length]

noncomputable def visibleSignature (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Generic P) : VisibleSignatureData n := by
  haveI : NeZero n := ⟨by omega⟩
  exact (turn P, crossingSet P, gaussSupportWord hn hP)

theorem visibleSignature_turns (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) :
    (visibleSignature hn P hP).1 = turn P := rfl

theorem visibleSignature_crossings [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Generic P) : (visibleSignature hn P hP).2.1 = crossingSet P := rfl

theorem visibleSignature_word (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) :
    (visibleSignature hn P hP).2.2 =
      (gaussWord hn hP).map (fun c : Crossing P => c.val) := rfl

variable {α : Type*} [TopologicalSpace α] [PreconnectedSpace α]

theorem generic_family_gaussSupportWord (hn : 3 ≤ n) {F : α → GenericTuple n}
    (hF : Continuous F) (s t : α) :
    gaussSupportWord hn (F s).property = gaussSupportWord hn (F t).property := by
  have h := congrArg (fun w : Cycle (Crossing (F t).val) => w.map (fun c => c.val))
    (generic_family_gaussWord hn hF s t)
  rw [cycle_map_map] at h
  exact h

theorem generic_family_visibleSignature (hn : 3 ≤ n) {F : α → GenericTuple n}
    (hF : Continuous F) (s t : α) :
    visibleSignature hn (F s).val (F s).property =
      visibleSignature hn (F t).val (F t).property := by
  haveI : NeZero n := ⟨by omega⟩
  apply Prod.ext
  · funext i
    exact generic_family_chi_constant hF s t (i - 1) i (i + 1)
  · apply Prod.ext
    · apply Finset.ext
      intro c
      change c ∈ crossingSet (F s).val ↔ c ∈ crossingSet (F t).val
      rw [mem_crossingSet, mem_crossingSet]
      exact generic_family_crossing_constant hn hF s t c
    · exact generic_family_gaussSupportWord hn hF s t

end SM
