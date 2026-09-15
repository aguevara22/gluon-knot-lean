import SM.VisibleChambers

/-! Full def:visible: the actual triple, faithful Gauss alphabet embedding,
constancy on actual labelled components, and the source's explicitly permitted
labelled/equivariant reading on arbitrary representatives of quotient chambers. -/

namespace SM

variable {n : ℕ}

theorem visible_signature_definition (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) :
    (visibleSignature hn P hP).1 = turn P ∧
    (∀ s : Finset (ZMod n), s ∈ (visibleSignature hn P hP).2.1 ↔ IsCrossing P s) ∧
    (visibleSignature hn P hP).2.2 =
      (gaussWord hn hP).map (fun c : Crossing P => c.val) ∧
    Function.Injective (fun w : Cycle (Crossing P) => w.map (fun c => c.val)) ∧
    (∀ s : Finset (ZMod n), s ∈ (visibleSignature hn P hP).2.2 ↔
      s ∈ (visibleSignature hn P hP).2.1) ∧
    (visibleSignature hn P hP).2.2.length = 2 * Nat.card (Crossing P) ∧
    (∀ Q : GenericTuple n, Q ∈ labelledChamber (⟨P, hP⟩ : GenericTuple n) →
      visibleSignature hn P hP = visibleSignature hn Q.val Q.property) ∧
    (∀ a : ZMod n,
      visibleSignature hn (shift a P) ((generic_shift a P).mpr hP) =
        visibleSignatureShift a (visibleSignature hn P hP)) ∧
    (∀ Q : GenericTuple n,
      polygonProjection Q ∈ chamber (polygonProjection (⟨P, hP⟩ : GenericTuple n)) →
      ∃ a : ZMod n, visibleSignature hn Q.val Q.property =
        visibleSignatureShift a (visibleSignature hn P hP)) ∧
    (∀ s : VisibleSignatureData n, visibleSignatureShift 0 s = s) ∧
    (∀ a b : ZMod n, ∀ s : VisibleSignatureData n,
      visibleSignatureShift a (visibleSignatureShift b s) = visibleSignatureShift (a + b) s) := by
  haveI : NeZero n := ⟨by omega⟩
  refine ⟨rfl, mem_crossingSet P, rfl, gaussSupportEmbedding_injective P, ?_,
    gaussSupportWord_length hn hP, visibleSignature_labelledChamber hn ⟨P, hP⟩,
    visibleSignature_shift hn P hP, visibleSignature_quotientChamber hn ⟨P, hP⟩,
    visibleSignatureShift_zero, visibleSignatureShift_add⟩
  intro s
  exact (mem_gaussSupportWord hn hP s).trans (mem_crossingSet P s).symm

end SM
