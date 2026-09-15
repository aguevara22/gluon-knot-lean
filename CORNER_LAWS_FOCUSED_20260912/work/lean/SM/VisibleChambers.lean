import SM.VisibleRelabel
import SM.CyclicChambers

/-! Visible-signature constancy on the actual generic connected components,
and its full quotient-chamber meaning for arbitrary labelled representatives. -/

namespace SM

variable {n : ℕ}

theorem visibleSignature_labelledChamber (hn : 3 ≤ n) (P Q : GenericTuple n)
    (hQ : Q ∈ labelledChamber P) :
    visibleSignature hn P.val P.property = visibleSignature hn Q.val Q.property := by
  letI : PreconnectedSpace (labelledChamber P) :=
    Subtype.preconnectedSpace isPreconnected_connectedComponent
  exact generic_family_visibleSignature hn
    (F := fun x : labelledChamber P => x.val) continuous_subtype_val
    ⟨P, mem_connectedComponent⟩ ⟨Q, hQ⟩

/-- The source allows labelled constructions with their proved equivariance.
For every pair of representatives above a quotient chamber, the signatures
agree by an actual cyclic shift. No combinatorial chamber replacement or
unproved path-lifting principle is used. -/
theorem visibleSignature_quotientChamber (hn : 3 ≤ n) (P Q : GenericTuple n)
    (hQ : polygonProjection Q ∈ chamber (polygonProjection P)) :
    ∃ a : ZMod n, visibleSignature hn Q.val Q.property =
      visibleSignatureShift a (visibleSignature hn P.val P.property) := by
  change Q ∈ polygonProjection ⁻¹' chamber (polygonProjection P) at hQ
  rw [chamber_preimage_eq_cyclic_union hn P] at hQ
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hQ
  have he := visibleSignature_labelledChamber hn (genericShift a P) Q ha
  exact ⟨a, he.symm.trans (visibleSignature_shift hn P.val P.property a)⟩

end SM
