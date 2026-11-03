import LiteralCarrierHistory

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain ActiveArc ActiveArc.Cursor ActiveArc.Split
open ActiveArc.ExposedChart

/-- Literal line-incidence property to be proved along histories. It is not
part of any history constructor and does not encode auxiliary admissibility. -/
def OriginalCarrierProvenance {N : ℕ} (Q : Fin N → PlanarPoint ℝ) :
    LiteralCarrierState → Prop
  | .inl ⟨m,d⟩ => ∃ f : Fin m → Fin N, Function.Injective f ∧
      ∀ i, lineValue (polygonCarrierCoordinates Q (f i)) (d i)=0 ∧
        lineValue (polygonCarrierCoordinates Q (f i)) (d (cyclicSuccessor i))=0
  | .inr ⟨n,q⟩ => ∃ f : Fin (n+1) → Fin N, Function.Injective f ∧
      ∀ i, lineValue (polygonCarrierCoordinates Q (f i)) (q i.castSucc)=0 ∧
        lineValue (polygonCarrierCoordinates Q (f i)) (q i.succ)=0

theorem originalCarrierProvenance_closed_iff {N m : ℕ}
    (Q : Fin N → PlanarPoint ℝ) (d : Fin m → PlanarPoint ℝ) :
    OriginalCarrierProvenance Q (.inl ⟨m,d⟩) ↔
      ∃ f : Fin m → Fin N, Function.Injective f ∧
        ∀ i, lineValue (polygonCarrierCoordinates Q (f i)) (d i)=0 ∧
          lineValue (polygonCarrierCoordinates Q (f i)) (d (cyclicSuccessor i))=0 := Iff.rfl

theorem originalCarrierProvenance_open_iff {N n : ℕ}
    (Q : Fin N → PlanarPoint ℝ) (q : Fin (n+2) → PlanarPoint ℝ) :
    OriginalCarrierProvenance Q (.inr ⟨n,q⟩) ↔
      ∃ f : Fin (n+1) → Fin N, Function.Injective f ∧
        ∀ i, lineValue (polygonCarrierCoordinates Q (f i)) (q i.castSucc)=0 ∧
          lineValue (polygonCarrierCoordinates Q (f i)) (q i.succ)=0 := Iff.rfl

theorem literalCarrierStep_preserves_original {N : ℕ} (Q : Fin N → PlanarPoint ℝ)
    (hT : PairTransverse (polygonCarrierCoordinates Q)) {s t : LiteralCarrierState}
    (h : LiteralCarrierStep s t) (hs : OriginalCarrierProvenance Q s) :
    OriginalCarrierProvenance Q t := by
  cases h with
  | cut d hd e =>
    obtain ⟨f,hf,hi⟩ := hs
    exact ⟨f ∘ edgeLabel e,hf.comp (edgeLabel_injective e),
      physical_cut_incidence d e (polygonCarrierCoordinates Q ∘ f) hi⟩
  | truncateCut d hd a p hp scale ε hscale hε =>
    obtain ⟨f,hf,hi⟩ := hs
    have hx := original_carrier_incidence_iff Q d hd f hf hT hi
    obtain ⟨hg,hginc⟩ := truncated_cut_physical_carriers d a p hp scale ε
    refine ⟨fun i => f (ShortEdgeCyclicAdapter.collapseFin a (edgeLabel a.castSucc i)),hf.comp hg,?_⟩
    intro i
    exact ⟨(hx _ _).mpr (hginc i).1,(hx _ _).mpr (hginc i).2⟩
  | move q hR x hx0 hx1 =>
    obtain ⟨f,hf,hi⟩ := hs
    exact ⟨f,hf,physical_moveStart_incidence q (polygonCarrierCoordinates Q ∘ f) hi x⟩
  | parent q hR c hc hcut =>
    obtain ⟨f,hf,hi⟩ := hs
    exact ⟨f ∘ edge,hf.comp edge_injective,
      physical_parent_incidence q c hcut (polygonCarrierCoordinates Q ∘ f) hi⟩
  | corner q hR ha =>
    obtain ⟨f,hf,hi⟩ := hs
    exact ⟨f ∘ edge,hf.comp edge_injective,
      physical_suffix_incidence q (polygonCarrierCoordinates Q ∘ f) hi⟩
  | detach q hR c hc hcut =>
    obtain ⟨f,hf,hi⟩ := hs
    exact ⟨f ∘ childEdge,hf.comp childEdge_injective,
      child_physical_carrier_incidence q hR c hc.1 hcut (polygonCarrierCoordinates Q ∘ f) hi⟩

theorem literalCarrierPath_preserves_original {N : ℕ} (Q : Fin N → PlanarPoint ℝ)
    (hT : PairTransverse (polygonCarrierCoordinates Q)) {s t : LiteralCarrierState}
    (h : LiteralCarrierPath s t) :
    OriginalCarrierProvenance Q s → OriginalCarrierProvenance Q t := by
  induction h with
  | nil => exact id
  | cons h tail ih =>
    intro hs
    exact ih (literalCarrierStep_preserves_original Q hT h hs)

/-- Every closed component and every physical open edge of every finite literal
history receives an injective ORIGINAL carrier list. No provenance premise. -/
theorem literalCarrierHistory_original_provenance {N : ℕ}
    (Q : Fin N → PlanarPoint ℝ) (hT : PairTransverse (polygonCarrierCoordinates Q))
    (t : LiteralCarrierState) (h : LiteralCarrierPath (.inl ⟨N,Q⟩) t) :
    OriginalCarrierProvenance Q t := by
  apply literalCarrierPath_preserves_original Q hT h
  exact ⟨id,Function.injective_id,fun i =>
    ⟨polygonCarrierCoordinates_value_start Q i,polygonCarrierCoordinates_value_successor Q i⟩⟩

end DirectGLSSW.CyclicCarrierClearing





