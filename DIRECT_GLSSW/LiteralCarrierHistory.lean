import RecursiveCarrierIncidenceEquivalence
import ActiveArcCombinedRecursion

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open ActiveArc ActiveArc.Cursor ActiveArc.Split ActiveArc.ExposedChart TruncationDirection

abbrev LiteralCarrierState := (Σ m : ℕ, Fin m → PlanarPoint ℝ) ⊕
  ActiveArc.ChildRestartRecursion.ActiveWordState

/-- Raw finite geometric operations. No provenance, auxiliary admissibility,
amplitude equality, or descent conclusion is a constructor premise. -/
inductive LiteralCarrierStep : LiteralCarrierState → LiteralCarrierState → Prop where
  | cut {n : ℕ} (d : Fin (n+2) → PlanarPoint ℝ) (hd : CyclicGeneric d) (e : Fin (n+2)) :
      LiteralCarrierStep (.inl ⟨n+2,d⟩) (.inr ⟨n,cutArc d e⟩)
  | truncateCut {n : ℕ} (d : Fin (n+1) → PlanarPoint ℝ) (hd : CyclicGeneric d)
      (a p : Fin (n+1)) (hp : cyclicSuccessor p=a) (scale ε : ℝ)
      (hs : 0 < scale) (hε : 0 < ε) :
      LiteralCarrierStep (.inl ⟨n+1,d⟩)
        (.inr ⟨n,cutArc (truncateCyclicCorner d a p scale ε) a.castSucc⟩)
  | move {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
      (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
      LiteralCarrierStep (.inr ⟨n,q⟩) (.inr ⟨n,moveStart q t⟩)
  | parent {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
      (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a) :
      LiteralCarrierStep (.inr ⟨a+b,q⟩) (.inr ⟨b,ActiveArc.Split.parent q c hcut⟩)
  | corner {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q) (ha : 0 < a) :
      LiteralCarrierStep (.inr ⟨a+b,q⟩) (.inr ⟨b,suffix q⟩)
  | detach {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
      (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a) :
      LiteralCarrierStep (.inr ⟨a+b,q⟩) (.inl ⟨a+1,child q hR c hc.1 hcut⟩)

inductive LiteralCarrierPath : LiteralCarrierState → LiteralCarrierState → Prop where
  | nil (s : LiteralCarrierState) : LiteralCarrierPath s s
  | cons {s u t : LiteralCarrierState} :
      LiteralCarrierStep s u → LiteralCarrierPath u t → LiteralCarrierPath s t

theorem literalCarrierPath_iff (s t : LiteralCarrierState) :
    LiteralCarrierPath s t ↔ s=t ∨ ∃ u, LiteralCarrierStep s u ∧ LiteralCarrierPath u t := by
  constructor
  · intro h
    cases h with
    | nil => exact Or.inl rfl
    | cons h tail => exact Or.inr ⟨_,h,tail⟩
  · rintro (rfl|⟨u,h,tail⟩)
    · exact .nil _
    · exact .cons h tail

theorem literalCarrierStep_iff (s t : LiteralCarrierState) :
    LiteralCarrierStep s t ↔
    (∃ (n : ℕ) (d : Fin (n+2) → PlanarPoint ℝ) (hd : CyclicGeneric d) (e : Fin (n+2)),
      s=.inl ⟨n+2,d⟩ ∧ t=.inr ⟨n,cutArc d e⟩) ∨
    (∃ (n : ℕ) (d : Fin (n+1) → PlanarPoint ℝ) (hd : CyclicGeneric d)
      (a p : Fin (n+1)) (hp : cyclicSuccessor p=a) (scale ε : ℝ),
      0 < scale ∧ 0 < ε ∧ s=.inl ⟨n+1,d⟩ ∧
      t=.inr ⟨n,cutArc (truncateCyclicCorner d a p scale ε) a.castSucc⟩) ∨
    (∃ (n : ℕ) (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q) (x : ℝ),
      0 ≤ x ∧ x < 1 ∧ s=.inr ⟨n,q⟩ ∧ t=.inr ⟨n,moveStart q x⟩) ∨
    (∃ (a b : ℕ) (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
      (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a),
      s=.inr ⟨a+b,q⟩ ∧ t=.inr ⟨b,parent q c hcut⟩) ∨
    (∃ (a b : ℕ) (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q),
      0 < a ∧ s=.inr ⟨a+b,q⟩ ∧ t=.inr ⟨b,suffix q⟩) ∨
    (∃ (a b : ℕ) (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
      (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a),
      s=.inr ⟨a+b,q⟩ ∧ t=.inl ⟨a+1,child q hR c hc.1 hcut⟩) := by
  constructor
  · intro h
    cases h with
    | cut d hd e => exact Or.inl ⟨_,d,hd,e,rfl,rfl⟩
    | truncateCut d hd a p hp scale ε hs hε => exact Or.inr (Or.inl ⟨_,d,hd,a,p,hp,scale,ε,hs,hε,rfl,rfl⟩)
    | move q hR x hx0 hx1 => exact Or.inr (Or.inr (Or.inl ⟨_,q,hR,x,hx0,hx1,rfl,rfl⟩))
    | parent q hR c hc hcut => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_,_,q,hR,c,hc,hcut,rfl,rfl⟩)))
    | corner q hR ha => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_,_,q,hR,ha,rfl,rfl⟩))))
    | detach q hR c hc hcut => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_,_,q,hR,c,hc,hcut,rfl,rfl⟩))))
  · rintro (⟨n,d,hd,e,rfl,rfl⟩|⟨n,d,hd,a,p,hp,scale,ε,hs,hε,rfl,rfl⟩|
      ⟨n,q,hR,x,hx0,hx1,rfl,rfl⟩|⟨a,b,q,hR,c,hc,hcut,rfl,rfl⟩|
      ⟨a,b,q,hR,ha,rfl,rfl⟩|⟨a,b,q,hR,c,hc,hcut,rfl,rfl⟩)
    · exact .cut d hd e
    · exact .truncateCut d hd a p hp scale ε hs hε
    · exact .move q hR x hx0 hx1
    · exact .parent q hR c hc hcut
    · exact .corner q hR ha
    · exact .detach q hR c hc hcut

end DirectGLSSW.CyclicCarrierClearing


