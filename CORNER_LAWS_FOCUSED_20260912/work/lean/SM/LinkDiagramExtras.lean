import SM.LinkDiagram
import SM.GaussVisits
import SM.CarrierVisitTwin

/-! Chapter-3 representation layer, module LinkDiagramExtras: closing the open items of LinkDiagram: over/under strands of the derived diagrams, involutivity of reverse and mirror, the one-component agreement with the accepted Gauss data (visitPosition, visitTwin), and the per-operation positivity lemmas. Written 2026-09-13 by a Claude Code prover subagent of the pod executor
(workflow close-phase1-open-items), checked with `lake env lean` (sorry-free, standard axioms) and ported verbatim from
work/drafts/LinkDiagramExtras.lean (only this header added and #print lines removed). Declarations live in `SM.Link`. -/

/-! # Extras for polygonal oriented link diagrams (closing the open items of `SM.LinkDiagram`)

Chapter-3 representation layer, module LinkDiagramExtras.  Written 2026-09-13 by a Claude Code
prover subagent; checked with `lake env lean` (sorry-free, standard axioms).  Everything lives in
`SM.Link`.  Source frame: reference/SM/sm-3-statesum.tex, def:positive-lift (325-335), the
named-record bridge paragraph (337-351), def:gauss-record (352-372) and lp:lm (935-960), as rendered
by `SM.LinkDiagram`; nothing new is read from the source here — this file only closes the design
items recorded in the docstrings of `SM.LinkDiagram`.

Contents.
1. Over/under strands of the derived diagrams (`toFun_reverse_overStrand`, `mirror_overStrand`,
   `toFun_restrict_overStrand`, ...); transport of strands and crossings along a propositional
   equality of shadows (`Shadow.castStrand`, `Shadow.castCrossing`); the extensionality lemmas
   `Diagram.mk_eq_mk`, `Diagram.ext_of_eq`, `Diagram.ext_overStrand`; involutivity of the shadow
   operations (`Shadow.reverseShadow_reverseShadow`, `Shadow.mirrorShadow_mirrorShadow`) and the
   literal diagram-level involutions `Diagram.reverse_reverse`, `Diagram.mirror_mirror`; reversal
   and mirror commute (`Diagram.reverse_mirror`).
2. The one-component comparison with the accepted Gauss data: on the shadow `single C` of a
   generic polygon, `Diagram.visitPt` is the accepted `visitPosition` (GaussVisits.lean:
   `visitPt_single`, `crossingParam_single`) and the other occurrence `Shadow.otherVisit` is the
   accepted `Carrier.visitTwin` (CarrierVisitTwin.lean: `singleVisitEquiv_otherVisit`,
   `singleStrandEquiv_other`); the crossing sign is the accepted `crossingSign` (`sign_single`).
3. Positivity of the derived diagrams per operation: `reverse_isPositive_iff`,
   `restrict_isPositive_iff` (with `mirror_isPositive_iff` from `SM.LinkDiagram`), the restricted
   writhe `restrict_writhe`, and `pullback_isOver_iff` with the visit transport `StrandMap.mapVisit`.
4. `switch` on the derived diagrams: `switch_sign`, `switch_isPositive_iff`; `switch` commutes with
   `pullback` (`pullback_switch_of_mapCrossing_eq`, `pullback_switch_of_not_mem_range`), hence
   `switch_reverse` / `reverse_switch`, `switch_mirror` / `mirror_switch`,
   `switch_restrict_of_internal` / `switch_restrict_of_external`. -/

namespace SM.Link

open SM

noncomputable section

/-! ## 1. Strands of the derived diagrams; transport; extensionality; involutions -/

namespace Diagram

variable (D : Diagram)

/-- The over strand of the reversed diagram, read back in the original shadow: it is the over strand
of the corresponding crossing (the strand relabelling `⟨i, a⟩ ↦ ⟨i, 1 - a⟩`). -/
theorem toFun_reverse_overStrand (x : D.Γ.reverseShadow.Crossing) :
    D.Γ.reverseMap.toFun (D.reverse.overStrand x) = D.overStrand (D.Γ.reverseCrossingEquiv x) :=
  toFun_pullback_overStrand D D.Γ.reverseMap (fun i => regular_reversal_forward (D.generic.regular i)) x

theorem toFun_reverse_underStrand (x : D.Γ.reverseShadow.Crossing) :
    D.Γ.reverseMap.toFun (D.reverse.underStrand x) = D.underStrand (D.Γ.reverseCrossingEquiv x) :=
  toFun_pullback_underStrand D D.Γ.reverseMap (fun i => regular_reversal_forward (D.generic.regular i)) x

/-- The strands of the mirror shadow are the strands of the shadow (same labels); the over strand of
the mirror image is the over strand of the corresponding crossing. -/
@[simp] theorem mirror_overStrand (x : D.Γ.mirrorShadow.Crossing) :
    D.mirror.overStrand x = D.overStrand (D.Γ.mirrorCrossingEquiv x) :=
  toFun_pullback_overStrand D D.Γ.mirrorMap (fun i => regular_reflect (D.generic.regular i)) x

@[simp] theorem mirror_underStrand (x : D.Γ.mirrorShadow.Crossing) :
    D.mirror.underStrand x = D.underStrand (D.Γ.mirrorCrossingEquiv x) :=
  toFun_pullback_underStrand D D.Γ.mirrorMap (fun i => regular_reflect (D.generic.regular i)) x

theorem toFun_restrict_overStrand (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty)
    (x : (D.Γ.restrictShadow B hB).Crossing) :
    (D.Γ.restrictMap B hB).toFun ((D.restrict B hB).overStrand x) =
      D.overStrand ((D.Γ.restrictMap B hB).mapCrossing x) :=
  toFun_pullback_overStrand D (D.Γ.restrictMap B hB)
    (fun j => D.generic.regular (B.orderEmbOfFin rfl j)) x

theorem toFun_restrict_underStrand (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty)
    (x : (D.Γ.restrictShadow B hB).Crossing) :
    (D.Γ.restrictMap B hB).toFun ((D.restrict B hB).underStrand x) =
      D.underStrand ((D.Γ.restrictMap B hB).mapCrossing x) :=
  toFun_pullback_underStrand D (D.Γ.restrictMap B hB)
    (fun j => D.generic.regular (B.orderEmbOfFin rfl j)) x

/-- The restricted over strand, spelled out: same edge label, component reindexed by the block. -/
theorem restrict_overStrand (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty)
    (x : (D.Γ.restrictShadow B hB).Crossing) :
    (⟨B.orderEmbOfFin rfl ((D.restrict B hB).overStrand x).1, ((D.restrict B hB).overStrand x).2⟩ :
      D.Γ.Strand) = D.overStrand ((D.Γ.restrictMap B hB).mapCrossing x) :=
  D.toFun_restrict_overStrand B hB x

theorem restrict_underStrand (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty)
    (x : (D.Γ.restrictShadow B hB).Crossing) :
    (⟨B.orderEmbOfFin rfl ((D.restrict B hB).underStrand x).1, ((D.restrict B hB).underStrand x).2⟩ :
      D.Γ.Strand) = D.underStrand ((D.Γ.restrictMap B hB).mapCrossing x) :=
  D.toFun_restrict_underStrand B hB x

end Diagram

namespace Shadow

/-- Transport of a strand along an equality of shadows. -/
def castStrand {Γ Γ' : Shadow} (h : Γ = Γ') (s : Γ.Strand) : Γ'.Strand :=
  cast (congrArg Shadow.Strand h) s

/-- Transport of a crossing along an equality of shadows. -/
def castCrossing {Γ Γ' : Shadow} (h : Γ = Γ') (x : Γ.Crossing) : Γ'.Crossing :=
  cast (congrArg Shadow.Crossing h) x

@[simp] theorem castStrand_rfl {Γ : Shadow} (s : Γ.Strand) : castStrand rfl s = s := rfl

@[simp] theorem castCrossing_rfl {Γ : Shadow} (x : Γ.Crossing) : castCrossing rfl x = x := rfl

theorem castStrand_injective {Γ Γ' : Shadow} (h : Γ = Γ') : Function.Injective (castStrand h) := by
  subst h
  intro s t hst
  exact hst

/-- The strand transport as an embedding. -/
def castStrandEmb {Γ Γ' : Shadow} (h : Γ = Γ') : Γ.Strand ↪ Γ'.Strand :=
  ⟨castStrand h, castStrand_injective h⟩

@[simp] theorem castStrandEmb_apply {Γ Γ' : Shadow} (h : Γ = Γ') (s : Γ.Strand) :
    castStrandEmb h s = castStrand h s := rfl

theorem castCrossing_val {Γ Γ' : Shadow} (h : Γ = Γ') (x : Γ.Crossing) :
    (castCrossing h x).val = x.val.map (castStrandEmb h) := by
  subst h
  change x.val = x.val.map (castStrandEmb rfl)
  have : castStrandEmb (rfl : Γ = Γ) = Function.Embedding.refl _ :=
    Function.Embedding.ext fun _ => rfl
  rw [this, Finset.map_refl]

theorem mem_castCrossing_iff {Γ Γ' : Shadow} (h : Γ = Γ') (x : Γ.Crossing) (s : Γ.Strand) :
    castStrand h s ∈ (castCrossing h x).val ↔ s ∈ x.val := by
  subst h
  exact Iff.rfl

end Shadow

namespace Diagram

/-- Two diagrams built by the constructor agree once their shadows agree propositionally and their
over strands agree along the transport. -/
theorem mk_eq_mk {Γ Γ' : Shadow} {g : Γ.Generic} {g' : Γ'.Generic} {ov : Γ.Crossing → Γ.Strand}
    {ov' : Γ'.Crossing → Γ'.Strand} {hov : ∀ x, ov x ∈ x.val} {hov' : ∀ x, ov' x ∈ x.val}
    (hΓ : Γ = Γ') (h : ∀ x, Shadow.castStrand hΓ (ov x) = ov' (Shadow.castCrossing hΓ x)) :
    Diagram.mk Γ g ov hov = Diagram.mk Γ' g' ov' hov' := by
  subst hΓ
  have : ov = ov' := funext fun x => h x
  subst this
  rfl

/-- Extensionality for diagrams: same shadow (propositionally) and the same over strand at every
crossing, up to the transport along the shadow equality. -/
theorem ext_of_eq {D D' : Diagram} (hΓ : D.Γ = D'.Γ)
    (h : ∀ x, Shadow.castStrand hΓ (D.overStrand x) = D'.overStrand (Shadow.castCrossing hΓ x)) :
    D = D' := by
  obtain ⟨Γ, g, ov, hov⟩ := D
  obtain ⟨Γ', g', ov', hov'⟩ := D'
  exact mk_eq_mk hΓ h

/-- Extensionality when the shadows are literally the same term: only the over data matters. -/
theorem ext_overStrand {D D' : Diagram} (hΓ : D.Γ = D'.Γ) (h : HEq D.overStrand D'.overStrand) :
    D = D' := by
  obtain ⟨Γ, g, ov, hov⟩ := D
  obtain ⟨Γ', g', ov', hov'⟩ := D'
  dsimp only at hΓ h
  subst hΓ
  obtain rfl := eq_of_heq h
  rfl

end Diagram

/-! ### Involutivity of the shadow operations -/

theorem PolyComp.reverse_reverse (C : PolyComp) : C.reverse.reverse = C :=
  congrArg (PolyComp.mk C.k C.hk) (reversal_involutive C.P)

theorem PolyComp.mirror_mirror (C : PolyComp) : C.mirror.mirror = C := by
  have : reflect ∘ (reflect ∘ C.P) = C.P := by
    funext i
    simp [Function.comp]
  exact congrArg (PolyComp.mk C.k C.hk) this

namespace Shadow

theorem reverseShadow_reverseShadow (Γ : Shadow) : Γ.reverseShadow.reverseShadow = Γ := by
  obtain ⟨c, hc, comp⟩ := Γ
  have : (fun i => (comp i).reverse.reverse) = comp := funext fun i => PolyComp.reverse_reverse _
  exact congrArg (Shadow.mk c hc) this

theorem mirrorShadow_mirrorShadow (Γ : Shadow) : Γ.mirrorShadow.mirrorShadow = Γ := by
  obtain ⟨c, hc, comp⟩ := Γ
  have : (fun i => (comp i).mirror.mirror) = comp := funext fun i => PolyComp.mirror_mirror _
  exact congrArg (Shadow.mk c hc) this

/-- The strands of `Γ.reverseShadow.reverseShadow` are (definitionally) the strands of `Γ`, and the
transport along the involutivity equality is the identity. -/
theorem castStrand_reverseShadow_reverseShadow (Γ : Shadow)
    (s : Γ.reverseShadow.reverseShadow.Strand) :
    castStrand (reverseShadow_reverseShadow Γ) s = s := rfl

theorem castStrand_mirrorShadow_mirrorShadow (Γ : Shadow) (s : Γ.mirrorShadow.mirrorShadow.Strand) :
    castStrand (mirrorShadow_mirrorShadow Γ) s = s := rfl

variable (Γ : Shadow)

/-- Reversing twice relabels every strand by the identity (`1 - (1 - a) = a`). -/
theorem reverseMap_toFun_reverseMap_toFun (s : Γ.reverseShadow.reverseShadow.Strand) :
    Γ.reverseMap.toFun (Γ.reverseShadow.reverseMap.toFun s) = s := by
  obtain ⟨i, a⟩ := s
  rw [reverseMap_toFun, reverseMap_toFun]
  change (⟨i, 1 - (1 - a)⟩ : Γ.Strand) = ⟨i, a⟩
  rw [sub_sub_cancel]

/-- The composite of the two reversal embeddings is the identity embedding. -/
theorem reverseMap_emb_trans_reverseMap_emb :
    Γ.reverseShadow.reverseMap.emb.trans Γ.reverseMap.emb = Function.Embedding.refl _ :=
  Function.Embedding.ext fun s => Γ.reverseMap_toFun_reverseMap_toFun s

theorem reverseCrossingEquiv_reverseCrossingEquiv (x : Γ.reverseShadow.reverseShadow.Crossing) :
    Γ.reverseCrossingEquiv (Γ.reverseShadow.reverseCrossingEquiv x) =
      castCrossing (reverseShadow_reverseShadow Γ) x := by
  apply Subtype.ext
  rw [castCrossing_val, reverseCrossingEquiv_apply, reverseCrossingEquiv_apply,
    StrandMap.mapCrossing_val, StrandMap.mapCrossing_val, Finset.map_map,
    reverseMap_emb_trans_reverseMap_emb, Finset.map_refl]
  have : castStrandEmb (reverseShadow_reverseShadow Γ) = Function.Embedding.refl _ :=
    Function.Embedding.ext fun _ => rfl
  rw [this, Finset.map_refl]

/-- Mirroring twice relabels every strand by the identity. -/
theorem mirrorMap_toFun_mirrorMap_toFun (s : Γ.mirrorShadow.mirrorShadow.Strand) :
    Γ.mirrorMap.toFun (Γ.mirrorShadow.mirrorMap.toFun s) = s := rfl

theorem mirrorMap_emb_trans_mirrorMap_emb :
    Γ.mirrorShadow.mirrorMap.emb.trans Γ.mirrorMap.emb = Function.Embedding.refl _ :=
  Function.Embedding.ext fun _ => rfl

theorem mirrorCrossingEquiv_mirrorCrossingEquiv (x : Γ.mirrorShadow.mirrorShadow.Crossing) :
    Γ.mirrorCrossingEquiv (Γ.mirrorShadow.mirrorCrossingEquiv x) =
      castCrossing (mirrorShadow_mirrorShadow Γ) x := by
  apply Subtype.ext
  rw [castCrossing_val, mirrorCrossingEquiv_apply, mirrorCrossingEquiv_apply,
    StrandMap.mapCrossing_val, StrandMap.mapCrossing_val, Finset.map_map,
    mirrorMap_emb_trans_mirrorMap_emb, Finset.map_refl]
  have : castStrandEmb (mirrorShadow_mirrorShadow Γ) = Function.Embedding.refl _ :=
    Function.Embedding.ext fun _ => rfl
  rw [this, Finset.map_refl]

/-- The shadows `Γ.reverseShadow.mirrorShadow` and `Γ.mirrorShadow.reverseShadow` are definitionally
equal (both trace `reflect (P (2 - i))`), and the two composite strand relabellings agree
(`⟨i, a⟩ ↦ ⟨i, 1 - a⟩`), so the corresponding crossings of `Γ` agree. -/
theorem reverseMap_mapCrossing_mirrorMap_mapCrossing (x : Γ.reverseShadow.mirrorShadow.Crossing) :
    Γ.reverseMap.mapCrossing (Γ.reverseShadow.mirrorMap.mapCrossing x) =
      Γ.mirrorMap.mapCrossing (Γ.mirrorShadow.reverseMap.mapCrossing x) := by
  apply Subtype.ext
  show Finset.map Γ.reverseMap.emb (Finset.map Γ.reverseShadow.mirrorMap.emb x.val) =
    Finset.map Γ.mirrorMap.emb (Finset.map Γ.mirrorShadow.reverseMap.emb x.val)
  rw [Finset.map_map, Finset.map_map]
  congr 1

end Shadow

namespace Diagram

variable (D : Diagram)

/-- Reversing every component twice gives back the diagram (literal equality; the shadows agree by
`reversal_involutive`, the over data by injectivity of the strand relabelling). -/
theorem reverse_reverse : D.reverse.reverse = D := by
  apply ext_of_eq (Shadow.reverseShadow_reverseShadow D.Γ)
  intro x
  have h₂ : D.Γ.reverseShadow.reverseMap.toFun (D.reverse.reverse.overStrand x) =
      D.reverse.overStrand (D.Γ.reverseShadow.reverseCrossingEquiv x) :=
    toFun_reverse_overStrand D.reverse x
  have h₁ : D.Γ.reverseMap.toFun (D.reverse.overStrand (D.Γ.reverseShadow.reverseCrossingEquiv x)) =
      D.overStrand (D.Γ.reverseCrossingEquiv (D.Γ.reverseShadow.reverseCrossingEquiv x)) :=
    toFun_reverse_overStrand D _
  have h₃ : D.Γ.reverseMap.toFun (D.Γ.reverseShadow.reverseMap.toFun (D.reverse.reverse.overStrand x)) =
      D.reverse.reverse.overStrand x :=
    D.Γ.reverseMap_toFun_reverseMap_toFun _
  have h₄ : D.Γ.reverseCrossingEquiv (D.Γ.reverseShadow.reverseCrossingEquiv x) =
      Shadow.castCrossing (Shadow.reverseShadow_reverseShadow D.Γ) x :=
    D.Γ.reverseCrossingEquiv_reverseCrossingEquiv x
  exact h₃.symm.trans ((congrArg _ h₂).trans (h₁.trans (congrArg _ h₄)))

theorem reverse_involutive : Function.Involutive Diagram.reverse := reverse_reverse

theorem reverse_injective : Function.Injective Diagram.reverse := reverse_involutive.injective

theorem reverse_surjective : Function.Surjective Diagram.reverse := reverse_involutive.surjective

/-- Mirroring twice gives back the diagram (literal equality). -/
theorem mirror_mirror : D.mirror.mirror = D := by
  apply ext_of_eq (Shadow.mirrorShadow_mirrorShadow D.Γ)
  intro x
  have h₂ : D.mirror.mirror.overStrand x =
      D.mirror.overStrand (D.Γ.mirrorShadow.mirrorCrossingEquiv x) :=
    mirror_overStrand D.mirror x
  have h₁ : D.mirror.overStrand (D.Γ.mirrorShadow.mirrorCrossingEquiv x) =
      D.overStrand (D.Γ.mirrorCrossingEquiv (D.Γ.mirrorShadow.mirrorCrossingEquiv x)) :=
    mirror_overStrand D _
  have h₄ : D.Γ.mirrorCrossingEquiv (D.Γ.mirrorShadow.mirrorCrossingEquiv x) =
      Shadow.castCrossing (Shadow.mirrorShadow_mirrorShadow D.Γ) x :=
    D.Γ.mirrorCrossingEquiv_mirrorCrossingEquiv x
  exact h₂.trans (h₁.trans (congrArg _ h₄))

theorem mirror_involutive : Function.Involutive Diagram.mirror := mirror_mirror

theorem mirror_injective : Function.Injective Diagram.mirror := mirror_involutive.injective

theorem mirror_surjective : Function.Surjective Diagram.mirror := mirror_involutive.surjective

/-- Reversal and mirror image commute (the two shadows are definitionally the same: both reflect
`P (2 - i)`). -/
theorem reverse_mirror : D.reverse.mirror = D.mirror.reverse := by
  refine ext_overStrand ?_ ?_
  · rfl
  apply heq_of_eq
  funext x
  apply D.Γ.mirrorShadow.reverseMap.inj
  have h₁ : D.Γ.mirrorShadow.reverseMap.toFun (D.reverse.mirror.overStrand x) =
      D.overStrand (D.Γ.reverseMap.mapCrossing (D.Γ.reverseShadow.mirrorMap.mapCrossing x)) := by
    have e₁ : D.reverse.mirror.overStrand x =
        D.reverse.overStrand (D.Γ.reverseShadow.mirrorCrossingEquiv x) := mirror_overStrand D.reverse x
    have e₂ : D.Γ.reverseMap.toFun (D.reverse.overStrand (D.Γ.reverseShadow.mirrorCrossingEquiv x)) =
        D.overStrand (D.Γ.reverseCrossingEquiv (D.Γ.reverseShadow.mirrorCrossingEquiv x)) :=
      toFun_reverse_overStrand D _
    exact e₁ ▸ e₂
  have h₂ : D.Γ.mirrorShadow.reverseMap.toFun (D.mirror.reverse.overStrand x) =
      D.overStrand (D.Γ.mirrorMap.mapCrossing (D.Γ.mirrorShadow.reverseMap.mapCrossing x)) := by
    have e₁ : D.Γ.mirrorShadow.reverseMap.toFun (D.mirror.reverse.overStrand x) =
        D.mirror.overStrand (D.Γ.mirrorShadow.reverseCrossingEquiv x) :=
      toFun_reverse_overStrand D.mirror x
    rw [e₁, mirror_overStrand D]
    rfl
  exact h₁.trans ((congrArg _ (D.Γ.reverseMap_mapCrossing_mirrorMap_mapCrossing x)).trans h₂.symm)

theorem mirror_reverse : D.mirror.reverse = D.reverse.mirror := (D.reverse_mirror).symm

end Diagram

/-! ## 2. One-component shadows versus the accepted Gauss data -/

namespace Shadow

variable (Γ : Shadow)

/-- The other occurrence of the same crossing (the pairing `τ` of def:gauss-record at the level of
shadows; multi-component copy of the accepted `Carrier.visitTwin`). -/
def otherVisit (v : Γ.Visit) : Γ.Visit := ⟨v.1, ⟨Γ.other v.1 v.2.2, Γ.other_mem v.1 v.2.2⟩⟩

@[simp] theorem otherVisit_fst (v : Γ.Visit) : (Γ.otherVisit v).1 = v.1 := rfl

@[simp] theorem otherVisit_strand (v : Γ.Visit) : (Γ.otherVisit v).2.val = Γ.other v.1 v.2.2 := rfl

theorem otherVisit_ne (v : Γ.Visit) : Γ.otherVisit v ≠ v := fun h =>
  Γ.other_ne v.1 v.2.2 (congrArg (fun w : Γ.Visit => w.2.val) h)

@[simp] theorem otherVisit_otherVisit (v : Γ.Visit) : Γ.otherVisit (Γ.otherVisit v) = v := by
  obtain ⟨x, s, hs⟩ := v
  simp only [otherVisit]
  congr 1
  exact Subtype.ext (Γ.other_other x hs)

theorem visit_eq_or_otherVisit (v w : Γ.Visit) (h : w.1 = v.1) : w = v ∨ w = Γ.otherVisit v := by
  obtain ⟨x, s, hs⟩ := v
  obtain ⟨y, t, ht⟩ := w
  dsimp only at h
  subst h
  rcases (Γ.mem_iff_eq_or_other y hs t).mp ht with h | h
  · left
    congr 1
    exact Subtype.ext h
  · right
    simp only [otherVisit]
    congr 1
    exact Subtype.ext h

theorem otherVisit_unique (v w : Γ.Visit) (h : w.1 = v.1) (hne : w ≠ v) : w = Γ.otherVisit v :=
  (Γ.visit_eq_or_otherVisit v w h).resolve_left hne

theorem otherVisit_injective : Function.Injective Γ.otherVisit := by
  intro v w h
  rw [← Γ.otherVisit_otherVisit v, h, Γ.otherVisit_otherVisit]

/-- The pairing involution of the occurrences of a shadow. -/
def otherVisitPerm : Equiv.Perm Γ.Visit where
  toFun := Γ.otherVisit
  invFun := Γ.otherVisit
  left_inv := Γ.otherVisit_otherVisit
  right_inv := Γ.otherVisit_otherVisit

@[simp] theorem otherVisitPerm_apply (v : Γ.Visit) : Γ.otherVisitPerm v = Γ.otherVisit v := rfl

end Shadow

namespace Diagram

variable (D : Diagram)

theorem underVisit_eq_otherVisit_overVisit (x : D.Γ.Crossing) :
    D.underVisit x = D.Γ.otherVisit (D.overVisit x) := rfl

theorem overVisit_eq_otherVisit_underVisit (x : D.Γ.Crossing) :
    D.overVisit x = D.Γ.otherVisit (D.underVisit x) := by
  rw [underVisit_eq_otherVisit_overVisit, Shadow.otherVisit_otherVisit]

theorem isOver_otherVisit_iff (v : D.Γ.Visit) : D.isOver (D.Γ.otherVisit v) ↔ ¬ D.isOver v := by
  unfold isOver
  rw [Shadow.otherVisit_strand, Shadow.otherVisit_fst]
  constructor
  · intro h hv
    exact D.Γ.other_ne v.1 v.2.2 (h.trans hv.symm)
  · intro hv
    exact (D.Γ.eq_other_of_mem_of_ne v.1 v.2.2 (D.over_mem v.1) (Ne.symm hv)).symm

end Diagram

namespace Shadow

variable (C : PolyComp)

/-- On a one-component shadow, `Shadow.otherVisit` is the accepted `Carrier.visitTwin`
(CarrierVisitTwin.lean, `visitTwin_unique`). -/
theorem singleVisitEquiv_otherVisit (v : (single C).Visit) :
    singleVisitEquiv C ((single C).otherVisit v) = Carrier.visitTwin (singleVisitEquiv C v) := by
  apply Carrier.visitTwin_unique
  · rfl
  · intro h
    exact (single C).otherVisit_ne v ((singleVisitEquiv C).injective h)

theorem singleVisitEquiv_symm_visitTwin (w : SM.Visit C.P) :
    (singleVisitEquiv C).symm (Carrier.visitTwin w) =
      (single C).otherVisit ((singleVisitEquiv C).symm w) := by
  rw [Equiv.symm_apply_eq, singleVisitEquiv_otherVisit, Equiv.apply_symm_apply]

/-- On a one-component shadow, the other strand of a crossing is the strand of the accepted twin
visit. -/
theorem singleStrandEquiv_other (x : (single C).Crossing) {s : (single C).Strand} (hs : s ∈ x.val) :
    singleStrandEquiv C ((single C).other x hs) =
      (Carrier.visitTwin (singleVisitEquiv C ⟨x, ⟨s, hs⟩⟩)).2.val :=
  congrArg (fun w : SM.Visit C.P => w.2.val) (singleVisitEquiv_otherVisit C ⟨x, ⟨s, hs⟩⟩)

/-- The pairing involutions correspond under the one-component identification. -/
theorem singleVisitEquiv_otherVisitPerm :
    (singleVisitEquiv C).symm.trans (((single C).otherVisitPerm).trans (singleVisitEquiv C)) =
      Carrier.visitTwinPerm :=
  Equiv.ext fun w => by
    simp only [Equiv.trans_apply, otherVisitPerm_apply, Carrier.visitTwinPerm_apply,
      singleVisitEquiv_otherVisit, Equiv.apply_symm_apply]

end Shadow

namespace Diagram

variable {C : PolyComp}

/-- The crossing parameter of a one-component diagram is the accepted `crossingParameter` (the edge
parameter of a transverse crossing point is unique: `edgePoint_injective`). -/
theorem crossingParam_single (hP : SM.Generic C.P) (g : (Shadow.single C).Generic)
    (ov : (Shadow.single C).Crossing → (Shadow.single C).Strand) (hov : ∀ x, ov x ∈ x.val)
    (x : (Shadow.single C).Crossing) {s : (Shadow.single C).Strand} (hs : s ∈ x.val) :
    (Diagram.mk (Shadow.single C) g ov hov).crossingParam x hs =
      crossingParameter (Shadow.singleCrossingEquiv C x) (Shadow.singleStrandEquiv C s)
        ((Shadow.mem_singleCrossingEquiv_iff C x s).mpr hs) := by
  have hedge : edge C.P (Shadow.singleStrandEquiv C s) ≠ 0 := g1_edge_ne_zero C.hk hP.1 _
  apply edgePoint_injective hedge
  have h1 := ((Diagram.mk (Shadow.single C) g ov hov).crossingParam_spec x hs).2.2
  have h2 := (crossingParameter_spec (Shadow.singleCrossingEquiv C x) (Shadow.singleStrandEquiv C s)
    ((Shadow.mem_singleCrossingEquiv_iff C x s).mpr hs)).2.2
  change (Shadow.single C).crossingPoint x = edgePoint C.P (Shadow.singleStrandEquiv C s) _ at h1
  rw [← h1, ← h2, Shadow.single_crossingPoint C g]

/-- On the one-component shadow of a generic polygon, `Diagram.visitPt` is the accepted
`visitPosition` (GaussVisits.lean), as the second component of the traversal point. -/
theorem visitPt_single_snd (hP : SM.Generic C.P) (g : (Shadow.single C).Generic)
    (ov : (Shadow.single C).Crossing → (Shadow.single C).Strand) (hov : ∀ x, ov x ∈ x.val)
    (v : (Shadow.single C).Visit) :
    ((Diagram.mk (Shadow.single C) g ov hov).visitPt v).2 =
      visitPosition C.hk hP.1 (Shadow.singleVisitEquiv C v) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact crossingParam_single hP g ov hov v.1 v.2.2

theorem visitPt_single (hP : SM.Generic C.P) (g : (Shadow.single C).Generic)
    (ov : (Shadow.single C).Crossing → (Shadow.single C).Strand) (hov : ∀ x, ov x ∈ x.val)
    (v : (Shadow.single C).Visit) :
    (Diagram.mk (Shadow.single C) g ov hov).visitPt v =
      ⟨0, visitPosition C.hk hP.1 (Shadow.singleVisitEquiv C v)⟩ := by
  apply Sigma.ext
  · exact Subsingleton.elim _ _
  · exact heq_of_eq (visitPt_single_snd hP g ov hov v)

/-- The traversal key of an occurrence is the accepted `visitKey`. -/
theorem traversalKey_visitPt_single (hP : SM.Generic C.P) (g : (Shadow.single C).Generic)
    (ov : (Shadow.single C).Crossing → (Shadow.single C).Strand) (hov : ∀ x, ov x ∈ x.val)
    (v : (Shadow.single C).Visit) :
    traversalKey ((Diagram.mk (Shadow.single C) g ov hov).visitPt v).2 =
      visitKey C.hk hP.1 (Shadow.singleVisitEquiv C v) := by
  rw [visitPt_single_snd hP g ov hov v]
  rfl

/-- The crossing sign of a one-component diagram is the accepted `crossingSign` of the polygon at
the (over, under) pair of edge labels (eq:gauss-cross-sign). -/
theorem sign_single (g : (Shadow.single C).Generic)
    (ov : (Shadow.single C).Crossing → (Shadow.single C).Strand) (hov : ∀ x, ov x ∈ x.val)
    (x : (Shadow.single C).Crossing) :
    (Diagram.mk (Shadow.single C) g ov hov).sign x =
      crossingSign C.P (Shadow.singleStrandEquiv C (ov x))
        (Shadow.singleStrandEquiv C ((Diagram.mk (Shadow.single C) g ov hov).underStrand x)) := rfl

end Diagram

/-! ## 3. Positivity of the derived diagrams; restricted writhe; over bits -/

namespace StrandMap

variable {Γ' Γ : Shadow} (m : StrandMap Γ' Γ)

/-- The occurrence of `Γ` corresponding to an occurrence of `Γ'`. -/
def mapVisit (v : Γ'.Visit) : Γ.Visit := ⟨m.mapCrossing v.1, ⟨m.toFun v.2.val, m.toFun_mem_of_mem v.2.2⟩⟩

@[simp] theorem mapVisit_fst (v : Γ'.Visit) : (m.mapVisit v).1 = m.mapCrossing v.1 := rfl

@[simp] theorem mapVisit_strand (v : Γ'.Visit) : (m.mapVisit v).2.val = m.toFun v.2.val := rfl

theorem mapVisit_injective : Function.Injective m.mapVisit := by
  rintro ⟨x, s, hs⟩ ⟨y, t, ht⟩ h
  have hx : m.mapCrossing x = m.mapCrossing y := congrArg Sigma.fst h
  have hxy : x = y := m.mapCrossing_injective hx
  subst hxy
  have hst : m.toFun s = m.toFun t := by
    have := congrArg (fun w : Γ.Visit => w.2.val) h
    exact this
  congr 1
  exact Subtype.ext (m.inj hst)

theorem mapVisit_otherVisit (v : Γ'.Visit) : m.mapVisit (Γ'.otherVisit v) = Γ.otherVisit (m.mapVisit v) := by
  obtain ⟨x, s, hs⟩ := v
  simp only [mapVisit, Shadow.otherVisit]
  congr 1
  exact Subtype.ext (m.other_mapCrossing hs).symm

end StrandMap

namespace Diagram

variable (D : Diagram)

section Pullback

variable {Γ' : Shadow} (m : StrandMap Γ' D.Γ) (hreg : ∀ i, Regular (Γ'.comp i).P)

/-- The over bit transports along a strand relabelling. -/
theorem pullback_isOver_iff (v : Γ'.Visit) : (D.pullback m hreg).isOver v ↔ D.isOver (m.mapVisit v) := by
  unfold isOver
  rw [StrandMap.mapVisit_strand, StrandMap.mapVisit_fst, ← toFun_pullback_overStrand D m hreg]
  exact ⟨fun h => congrArg m.toFun h, fun h => m.inj h⟩

theorem pullback_overVisit (x : Γ'.Crossing) :
    m.mapVisit ((D.pullback m hreg).overVisit x) = D.overVisit (m.mapCrossing x) := by
  simp only [overVisit, StrandMap.mapVisit]
  congr 1
  exact Subtype.ext (toFun_pullback_overStrand D m hreg x)

theorem pullback_underVisit (x : Γ'.Crossing) :
    m.mapVisit ((D.pullback m hreg).underVisit x) = D.underVisit (m.mapCrossing x) := by
  simp only [underVisit, StrandMap.mapVisit]
  congr 1
  exact Subtype.ext (toFun_pullback_underStrand D m hreg x)

end Pullback

/-- Reversing all components preserves positivity (both directions flip, `det` unchanged). -/
theorem reverse_isPositive_iff (x : D.Γ.reverseShadow.Crossing) :
    D.reverse.IsPositive x ↔ D.IsPositive (D.Γ.reverseCrossingEquiv x) := by
  rw [D.isPositive_iff_sign_eq_one, ← reverse_sign]
  exact D.reverse.isPositive_iff_sign_eq_one x

/-- Block restriction preserves positivity at every internal crossing. -/
theorem restrict_isPositive_iff (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty)
    (x : (D.Γ.restrictShadow B hB).Crossing) :
    (D.restrict B hB).IsPositive x ↔ D.IsPositive ((D.Γ.restrictMap B hB).mapCrossing x) := by
  rw [D.isPositive_iff_sign_eq_one, ← restrict_sign]
  exact (D.restrict B hB).isPositive_iff_sign_eq_one x

/-- The sign of the restriction, indexed through the internal-crossing bijection. -/
theorem restrict_sign_equiv (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty)
    (x : (D.Γ.restrictShadow B hB).Crossing) :
    (D.restrict B hB).sign x = D.sign (D.Γ.restrictCrossingEquiv B hB x).val :=
  restrict_sign D B hB x

/-- The writhe of the block restriction is the sum of the signs of the internal crossings of the
block (mp:stack / mp:lowest). -/
theorem restrict_writhe (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty) :
    (D.restrict B hB).writhe =
      ∑ x : {x : D.Γ.Crossing // ∀ s ∈ x.val, s.1 ∈ B}, (D.sign x.val : ℤ) := by
  unfold writhe
  exact Fintype.sum_equiv (D.Γ.restrictCrossingEquiv B hB) _ _ fun x => by
    rw [restrict_sign_equiv]

theorem reverse_isOver_iff (v : D.Γ.reverseShadow.Visit) :
    D.reverse.isOver v ↔ D.isOver (D.Γ.reverseMap.mapVisit v) :=
  pullback_isOver_iff D D.Γ.reverseMap _ v

theorem mirror_isOver_iff (v : D.Γ.mirrorShadow.Visit) :
    D.mirror.isOver v ↔ D.isOver (D.Γ.mirrorMap.mapVisit v) :=
  pullback_isOver_iff D D.Γ.mirrorMap _ v

theorem restrict_isOver_iff (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty)
    (v : (D.Γ.restrictShadow B hB).Visit) :
    (D.restrict B hB).isOver v ↔ D.isOver ((D.Γ.restrictMap B hB).mapVisit v) :=
  pullback_isOver_iff D (D.Γ.restrictMap B hB) _ v

end Diagram

/-! ## 4. `switch` on the derived diagrams -/

namespace Diagram

variable (D : Diagram)

/-- The sign after a switch, in one formula. -/
theorem switch_sign (x₀ x : D.Γ.Crossing) :
    (D.switch x₀).sign x = if x = x₀ then -D.sign x else D.sign x := by
  by_cases h : x = x₀
  · subst h
    simp [switch_sign_self]
  · simp [h, switch_sign_of_ne D h]

/-- Positivity after a switch: unchanged away from `x₀`, negated at `x₀`. -/
theorem switch_isPositive_iff (x₀ x : D.Γ.Crossing) :
    (D.switch x₀).IsPositive x ↔ (D.IsPositive x ↔ x ≠ x₀) := by
  by_cases h : x = x₀
  · subst h
    rw [switch_isPositive_self]
    simp
  · rw [switch_isPositive_of_ne D h]
    simp [h]

theorem switch_isOver_iff (x₀ : D.Γ.Crossing) (v : D.Γ.Visit) :
    (D.switch x₀).isOver v ↔ (D.isOver v ↔ v.1 ≠ x₀) := by
  unfold isOver
  obtain ⟨x, s, hs⟩ := v
  dsimp only
  by_cases h : x = x₀
  · subst h
    rw [switch_overStrand_self]
    simp only [ne_eq, not_true_eq_false, iff_false]
    constructor
    · intro hv hv'
      exact D.over_ne_under x (hv'.symm.trans hv)
    · intro hv
      exact D.eq_under_of_mem_of_ne x hs hv
  · rw [switch_overStrand_of_ne D h]
    simp [h]

section Pullback

variable {Γ' : Shadow} (m : StrandMap Γ' D.Γ) (hreg : ∀ i, Regular (Γ'.comp i).P)

/-- Switching at a crossing in the image of the relabelling, then pulling back, is pulling back and
switching at the preimage crossing. -/
theorem pullback_switch_of_mapCrossing_eq {x₀ : D.Γ.Crossing} {y₀ : Γ'.Crossing}
    (h : m.mapCrossing y₀ = x₀) :
    (D.switch x₀).pullback m hreg = (D.pullback m hreg).switch y₀ := by
  subst h
  refine ext_overStrand ?_ ?_
  · rfl
  apply heq_of_eq
  funext y
  change Γ'.Crossing at y
  apply m.inj
  have e₁ : m.toFun (((D.switch (m.mapCrossing y₀)).pullback m hreg).overStrand y) =
      (D.switch (m.mapCrossing y₀)).overStrand (m.mapCrossing y) :=
    toFun_pullback_overStrand (D.switch (m.mapCrossing y₀)) m hreg y
  refine e₁.trans ?_
  by_cases hy : y = y₀
  · subst hy
    have e₂ : m.toFun ((D.pullback m hreg).underStrand y) = D.underStrand (m.mapCrossing y) :=
      toFun_pullback_underStrand D m hreg y
    have e₃ : ((D.pullback m hreg).switch y).overStrand y = (D.pullback m hreg).underStrand y :=
      switch_overStrand_self (D.pullback m hreg) y
    rw [switch_overStrand_self, e₃, e₂]
  · have e₂ : m.toFun ((D.pullback m hreg).overStrand y) = D.overStrand (m.mapCrossing y) :=
      toFun_pullback_overStrand D m hreg y
    have e₃ : ((D.pullback m hreg).switch y₀).overStrand y = (D.pullback m hreg).overStrand y :=
      switch_overStrand_of_ne (D.pullback m hreg) hy
    rw [e₃, e₂, switch_overStrand_of_ne D]
    intro hxy
    exact hy (m.mapCrossing_injective hxy)

/-- Switching at a crossing outside the image of the relabelling is invisible to the pullback. -/
theorem pullback_switch_of_not_mem_range {x₀ : D.Γ.Crossing} (h : ∀ y, m.mapCrossing y ≠ x₀) :
    (D.switch x₀).pullback m hreg = D.pullback m hreg := by
  refine ext_overStrand ?_ ?_
  · rfl
  apply heq_of_eq
  funext y
  apply m.inj
  have e₁ : m.toFun (((D.switch x₀).pullback m hreg).overStrand y) =
      (D.switch x₀).overStrand (m.mapCrossing y) :=
    toFun_pullback_overStrand (D.switch x₀) m hreg y
  have e₂ : m.toFun ((D.pullback m hreg).overStrand y) = D.overStrand (m.mapCrossing y) :=
    toFun_pullback_overStrand D m hreg y
  rw [e₁, e₂, switch_overStrand_of_ne _ (h y)]

end Pullback

/-- `switch` commutes with `reverse`. -/
theorem switch_reverse (x₀ : D.Γ.Crossing) :
    (D.switch x₀).reverse = D.reverse.switch (D.Γ.reverseCrossingEquiv.symm x₀) :=
  pullback_switch_of_mapCrossing_eq D D.Γ.reverseMap _
    ((D.Γ.reverseCrossingEquiv_apply _).symm.trans (Equiv.apply_symm_apply _ _))

theorem reverse_switch (y₀ : D.Γ.reverseShadow.Crossing) :
    D.reverse.switch y₀ = (D.switch (D.Γ.reverseCrossingEquiv y₀)).reverse :=
  (pullback_switch_of_mapCrossing_eq D D.Γ.reverseMap _ (D.Γ.reverseCrossingEquiv_apply y₀).symm).symm

/-- `switch` commutes with `mirror`. -/
theorem switch_mirror (x₀ : D.Γ.Crossing) :
    (D.switch x₀).mirror = D.mirror.switch (D.Γ.mirrorCrossingEquiv.symm x₀) :=
  pullback_switch_of_mapCrossing_eq D D.Γ.mirrorMap _
    ((D.Γ.mirrorCrossingEquiv_apply _).symm.trans (Equiv.apply_symm_apply _ _))

theorem mirror_switch (y₀ : D.Γ.mirrorShadow.Crossing) :
    D.mirror.switch y₀ = (D.switch (D.Γ.mirrorCrossingEquiv y₀)).mirror :=
  (pullback_switch_of_mapCrossing_eq D D.Γ.mirrorMap _ (D.Γ.mirrorCrossingEquiv_apply y₀).symm).symm

/-- Switching an internal crossing of the block commutes with the restriction. -/
theorem switch_restrict_of_internal (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty)
    (y₀ : (D.Γ.restrictShadow B hB).Crossing) :
    (D.switch ((D.Γ.restrictMap B hB).mapCrossing y₀)).restrict B hB = (D.restrict B hB).switch y₀ :=
  pullback_switch_of_mapCrossing_eq D (D.Γ.restrictMap B hB) _ rfl

theorem restrict_switch (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty)
    (y₀ : (D.Γ.restrictShadow B hB).Crossing) :
    (D.restrict B hB).switch y₀ = (D.switch ((D.Γ.restrictMap B hB).mapCrossing y₀)).restrict B hB :=
  (D.switch_restrict_of_internal B hB y₀).symm

/-- Switching a crossing that is not internal to the block leaves the restriction unchanged. -/
theorem switch_restrict_of_external (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty) {x₀ : D.Γ.Crossing}
    (h : ¬ ∀ s ∈ x₀.val, s.1 ∈ B) : (D.switch x₀).restrict B hB = D.restrict B hB :=
  pullback_switch_of_not_mem_range D (D.Γ.restrictMap B hB) _ fun y hy =>
    h ((D.Γ.restrict_mapCrossing_range_iff B hB x₀).mp ⟨y, hy⟩)

/-! ### Traversal points of the derived diagrams -/

/-- The crossing parameter of the mirror image is the original one (`edgePoint_reflect`). -/
theorem crossingParam_mirror (x : D.Γ.mirrorShadow.Crossing) {s : D.Γ.mirrorShadow.Strand}
    (hs : s ∈ x.val) :
    D.mirror.crossingParam x hs =
      D.crossingParam (D.Γ.mirrorCrossingEquiv x) (D.Γ.mirrorMap.toFun_mem_of_mem hs) := by
  have hedge : edge (D.Γ.comp s.1).P s.2 ≠ 0 :=
    ((regular_iff_edges _).mp (D.generic.regular s.1) s.2).1
  apply edgePoint_injective hedge
  have h1 := (D.mirror.crossingParam_spec x hs).2.2
  have h2 := (D.crossingParam_spec (D.Γ.mirrorCrossingEquiv x)
    (D.Γ.mirrorMap.toFun_mem_of_mem hs)).2.2
  have h3 := D.Γ.mirrorMap.crossingPoint_mapCrossing D.generic x
  change D.Γ.mirrorShadow.crossingPoint x = edgePoint (reflect ∘ (D.Γ.comp s.1).P) s.2 _ at h1
  rw [edgePoint_reflect] at h1
  change D.Γ.crossingPoint (D.Γ.mirrorMap.mapCrossing x) = edgePoint (D.Γ.comp s.1).P s.2 _ at h2
  change D.Γ.crossingPoint (D.Γ.mirrorMap.mapCrossing x) =
    reflect (D.Γ.mirrorShadow.crossingPoint x) at h3
  rw [h3, h1, reflect_reflect] at h2
  exact h2

/-- The crossing parameter of the reversed diagram is `1 - τ` (`edgePoint_reversal`). -/
theorem crossingParam_reverse (x : D.Γ.reverseShadow.Crossing) {s : D.Γ.reverseShadow.Strand}
    (hs : s ∈ x.val) :
    D.reverse.crossingParam x hs =
      1 - D.crossingParam (D.Γ.reverseCrossingEquiv x) (D.Γ.reverseMap.toFun_mem_of_mem hs) := by
  have hedge : edge (D.Γ.comp s.1).P (1 - s.2) ≠ 0 :=
    ((regular_iff_edges _).mp (D.generic.regular s.1) _).1
  have h1 := (D.reverse.crossingParam_spec x hs).2.2
  have h2 := (D.crossingParam_spec (D.Γ.reverseCrossingEquiv x)
    (D.Γ.reverseMap.toFun_mem_of_mem hs)).2.2
  have h3 := D.Γ.reverseMap.crossingPoint_mapCrossing D.generic x
  change D.Γ.reverseShadow.crossingPoint x = edgePoint (reversal (D.Γ.comp s.1).P) s.2 _ at h1
  rw [edgePoint_reversal] at h1
  change D.Γ.crossingPoint (D.Γ.reverseMap.mapCrossing x) =
    edgePoint (D.Γ.comp s.1).P (1 - s.2) _ at h2
  change D.Γ.crossingPoint (D.Γ.reverseMap.mapCrossing x) = D.Γ.reverseShadow.crossingPoint x at h3
  rw [h3, h1] at h2
  have := edgePoint_injective hedge h2
  linarith

/-- The crossing parameter of a block restriction is the original one (same polygons). -/
theorem crossingParam_restrict (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty)
    (x : (D.Γ.restrictShadow B hB).Crossing) {s : (D.Γ.restrictShadow B hB).Strand} (hs : s ∈ x.val) :
    (D.restrict B hB).crossingParam x hs =
      D.crossingParam ((D.Γ.restrictMap B hB).mapCrossing x)
        ((D.Γ.restrictMap B hB).toFun_mem_of_mem hs) := by
  have hedge : edge (D.Γ.comp (B.orderEmbOfFin rfl s.1)).P s.2 ≠ 0 :=
    ((regular_iff_edges _).mp (D.generic.regular _) _).1
  apply edgePoint_injective hedge
  have h1 := ((D.restrict B hB).crossingParam_spec x hs).2.2
  have h2 := (D.crossingParam_spec ((D.Γ.restrictMap B hB).mapCrossing x)
    ((D.Γ.restrictMap B hB).toFun_mem_of_mem hs)).2.2
  have h3 := (D.Γ.restrictMap B hB).crossingPoint_mapCrossing D.generic x
  change (D.Γ.restrictShadow B hB).crossingPoint x =
    edgePoint (D.Γ.comp (B.orderEmbOfFin rfl s.1)).P s.2 _ at h1
  change D.Γ.crossingPoint ((D.Γ.restrictMap B hB).mapCrossing x) =
    edgePoint (D.Γ.comp (B.orderEmbOfFin rfl s.1)).P s.2 _ at h2
  change D.Γ.crossingPoint ((D.Γ.restrictMap B hB).mapCrossing x) =
    (D.Γ.restrictShadow B hB).crossingPoint x at h3
  exact h1.symm.trans (h3.symm.trans h2)

/-- The traversal point of an occurrence of the mirror image is that of the original occurrence
(the parameter circles are unchanged by reflection). -/
theorem mirror_visitPt (v : D.Γ.mirrorShadow.Visit) :
    D.mirror.visitPt v = D.visitPt (D.Γ.mirrorMap.mapVisit v) :=
  Sigma.ext rfl (heq_of_eq (Prod.ext rfl (Subtype.ext (D.crossingParam_mirror v.1 v.2.2))))

/-- The traversal point of an occurrence of the reversed diagram: same component, the edge label of
the reversed strand (`visitPt_edge`; the original label is `1 - a`, `Shadow.reverseMap_toFun`), and
parameter `1 - τ` for the original parameter `τ`. -/
theorem reverse_visitPt_fst (v : D.Γ.reverseShadow.Visit) :
    (D.reverse.visitPt v).1 = (D.visitPt (D.Γ.reverseMap.mapVisit v)).1 := rfl

theorem reverse_visitPt_param (v : D.Γ.reverseShadow.Visit) :
    (D.reverse.visitPt v).2.2.val = 1 - (D.visitPt (D.Γ.reverseMap.mapVisit v)).2.2.val :=
  D.crossingParam_reverse v.1 v.2.2

/-- The traversal point of an occurrence of a block restriction: the component is reindexed by the
block, the traversal point on that component is unchanged. -/
theorem restrict_visitPt_fst (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty)
    (v : (D.Γ.restrictShadow B hB).Visit) :
    B.orderEmbOfFin rfl ((D.restrict B hB).visitPt v).1 =
      (D.visitPt ((D.Γ.restrictMap B hB).mapVisit v)).1 := rfl

theorem restrict_visitPt_snd (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty)
    (v : (D.Γ.restrictShadow B hB).Visit) :
    ((D.restrict B hB).visitPt v).2 = (D.visitPt ((D.Γ.restrictMap B hB).mapVisit v)).2 :=
  Prod.ext rfl (Subtype.ext (D.crossingParam_restrict B hB v.1 v.2.2))

/-- Writhe bookkeeping on the derived diagrams. -/
theorem switch_reverse_writhe (x₀ : D.Γ.Crossing) :
    (D.switch x₀).reverse.writhe = D.writhe - 2 * (D.sign x₀ : ℤ) := by
  rw [reverse_writhe, switch_writhe]

theorem switch_mirror_writhe (x₀ : D.Γ.Crossing) :
    (D.switch x₀).mirror.writhe = -D.writhe + 2 * (D.sign x₀ : ℤ) := by
  rw [mirror_writhe, switch_writhe]
  ring

end Diagram

end

/-! ## Axiom audit -/


end SM.Link
