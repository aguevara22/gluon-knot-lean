import SM.LinkDiagram

/-! Source mp:zero-link (reference/SM/sm-3-statesum.tex:1538-1545, frame SM15): mixed signed crossings in
a stack. Main declaration: `SM.zero_link`.

Notation (namespace `SM.Link`): "an actual generic oriented plane diagram" is `D : Diagram`; its
components are `Fin D.Γ.c`; a strand `s : D.Γ.Strand` lies on component `s.1` with direction `D.Γ.dir s`
(the oriented edge vector `u`); "the transverse intersections of two distinct components `i ≠ j`, in this
fixed component order" are the crossings `{s, t}` with `s` on `i` and `t` on `j` (`Shadow.MixedPair`; each
mixed crossing between `i` and `j` is exactly one such ordered pair), and `sgn det(u₁, u₂)` is
`SignType.sign (det (D.Γ.dir s) (D.Γ.dir t))`; "the decorated crossing signs" are `D.sign x =
sgn det(u_over, u_under)` (def:positive-lift); "one component is always over the other" is: at every
mixed crossing the over strand lies on `i`, or at every mixed crossing it lies on `j`. -/

namespace SM

open SM.Link Classical

namespace Link.Shadow

/-- The ordered strand pairs `(s, t)` with `s` on component `i`, `t` on component `j`, forming a
crossing: the transverse intersections of the two components in the fixed order `(i, j)`. -/
def MixedPair (Γ : Shadow) (i j : Fin Γ.c) (s t : Γ.Strand) : Prop :=
  s.1 = i ∧ t.1 = j ∧ Γ.IsCrossing {s, t}

end Link.Shadow

/-- The sum of the decorated signs over the mixed crossings between components `i` and `j`. -/
noncomputable def mixedSignSum (D : Diagram) (i j : Fin D.Γ.c) : ℤ :=
  ∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand,
    if h : D.Γ.MixedPair i j s t then ((D.sign ⟨{s, t}, h.2.2⟩ : SignType) : ℤ) else 0

/-- mp:zero-link as printed. -/
structure ZeroLinkData : Prop where
  /-- "For two distinct components of an actual generic oriented plane diagram, the sum of
  `sgn det(u₁, u₂)` over their transverse intersections, in this fixed component order, is zero." -/
  fixed_order_sum : ∀ (D : Diagram) (i j : Fin D.Γ.c), i ≠ j →
    (∑ s : D.Γ.Strand, ∑ t : D.Γ.Strand,
      if D.Γ.MixedPair i j s t then ((SignType.sign (det (D.Γ.dir s) (D.Γ.dir t)) : SignType) : ℤ)
      else 0) = 0
  /-- "Consequently the half-sum of decorated crossing signs is an integer". -/
  half_sum_integer : ∀ (D : Diagram) (i j : Fin D.Γ.c), i ≠ j → ∃ k : ℤ, mixedSignSum D i j = 2 * k
  /-- "and it is zero if one component is always over the other." -/
  over_constant : ∀ (D : Diagram) (i j : Fin D.Γ.c), i ≠ j →
    ((∀ (s t : D.Γ.Strand) (h : D.Γ.MixedPair i j s t), D.overStrand ⟨{s, t}, h.2.2⟩ = s) ∨
     (∀ (s t : D.Γ.Strand) (h : D.Γ.MixedPair i j s t), D.overStrand ⟨{s, t}, h.2.2⟩ = t)) →
    mixedSignSum D i j = 0

theorem zero_link : ZeroLinkData := by
  sorry

end SM
