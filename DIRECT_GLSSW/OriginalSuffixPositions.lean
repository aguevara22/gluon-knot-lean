import MarkedSuffixEndpoint
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits
attribute [local instance] Classical.propDecidable
namespace MarkedParentTrace
variable {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
include h c hc

/-- The actual root-origin equation at the selected branch, without any historical branch-order assumption. -/
theorem suffixRoot_origin :
    h.arcOrigin (markedOrbitRoot t (t.1.incoming c (firstVisitedBranch t.2.1 c))) =
      some (markedOrbitRoot s (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c))) := by
  have hh := h.arcOrigin_root c
  rw [markedOrbitRoot_eq t (t.1.incoming c 0) (t.1.incoming c (firstVisitedBranch t.2.1 c)),
    markedOrbitRoot_eq s (s.1.incoming (h.crossingOrigin c) 0)
      (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c))] at hh
  exact hh

/-- No positive suffix position can be the original stored root: ancestry is injective and the actual current visit is positive. -/
theorem suffixOriginalArc_ne_root
    (i : Fin (markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c))))
    (hi : 0 < i.val) :
    h.suffixOriginalArc c hc i ≠
      markedOrbitRoot s (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) := by
  intro he
  have hs := h.suffixOriginalArc_spec c hc i
  rw [he] at hs
  have heq := h.arcOrigin_some_injective _ _ _ hs (h.suffixRoot_origin c hc)
  have hp := congrArg (visitPosition t.2.1) heq
  rw [markedSuffixArc_visitPosition,markedOrbitRoot_visitPosition] at hp
  omega

/-- Original rooted positions are the exact unwrapped consecutive positions; this derives the missing original order. -/
theorem suffixOriginalArc_visitPosition
    (i : Fin (markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c)))) :
    visitPosition s.2.1 (h.suffixOriginalArc c hc i) =
      visitPosition s.2.1 (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) + i.val := by
  have H : ∀ n (hn : n < markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c))),
      visitPosition s.2.1 (h.suffixOriginalArc c hc ⟨n,hn⟩) =
        visitPosition s.2.1 (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) + n := by
    intro n
    induction n with
    | zero =>
      intro hn
      rw [h.suffixOriginalArc_zero c hc,Nat.add_zero]
    | succ n ih =>
      intro hn
      have hn' : n < markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c)) := by omega
      have hs := h.suffixOriginalArc_successor c hc ⟨n,hn'⟩ ⟨n+1,hn⟩ rfl
      have hne : s.1.continuation (h.suffixOriginalArc c hc ⟨n,hn'⟩) ≠
          (s.2.1.baseArc (componentOf s.1.continuation (h.suffixOriginalArc c hc ⟨n,hn'⟩))).val := by
        rw [hs]
        change h.suffixOriginalArc c hc ⟨n+1,hn⟩ ≠ markedOrbitRoot s _
        rw [markedOrbitRoot_eq s _ (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c))]
        exact h.suffixOriginalArc_ne_root c hc ⟨n+1,hn⟩ (Nat.succ_pos _)
      rw [← hs,visitPosition_continuation_of_ne_root s.1 s.2.1 _ hne,ih hn']
      omega
  exact H i.val i.isLt

/-- Final wrap of the original ancestor chain is the actual stored original root. -/
theorem suffixOriginalArc_last_continuation :
    s.1.continuation (h.suffixOriginalArc c hc
      ⟨markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c))-1,
        by have := markedSuffixSize_pos t (t.1.incoming c (firstVisitedBranch t.2.1 c));omega⟩) =
      markedOrbitRoot s (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) :=
  h.arcOrigin_continuation _ _ _ _ (markedSuffixArc_last_continuation t _)
    (h.suffixOriginalArc_spec c hc _) (h.suffixRoot_origin c hc)

/-- No original arc is omitted from the terminal suffix: its actual length is unchanged. -/
theorem suffixOriginalArc_length :
    markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c)) =
      markedSuffixSize s (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) := by
  let i : Fin (markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c))) :=
    ⟨markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c))-1,
      by have := markedSuffixSize_pos t (t.1.incoming c (firstVisitedBranch t.2.1 c));omega⟩
  have hp := h.suffixOriginalArc_visitPosition c hc i
  have hl := marked_visitPosition_of_continuation_root s
    (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c))
    (h.suffixOriginalArc c hc i) (h.suffixOriginalArc_last_continuation c hc)
  have hm := markedSuffixSize_pos t (t.1.incoming c (firstVisitedBranch t.2.1 c))
  change visitPosition s.2.1 (h.suffixOriginalArc c hc i) =
    visitPosition s.2.1 (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) +
      (markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c))-1) at hp
  change markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c)) =
    markedOrbitSize s (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) -
      visitPosition s.2.1 (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c))
  omega

end MarkedParentTrace
end DirectGLSSW.HOMFLY
