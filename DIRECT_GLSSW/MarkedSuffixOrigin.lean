import MarkedSuffixCoordinates
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- No processed mark lies at or beyond the actual first incoming port of a bad crossing. -/
theorem markedSuffixArc_not_marked (t : MarkedParentState) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c)
    (i : Fin (markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c)))) :
    markedSuffixArc t (t.1.incoming c (firstVisitedBranch t.2.1 c)) i ∉ t.2.2.marks := by
  intro hm
  have hh := t.2.2.mark_before_cut c hc ⟨_,hm⟩
  rw [markedSuffixArc_visitPosition] at hh
  omega

namespace MarkedParentTrace
variable {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
include h c hc

theorem suffixArc_has_origin
    (i : Fin (markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c)))) :
    ∃ a : Fin s.1.nArc,
      h.arcOrigin (markedSuffixArc t (t.1.incoming c (firstVisitedBranch t.2.1 c)) i) = some a := by
  cases ho : h.arcOrigin (markedSuffixArc t (t.1.incoming c (firstVisitedBranch t.2.1 c)) i) with
  | some a => exact ⟨a,rfl⟩
  | none => exact (markedSuffixArc_not_marked t c hc i (h.arcOrigin_none_marked _ ho)).elim

/-- Actual original ancestor, chosen only after proving existence; no fallback label. -/
def suffixOriginalArc
    (i : Fin (markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c)))) : Fin s.1.nArc :=
  Classical.choose (h.suffixArc_has_origin c hc i)

theorem suffixOriginalArc_spec
    (i : Fin (markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c)))) :
    h.arcOrigin (markedSuffixArc t (t.1.incoming c (firstVisitedBranch t.2.1 c)) i) =
      some (h.suffixOriginalArc c hc i) :=
  Classical.choose_spec (h.suffixArc_has_origin c hc i)

theorem suffixOriginalArc_zero :
    h.suffixOriginalArc c hc ⟨0,markedSuffixSize_pos t _⟩ =
      s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c) := by
  have hh := h.suffixOriginalArc_spec c hc ⟨0,markedSuffixSize_pos t _⟩
  rw [markedSuffixArc_zero,h.crossingOrigin_incoming] at hh
  exact (Option.some.inj hh).symm

theorem suffixOriginalArc_successor
    (i j : Fin (markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c))))
    (hij : j.val=i.val+1) :
    s.1.continuation (h.suffixOriginalArc c hc i) = h.suffixOriginalArc c hc j :=
  h.arcOrigin_continuation _ _ _ _ (markedSuffixArc_successor t _ i j hij)
    (h.suffixOriginalArc_spec c hc i) (h.suffixOriginalArc_spec c hc j)

theorem suffixOriginalArc_injective : Function.Injective (h.suffixOriginalArc c hc) := by
  intro i j hij
  apply markedSuffixArc_injective t (t.1.incoming c (firstVisitedBranch t.2.1 c))
  exact h.arcOrigin_some_injective _ _ _ (h.suffixOriginalArc_spec c hc i)
    (hij.symm ▸ h.suffixOriginalArc_spec c hc j)

/-- Literal continuation powers in the starting diagram, with the actual selected
branch label. This does not assume global first-visited-branch preservation. -/
theorem suffixOriginalArc_eq_pow
    (i : Fin (markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c)))) :
    h.suffixOriginalArc c hc i = (s.1.continuation ^ i.val)
      (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) := by
  have H : ∀ n (hn : n < markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c))),
      h.suffixOriginalArc c hc ⟨n,hn⟩ = (s.1.continuation ^ n)
        (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) := by
    intro n
    induction n with
    | zero => intro hn; exact h.suffixOriginalArc_zero c hc
    | succ n ih =>
      intro hn
      have hn' : n < markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c)) := by omega
      rw [← h.suffixOriginalArc_successor c hc ⟨n,hn'⟩ ⟨n+1,hn⟩ rfl,ih hn',
        pow_succ',Equiv.Perm.mul_apply]
  exact H i.val i.isLt

end MarkedParentTrace
end DirectGLSSW.HOMFLY
