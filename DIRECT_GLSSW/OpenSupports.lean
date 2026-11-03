import ActiveArcGammaM

set_option autoImplicit false
namespace DirectGLSSW.ActiveArc.OpenSupports
open DirectGLSSW.ActiveArc DirectGLSSW.PermutationOrbits
open DirectGLSSW.ActiveArc.Nonalternation DirectGLSSW.ActiveArc.RetainedWords
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : ActiveArc.Regular q)

/-- A smoothing site is a pair of actual arc edges. The auxiliary
terminal-to-start segment has no edge label and cannot belong to a support. -/
theorem support_sites_physical (S : Support q hR) (c : ActiveArc.Crossing q)
    (_hc : c ∈ S.val) :
    c.val.1.val < n+1 ∧ c.val.2.val < n+1 := by
  exact ⟨c.val.1.isLt, c.val.2.isLt⟩

/-- The two endpoints of the actual arc lie in the same distinguished
incoming-smoothing orbit. All other components avoid both endpoints. -/
theorem unique_open_endpoint_component (S : Support q hR) :
    componentOf (ActiveArc.incoming q hR.noTriple S.val) (ActiveArc.start q) =
        ActiveArc.openComponent q hR.noTriple S.val ∧
    componentOf (ActiveArc.incoming q hR.noTriple S.val) (ActiveArc.terminal q) =
        ActiveArc.openComponent q hR.noTriple S.val ∧
    ∀ C : Component (ActiveArc.incoming q hR.noTriple S.val),
      C ≠ ActiveArc.openComponent q hR.noTriple S.val →
      ∀ x : Fibre (ActiveArc.incoming q hR.noTriple S.val) C,
        x.val ≠ ActiveArc.start q ∧ x.val ≠ ActiveArc.terminal q := by
  refine ⟨rfl,ActiveArc.component_endpoints_eq q hR.noTriple S.val,?_⟩
  intro C hC x
  exact ActiveArc.closedComponent_avoids_endpoints q hR.noTriple S.val C hC x

/-- The retained point word of the unique open orbit is an actual smoothing
of the physical arc, beginning and ending at the original endpoints. -/
theorem open_word_preserves_endpoints (S : Support q hR) :
    2 ≤ openCount q hR S.val ∧
    vertex q hR S.val (ActiveArc.start q) (openFirst q hR S.val) =
        q ⟨0, by omega⟩ ∧
    vertex q hR S.val (ActiveArc.start q) (openLast q hR S.val) =
        q ⟨n+1, by omega⟩ := by
  exact ⟨open_count_ge_two q hR S.val,
    open_vertex_first q hR S.val,
    open_vertex_last q hR S.val⟩

/-- Every consecutive side of the actual open component is a positive
subsegment of a real arc edge; there is no terminal-to-start side. -/
theorem open_word_sides_physical (S : Support q hR)
    (i : Fin (openCount q hR S.val))
    (hi : i.val+1 < openCount q hR S.val) :
    ∃ e : Fin (n+1), ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      vertex q hR S.val (ActiveArc.start q) i =
        affinePoint (q e.castSucc) (q e.succ) a ∧
      vertex q hR S.val (ActiveArc.start q) ⟨i.val+1, hi⟩ =
        affinePoint (q e.castSucc) (q e.succ) b := by
  obtain ⟨e,a,b,ha,hab,hb,hfirst,hlast,_⟩ :=
    open_vertex_side_physical q hR S.val i hi
  exact ⟨e,a,b,ha,hab,hb,hfirst,hlast⟩

/-- Every side, including the cyclic wrap, of any other actual component
is a positive subsegment of a real arc edge. Its orbit contains no endpoint. -/
theorem closed_word_sides_physical (S : Support q hR)
    (C : Component (ActiveArc.incoming q hR.noTriple S.val))
    (hC : C ≠ ActiveArc.openComponent q hR.noTriple S.val)
    (i : Fin (Fintype.card (Corner q hR S.val
      (ActiveArc.closedRoot q hR.noTriple S.val C hC)))) :
    ∃ e : Fin (n+1), ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      vertex q hR S.val (ActiveArc.closedRoot q hR.noTriple S.val C hC) i =
        affinePoint (q e.castSucc) (q e.succ) a ∧
      vertex q hR S.val (ActiveArc.closedRoot q hR.noTriple S.val C hC)
        (cyclicSuccessor i) = affinePoint (q e.castSucc) (q e.succ) b := by
  obtain ⟨e,a,b,ha,hab,hb,hfirst,hlast,_⟩ :=
    closed_vertex_side_physical q hR S.val C hC i
  exact ⟨e,a,b,ha,hab,hb,hfirst,hlast⟩

/-- Exact source open-smoothing component claim on physical arc sites: one
endpoint-bearing open component and exactly `|S|` other, closed components. -/
theorem one_open_and_card_closed (S : Support q hR) :
    (componentOf (ActiveArc.incoming q hR.noTriple S.val) (ActiveArc.start q) =
      componentOf (ActiveArc.incoming q hR.noTriple S.val) (ActiveArc.terminal q)) ∧
    (∀ C : Component (ActiveArc.incoming q hR.noTriple S.val),
      C ≠ ActiveArc.openComponent q hR.noTriple S.val →
      ∀ x : Fibre (ActiveArc.incoming q hR.noTriple S.val) C,
        x.val ≠ ActiveArc.start q ∧ x.val ≠ ActiveArc.terminal q) ∧
    (Finset.univ.erase (ActiveArc.openComponent q hR.noTriple S.val)).card =
      S.val.card ∧
    (vertex q hR S.val (ActiveArc.start q) (openFirst q hR S.val) =
      q ⟨0, by omega⟩ ∧
     vertex q hR S.val (ActiveArc.start q) (openLast q hR S.val) =
      q ⟨n+1, by omega⟩) := by
  have hOpen := unique_open_endpoint_component q hR S
  have hWord := open_word_preserves_endpoints q hR S
  exact ⟨hOpen.1.trans hOpen.2.1.symm, hOpen.2.2,
    closed_component_count q hR S, hWord.2⟩

end DirectGLSSW.ActiveArc.OpenSupports






