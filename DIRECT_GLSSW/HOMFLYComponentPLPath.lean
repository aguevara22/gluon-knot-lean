import DirectGLSSW.HOMFLY.PLDiagrams
import Mathlib.Topology.Path

/-!
Source-only work in progress. Not compiled, exported, or accepted.

The actual polygonal component trace is built by concatenating its actual
straight arcs. Closedness follows from the continuation orbit, not a field
asserting that an arbitrary curve represents the diagram. This carrier does
not assert simplicity, Reidemeister reduction, or evaluator invariance.
-/

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
noncomputable section

def diagramArcPath (D : PLLinkDiagram) (e : Fin D.nArc) :
    Path (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) where
  toFun t := affinePoint (D.vertexPoint (D.arcSource e))
    (D.vertexPoint (D.arcTarget e)) t.val
  continuous_toFun := by
    unfold affinePoint
    fun_prop
  source' := affinePoint_zero _ _
  target' := affinePoint_one _ _

@[simp] theorem diagramArcPath_apply (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : unitInterval) :
    diagramArcPath D e t = affinePoint (D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcTarget e)) t.val := rfl

theorem diagramArcPath_injective (D : PLLinkDiagram) (e : Fin D.nArc) :
    Function.Injective (diagramArcPath D e) := by
  intro s t h
  apply Subtype.ext
  apply affinePoint_injective (D.vertexPoint (D.arcSource e))
    (D.vertexPoint (D.arcTarget e))
    (fun he => D.arc_endpoints_distinct e (D.vertexPoint_injective he))
  exact h

def continuationArcPath (D : PLLinkDiagram) (e : Fin D.nArc) :
    Path (D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcSource (D.continuation e))) :=
  (diagramArcPath D e).cast rfl
    (congrArg D.vertexPoint (D.continuation_incidence e).symm)

def continuationPath (D : PLLinkDiagram) (e : Fin D.nArc) :
    (n : ℕ) → Path (D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcSource ((D.continuation ^ n) e)))
  | 0 => (Path.refl _).cast rfl (by simp)
  | 1 => (continuationArcPath D e).cast rfl (by simp)
  | n + 2 =>
      ((continuationPath D e (n+1)).trans
        (continuationArcPath D ((D.continuation ^ (n+1)) e))).cast rfl
          (by simp only [pow_succ', Perm.mul_apply])

def componentArcLength (D : PLLinkDiagram) (e : Fin D.nArc) : ℕ :=
  Fintype.card (Fibre D.continuation (componentOf D.continuation e))

theorem componentArcLength_pos (D : PLLinkDiagram) (e : Fin D.nArc) :
    0 < componentArcLength D e := by
  exact Fintype.card_pos

theorem continuation_pow_componentArcLength (D : PLLinkDiagram) (e : Fin D.nArc) :
    (D.continuation ^ componentArcLength D e) e = e := by
  classical
  let C := componentOf D.continuation e
  let x : Fibre D.continuation C := ⟨e, rfl⟩
  have hc : (fibrePerm D.continuation C).IsCycleOn
      (Finset.univ : Finset (Fibre D.continuation C)) := by
    simpa using fibrePerm_isCycleOn D.continuation C
  have hp := congrArg Subtype.val (hc.pow_card_apply (Finset.mem_univ x))
  simpa only [Finset.card_univ, fibrePerm_pow_apply_val] using hp

def componentPLLoop (D : PLLinkDiagram) (e : Fin D.nArc) :
    Path (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcSource e)) :=
  (continuationPath D e (componentArcLength D e)).cast rfl
    (congrArg (fun a => D.vertexPoint (D.arcSource a))
      (continuation_pow_componentArcLength D e).symm)

theorem mem_range_continuationPath (D : PLLinkDiagram) (e : Fin D.nArc)
    (n : ℕ) (z : PlanarPoint ℝ) :
    z ∈ Set.range (continuationPath D e n) ↔
      z = D.vertexPoint (D.arcSource e) ∨
        ∃ k : ℕ, k < n ∧ z ∈ Set.range (diagramArcPath D ((D.continuation ^ k) e)) := by
  induction n with
  | zero =>
      simp only [continuationPath, Path.cast_coe, Path.refl_range,
        Set.mem_singleton_iff, Nat.not_lt_zero, false_and, exists_false, or_false]
  | succ n ih =>
      cases n with
      | zero =>
          simp only [continuationPath, continuationArcPath, Path.cast_coe]
          constructor
          · intro hz
            exact Or.inr ⟨0, Nat.zero_lt_one, by simpa using hz⟩
          · rintro (hz | ⟨k,hk,hz⟩)
            · exact ⟨0, (diagramArcPath D e).source.trans hz.symm⟩
            · have hk0 : k = 0 := by omega
              subst k
              simpa only [pow_zero, Perm.one_apply] using hz
      | succ n =>
        simp only [continuationPath, Path.cast_coe, Path.trans_range, Set.mem_union,
          continuationArcPath, Path.cast_coe]
        rw [ih]
        constructor
        · rintro ((hz | ⟨k,hk,hz⟩) | hz)
          · exact Or.inl hz
          · exact Or.inr ⟨k, Nat.lt.step hk, hz⟩
          · exact Or.inr ⟨n+1, Nat.lt_succ_self (n+1), hz⟩
        · rintro (hz | ⟨k,hk,hz⟩)
          · exact Or.inl (Or.inl hz)
          · by_cases hkn : k < n+1
            · exact Or.inl (Or.inr ⟨k,hkn,hz⟩)
            · have heq : k = n+1 := by omega
              subst k
              exact Or.inr hz

theorem componentPLLoop_trace (D : PLLinkDiagram) (e : Fin D.nArc)
    (z : PlanarPoint ℝ) :
    z ∈ Set.range (componentPLLoop D e) ↔
      ∃ f : Fin D.nArc, componentOf D.continuation f = componentOf D.continuation e ∧
        z ∈ Set.range (diagramArcPath D f) := by
  classical
  simp only [componentPLLoop, Path.cast_coe, mem_range_continuationPath]
  constructor
  · rintro (hz | ⟨k,hk,hz⟩)
    · refine ⟨e,rfl,0,?_⟩
      exact (diagramArcPath D e).source.trans hz.symm
    · exact ⟨(D.continuation ^ k) e, componentOf_pow_apply _ _ _, hz⟩
  · rintro ⟨f,hf,hz⟩
    let C := componentOf D.continuation e
    let x : Fibre D.continuation C := ⟨e,rfl⟩
    let y : Fibre D.continuation C := ⟨f,hf⟩
    have hc : (fibrePerm D.continuation C).IsCycleOn
        (Finset.univ : Finset (Fibre D.continuation C)) := by
      simpa using fibrePerm_isCycleOn D.continuation C
    obtain ⟨k,hk,hke⟩ := hc.exists_pow_eq (Finset.mem_univ x) (Finset.mem_univ y)
    have hv : (D.continuation ^ k) e = f := by
      simpa only [fibrePerm_pow_apply_val] using congrArg Subtype.val hke
    refine Or.inr ⟨k,?_,?_⟩
    · simpa only [Finset.card_univ] using hk
    · rw [hv]
      exact hz

end
end DirectGLSSW.HOMFLY









