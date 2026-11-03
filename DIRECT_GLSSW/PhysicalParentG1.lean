import PhysicalEmptyAnchor
import ActiveArcParentFarFamily
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.TraversalClosure
open DirectGLSSW ActiveArc Cursor Split Primitive RetainedWords OpenCarrier
attribute [local instance] Classical.propDecidable

/-- Canonical parent far nonvanishing applies to every pair of later actual
anchors through the genuinely empty-support retained-word embedding. -/
lemma parent_root_far {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
    (hR : Regular q) (hG : cyclicNoncollinear q)
    (c : Crossing q) (hcut : c.val.2.val=a)
    (hL : parentFarLocus q hR c hcut (parentChartLines q))
    (i j : Fin (b+2)) (hi : i≠0) (hj : j≠0) (hij : i≠j) :
    planarDet (parent q c hcut i-crossingPoint q c)
      (parent q c hcut j-crossingPoint q c)≠0 := by
  let P := parent q c hcut
  let hP := regular_parent q hR c hcut
  let T : Support P hP := ⟨∅,by intro d hd; simp at hd⟩
  let I := emptyAnchorIndex P hP i
  let J := emptyAnchorIndex P hP j
  have hI : 0<I.val := Nat.pos_of_ne_zero (emptyAnchorIndex_ne_zero P hP i hi)
  have hJ : 0<J.val := Nat.pos_of_ne_zero (emptyAnchorIndex_ne_zero P hP j hj)
  have hIJ : I≠J := fun hh => hij (emptyAnchorIndex_injective P hP hh)
  have hpoint (v : Fin (b+2)) :
      OpenVertex P hP T (emptyAnchorIndex P hP v)=P v := emptyAnchorIndex_vertex P hP v
  have hval : I.val≠J.val := fun hh => hIJ (Fin.ext hh)
  rcases lt_or_gt_of_ne hval with hlt|hgt
  · have hh : planarDet (OpenVertex P hP T I-crossingPoint q c)
        (OpenVertex P hP T J-crossingPoint q c)≠0 := by
      intro hz
      exact hL T I J hI hlt ((parent_far_numerator_zero_iff q hR c hcut hG T I J).mpr hz)
    simpa only [I,J,hpoint] using hh
  · have hh : planarDet (OpenVertex P hP T J-crossingPoint q c)
        (OpenVertex P hP T I-crossingPoint q c)≠0 := by
      intro hz
      exact hL T J I hJ hgt ((parent_far_numerator_zero_iff q hR c hcut hG T J I).mpr hz)
    rw [hpoint,hpoint] at hh
    intro hz
    apply hh
    unfold planarDet at hz ⊢
    simp only [Prod.fst_sub,Prod.snd_sub] at hz ⊢
    nlinarith

private lemma G1_of_tail_rootFar {n : ℕ} (p : Fin (n+2) → PlanarPoint ℝ)
    (hTail : ∀ i j k : Fin (n+1), i≠j → j≠k → i≠k →
      planarDet (p j.succ-p k.succ) (p i.succ-p k.succ)≠0)
    (hFar : ∀ i j : Fin (n+1), i≠j → planarDet (p i.succ-p 0) (p j.succ-p 0)≠0) :
    cyclicNoncollinear p := by
  intro i j k hij hjk hik
  cases i using Fin.cases <;> cases j using Fin.cases <;> cases k using Fin.cases
  · exact False.elim (hij rfl)
  · exact False.elim (hij rfl)
  · exact False.elim (hik rfl)
  · rename_i j k
    have hh := hFar j k (fun he => hjk (congrArg Fin.succ he))
    intro hz
    apply hh
    unfold planarDet at hz ⊢
    simp only [Prod.fst_sub,Prod.snd_sub] at hz ⊢
    nlinarith
  · exact False.elim (hjk rfl)
  · rename_i i k
    have hh := hFar i k (fun he => hik (congrArg Fin.succ he))
    intro hz
    apply hh
    unfold planarDet at hz ⊢
    simp only [Prod.fst_sub,Prod.snd_sub] at hz ⊢
    nlinarith
  · rename_i i j
    exact hFar j i (fun he => hij (congrArg Fin.succ he.symm))
  · rename_i i j k
    exact hTail i j k (fun he => hij (congrArg Fin.succ he))
      (fun he => hjk (congrArg Fin.succ he)) (fun he => hik (congrArg Fin.succ he))

/-- All distinct parent vertex triples are noncollinear. Source G1 handles
triples of unchanged anchors; canonical hL handles the actual cut root. -/
theorem parent_G1_of_parentFar {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
    (hR : Regular q) (hG : cyclicNoncollinear q)
    (c : Crossing q) (hcut : c.val.2.val=a)
    (hL : parentFarLocus q hR c hcut (parentChartLines q)) :
    cyclicNoncollinear (parent q c hcut) := by
  apply G1_of_tail_rootFar
  · intro i j k hij hjk hik
    simp only [parent_succ]
    exact hG (Split.vertex i.succ) (Split.vertex j.succ) (Split.vertex k.succ)
      (fun he => hij (Fin.succ_inj.mp (vertex_injective he)))
      (fun he => hjk (Fin.succ_inj.mp (vertex_injective he)))
      (fun he => hik (Fin.succ_inj.mp (vertex_injective he)))
  · intro i j hij
    rw [parent_zero]
    exact parent_root_far q hR hG c hcut hL i.succ j.succ
      (Fin.succ_ne_zero i) (Fin.succ_ne_zero j) (fun he => hij (Fin.succ_inj.mp he))
end DirectGLSSW.ActiveArc.TraversalClosure
