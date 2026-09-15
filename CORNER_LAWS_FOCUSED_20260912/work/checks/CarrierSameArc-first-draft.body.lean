namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {P : LabelledTuple n}

/-- For distinct actual crossings and either ordering of each actual visit pair,
noninterlacement is exactly equality of the two open-arc membership statuses. -/
theorem not_interlaces_iff_same_arc_status (hn : 3 ≤ n) (hP : Generic P)
    {x y : Crossing P} (hxy : x ≠ y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (y₀ y₁ : {i // i ∈ y.val}) (hy : y₀ ≠ y₁) :
    ¬ Interlaces hn hP x y ↔
      (crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ ↔
        crossingVisitBetween hn hP.1 x x₀ x₁ y y₁) := by
  constructor
  · intro hNI
    constructor
    · intro h₀
      by_contra h₁
      exact hNI ⟨hxy, x₀, x₁, y₀, y₁, hx, hy, h₀,
        (crossingVisitBetween_complement hn hP hxy x₁ x₀ hx.symm y₁).mpr h₁⟩
    · intro h₁
      by_contra h₀
      exact hNI ⟨hxy, x₀, x₁, y₁, y₀, hx, hy.symm, h₁,
        (crossingVisitBetween_complement hn hP hxy x₁ x₀ hx.symm y₀).mpr h₀⟩
  · intro hsame hI
    obtain ⟨j, hj, hu⟩ := (interlaces_iff_unique hn hP x y x₀ x₁ hx).mp hI |>.2
    have h₀ : crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ := by
      rcases crossing_visits_exhaust y y₀ y₁ hy j with he | he
      · exact he ▸ hj
      · exact hsame.mpr (he ▸ hj)
    exact hy ((hu y₀ h₀).trans (hu y₁ (hsame.mp h₀)).symm)

/-- The equivalent statuses put both actual visits in one of the two oriented
open arcs. The complement law uses distinct crossing positions, so no endpoint
case is silently discarded. -/
theorem not_interlaces_iff_one_open_arc (hn : 3 ≤ n) (hP : Generic P)
    {x y : Crossing P} (hxy : x ≠ y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (y₀ y₁ : {i // i ∈ y.val}) (hy : y₀ ≠ y₁) :
    ¬ Interlaces hn hP x y ↔
      (crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ ∧
        crossingVisitBetween hn hP.1 x x₀ x₁ y y₁) ∨
      (crossingVisitBetween hn hP.1 x x₁ x₀ y y₀ ∧
        crossingVisitBetween hn hP.1 x x₁ x₀ y y₁) := by
  rw [not_interlaces_iff_same_arc_status hn hP hxy x₀ x₁ hx y₀ y₁ hy,
    crossingVisitBetween_complement hn hP hxy x₁ x₀ hx.symm y₀,
    crossingVisitBetween_complement hn hP hxy x₁ x₀ hx.symm y₁]
  tauto

/-- No choice of first visit of the second crossing affects its arc membership
when the actual crossings do not interlace. The two input visits may coincide. -/
theorem not_interlaces_all_visits_same_arc (hn : 3 ≤ n) (hP : Generic P)
    {x y : Crossing P} (hxy : x ≠ y) (hNI : ¬ Interlaces hn hP x y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (j k : {i // i ∈ y.val}) :
    crossingVisitBetween hn hP.1 x x₀ x₁ y j ↔
      crossingVisitBetween hn hP.1 x x₀ x₁ y k := by
  by_cases hjk : j = k
  · subst k
    exact Iff.rfl
  · exact (not_interlaces_iff_same_arc_status hn hP hxy x₀ x₁ hx j k hjk).mp hNI

/-- Actual independent support supplies noninterlacement for any two distinct
selected crossings; no hypothesis about current carrier ownership is used. -/
theorem independent_crossing_visits_same_arc (hn : 3 ≤ n) (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    {x y : Crossing P} (hxS : x ∈ S) (hyS : y ∈ S) (hxy : x ≠ y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (j k : {i // i ∈ y.val}) :
    crossingVisitBetween hn hP.1 x x₀ x₁ y j ↔
      crossingVisitBetween hn hP.1 x x₀ x₁ y k :=
  not_interlaces_all_visits_same_arc hn hP hxy
    ((mem_independentSupports_iff hn hP S).mp hS x hxS y hyS hxy) x₀ x₁ hx j k

/-- The other selected pair is wholly in one original open arc of the selected
pair, the noninterlacement input needed for the source's splitting induction. -/
theorem independent_crossing_visits_one_open_arc (hn : 3 ≤ n) (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    {x y : Crossing P} (hxS : x ∈ S) (hyS : y ∈ S) (hxy : x ≠ y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (y₀ y₁ : {i // i ∈ y.val}) (hy : y₀ ≠ y₁) :
    (crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ ∧
      crossingVisitBetween hn hP.1 x x₀ x₁ y y₁) ∨
    (crossingVisitBetween hn hP.1 x x₁ x₀ y y₀ ∧
      crossingVisitBetween hn hP.1 x x₁ x₀ y y₁) :=
  (not_interlaces_iff_one_open_arc hn hP hxy x₀ x₁ hx y₀ y₁ hy).mp
    ((mem_independentSupports_iff hn hP S).mp hS x hxS y hyS hxy)

/-- The status equivalence for the constructed actual twin pairing, written
literally in physical traversal positions. The pair inequalities are derived
from the checked construction rather than supplied as extra premises. -/
theorem not_interlaces_iff_twin_same_arc (hn : 3 ≤ n) (hP : Generic P)
    (v w : Visit P) (hvw : v.1 ≠ w.1) :
    ¬ Interlaces hn hP v.1 w.1 ↔
      (traversalBetween (visitPosition hn hP.1 v) (visitPosition hn hP.1 w)
          (visitPosition hn hP.1 (visitTwin v)) ↔
        traversalBetween (visitPosition hn hP.1 v)
          (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 (visitTwin v))) := by
  have hv : v.2 ≠ (visitTwin v).2 :=
    (Classical.choose_spec (crossing_other_visit v.1 v.2)).symm
  have hw : w.2 ≠ (visitTwin w).2 :=
    (Classical.choose_spec (crossing_other_visit w.1 w.2)).symm
  exact not_interlaces_iff_same_arc_status hn hP hvw
    v.2 (visitTwin v).2 hv w.2 (visitTwin w).2 hw

/-- Noninterlacement places the actual twin pair together on either the forward
or backward open arc of the other actual twin pair, including wraparound. -/
theorem not_interlaces_iff_twin_one_open_arc (hn : 3 ≤ n) (hP : Generic P)
    (v w : Visit P) (hvw : v.1 ≠ w.1) :
    ¬ Interlaces hn hP v.1 w.1 ↔
      (traversalBetween (visitPosition hn hP.1 v) (visitPosition hn hP.1 w)
          (visitPosition hn hP.1 (visitTwin v)) ∧
        traversalBetween (visitPosition hn hP.1 v)
          (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 (visitTwin v))) ∨
      (traversalBetween (visitPosition hn hP.1 (visitTwin v)) (visitPosition hn hP.1 w)
          (visitPosition hn hP.1 v) ∧
        traversalBetween (visitPosition hn hP.1 (visitTwin v))
          (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 v)) := by
  have hv : v.2 ≠ (visitTwin v).2 :=
    (Classical.choose_spec (crossing_other_visit v.1 v.2)).symm
  have hw : w.2 ≠ (visitTwin w).2 :=
    (Classical.choose_spec (crossing_other_visit w.1 w.2)).symm
  exact not_interlaces_iff_one_open_arc hn hP hvw
    v.2 (visitTwin v).2 hv w.2 (visitTwin w).2 hw

/-- In an actual independent support, every other selected twin pair lies in
one original oriented open arc of the selected pair. This is a statement about
actual traversal positions, not a supplied current-cycle correspondence. -/
theorem independent_twin_one_open_arc (hn : 3 ≤ n) (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (v w : Visit P) (hvS : v.1 ∈ S) (hwS : w.1 ∈ S) (hvw : v.1 ≠ w.1) :
    (traversalBetween (visitPosition hn hP.1 v) (visitPosition hn hP.1 w)
        (visitPosition hn hP.1 (visitTwin v)) ∧
      traversalBetween (visitPosition hn hP.1 v)
        (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 (visitTwin v))) ∨
    (traversalBetween (visitPosition hn hP.1 (visitTwin v)) (visitPosition hn hP.1 w)
        (visitPosition hn hP.1 v) ∧
      traversalBetween (visitPosition hn hP.1 (visitTwin v))
        (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 v)) :=
  (not_interlaces_iff_twin_one_open_arc hn hP v w hvw).mp
    ((mem_independentSupports_iff hn hP S).mp hS v.1 hvS w.1 hwS hvw)

end
end SM.Carrier
