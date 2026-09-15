import SM.FirstTwoLinePolynomials
import SM.LinearConcurrenceCore

/-! Irreducibility and nonzeroness of the actual three-line determinant T.
The first-two-line coefficients are concrete polynomials; their coprimality and
all variable-separation obligations are proved before applying the linear core.
The full polynomial-controls lemma additionally requires its later clauses. -/

namespace SM

open MvPolynomial

noncomputable section

variable {n : ℕ}

def freeConcurrencePolynomial (e f g : ZMod n) : CoordinatePolynomial n :=
  (freeLinePairC e f * coordinateX g - freeLinePairA e f) * coordinateY (g + 1) +
    (freeLinePairB e f - freeLinePairC e f * coordinateY g) * coordinateX (g + 1)

theorem freeConcurrencePolynomial_irreducible [Nontrivial (ZMod n)]
    (e f g : ZMod n) (hef : remote e f) (heg : remote e g) (hfg : remote f g) :
    Irreducible (freeConcurrencePolynomial e f g) := by
  obtain ⟨hge, hge1, hg1e, hg1e1⟩ := remote_endpoints e g heg
  obtain ⟨hgf, hgf1, hg1f, hg1f1⟩ := remote_endpoints f g hfg
  have ht (s : Fin 2) := freeLinePair_avoids (g, s) e f hge hge1 hgf hgf1
  have hh (s : Fin 2) := freeLinePair_avoids (g + 1, s) e f hg1e hg1e1 hg1f hg1f1
  have hfresh : ∀ z ∈ ({(g, 0), (g, 1), (g + 1, 0), (g + 1, 1)} : Set (ScalarCoordinate n)),
      z ∉ (freeLinePairA e f).vars ∧ z ∉ (freeLinePairB e f).vars ∧
        z ∉ (freeLinePairC e f).vars := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ht 0
    · exact ht 1
    · exact hh 0
    · exact hh 1
  exact linearConcurrence_irreducible (freeLinePairA e f) (freeLinePairB e f)
    (freeLinePairC e f) (g, 0) (g, 1) (g + 1, 0) (g + 1, 1)
    (by simp) (by simpa using (next_ne_self g).symm) (by simp)
    (by simpa using (next_ne_self g).symm) (by simp)
    (fun z hz => (hfresh z hz).1) (fun z hz => (hfresh z hz).2.1)
    (fun z hz => (hfresh z hz).2.2) (freeLinePairC_irreducible e f hef).ne_zero
    (freeLinePairCA_relprime e f hef)

theorem tailDirectionTranslation_concurrence (E : Finset (ZMod n)) (hE : SeparatedEdgeHeads E)
    (e f g : ZMod n) (he : e ∈ E) (hf : f ∈ E) (hg : g ∈ E) :
    tailDirectionTranslation E hE (freeConcurrencePolynomial e f g) =
      concurrencePolynomial e f g := by
  rw [concurrencePolynomial_formula]
  simp only [freeConcurrencePolynomial, freeLinePairA, freeLinePairB, freeLinePairC,
    freeLineConstant, map_add, map_sub, map_mul,
    tailDirectionTranslation_tail_X E hE e he, tailDirectionTranslation_tail_Y E hE e he,
    tailDirectionTranslation_tail_X E hE f hf, tailDirectionTranslation_tail_Y E hE f hf,
    tailDirectionTranslation_tail_X E hE g hg, tailDirectionTranslation_tail_Y E hE g hg,
    tailDirectionTranslation_X E hE e he, tailDirectionTranslation_Y E hE e he,
    tailDirectionTranslation_X E hE f hf, tailDirectionTranslation_Y E hE f hf,
    tailDirectionTranslation_X E hE g hg, tailDirectionTranslation_Y E hE g hg,
    linePolynomialA, linePolynomialB, linePolynomialC]
  ring

theorem concurrencePolynomial_irreducible_of_nontrivial [Nontrivial (ZMod n)]
    (e f g : ZMod n) (hef : remote e f) (heg : remote e g) (hfg : remote f g) :
    Irreducible (concurrencePolynomial e f g) := by
  have hE := separatedEdgeHeads_triple e f g hef heg hfg
  have he : e ∈ ({e, f, g} : Finset (ZMod n)) := by simp
  have hf : f ∈ ({e, f, g} : Finset (ZMod n)) := by simp
  have hg : g ∈ ({e, f, g} : Finset (ZMod n)) := by simp
  have hi := (MulEquiv.irreducible_iff (tailDirectionTranslation {e, f, g} hE)).mpr
    (freeConcurrencePolynomial_irreducible e f g hef heg hfg)
  rwa [tailDirectionTranslation_concurrence _ hE e f g he hf hg] at hi

theorem concurrencePolynomial_irreducible (hn : 3 ≤ n)
    (e f g : ZMod n) (hef : remote e f) (heg : remote e g) (hfg : remote f g) :
    Irreducible (concurrencePolynomial e f g) := by
  letI : Fact (1 < n) := ⟨by omega⟩
  exact concurrencePolynomial_irreducible_of_nontrivial e f g hef heg hfg

theorem concurrencePolynomial_ne_zero (hn : 3 ≤ n)
    (e f g : ZMod n) (hef : remote e f) (heg : remote e g) (hfg : remote f g) :
    concurrencePolynomial e f g ≠ 0 :=
  (concurrencePolynomial_irreducible hn e f g hef heg hfg).ne_zero

end

end SM
