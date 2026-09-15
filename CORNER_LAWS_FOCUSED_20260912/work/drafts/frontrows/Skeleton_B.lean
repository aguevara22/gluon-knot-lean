import SM.FrontRealizeGeometry
import SM.FrontRealizeBase
import SM.FrontRealizeDeform
import SM.FrontInterfaces
import SM.FrontWordsBase
import SM.FrontGeomModel
import SM.PolynomialBlock

/-! # Front certificate rows 76-83 — PROOF SKELETON (TAG B)

Draft 2026-09-14, work/drafts/frontrows/Skeleton_B.lean; statements as in Statements_B.lean (copied
verbatim below), plan in PLAN_B.md.  The eight row theorems are ASSEMBLED here from named leaves; every
`sorry` is a leaf (section "Leaves"), none is a row.  Leaf groups (PLAN_B.md §5 gives the unit split):

* L-deg: Laurent-degree arithmetic on `R` (`delta_ne_zero`, `degAZ_delta`, the two skein degree bounds).
* L-cnt: the count changes `ΔD`, `Δw` of each pattern, read off the realization through the accepted
  letter tracing (`realize_downCount`, `realize_writhe`) — the displays ng:type-I-counts,
  ng:zigzag-counts, ng:crossed-cusp-counts, ng:circle-counts and the (t,u) table.
* L-rec: polynomial equalities obtained through named RECORDS (`presentations`, `P_addFree`, the
  accepted `exists_smoothing_record`): commutation, zigzag, circle deletion, the cusp-skein site.
* L-geo: polynomial equalities obtained through the accepted geometric moves (`P_reidemeister_I/II/III`)
  on a vertex-moved realization: type I, type II, type III, crossed cusp.
* L-PL: the planarity fact `D = c` for an arbitrary PL union of standard circles (row 81 sentence 2).
* L-smooth: the two smooth clauses of row 76 (nonsingular deformation; representation).

Checked with `lake env lean` (Lean v4.34.0-rc2, the project's Mathlib pin). -/

namespace SM

open SM.FrontWord SM.Link
open scoped ContDiff

/-! ## Statements (verbatim from Statements_B.lean) -/

structure SmoothFront.NonsingularDeformation (F F' : SmoothFront) where
  path : ℝ → SmoothFront
  start : path 0 = F
  stop : path 1 = F'
  c_eq : ∀ t, (path t).c = F.c
  smooth : ∀ i : Fin F.c, ContDiffOn ℝ ∞
    (fun p : ℝ × ℝ => ((path p.1).comp (Fin.cast (c_eq p.1).symm i)).γ p.2) (Set.Icc 0 1 ×ˢ Set.univ)

structure NgCommutationClauses : Prop where
  comm_D : ∀ W W' : OWord, IsComm W.letters W'.letters →
    (realize W).downCount = (realize W').downCount
  comm_w : ∀ W W' : OWord, IsComm W.letters W'.letters → (realize W).writhe = (realize W').writhe
  comm_d : ∀ W W' : OWord, IsComm W.letters W'.letters →
    degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  comm_B : ∀ W W' : OWord, IsComm W.letters W'.letters → (realize W).defect = (realize W').defect
  deform_D : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') → F.downCount = F'.downCount
  deform_w : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') → F.writhe = F'.writhe
  deform_d : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') →
    ∀ S S' : Diagram, F.IsRounding S → F'.IsRounding S' → degAZ (P S) = degAZ (P S')
  deform_B : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') →
    ∀ S S' : Diagram, F.IsRounding S → F'.IsRounding S' → F.defect S = F'.defect S'
  represent : ∀ F : SmoothFront, ∃ W : OWord,
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧ F.sCount = (realize W).sCount ∧
    ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record)

structure NgFrontIClauses : Prop where
  typeI_B : ∀ W W' : OWord, IsTypeI W.letters W'.letters → (realize W).defect = (realize W').defect

structure NgFrontIIClauses : Prop where
  typeII_D : ∀ W W' : OWord, IsTypeII W.letters W'.letters →
    (realize W).downCount = (realize W').downCount
  typeII_w : ∀ W W' : OWord, IsTypeII W.letters W'.letters → (realize W).writhe = (realize W').writhe
  typeII_d : ∀ W W' : OWord, IsTypeII W.letters W'.letters →
    degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  typeII_B : ∀ W W' : OWord, IsTypeII W.letters W'.letters → (realize W).defect = (realize W').defect

structure NgFrontIIIClauses : Prop where
  typeIII_D : ∀ W W' : OWord, IsTypeIII W.letters W'.letters →
    (realize W).downCount = (realize W').downCount
  typeIII_w : ∀ W W' : OWord, IsTypeIII W.letters W'.letters → (realize W).writhe = (realize W').writhe
  typeIII_d : ∀ W W' : OWord, IsTypeIII W.letters W'.letters →
    degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  typeIII_B : ∀ W W' : OWord, IsTypeIII W.letters W'.letters → (realize W).defect = (realize W').defect

structure NgDeletionsClauses : Prop where
  zigzag_s : ∀ W W' : OWord, IsZigzagDeletion W.letters W'.letters →
    (realize W').sCount + 2 = (realize W).sCount
  zigzag_B : ∀ W W' : OWord, IsZigzagDeletion W.letters W'.letters →
    (realize W').defect ≤ (realize W).defect
  crossedCusp_s : ∀ W W' : OWord, IsCrossedCuspShortcut W.letters W'.letters →
    (realize W').sCount + 1 = (realize W).sCount
  crossedCusp_B : ∀ W W' : OWord, IsCrossedCuspShortcut W.letters W'.letters →
    (realize W').defect ≤ (realize W).defect

structure NgCircleClauses : Prop where
  circleDeletion_B : ∀ W W' : OWord, IsCircleDeletion W.letters W'.letters →
    (realize W).defect = (realize W').defect
  single_B : ∀ F : PLFront, F.IsStandardCircles → F.Γ.c = 1 → F.defect = 0
  union_B : ∀ F : PLFront, F.IsStandardCircles → F.defect = 0

structure NgCuspSkeinClauses : Prop where
  earlier_branch : ∀ A A' C : OWord, IsCuspSkein A.letters A'.letters C.letters →
    min (realize A').defect (realize C).defect ≤ (realize A).defect
  unique_smoothing : ∀ A A' C C' : OWord, IsCuspSkein A.letters A'.letters C.letters →
    IsCuspSkein A.letters A'.letters C'.letters → C.letters = C'.letters
  smoothing_s : ∀ A A' C : OWord, IsCuspSkein A.letters A'.letters C.letters →
    (realize C).sCount + 1 = (realize A).sCount
  principal_s : ∀ A A' C : OWord, IsCuspSkein A.letters A'.letters C.letters →
    (realize A').sCount = (realize A).sCount

structure NgLocalFrontBoundClauses : Prop where
  front_inequality : ∀ (F : SmoothFront) (S : Diagram), F.IsRounding S →
    F.writhe - (F.downCount : ℤ) ≤ -degAZ (P S) - 1

/-! ## Leaves -/

section Leaves

/-! ### L-deg — Laurent-degree arithmetic (def:adeg, `SM/LinkLaurentRing.lean`) -/

/-- `δ = (a − a⁻¹) z⁻¹ ≠ 0` (units and a domain). -/
theorem delta_ne_zero : R.delta ≠ 0 := sorry

/-- "The leading a coefficient of δ is z⁻¹, in degree one" (sm-3:2060-2061): `deg_a δ = 1`. -/
theorem degAZ_delta : degAZ R.delta = 1 := sorry

/-- `deg_a δ^n = n` (from `degAZ_mul` in the domain `R`). -/
theorem degAZ_delta_pow (n : ℕ) : degAZ (R.delta ^ n) = n := by
  induction n with
  | zero => simp [degAZ, degA_one]
  | succ n ih =>
    rw [pow_succ, degAZ_mul (pow_ne_zero _ delta_ne_zero) delta_ne_zero, ih, degAZ_delta]
    push_cast; ring

/-- eq. ng:skein-plus solved for degrees (sm-3:2130-2140): "The degree of a nonzero sum is at most the
maximum of the summand degrees.  Multiplication by a^k shifts degree by k, and multiplication by z does
not change it": from `f = a⁻² g + a⁻¹ z h`, `deg_a f ≤ max (deg_a g − 2) (deg_a h − 1)`. -/
theorem degAZ_le_of_eq_pos {f g h : R} (hg : g ≠ 0) (hh : h ≠ 0)
    (e : f = R.aInv * R.aInv * g + R.aInv * R.z * h) (hf : f ≠ 0) :
    degAZ f ≤ max (degAZ g - 2) (degAZ h - 1) := sorry

/-- eq. ng:skein-minus solved for degrees (sm-3:2134-2149): from `f = a² g − a z h`,
`deg_a f ≤ max (deg_a g + 2) (deg_a h + 1)`. -/
theorem degAZ_le_of_eq_neg {f g h : R} (hg : g ≠ 0) (hh : h ≠ 0)
    (e : f = R.a * R.a * g - R.a * R.z * h) (hf : f ≠ 0) :
    degAZ f ≤ max (degAZ g + 2) (degAZ h + 1) := sorry

/-- "Solving the skein relation separately in the two directions" (sm-3:2128-2136): the recursion at a
positive crossing, solved for the switched diagram. -/
theorem switch_of_recursion_pos {f g h : R} (e : f = R.aInv * R.aInv * g + R.aInv * R.z * h) :
    g = R.a * R.a * f - R.a * R.z * h := by
  subst e
  linear_combination (-(g * (R.a * R.aInv + 1) + R.a * R.z * h)) * R.a_mul_aInv

/-- The recursion at a negative crossing, solved for the switched diagram. -/
theorem switch_of_recursion_neg {f g h : R} (e : f = R.a * R.a * g - R.a * R.z * h) :
    g = R.aInv * R.aInv * f + R.aInv * R.z * h := by
  subst e
  linear_combination (-(g * (R.a * R.aInv + 1) - R.aInv * R.z * h)) * R.a_mul_aInv

/-! ### L-cnt — the count changes, read on the realization through the accepted letter tracing
(`realize_downCount`, `realize_writhe`, `isDownCusp_iff`, `sign_crossingOf`) -/

/-- ng:commutation (sm-3:1928-1933): "The cusp directions and crossing signs are unchanged, so D and w
are unchanged as well." -/
theorem comm_counts {W W' : OWord} (h : IsComm W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe := sorry

/-- display ng:type-I-counts (sm-3:1964-1967), deletion direction: `ΔD = −1`, `Δw = −1` ("Exactly one of
the two cusps is downward"; "Its crossing is also positive"). -/
theorem typeI_counts {W W' : OWord} (h : IsTypeI W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount + 1 ∧ (realize W).writhe = (realize W').writhe + 1 :=
  sorry

/-- ng:front-II (sm-3:1979-1986): "Their signs are opposite ... The same upper and lower cusp arms remain
after deletion.  Thus Δw = ΔD = 0." -/
theorem typeII_counts {W W' : OWord} (h : IsTypeII W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe := sorry

/-- ng:front-III (sm-3:1997-2002): "Each physical pair crosses on both sides with the same over/under
bit and transported arrows" — no cusp letter, signs preserved. -/
theorem typeIII_counts {W W' : OWord} (h : IsTypeIII W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe := sorry

/-- display ng:zigzag-counts (sm-3:2020-2023): `Δw = 0`, `ΔD ∈ {0, −2}` ("Their directions are both
downward or both upward"). -/
theorem zigzag_counts {W W' : OWord} (h : IsZigzagDeletion W.letters W'.letters) :
    (realize W).writhe = (realize W').writhe ∧
    ((realize W).downCount = (realize W').downCount ∨ (realize W).downCount = (realize W').downCount + 2) :=
  sorry

/-- display ng:crossed-cusp-counts (sm-3:2030-2038): "the old crossing has sign −1.  Deletion raises w by
one and flips the cusp direction ... If the old cusp was downward, ΔD = −1; otherwise ΔD = 1." -/
theorem crossedCusp_counts {W W' : OWord} (h : IsCrossedCuspShortcut W.letters W'.letters) :
    (realize W').writhe = (realize W).writhe + 1 ∧
    ((realize W').downCount + 1 = (realize W).downCount ∨ (realize W').downCount = (realize W).downCount + 1) :=
  sorry

/-- display ng:circle-counts (sm-3:2062-2066): `D_before = D_after + 1`, "The writhe is unchanged". -/
theorem circleDeletion_counts {W W' : OWord} (h : IsCircleDeletion W.letters W'.letters) :
    (realize W).writhe = (realize W').writhe ∧ (realize W).downCount = (realize W').downCount + 1 := sorry

/-- the (t,u) table, last column (sm-3:2107-2126): "the same downward-cusp count in all three diagrams". -/
theorem skein_downCount {A A' C : OWord} (h : IsCuspSkeinStep A.letters A'.letters C.letters) :
    (realize A).downCount = (realize C).downCount ∧ (realize A').downCount = (realize C).downCount := sorry

/-! ### L-rec — polynomial equalities through named records (rp:record-polynomial `presentations`,
lp:split-circle in record form `P_addFree`, the smoothing gate `exists_smoothing_record`) -/

/-- ng:commutation (sm-3:1931-1932): "equivalently, the full named records are the same"; then
rp:record-polynomial. -/
theorem P_comm {W W' : OWord} (h : IsComm W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := sorry

/-- ng:deletions (sm-3:2018-2020): the zigzag "is a simple ordinary arc, positively page isotopic relative
to its endpoints to the straightened arc" — no crossing is touched, so the named records coincide. -/
theorem P_zigzag {W W' : OWord} (h : IsZigzagDeletion W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := sorry

/-- ng:circle (sm-3:2059): "For nonempty remainder, P_before = δ P_after" (lp:split-circle, record form:
the circle is a free component of the record, `P_addFree`). -/
theorem P_circleDeletion {W W' : OWord} (h : IsCircleDeletion W.letters W'.letters) :
    P (realize W).diagram = R.delta * P (realize W').diagram := sorry

/-- ng:cusp-skein (sm-3:2094-2101, 2119-2127): the crossing of `A` is an ordinary skein site; "Exchanging
over and under at that crossing makes their local ordered crossing records identical ... After gluing any
same actual exterior, the full named records are identical" (`A'` vs the switch); "Only the one compatible
smoothing is used" (a geometric oriented smoothing with the record of `C`, via the accepted
`exists_smoothing_record`); and the sign table: `sign(A) = −tu`, `w_± = w₀ ± 1`. -/
theorem skein_site {A A' C : OWord} (h : IsCuspSkeinStep A.letters A'.letters C.letters) :
    ∃ (x : (realize A).diagram.Γ.Crossing) (D₀ : Diagram),
      IsOrientedSmoothing (realize A).diagram x D₀ ∧
      P (realize A').diagram = P ((realize A).diagram.switch x) ∧
      P D₀ = P (realize C).diagram ∧
      (((realize A).diagram.IsPositive x ∧ (realize A).writhe = (realize C).writhe + 1 ∧
          (realize A').writhe = (realize C).writhe - 1) ∨
       (¬ (realize A).diagram.IsPositive x ∧ (realize A).writhe = (realize C).writhe - 1 ∧
          (realize A').writhe = (realize C).writhe + 1)) := sorry

/-- "the unique compatible smoothing": the pattern determines `C` (the two words differ first at the cusp
letter, which fixes `X`, `m`, `d`, `Y`; the through-strand bit is read from `X`). -/
theorem skein_unique {A A' C C' : Word} (h : IsCuspSkein A A' C) (h' : IsCuspSkein A A' C') : C = C' :=
  sorry

/-! ### L-geo — polynomial equalities through the accepted geometric moves on a vertex-moved realization
(`P_reidemeister_I/II/III`; PLAN_B.md §4) -/

/-- ng:front-I (sm-3:1956-1957): "After rounding its two cusps, the unique crossing bounds an empty
ordinary monogon" — an `RI` site; `P_reidemeister_I`. -/
theorem P_typeI {W W' : OWord} (h : IsTypeI W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := sorry

/-- ng:front-II (sm-3:1982-1984): "the arcs bound an empty ordinary bigon with one common over-strand: an
oriented Reidemeister-II site"; `P_reidemeister_II`. -/
theorem P_typeII {W W' : OWord} (h : IsTypeII W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := sorry

/-- ng:front-III (sm-3:1995-2003): "an actual ordinary Reidemeister-III configuration ... one strict
height order"; `P_reidemeister_III`. -/
theorem P_typeIII {W W' : OWord} (h : IsTypeIII W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := sorry

/-- ng:deletions (sm-3:2027-2030): "After rounding, ordinary Reidemeister I deletes its empty monogon";
`P_reidemeister_I` with a kink of sign −1. -/
theorem P_crossedCusp {W W' : OWord} (h : IsCrossedCuspShortcut W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := sorry

/-! ### L-PL — the planarity fact for an arbitrary PL union of standard circles -/

/-- ng:circle (sm-3:2053-2054): "A simple crossing-free component with exactly one left and one right cusp
has D = 1": on a `PLFront`, the two x-monotone arcs between the cusps never meet, so one lies above the
other and exactly one cusp is traversed upper arm → lower arm.  (Accepted for realizations:
`FrontRealizeStandard.IsStandardCircles.downCount_eq_c`.) -/
theorem PLFront.IsStandardCircles.downCount_eq_c_general (F : PLFront) (h : F.IsStandardCircles) :
    F.downCount = F.Γ.c := sorry

/-! ### L-smooth — the smooth clauses of row 76 -/

/-- ng:commutation (sm-3:1935-1937): "A deformation without a singular event preserves the records, D and
w: signs, cusp directions and cyclic attachments cannot change." — `D`. -/
theorem deform_downCount (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) :
    F.downCount = F'.downCount := sorry

/-- the same for `w` -/
theorem deform_writhe (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) :
    F.writhe = F'.writhe := sorry

/-- the same for the records of the roundings, hence (sm-3:1937-1938 "Lemma rp:record-polynomial gives
scalar equality") the polynomial -/
theorem deform_P (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) (S S' : Diagram)
    (hS : F.IsRounding S) (hS' : F'.IsRounding S') : P S = P S' := sorry

/-- ng:commutation (sm-3:1925-1926, proof 1940-1947): "Every supplied finite front can be represented by a
finite elementary front word" — the block's analytic bridge (FINAL §8 risk 1). -/
theorem represent (F : SmoothFront) : ∃ W : OWord,
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧ F.sCount = (realize W).sCount ∧
    ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record) := sorry

end Leaves

/-! ## Small proved helpers -/

section Helpers

namespace FrontWord

theorem IsZigzagDeletion.source_ne_nil {W W' : Word} (h : IsZigzagDeletion W W') : W ≠ [] := by
  obtain ⟨X, Y, m, d, -, hpat, -⟩ := h
  rcases hpat with rfl | rfl <;> simp

theorem IsCrossedCuspShortcut.ne_nil {W W' : Word} (h : IsCrossedCuspShortcut W W') : W ≠ [] ∧ W' ≠ [] := by
  obtain ⟨X, Y, i, -, hpat⟩ := h
  rcases hpat with ⟨d, rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem IsCuspSkeinStep.ne_nil {A A' C : Word} (h : IsCuspSkeinStep A A' C) : A ≠ [] ∧ A' ≠ [] ∧ C ≠ [] := by
  obtain ⟨X, Y, m, d, a, P, L, -, -, -, rfl, rfl, hC⟩ := h
  rcases hC with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp

theorem IsCuspSkein.ne_nil {A A' C : Word} (h : IsCuspSkein A A' C) : A ≠ [] ∧ A' ≠ [] ∧ C ≠ [] := by
  rcases h with h | h
  · exact h.ne_nil
  · obtain ⟨h1, h2, h3⟩ := h.ne_nil; exact ⟨h2, h1, h3⟩

end FrontWord

/-- the base clause of the descent on the syntactic base of `SM.ng_finite_word` (ng:circle's "B = 0" for
the base, with the accepted planarity fact for realizations) -/
theorem base_defect_nonneg (W : OWord) (hW : W.IsStandardCircleBase) : 0 ≤ (realize W).defect := by
  have hstd := realize_isStandardCircles_of_base W hW
  have hD := realize_downCount_eq_c_of_base W hW
  rw [hstd.defect_eq, hD, P_crossingFree hstd.1, degAZ_delta_pow]
  have hc := (realize W).Γ.hc
  have hcc : (realize W).diagram.componentCount = (realize W).Γ.c := rfl
  omega

end Helpers

/-! ## Assembly of the rows -/

/-- **ng:commutation** (row 76), assembled. -/
theorem ng_commutation : NgCommutationClauses where
  comm_D := fun _ _ h => (comm_counts h).1
  comm_w := fun _ _ h => (comm_counts h).2
  comm_d := fun _ _ h => by rw [P_comm h]
  comm_B := fun _ _ h => by
    unfold PLFront.defect
    rw [(comm_counts h).1, (comm_counts h).2, P_comm h]
  deform_D := deform_downCount
  deform_w := deform_writhe
  deform_d := fun F F' h S S' hS hS' => by rw [deform_P F F' h S S' hS hS']
  deform_B := fun F F' h S S' hS hS' => by
    unfold SmoothFront.defect SmoothFront.dOf
    rw [deform_downCount F F' h, deform_writhe F F' h, deform_P F F' h S S' hS hS']
  represent := represent

/-- **ng:front-I** (row 77), assembled: display ng:type-I-counts and `Δd = 0` give `ΔB = 0`
(sm-3:1968). -/
theorem ng_front_I : NgFrontIClauses where
  typeI_B := fun _ _ h => by
    obtain ⟨hD, hw⟩ := typeI_counts h
    unfold PLFront.defect
    rw [P_typeI h, hD, hw]
    push_cast; ring

/-- **ng:front-II** (row 78), assembled. -/
theorem ng_front_II : NgFrontIIClauses where
  typeII_D := fun _ _ h => (typeII_counts h).1
  typeII_w := fun _ _ h => (typeII_counts h).2
  typeII_d := fun _ _ h => by rw [P_typeII h]
  typeII_B := fun _ _ h => by
    unfold PLFront.defect
    rw [(typeII_counts h).1, (typeII_counts h).2, P_typeII h]

/-- **ng:front-III** (row 79), assembled. -/
theorem ng_front_III : NgFrontIIIClauses where
  typeIII_D := fun _ _ h => (typeIII_counts h).1
  typeIII_w := fun _ _ h => (typeIII_counts h).2
  typeIII_d := fun _ _ h => by rw [P_typeIII h]
  typeIII_B := fun _ _ h => by
    unfold PLFront.defect
    rw [(typeIII_counts h).1, (typeIII_counts h).2, P_typeIII h]

/-- **ng:deletions** (row 80), assembled: the `s` clauses from the accepted syntactic counts through
`realize_sCount` (both words nonempty), the `B` clauses from the count displays and the polynomial
leaves. -/
theorem ng_deletions : NgDeletionsClauses where
  zigzag_s := fun W W' h => by
    rw [realize_sCount W h.source_ne_nil, realize_sCount W' (IsZigzagDeletion.ne_nil h W.closed)]
    exact h.sCount
  zigzag_B := fun W W' h => by
    obtain ⟨hw, hD⟩ := zigzag_counts h
    unfold PLFront.defect
    rw [P_zigzag h, hw]
    rcases hD with hD | hD
    · rw [hD]
    · rw [hD]; push_cast; omega
  crossedCusp_s := fun W W' h => by
    rw [realize_sCount W h.ne_nil.1, realize_sCount W' h.ne_nil.2]
    exact h.sCount
  crossedCusp_B := fun W W' h => by
    obtain ⟨hw, hD⟩ := crossedCusp_counts h
    unfold PLFront.defect
    rw [P_crossedCusp h, hw]
    rcases hD with hD | hD <;> omega

/-- ng:circle, second sentence, for an arbitrary PL union of standard circles: `D = c`, `w = 0`,
`P = δ^{c−1}` (lp:split-circle's crossing-free clause), so `B = c − (c − 1) − 1 = 0`. -/
theorem PLFront.IsStandardCircles.defect_eq_zero (F : PLFront) (h : F.IsStandardCircles) : F.defect = 0 := by
  rw [h.defect_eq, PLFront.IsStandardCircles.downCount_eq_c_general F h, P_crossingFree h.1, degAZ_delta_pow]
  have hc := F.Γ.hc
  have hcc : F.diagram.componentCount = F.Γ.c := rfl
  omega

/-- **ng:circle** (row 81), assembled: display ng:circle-counts with `deg_a (δ P) = deg_a P + 1`
("Its product with the leading coefficient of P_after is nonzero because the coefficient ring is an
integral domain", sm-3:2061-2063: `degAZ_mul` in the domain `R`). -/
theorem ng_circle : NgCircleClauses where
  circleDeletion_B := fun W W' h => by
    obtain ⟨hw, hD⟩ := circleDeletion_counts h
    have hdeg : degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram) + 1 := by
      rw [P_circleDeletion h, degAZ_mul delta_ne_zero (P_ne_zero _), degAZ_delta]; ring
    unfold PLFront.defect
    rw [hdeg, hw, hD]
    push_cast; ring
  single_B := fun F h _ => PLFront.IsStandardCircles.defect_eq_zero F h
  union_B := fun F h => PLFront.IsStandardCircles.defect_eq_zero F h

section Skein

/-- display ng:skein-defect, first line, for the direction `A = l_{m+1}σ_m`, `A' = l_mσ_{m+1}`
(sm-3:2128-2160). -/
theorem skein_ineq_forward {A A' C : OWord} (h : IsCuspSkeinStep A.letters A'.letters C.letters) :
    min (realize A').defect (realize C).defect ≤ (realize A).defect := by
  obtain ⟨x, D₀, hsm, hPA', hP₀, hsign⟩ := skein_site h
  obtain ⟨hDA, hDA'⟩ := skein_downCount h
  unfold PLFront.defect
  rw [hDA, hDA']
  rcases hsign with ⟨hpos, hwA, hwA'⟩ | ⟨hneg, hwA, hwA'⟩
  · have e := P_recursion_pos hsm hpos
    rw [← hPA', hP₀] at e
    have hb := degAZ_le_of_eq_pos (P_ne_zero _) (P_ne_zero _) e (P_ne_zero _)
    rw [hwA, hwA']
    rcases le_max_iff.1 hb with h1 | h1
    · exact le_trans (min_le_left _ _) (by omega)
    · exact le_trans (min_le_right _ _) (by omega)
  · have e := P_recursion_neg hsm hneg
    rw [← hPA', hP₀] at e
    have hb := degAZ_le_of_eq_neg (P_ne_zero _) (P_ne_zero _) e (P_ne_zero _)
    rw [hwA, hwA']
    rcases le_max_iff.1 hb with h1 | h1
    · exact le_trans (min_le_left _ _) (by omega)
    · exact le_trans (min_le_right _ _) (by omega)

/-- display ng:skein-defect, second line ("the other principal direction"): the site lives in `A'`, and
the recursion is solved the other way (sm-3:2134-2136, 2147-2150). -/
theorem skein_ineq_backward {A A' C : OWord} (h : IsCuspSkeinStep A'.letters A.letters C.letters) :
    min (realize A').defect (realize C).defect ≤ (realize A).defect := by
  obtain ⟨x, D₀, hsm, hPA, hP₀, hsign⟩ := skein_site h
  obtain ⟨hDA', hDA⟩ := skein_downCount h
  unfold PLFront.defect
  rw [hDA, hDA']
  rcases hsign with ⟨hpos, hwA', hwA⟩ | ⟨hneg, hwA', hwA⟩
  · have e := P_recursion_pos hsm hpos
    rw [← hPA, hP₀] at e
    have e' := switch_of_recursion_pos e
    have hb := degAZ_le_of_eq_neg (P_ne_zero _) (P_ne_zero _) e' (P_ne_zero _)
    rw [hwA, hwA']
    rcases le_max_iff.1 hb with h1 | h1
    · exact le_trans (min_le_left _ _) (by omega)
    · exact le_trans (min_le_right _ _) (by omega)
  · have e := P_recursion_neg hsm hneg
    rw [← hPA, hP₀] at e
    have e' := switch_of_recursion_neg e
    have hb := degAZ_le_of_eq_pos (P_ne_zero _) (P_ne_zero _) e' (P_ne_zero _)
    rw [hwA, hwA']
    rcases le_max_iff.1 hb with h1 | h1
    · exact le_trans (min_le_left _ _) (by omega)
    · exact le_trans (min_le_right _ _) (by omega)

end Skein

/-- **ng:cusp-skein** (row 82), assembled. -/
theorem ng_cusp_skein : NgCuspSkeinClauses where
  earlier_branch := fun _ _ _ h => by
    rcases h with h | h
    · exact skein_ineq_forward h
    · exact skein_ineq_backward h
  unique_smoothing := fun _ _ _ _ h h' => skein_unique h h'
  smoothing_s := fun A A' C h => by
    obtain ⟨hA, -, hC⟩ := h.ne_nil
    rw [realize_sCount A hA, realize_sCount C hC]
    exact h.sCount.2
  principal_s := fun A A' C h => by
    obtain ⟨hA, hA', -⟩ := h.ne_nil
    rw [realize_sCount A hA, realize_sCount A' hA']
    exact h.sCount.1

/-- Both displayed inequalities of ng:skein-defect (sm-3:2154-2158) from the row (the interchange is
symmetric in its principal branches). -/
theorem ng_cusp_skein_both {A A' C : OWord} (h : IsCuspSkein A.letters A'.letters C.letters) :
    min (realize A').defect (realize C).defect ≤ (realize A).defect ∧
    min (realize A).defect (realize C).defect ≤ (realize A').defect :=
  ⟨ng_cusp_skein.earlier_branch A A' C h, ng_cusp_skein.earlier_branch A' A C h.symm⟩

/-! ## Row 83: the word bound, then the smooth front -/

/-- The seven laws of the descent (`Moves.Laws`) for the moves of `SM.ng_finite_word` with the geometric
`s`, `B` of the realization: `pres_B` = rows 76(1), 77, 78, 79; `del_B` = rows 80, 81(1); `skein_B` =
row 82; `base_B` = row 81(2-3) on the syntactic base; the three `s` laws are the accepted
`wordMoves_pres_s/del_s/skein_s`. -/
theorem certificate_laws :
    (wordMovesOf (fun W => (realize W).sCount) (fun W => (realize W).defect) OWord.IsStandardCircleBase).Laws where
  pres_B := fun F F' h => by
    rcases h with h | h | h | h
    · exact ng_commutation.comm_B F F' h
    · exact ng_front_I.typeI_B F F' h
    · exact ng_front_II.typeII_B F F' h
    · exact ng_front_III.typeIII_B F F' h
  pres_s := fun F F' h => wordMoves_pres_s F F' h
  del_B := fun F F' h => by
    rcases h with h | h | h
    · exact ng_deletions.zigzag_B F F' h
    · exact ng_deletions.crossedCusp_B F F' h
    · exact (ng_circle.circleDeletion_B F F' h).symm.le
  del_s := fun F F' h => wordMoves_del_s F F' h
  skein_B := fun F F' C h => ng_cusp_skein.earlier_branch F F' C h
  skein_s := fun F F' C h => wordMoves_skein_s F F' C h
  base_B := fun W hW => base_defect_nonneg W hW

/-- ng:local-front-bound on words (sm-3:2314-2343, the degree induction along the principal chains of
Literature input ng:finite-word): `B ≥ 0` on every closed oriented word's realization.  Consumes
`SM.ng_finite_word`. -/
theorem word_bound : ∀ W : OWord, 0 ≤ (realize W).defect :=
  ng_finite_word_bound _ _ certificate_laws

/-- **ng:local-front-bound** (row 83), assembled: the representation clause of ng:commutation carries `D`,
`w` and the rounding's record to a word; rp:record-polynomial (`presentations`) carries `P`; the word
bound gives `B ≥ 0`; display ng:defect converts (sm-3:2343). -/
theorem ng_local_front_bound : NgLocalFrontBoundClauses where
  front_inequality := fun F S hS => by
    obtain ⟨W, hD, hw, -, hrec⟩ := ng_commutation.represent F
    have hP : P S = P (realize W).diagram := presentations S _ (hrec S hS)
    have h0 := word_bound W
    rw [← F.defect_nonneg_iff S]
    unfold SmoothFront.defect SmoothFront.dOf
    rw [hD, hw, hP]
    exact h0

end SM
