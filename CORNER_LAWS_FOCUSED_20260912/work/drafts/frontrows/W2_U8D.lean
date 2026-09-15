import SM.FrontRealizeGeometry
import SM.FrontRealizeBase
import SM.FrontRealizeDeform
import SM.FrontInterfaces
import SM.FrontWordsBase
import SM.FrontGeomModel
import SM.PolynomialBlock
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-! # Front certificate rows 76-83 — PROOF SKELETON (FINAL, judge 2026-09-14)

work/drafts/frontrows/Skeleton_FINAL.lean.  The definitions and the eight bundles are copied verbatim from
Statements_FINAL.lean; the eight row theorems are ASSEMBLED at the end from the named LEAVES of section
"Leaves" (26 placeholders, none a row); all glue is proved.  Plan and unit split: PLAN_FINAL.md (units U1-U8).

Leaf groups (PLAN_FINAL.md §5):
* **L-deg** (U1): Laurent-degree arithmetic on `R` — `delta_ne_zero`, `degAZ_delta`, the two skein degree
  bounds (displays ng:skein-plus/minus, ng:degree-plus/minus).
* **L-cnt** (U1): the count changes `ΔD`, `Δw` of each pattern on the realization, through the accepted letter
  tracing (`realize_downCount`, `realize_writhe`) — displays ng:type-I-counts, ng:zigzag-counts,
  ng:crossed-cusp-counts, ng:circle-counts and the (t,u) table.
* **L-rec** (U3, on the record core U2): named-record isomorphisms for the moves that are NOT Reidemeister moves
  of the ordinary diagram — commutation, zigzag deletion, circle deletion (`Record.addFree`), the cusp-skein
  site (switch record + smoothing record + sign), and the uniqueness of the compatible smoothing.
* **L-geo** (U5, U6 on the geometry core U4): the disc-local moves — type III directly between the two standard
  realizations (`RIIIData` in a band disc hugging the three strands), types I, II and the crossed cusp through
  a vertex-moved diagram `D` (same shadow structure as `realize W`, the active strand's interior vertices moved
  inside a convex disc hugging the active strands; `RI`/`RII` there) whose named record is that of `realize W'`.
  NOT through the full-height block rectangle `BlockSetup.U`: `ArcCover` (LinkMoves.lean:208) forbids
  spectator strands inside the move disc (PLAN_FINAL.md §3 F1).
* **L-PL** (U7): the planarity fact `D = c` for an arbitrary PL union of standard circles (row 81 sentence 2).
* **L-smooth** (U8): the smooth clauses of row 76 (nonsingular deformation; representation).

Every leaf below is a TRUE statement about the accepted objects (audited in PLAN_FINAL.md §4); no leaf fixes a
move disc.  Checked with `cd work/lean && lake env lean`. -/

namespace SM

open SM.FrontWord SM.Link
open scoped ContDiff

/-! ## Statements (verbatim from Statements_FINAL.lean) -/

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

/-! ### Nonemptiness helpers (the `s` clauses read `realize_sCount`, which needs a nonempty word) -/

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

namespace FrontRows

/-! ## Leaves -/

section Leaves

/-! ### L-deg (unit U1) — Laurent-degree arithmetic (def:adeg, `SM/LinkLaurentRing.lean`) -/

/-- LEAF: `δ = (a − a⁻¹) z⁻¹ ≠ 0` (units and the domain `R`). -/
theorem u1_aInv_ne_zero : R.aInv ≠ 0 := (R.aUnit⁻¹).ne_zero
theorem u1_zInv_ne_zero : R.zInv ≠ 0 := (R.zUnit⁻¹).ne_zero

theorem u1_coeffAt_aInv (d k : ℤ) : coeffAt d k R.aInv = if ((-1 : ℤ), (0 : ℤ)) = (d, k) then 1 else 0 :=
  coeffAt_single ..

theorem u1_coeffAt_a_sub_aInv_one : coeffAt 1 0 (R.a - R.aInv) = 1 := by
  rw [coeffAt_sub, coeffAt_a, u1_coeffAt_aInv]
  simp

theorem u1_a_sub_aInv_ne_zero : R.a - R.aInv ≠ 0 := by
  intro h
  have := u1_coeffAt_a_sub_aInv_one
  rw [h, coeffAt_zero] at this
  exact absurd this (by decide)

theorem delta_ne_zero : R.delta ≠ 0 :=
  mul_ne_zero u1_a_sub_aInv_ne_zero u1_zInv_ne_zero

/-- LEAF (ng:circle, sm-3:2060-2061 "The leading a coefficient of δ is z⁻¹, in degree one"): `deg_a δ = 1`. -/
theorem u1_degAZ_of_degA {f : R} {d : ℤ} (h : degA f = (d : WithBot ℤ)) : degAZ f = d := by
  rw [degAZ, h, WithBot.unbotD_coe]

theorem u1_degAZ_a : degAZ R.a = 1 := u1_degAZ_of_degA (by rw [degA_a, WithBot.coe_one])
theorem u1_degAZ_aInv : degAZ R.aInv = -1 := u1_degAZ_of_degA degA_aInv
theorem u1_degAZ_z : degAZ R.z = 0 := u1_degAZ_of_degA (by rw [degA_z, WithBot.coe_zero])
theorem u1_degAZ_zInv : degAZ R.zInv = 0 := u1_degAZ_of_degA (degA_single 0 (-1) one_ne_zero)

theorem u1_degAZ_a_sub_aInv : degAZ (R.a - R.aInv) = 1 := by
  apply degAZ_eq_of_spec
  · exact ⟨0, by rw [u1_coeffAt_a_sub_aInv_one]; decide⟩
  · intro d k h
    rw [coeffAt_sub, coeffAt_a, u1_coeffAt_aInv] at h
    by_contra hlt
    rw [not_le] at hlt
    have h1 : ¬ ((1 : ℤ), (0 : ℤ)) = (d, k) := by
      intro e; rw [Prod.mk.injEq] at e; omega
    have h2 : ¬ ((-1 : ℤ), (0 : ℤ)) = (d, k) := by
      intro e; rw [Prod.mk.injEq] at e; omega
    simp [h1, h2] at h

theorem degAZ_delta : degAZ R.delta = 1 := by
  rw [R.delta, degAZ_mul u1_a_sub_aInv_ne_zero u1_zInv_ne_zero, u1_degAZ_a_sub_aInv, u1_degAZ_zInv]
  rfl

/-- LEAF (display ng:skein-plus solved for degrees, sm-3:2137-2146 "The degree of a nonzero sum is at most
the maximum of the summand degrees.  Multiplication by a^k shifts degree by k, and multiplication by z
does not change it"): from `f = a⁻² g + a⁻¹ z h`, `deg_a f ≤ max (deg_a g − 2) (deg_a h − 1)`
(`degA_add_le`, `degAZ_mul`, `degA_aInv`, `degA_z`). -/
theorem u1_degAZ_le_max_of_degA_le {f : R} {x y : ℤ} (hf : f ≠ 0)
    (h : degA f ≤ max (x : WithBot ℤ) (y : WithBot ℤ)) : degAZ f ≤ max x y := by
  rw [degA_eq_degAZ hf] at h
  rcases le_max_iff.1 h with h | h
  · exact le_max_of_le_left (WithBot.coe_le_coe.1 h)
  · exact le_max_of_le_right (WithBot.coe_le_coe.1 h)

theorem degAZ_le_of_eq_pos {f g h : R} (hg : g ≠ 0) (hh : h ≠ 0)
    (e : f = R.aInv * R.aInv * g + R.aInv * R.z * h) (hf : f ≠ 0) :
    degAZ f ≤ max (degAZ g - 2) (degAZ h - 1) := by
  have hg' : R.aInv * R.aInv * g ≠ 0 := mul_ne_zero (mul_ne_zero u1_aInv_ne_zero u1_aInv_ne_zero) hg
  have hh' : R.aInv * R.z * h ≠ 0 := mul_ne_zero (mul_ne_zero u1_aInv_ne_zero R.z_ne_zero) hh
  have h1 : degAZ (R.aInv * R.aInv * g) = degAZ g - 2 := by
    rw [degAZ_mul (mul_ne_zero u1_aInv_ne_zero u1_aInv_ne_zero) hg, degAZ_mul u1_aInv_ne_zero u1_aInv_ne_zero,
      u1_degAZ_aInv]; ring
  have h2 : degAZ (R.aInv * R.z * h) = degAZ h - 1 := by
    rw [degAZ_mul (mul_ne_zero u1_aInv_ne_zero R.z_ne_zero) hh, degAZ_mul u1_aInv_ne_zero R.z_ne_zero,
      u1_degAZ_aInv, u1_degAZ_z]; ring
  have hle := degA_add_le (R.aInv * R.aInv * g) (R.aInv * R.z * h)
  rw [← e, degA_eq_degAZ hg', degA_eq_degAZ hh', h1, h2] at hle
  exact u1_degAZ_le_max_of_degA_le hf hle

/-- LEAF (display ng:skein-minus solved for degrees, sm-3:2140-2148): from `f = a² g − a z h`,
`deg_a f ≤ max (deg_a g + 2) (deg_a h + 1)`. -/
theorem degAZ_le_of_eq_neg {f g h : R} (hg : g ≠ 0) (hh : h ≠ 0)
    (e : f = R.a * R.a * g - R.a * R.z * h) (hf : f ≠ 0) :
    degAZ f ≤ max (degAZ g + 2) (degAZ h + 1) := by
  have hg' : R.a * R.a * g ≠ 0 := mul_ne_zero (mul_ne_zero R.a_ne_zero R.a_ne_zero) hg
  have hh' : R.a * R.z * h ≠ 0 := mul_ne_zero (mul_ne_zero R.a_ne_zero R.z_ne_zero) hh
  have h1 : degAZ (R.a * R.a * g) = degAZ g + 2 := by
    rw [degAZ_mul (mul_ne_zero R.a_ne_zero R.a_ne_zero) hg, degAZ_mul R.a_ne_zero R.a_ne_zero, u1_degAZ_a]; ring
  have h2 : degAZ (R.a * R.z * h) = degAZ h + 1 := by
    rw [degAZ_mul (mul_ne_zero R.a_ne_zero R.z_ne_zero) hh, degAZ_mul R.a_ne_zero R.z_ne_zero,
      u1_degAZ_a, u1_degAZ_z]; ring
  have hle := degA_sub_le (R.a * R.a * g) (R.a * R.z * h)
  rw [← e, degA_eq_degAZ hg', degA_eq_degAZ hh', h1, h2] at hle
  exact u1_degAZ_le_max_of_degA_le hf hle

/-! ### L-cnt (unit U1) — the count changes on the realization, through the accepted letter tracing
(`realize_downCount`, `realize_writhe` = β1's `downCountFrom`/`writheFrom` over `X ++ P ++ Y` at the typed
cut before the factor; the printed displays are the factor's own contribution) -/

/-! ### U1 infrastructure — letter tracing of `D` and `w` on the word layer: `downCountFrom` /
`writheFrom` over appends (the run of the prefix fixes the cut before the factor), the bit values of the letters
at a decomposed cut (`downBit`, `signBit` read only the window of `arity` strands at the letter's position), and
the local value of every printed pattern on the symbolic cut — the displays ng:type-I-counts, ng:zigzag-counts,
ng:crossed-cusp-counts, ng:circle-counts, the (t,u) table, and the two disjoint-gadget commutations. -/
section U1Infra

open SM.FrontWord.Letter SM.FrontWord.Word

theorem u1_downCountFrom_nil (c : Cuts) : Word.downCountFrom [] c = 0 := rfl
theorem u1_writheFrom_nil (c : Cuts) : Word.writheFrom [] c = 0 := rfl

theorem u1_downCountFrom_cons {a : Letter} {V : Word} {c c' : Cuts} (h : a.step c = some c') :
    Word.downCountFrom (a :: V) c = a.downBit c + V.downCountFrom c' := by
  simp only [Word.downCountFrom, h]

theorem u1_writheFrom_cons {a : Letter} {V : Word} {c c' : Cuts} (h : a.step c = some c') :
    Word.writheFrom (a :: V) c = a.signBit c + V.writheFrom c' := by
  simp only [Word.writheFrom, h]

theorem u1_downCountFrom_append {V W : Word} {c c' : Cuts} (h : Word.run V c = some c') :
    (V ++ W).downCountFrom c = V.downCountFrom c + W.downCountFrom c' := by
  induction V generalizing c with
  | nil =>
    simp only [run_nil, Option.some.injEq] at h
    subst h
    simp [u1_downCountFrom_nil]
  | cons a V ih =>
    rw [run_cons, Option.bind_eq_some_iff] at h
    obtain ⟨c₁, h1, h2⟩ := h
    rw [List.cons_append, u1_downCountFrom_cons h1, u1_downCountFrom_cons h1, ih h2, add_assoc]

theorem u1_writheFrom_append {V W : Word} {c c' : Cuts} (h : Word.run V c = some c') :
    (V ++ W).writheFrom c = V.writheFrom c + W.writheFrom c' := by
  induction V generalizing c with
  | nil =>
    simp only [run_nil, Option.some.injEq] at h
    subst h
    simp [u1_writheFrom_nil]
  | cons a V ih =>
    rw [run_cons, Option.bind_eq_some_iff] at h
    obtain ⟨c₁, h1, h2⟩ := h
    rw [List.cons_append, u1_writheFrom_cons h1, u1_writheFrom_cons h1, ih h2, add_assoc]

theorem u1_run_append_some {X P : Word} {c₀ c₁ : Cuts} (hX : Word.run X [] = some c₀)
    (hP : Word.run P c₀ = some c₁) : Word.run (X ++ P) [] = some c₁ := by
  rw [run_append, hX]; exact hP

theorem u1_downCountFrom_append₃ (X P Y : Word) {c₀ c₁ : Cuts} (hX : Word.run X [] = some c₀)
    (hP : Word.run P c₀ = some c₁) :
    (X ++ P ++ Y).downCountFrom [] = X.downCountFrom [] + P.downCountFrom c₀ + Y.downCountFrom c₁ := by
  rw [u1_downCountFrom_append (u1_run_append_some hX hP), u1_downCountFrom_append hX]

theorem u1_writheFrom_append₃ (X P Y : Word) {c₀ c₁ : Cuts} (hX : Word.run X [] = some c₀)
    (hP : Word.run P c₀ = some c₁) :
    (X ++ P ++ Y).writheFrom [] = X.writheFrom [] + P.writheFrom c₀ + Y.writheFrom c₁ := by
  rw [u1_writheFrom_append (u1_run_append_some hX hP), u1_writheFrom_append hX]

/-! bit values -/

theorem u1_downBit_l (m : ℕ) (d : Bool) (c : Cuts) : (Letter.l m d).downBit c = if d then 0 else 1 := rfl
theorem u1_downBit_σ (m : ℕ) (c : Cuts) : (Letter.σ m).downBit c = 0 := rfl
theorem u1_signBit_l (m : ℕ) (d : Bool) (c : Cuts) : (Letter.l m d).signBit c = 0 := rfl
theorem u1_signBit_r (m : ℕ) (c : Cuts) : (Letter.r m).signBit c = 0 := rfl

theorem u1_downBit_r {m : ℕ} {A L : Cuts} (b : Bool) (hA : A.length = m - 1) :
    (Letter.r m).downBit (A ++ b :: L) = if b then 1 else 0 := by
  simp only [downBit]
  rw [List.drop_left' hA]
  cases b <;> rfl

theorem u1_signBit_σ {m : ℕ} {A L : Cuts} (a b : Bool) (hA : A.length = m - 1) :
    (Letter.σ m).signBit (A ++ a :: b :: L) = if a = b then 1 else -1 := by
  simp only [signBit]
  rw [List.drop_left' hA]

/-- the down bit of a letter reads only its window of `arity` strands at its position -/
theorem u1_downBit_window {ℓ : Letter} {n : ℕ} {A A' w R R' : Cuts} (hA : A.length = ℓ.idx - 1)
    (hA' : A'.length = n - 1) (hw : w.length = ℓ.arity) :
    (ℓ.reindex n).downBit (A' ++ (w ++ R')) = ℓ.downBit (A ++ (w ++ R)) := by
  cases ℓ with
  | l m d => rfl
  | σ m => rfl
  | r m =>
    simp only [downBit, reindex, idx] at hA hA' ⊢
    rw [List.drop_left' hA, List.drop_left' hA']
    obtain ⟨p, q, rfl⟩ : ∃ p q, w = [p, q] := by
      match w, hw with
      | [p, q], _ => exact ⟨p, q, rfl⟩
    cases p <;> rfl

theorem u1_signBit_window {ℓ : Letter} {n : ℕ} {A A' w R R' : Cuts} (hA : A.length = ℓ.idx - 1)
    (hA' : A'.length = n - 1) (hw : w.length = ℓ.arity) :
    (ℓ.reindex n).signBit (A' ++ (w ++ R')) = ℓ.signBit (A ++ (w ++ R)) := by
  cases ℓ with
  | l m d => rfl
  | r m => rfl
  | σ m =>
    simp only [signBit, reindex, idx] at hA hA' ⊢
    rw [List.drop_left' hA, List.drop_left' hA']
    obtain ⟨p, q, rfl⟩ : ∃ p q, w = [p, q] := by
      match w, hw with
      | [p, q], _ => exact ⟨p, q, rfl⟩
    rfl


/-! drop helpers -/

theorem u1_drop_eq₁ {A L : Cuts} {x : Bool} {k : ℕ} (hA : A.length + 1 = k) : (A ++ x :: L).drop k = L := by
  rw [List.append_cons]
  exact List.drop_left' (by rw [List.length_append, List.length_singleton]; exact hA)

theorem u1_downBit_r_drop {m : ℕ} {c L : Cuts} {b : Bool} (h : c.drop (m - 1) = b :: L) :
    (Letter.r m).downBit c = if b then 1 else 0 := by
  simp only [downBit]
  rw [h]
  cases b <;> rfl

theorem u1_signBit_σ_drop {m : ℕ} {c L : Cuts} {a b : Bool} (h : c.drop (m - 1) = a :: b :: L) :
    (Letter.σ m).signBit c = if a = b then 1 else -1 := by
  simp only [signBit]
  rw [h]

theorem u1_downBit_window' {ℓ : Letter} {A A' w R R' : Cuts} (hA : A.length = ℓ.idx - 1)
    (hA' : A'.length = ℓ.idx - 1) (hw : w.length = ℓ.arity) :
    ℓ.downBit (A' ++ (w ++ R')) = ℓ.downBit (A ++ (w ++ R)) := by
  have := u1_downBit_window (n := ℓ.idx) (R := R) (R' := R') hA hA' hw
  rwa [reindex_self] at this

theorem u1_signBit_window' {ℓ : Letter} {A A' w R R' : Cuts} (hA : A.length = ℓ.idx - 1)
    (hA' : A'.length = ℓ.idx - 1) (hw : w.length = ℓ.arity) :
    ℓ.signBit (A' ++ (w ++ R')) = ℓ.signBit (A ++ (w ++ R)) := by
  have := u1_signBit_window (n := ℓ.idx) (R := R) (R' := R') hA hA' hw
  rwa [reindex_self] at this

/-! ### Type I -/

theorem u1_typeI_left_local {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 2 ≤ m)
    (h : Word.run [.l m d, .σ (m - 1), .r m] c = some c') :
    Word.downCountFrom [.l m d, .σ (m - 1), .r m] c = 1 ∧
      Word.writheFrom [.l m d, .σ (m - 1), .r m] c = 1 := by
  rw [run_three_iff] at h
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  obtain ⟨A', a, rfl, hA'⟩ := exists_split_last A (m - 2) (by omega)
  have h2' : (Letter.σ (m - 1)).step (A' ++ [a] ++ d :: (!d) :: L) = some (A' ++ d :: a :: (!d) :: L) := by
    rw [List.append_assoc, List.singleton_append]
    exact step_of_prefix (ℓ := .σ (m - 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  rw [h2'] at h2
  obtain rfl := Option.some.inj h2
  have had : a = d := by
    have h3' := h3
    rw [show A' ++ d :: a :: (!d) :: L = (A' ++ [d]) ++ a :: (!d) :: L by simp,
      step_prefix (ℓ := .r m) (by idxomega) (by idxomega), act_r_cons] at h3'
    split_ifs at h3' with had
    · exact Bool.not_eq_not.mp had
    · simp at h3'
  have hdrop : (A' ++ d :: a :: (!d) :: L).drop (m - 1) = a :: (!d) :: L := u1_drop_eq₁ (by omega)
  have hdrop1 : (A' ++ [a] ++ d :: (!d) :: L).drop (m - 1 - 1) = a :: d :: (!d) :: L := by
    rw [List.append_assoc]; exact List.drop_left' (by omega)
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2', u1_downCountFrom_cons h3, u1_downCountFrom_nil,
      u1_downBit_l, u1_downBit_σ, u1_downBit_r_drop hdrop, had]
    cases d <;> simp
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2', u1_writheFrom_cons h3, u1_writheFrom_nil,
      u1_signBit_l, u1_signBit_r, u1_signBit_σ_drop hdrop1, had]
    simp

theorem u1_typeI_right_local {m : ℕ} {d : Bool} {c c' : Cuts} (_hm : 1 ≤ m)
    (h : Word.run [.l m d, .σ (m + 1), .r m] c = some c') :
    Word.downCountFrom [.l m d, .σ (m + 1), .r m] c = 1 ∧
      Word.writheFrom [.l m d, .σ (m + 1), .r m] c = 1 := by
  rw [run_three_iff] at h
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  obtain ⟨b, L₀, rfl⟩ : ∃ b L₀, L = b :: L₀ :=
    exists_cons_of_σ_succ (m := m) (A := A ++ [d]) (by idxomega)
      (by rw [show (A ++ [d]) ++ (!d) :: L = A ++ d :: (!d) :: L by simp]; exact h2)
  have h2' : (Letter.σ (m + 1)).step (A ++ d :: (!d) :: b :: L₀) = some (A ++ d :: b :: (!d) :: L₀) := by
    rw [show A ++ d :: (!d) :: b :: L₀ = (A ++ [d]) ++ (!d) :: b :: L₀ by simp,
      step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
    simp
  rw [h2'] at h2
  obtain rfl := Option.some.inj h2
  have hbd : b = !d := by
    have h3' := h3
    rw [step_prefix (ℓ := .r m) (by idxomega) (by idxomega), act_r_cons] at h3'
    split_ifs at h3' with hdb
    · exact Bool.eq_not.mpr (Ne.symm hdb)
    · simp at h3'
  have hdrop : (A ++ d :: b :: (!d) :: L₀).drop (m - 1) = d :: b :: (!d) :: L₀ := List.drop_left' hA
  have hdrop1 : (A ++ d :: (!d) :: b :: L₀).drop (m + 1 - 1) = (!d) :: b :: L₀ := u1_drop_eq₁ (by omega)
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2', u1_downCountFrom_cons h3, u1_downCountFrom_nil,
      u1_downBit_l, u1_downBit_σ, u1_downBit_r_drop hdrop]
    cases d <;> simp
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2', u1_writheFrom_cons h3, u1_writheFrom_nil,
      u1_signBit_l, u1_signBit_r, u1_signBit_σ_drop hdrop1, hbd]
    simp

/-! ### Zigzag, circle, crossed cusp -/

theorem u1_zigzag_below_local {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 1 ≤ m)
    (h : Word.run [.l m d, .r (m + 1)] c = some c') :
    Word.downCountFrom [.l m d, .r (m + 1)] c = (if d then 0 else 2) ∧
      Word.writheFrom [.l m d, .r (m + 1)] c = 0 := by
  rw [run_two_iff] at h
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  have hdrop : (A ++ d :: (!d) :: L).drop (m + 1 - 1) = (!d) :: L := u1_drop_eq₁ (by omega)
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2, u1_downCountFrom_nil, u1_downBit_l,
      u1_downBit_r_drop hdrop]
    cases d <;> simp
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2, u1_writheFrom_nil, u1_signBit_l, u1_signBit_r]
    simp

theorem u1_zigzag_above_local {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 1 ≤ m)
    (h : Word.run [.l (m + 1) d, .r m] c = some c') :
    Word.downCountFrom [.l (m + 1) d, .r m] c = (if d then 0 else 2) ∧
      Word.writheFrom [.l (m + 1) d, .r m] c = 0 := by
  rw [run_two_iff] at h
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  obtain ⟨A', b, rfl, hA'⟩ := exists_split_last A (m - 1) (by omega)
  have hbd : b = !d := by
    have h2' := h2
    rw [List.append_assoc, List.singleton_append, step_prefix (ℓ := .r m) (by idxomega) (by idxomega),
      act_r_cons] at h2'
    split_ifs at h2' with hbd
    · exact Bool.eq_not.mpr hbd
    · simp at h2'
  have hdrop : (A' ++ [b] ++ d :: (!d) :: L).drop (m - 1) = b :: d :: (!d) :: L := by
    rw [List.append_assoc]; exact List.drop_left' hA'
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2, u1_downCountFrom_nil, u1_downBit_l,
      u1_downBit_r_drop hdrop, hbd]
    cases d <;> simp
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2, u1_writheFrom_nil, u1_signBit_l, u1_signBit_r]
    simp

theorem u1_circle_local {m : ℕ} {d : Bool} {c c' : Cuts} (_hm : 1 ≤ m)
    (h : Word.run [.l m d, .r m] c = some c') :
    Word.downCountFrom [.l m d, .r m] c = 1 ∧ Word.writheFrom [.l m d, .r m] c = 0 := by
  rw [run_two_iff] at h
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  have hdrop : (A ++ d :: (!d) :: L).drop (m - 1) = d :: (!d) :: L := List.drop_left' hA
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2, u1_downCountFrom_nil, u1_downBit_l,
      u1_downBit_r_drop hdrop]
    cases d <;> simp
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2, u1_writheFrom_nil, u1_signBit_l, u1_signBit_r]
    simp

theorem u1_crossedCusp_l_local {i : ℕ} {d : Bool} {c c' : Cuts} (hi : 1 ≤ i)
    (h : Word.run [.l i d, .σ i] c = some c') :
    (Word.downCountFrom [.l i (!d)] c + 1 = Word.downCountFrom [.l i d, .σ i] c ∨
      Word.downCountFrom [.l i (!d)] c = Word.downCountFrom [.l i d, .σ i] c + 1) ∧
    Word.writheFrom [.l i d, .σ i] c = -1 ∧ Word.writheFrom [.l i (!d)] c = 0 := by
  rw [run_two_iff] at h
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  have h1' : (Letter.l i (!d)).step (A ++ L) = some (A ++ (!d) :: (!!d) :: L) :=
    step_of_prefix (ℓ := .l i (!d)) (by idxomega) (by idxomega) (act_l _ _ _)
  have hdrop : (A ++ d :: (!d) :: L).drop (i - 1) = d :: (!d) :: L := List.drop_left' hA
  refine ⟨?_, ?_, ?_⟩
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2, u1_downCountFrom_nil, u1_downBit_l,
      u1_downBit_σ, u1_downCountFrom_cons h1', u1_downCountFrom_nil, u1_downBit_l]
    cases d <;> simp
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2, u1_writheFrom_nil, u1_signBit_l,
      u1_signBit_σ_drop hdrop]
    cases d <;> simp
  · rw [u1_writheFrom_cons h1', u1_writheFrom_nil, u1_signBit_l]; simp

theorem u1_crossedCusp_r_local {i : ℕ} {c c' : Cuts} (hi : 1 ≤ i)
    (h : Word.run [.σ i, .r i] c = some c') :
    (Word.downCountFrom [.r i] c + 1 = Word.downCountFrom [.σ i, .r i] c ∨
      Word.downCountFrom [.r i] c = Word.downCountFrom [.σ i, .r i] c + 1) ∧
    Word.writheFrom [.σ i, .r i] c = -1 ∧ Word.writheFrom [.r i] c = 0 := by
  rw [run_two_iff] at h
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  obtain ⟨p, q, L₀, rfl, rfl⟩ := act_σ_eq_some_iff.1 hL
  simp only [idx] at hA
  have hpq : p ≠ q := by
    have h2' := h2
    rw [step_prefix (ℓ := .r i) (by idxomega) (by idxomega), act_r_cons] at h2'
    split_ifs at h2' with hqp
    · exact Ne.symm hqp
    · simp at h2'
  have h1' : (Letter.r i).step (A ++ p :: q :: L₀) = some (A ++ L₀) := by
    rw [step_prefix (ℓ := .r i) (by idxomega) (by idxomega), act_r_cons, ite_eq_left hpq]; rfl
  have hdrop : (A ++ p :: q :: L₀).drop (i - 1) = p :: q :: L₀ := List.drop_left' hA
  have hdrop1 : (A ++ q :: p :: L₀).drop (i - 1) = q :: p :: L₀ := List.drop_left' hA
  refine ⟨?_, ?_, ?_⟩
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2, u1_downCountFrom_nil, u1_downBit_σ,
      u1_downBit_r_drop hdrop1, u1_downCountFrom_cons h1', u1_downCountFrom_nil, u1_downBit_r_drop hdrop]
    cases p <;> cases q <;> simp_all
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2, u1_writheFrom_nil, u1_signBit_r,
      u1_signBit_σ_drop hdrop]
    simp [hpq]
  · rw [u1_writheFrom_cons h1', u1_writheFrom_nil, u1_signBit_r]; simp


/-! ### Type II -/

theorem u1_typeII_l_left_local {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 2 ≤ m)
    (h : Word.run [.l (m - 1) d, .σ m, .σ (m - 1)] c = some c') :
    Word.downCountFrom [.l (m - 1) d, .σ m, .σ (m - 1)] c = Word.downCountFrom [.l m d] c ∧
      Word.writheFrom [.l (m - 1) d, .σ m, .σ (m - 1)] c = Word.writheFrom [.l m d] c := by
  rw [run_three_iff] at h
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  obtain ⟨b, L₀, rfl⟩ : ∃ b L₀, L = b :: L₀ := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact exists_cons_of_σ_succ (m := m') (A := A ++ [d]) (by idxomega)
      (by rw [show (A ++ [d]) ++ (!d) :: L = A ++ d :: (!d) :: L by simp]; exact h2)
  have h2' : (Letter.σ m).step (A ++ d :: (!d) :: b :: L₀) = some (A ++ d :: b :: (!d) :: L₀) := by
    rw [show A ++ d :: (!d) :: b :: L₀ = (A ++ [d]) ++ (!d) :: b :: L₀ by simp,
      step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
    simp
  rw [h2'] at h2
  obtain rfl := Option.some.inj h2
  have h3' : (Letter.σ (m - 1)).step (A ++ d :: b :: (!d) :: L₀) = some (A ++ b :: d :: (!d) :: L₀) :=
    step_of_prefix (ℓ := .σ (m - 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  have hP' : (Letter.l m d).step (A ++ b :: L₀) = some (A ++ b :: d :: (!d) :: L₀) := by
    rw [show A ++ b :: L₀ = (A ++ [b]) ++ L₀ by simp,
      step_of_prefix (ℓ := .l m d) (by idxomega) (by idxomega) (act_l _ _ _)]
    simp
  have hdrop1 : (A ++ d :: (!d) :: b :: L₀).drop (m - 1) = (!d) :: b :: L₀ := u1_drop_eq₁ (by omega)
  have hdrop2 : (A ++ d :: b :: (!d) :: L₀).drop (m - 1 - 1) = d :: b :: (!d) :: L₀ := List.drop_left' hA
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2', u1_downCountFrom_cons h3', u1_downCountFrom_nil,
      u1_downCountFrom_cons hP', u1_downCountFrom_nil]
    simp only [u1_downBit_l, u1_downBit_σ, add_zero]
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2', u1_writheFrom_cons h3', u1_writheFrom_nil,
      u1_writheFrom_cons hP', u1_writheFrom_nil, u1_signBit_σ_drop hdrop1, u1_signBit_σ_drop hdrop2]
    simp only [u1_signBit_l]
    cases d <;> cases b <;> simp

theorem u1_typeII_l_right_local {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 1 ≤ m)
    (h : Word.run [.l (m + 1) d, .σ m, .σ (m + 1)] c = some c') :
    Word.downCountFrom [.l (m + 1) d, .σ m, .σ (m + 1)] c = Word.downCountFrom [.l m d] c ∧
      Word.writheFrom [.l (m + 1) d, .σ m, .σ (m + 1)] c = Word.writheFrom [.l m d] c := by
  rw [run_three_iff] at h
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  obtain ⟨A', b, rfl, hA'⟩ := exists_split_last A (m - 1) (by omega)
  have h2' : (Letter.σ m).step (A' ++ [b] ++ d :: (!d) :: L) = some (A' ++ d :: b :: (!d) :: L) := by
    rw [List.append_assoc, List.singleton_append]
    exact step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  rw [h2'] at h2
  obtain rfl := Option.some.inj h2
  have h3' : (Letter.σ (m + 1)).step (A' ++ d :: b :: (!d) :: L) = some (A' ++ d :: (!d) :: b :: L) := by
    rw [show A' ++ d :: b :: (!d) :: L = (A' ++ [d]) ++ b :: (!d) :: L by simp,
      step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
    simp
  have hP' : (Letter.l m d).step (A' ++ [b] ++ L) = some (A' ++ d :: (!d) :: b :: L) := by
    rw [List.append_assoc, List.singleton_append]
    exact step_of_prefix (ℓ := .l m d) (by idxomega) (by idxomega) (act_l _ _ _)
  have hdrop1 : (A' ++ [b] ++ d :: (!d) :: L).drop (m - 1) = b :: d :: (!d) :: L := by
    rw [List.append_assoc]; exact List.drop_left' hA'
  have hdrop2 : (A' ++ d :: b :: (!d) :: L).drop (m + 1 - 1) = b :: (!d) :: L := u1_drop_eq₁ (by omega)
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2', u1_downCountFrom_cons h3', u1_downCountFrom_nil,
      u1_downCountFrom_cons hP', u1_downCountFrom_nil]
    simp only [u1_downBit_l, u1_downBit_σ, add_zero]
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2', u1_writheFrom_cons h3', u1_writheFrom_nil,
      u1_writheFrom_cons hP', u1_writheFrom_nil, u1_signBit_σ_drop hdrop1, u1_signBit_σ_drop hdrop2]
    simp only [u1_signBit_l]
    cases d <;> cases b <;> simp

theorem u1_typeII_r_left_local {m : ℕ} {c c' : Cuts} (hm : 2 ≤ m)
    (h : Word.run [.σ (m - 1), .σ m, .r (m - 1)] c = some c') :
    Word.downCountFrom [.σ (m - 1), .σ m, .r (m - 1)] c = Word.downCountFrom [.r m] c ∧
      Word.writheFrom [.σ (m - 1), .σ m, .r (m - 1)] c = Word.writheFrom [.r m] c := by
  rw [run_three_iff] at h
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  obtain ⟨p, q, L₀, rfl, rfl⟩ := act_σ_eq_some_iff.1 hL
  simp only [idx] at hA
  obtain ⟨r, L₁, rfl⟩ : ∃ r L₁, L₀ = r :: L₁ := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact exists_cons_of_σ_succ (m := m') (A := A ++ [q]) (by idxomega)
      (by rw [show (A ++ [q]) ++ p :: L₀ = A ++ q :: p :: L₀ by simp]; exact h2)
  have h2' : (Letter.σ m).step (A ++ q :: p :: r :: L₁) = some (A ++ q :: r :: p :: L₁) := by
    rw [show A ++ q :: p :: r :: L₁ = (A ++ [q]) ++ p :: r :: L₁ by simp,
      step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
    simp
  rw [h2'] at h2
  obtain rfl := Option.some.inj h2
  have hqr : q ≠ r := by
    have h3' := h3
    rw [step_prefix (ℓ := .r (m - 1)) (by idxomega) (by idxomega), act_r_cons] at h3'
    split_ifs at h3' with hqr
    · exact hqr
    · simp at h3'
  have hP' : (Letter.r m).step (A ++ p :: q :: r :: L₁) = some (A ++ p :: L₁) := by
    rw [show A ++ p :: q :: r :: L₁ = (A ++ [p]) ++ q :: r :: L₁ by simp,
      step_prefix (ℓ := .r m) (by idxomega) (by idxomega), act_r_cons, ite_eq_left hqr]
    simp
  have hdrop0 : (A ++ p :: q :: r :: L₁).drop (m - 1 - 1) = p :: q :: r :: L₁ := List.drop_left' hA
  have hdrop1 : (A ++ q :: p :: r :: L₁).drop (m - 1) = p :: r :: L₁ := u1_drop_eq₁ (by omega)
  have hdrop2 : (A ++ q :: r :: p :: L₁).drop (m - 1 - 1) = q :: r :: p :: L₁ := List.drop_left' hA
  have hdropP : (A ++ p :: q :: r :: L₁).drop (m - 1) = q :: r :: L₁ := u1_drop_eq₁ (by omega)
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2', u1_downCountFrom_cons h3, u1_downCountFrom_nil,
      u1_downCountFrom_cons hP', u1_downCountFrom_nil, u1_downBit_r_drop hdrop2, u1_downBit_r_drop hdropP]
    simp only [u1_downBit_σ, add_zero, zero_add]
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2', u1_writheFrom_cons h3, u1_writheFrom_nil,
      u1_writheFrom_cons hP', u1_writheFrom_nil, u1_signBit_σ_drop hdrop0, u1_signBit_σ_drop hdrop1]
    simp only [u1_signBit_r]
    cases p <;> cases q <;> cases r <;> simp_all

theorem u1_typeII_r_right_local {m : ℕ} {c c' : Cuts} (hm : 1 ≤ m)
    (h : Word.run [.σ (m + 1), .σ m, .r (m + 1)] c = some c') :
    Word.downCountFrom [.σ (m + 1), .σ m, .r (m + 1)] c = Word.downCountFrom [.r m] c ∧
      Word.writheFrom [.σ (m + 1), .σ m, .r (m + 1)] c = Word.writheFrom [.r m] c := by
  rw [run_three_iff] at h
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  obtain ⟨q, r, L₀, rfl, rfl⟩ := act_σ_eq_some_iff.1 hL
  simp only [idx] at hA
  obtain ⟨A', p, rfl, hA'⟩ := exists_split_last A (m - 1) (by omega)
  have h2' : (Letter.σ m).step (A' ++ [p] ++ r :: q :: L₀) = some (A' ++ r :: p :: q :: L₀) := by
    rw [List.append_assoc, List.singleton_append]
    exact step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  rw [h2'] at h2
  obtain rfl := Option.some.inj h2
  have hpq : p ≠ q := by
    have h3' := h3
    rw [show A' ++ r :: p :: q :: L₀ = (A' ++ [r]) ++ p :: q :: L₀ by simp,
      step_prefix (ℓ := .r (m + 1)) (by idxomega) (by idxomega), act_r_cons] at h3'
    split_ifs at h3' with hpq
    · exact hpq
    · simp at h3'
  have hP' : (Letter.r m).step (A' ++ [p] ++ q :: r :: L₀) = some (A' ++ r :: L₀) := by
    rw [List.append_assoc, List.singleton_append, step_prefix (ℓ := .r m) (by idxomega) (by idxomega),
      act_r_cons, ite_eq_left hpq]
    simp
  have hdrop0 : (A' ++ [p] ++ q :: r :: L₀).drop (m + 1 - 1) = q :: r :: L₀ :=
    List.drop_left' (by rw [List.length_append, List.length_singleton]; omega)
  have hdrop1 : (A' ++ [p] ++ r :: q :: L₀).drop (m - 1) = p :: r :: q :: L₀ := by
    rw [List.append_assoc]; exact List.drop_left' hA'
  have hdrop2 : (A' ++ r :: p :: q :: L₀).drop (m + 1 - 1) = p :: q :: L₀ := u1_drop_eq₁ (by omega)
  have hdropP : (A' ++ [p] ++ q :: r :: L₀).drop (m - 1) = p :: q :: r :: L₀ := by
    rw [List.append_assoc]; exact List.drop_left' hA'
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2', u1_downCountFrom_cons h3, u1_downCountFrom_nil,
      u1_downCountFrom_cons hP', u1_downCountFrom_nil, u1_downBit_r_drop hdrop2, u1_downBit_r_drop hdropP]
    simp only [u1_downBit_σ, add_zero, zero_add]
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2', u1_writheFrom_cons h3, u1_writheFrom_nil,
      u1_writheFrom_cons hP', u1_writheFrom_nil, u1_signBit_σ_drop hdrop0, u1_signBit_σ_drop hdrop1]
    simp only [u1_signBit_r]
    cases p <;> cases q <;> cases r <;> simp_all

/-! ### Type III -/

theorem u1_typeIII_local {m : ℕ} {A L : Cuts} {p q r : Bool} (hm : 1 ≤ m) (hA : A.length = m - 1) :
    Word.downCountFrom [.σ (m + 1), .σ m, .σ (m + 1)] (A ++ p :: q :: r :: L) = 0 ∧
    Word.downCountFrom [.σ m, .σ (m + 1), .σ m] (A ++ p :: q :: r :: L) = 0 ∧
    Word.writheFrom [.σ (m + 1), .σ m, .σ (m + 1)] (A ++ p :: q :: r :: L) =
      Word.writheFrom [.σ m, .σ (m + 1), .σ m] (A ++ p :: q :: r :: L) := by
  have s1 : (Letter.σ (m + 1)).step (A ++ p :: q :: r :: L) = some (A ++ p :: r :: q :: L) := by
    rw [show A ++ p :: q :: r :: L = (A ++ [p]) ++ q :: r :: L by simp,
      step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
    simp
  have s2 : (Letter.σ m).step (A ++ p :: r :: q :: L) = some (A ++ r :: p :: q :: L) :=
    step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  have s3 : (Letter.σ (m + 1)).step (A ++ r :: p :: q :: L) = some (A ++ r :: q :: p :: L) := by
    rw [show A ++ r :: p :: q :: L = (A ++ [r]) ++ p :: q :: L by simp,
      step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
    simp
  have t1 : (Letter.σ m).step (A ++ p :: q :: r :: L) = some (A ++ q :: p :: r :: L) :=
    step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  have t2 : (Letter.σ (m + 1)).step (A ++ q :: p :: r :: L) = some (A ++ q :: r :: p :: L) := by
    rw [show A ++ q :: p :: r :: L = (A ++ [q]) ++ p :: r :: L by simp,
      step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
    simp
  have t3 : (Letter.σ m).step (A ++ q :: r :: p :: L) = some (A ++ r :: q :: p :: L) :=
    step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  have d1 : (A ++ p :: q :: r :: L).drop (m + 1 - 1) = q :: r :: L := u1_drop_eq₁ (by omega)
  have d2 : (A ++ p :: r :: q :: L).drop (m - 1) = p :: r :: q :: L := List.drop_left' hA
  have d3 : (A ++ r :: p :: q :: L).drop (m + 1 - 1) = p :: q :: L := u1_drop_eq₁ (by omega)
  have e1 : (A ++ p :: q :: r :: L).drop (m - 1) = p :: q :: r :: L := List.drop_left' hA
  have e2 : (A ++ q :: p :: r :: L).drop (m + 1 - 1) = p :: r :: L := u1_drop_eq₁ (by omega)
  have e3 : (A ++ q :: r :: p :: L).drop (m - 1) = q :: r :: p :: L := List.drop_left' hA
  refine ⟨?_, ?_, ?_⟩
  · rw [u1_downCountFrom_cons s1, u1_downCountFrom_cons s2, u1_downCountFrom_cons s3, u1_downCountFrom_nil]
    simp only [u1_downBit_σ, add_zero]
  · rw [u1_downCountFrom_cons t1, u1_downCountFrom_cons t2, u1_downCountFrom_cons t3, u1_downCountFrom_nil]
    simp only [u1_downBit_σ, add_zero]
  · rw [u1_writheFrom_cons s1, u1_writheFrom_cons s2, u1_writheFrom_cons s3, u1_writheFrom_nil,
      u1_writheFrom_cons t1, u1_writheFrom_cons t2, u1_writheFrom_cons t3, u1_writheFrom_nil,
      u1_signBit_σ_drop d1, u1_signBit_σ_drop d2, u1_signBit_σ_drop d3,
      u1_signBit_σ_drop e1, u1_signBit_σ_drop e2, u1_signBit_σ_drop e3]
    ring

/-! ### Cusp skein -/

theorem u1_skein_local {m : ℕ} {d a : Bool} {P L : Cuts} (hm : 1 ≤ m) (hP : P.length = m - 1) :
    Word.downCountFrom [.l (m + 1) d, .σ m] (P ++ a :: L) = (if d then 0 else 1) ∧
    Word.downCountFrom [.l m d, .σ (m + 1)] (P ++ a :: L) = (if d then 0 else 1) ∧
    Word.downCountFrom [.l m d] (P ++ a :: L) = (if d then 0 else 1) ∧
    Word.downCountFrom [.l (m + 1) d] (P ++ a :: L) = (if d then 0 else 1) ∧
    Word.writheFrom [.l (m + 1) d, .σ m] (P ++ a :: L) + Word.writheFrom [.l m d, .σ (m + 1)] (P ++ a :: L) = 0 ∧
    Word.writheFrom [.l m d] (P ++ a :: L) = 0 ∧ Word.writheFrom [.l (m + 1) d] (P ++ a :: L) = 0 := by
  have s1 : (Letter.l (m + 1) d).step (P ++ a :: L) = some (P ++ a :: d :: (!d) :: L) := by
    rw [show P ++ a :: L = (P ++ [a]) ++ L by simp,
      step_of_prefix (ℓ := .l (m + 1) d) (by idxomega) (by idxomega) (act_l _ _ _)]
    simp
  have s2 : (Letter.σ m).step (P ++ a :: d :: (!d) :: L) = some (P ++ d :: a :: (!d) :: L) :=
    step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  have t1 : (Letter.l m d).step (P ++ a :: L) = some (P ++ d :: (!d) :: a :: L) :=
    step_of_prefix (ℓ := .l m d) (by idxomega) (by idxomega) (act_l _ _ _)
  have t2 : (Letter.σ (m + 1)).step (P ++ d :: (!d) :: a :: L) = some (P ++ d :: a :: (!d) :: L) := by
    rw [show P ++ d :: (!d) :: a :: L = (P ++ [d]) ++ (!d) :: a :: L by simp,
      step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
    simp
  have d1 : (P ++ a :: d :: (!d) :: L).drop (m - 1) = a :: d :: (!d) :: L := List.drop_left' hP
  have d2 : (P ++ d :: (!d) :: a :: L).drop (m + 1 - 1) = (!d) :: a :: L := u1_drop_eq₁ (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u1_downCountFrom_cons s1, u1_downCountFrom_cons s2, u1_downCountFrom_nil]
    simp only [u1_downBit_l, u1_downBit_σ, add_zero]
  · rw [u1_downCountFrom_cons t1, u1_downCountFrom_cons t2, u1_downCountFrom_nil]
    simp only [u1_downBit_l, u1_downBit_σ, add_zero]
  · rw [u1_downCountFrom_cons t1, u1_downCountFrom_nil]
    simp only [u1_downBit_l, add_zero]
  · rw [u1_downCountFrom_cons s1, u1_downCountFrom_nil]
    simp only [u1_downBit_l, add_zero]
  · rw [u1_writheFrom_cons s1, u1_writheFrom_cons s2, u1_writheFrom_nil, u1_writheFrom_cons t1,
      u1_writheFrom_cons t2, u1_writheFrom_nil, u1_signBit_σ_drop d1, u1_signBit_σ_drop d2]
    simp only [u1_signBit_l]
    cases a <;> cases d <;> simp
  · rw [u1_writheFrom_cons t1, u1_writheFrom_nil]
    simp only [u1_signBit_l, add_zero]
  · rw [u1_writheFrom_cons s1, u1_writheFrom_nil]
    simp only [u1_signBit_l, add_zero]

/-! ### Commutations -/

theorem u1_comm_above_local {a b : Letter} {c c' : Cuts} (hab : b.idx + b.arity ≤ a.idx)
    (h : Word.run [a, b] c = some c') :
    Word.downCountFrom [a, b] c = Word.downCountFrom [b, a.reindex (a.idx + b.coarity - b.arity)] c ∧
    Word.writheFrom [a, b] c = Word.writheFrom [b, a.reindex (a.idx + b.coarity - b.arity)] c := by
  rw [run_two_iff] at h
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', ha1, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  obtain ⟨B, M, M', hb1, hB, hc₁, hM, rfl⟩ := step_eq_some_iff.1 h2
  obtain ⟨w, w', R, rfl, hw, hw', hw'len, rfl⟩ := act_window hM
  obtain ⟨A₁, H, rfl, hA₁⟩ := exists_split A (b.idx - 1 + b.arity) (by omega)
  have hlen : A₁.length = (B ++ w).length := by simp only [List.length_append]; omega
  rw [List.append_assoc, ← List.append_assoc B w R] at hc₁
  obtain ⟨rfl, hR⟩ := List.append_inj hc₁ hlen
  subst hR
  obtain ⟨v, v', S, rfl, hv, hv', hv'len, rfl⟩ := act_window hL
  have s1 : a.step (B ++ w ++ H ++ (v ++ S)) = some (B ++ (w ++ (H ++ (v' ++ S)))) := by
    rw [h1]; simp only [List.append_assoc]
  have s2 : b.step (B ++ (w ++ (H ++ (v' ++ S)))) = some (B ++ (w' ++ (H ++ (v' ++ S)))) :=
    step_of_prefix hb1 hB (by rw [act_append hw, hw']; rfl)
  have s1' : b.step (B ++ w ++ H ++ (v ++ S)) = some (B ++ w' ++ H ++ (v ++ S)) := by
    rw [show B ++ w ++ H ++ (v ++ S) = B ++ (w ++ (H ++ (v ++ S))) by simp only [List.append_assoc],
      step_of_prefix hb1 hB (L' := w' ++ (H ++ (v ++ S))) (by rw [act_append hw, hw']; rfl)]
    simp only [List.append_assoc]
  have s2' : (a.reindex (a.idx + b.coarity - b.arity)).step (B ++ w' ++ H ++ (v ++ S)) =
      some (B ++ w' ++ H ++ (v' ++ S)) :=
    step_of_prefix (ℓ := a.reindex _) (A := B ++ w' ++ H) (by lenomega) (by lenomega)
      (by rw [act_reindex]; exact hL)
  have e1 : (a.reindex (a.idx + b.coarity - b.arity)).downBit (B ++ w' ++ H ++ (v ++ S)) =
      a.downBit (B ++ w ++ H ++ (v ++ S)) := u1_downBit_window hA (by lenomega) hv
  have e2 : b.downBit (B ++ (w ++ (H ++ (v' ++ S)))) = b.downBit (B ++ w ++ H ++ (v ++ S)) := by
    rw [show B ++ w ++ H ++ (v ++ S) = B ++ (w ++ (H ++ (v ++ S))) by simp only [List.append_assoc]]
    exact u1_downBit_window' hB hB hw
  have f1 : (a.reindex (a.idx + b.coarity - b.arity)).signBit (B ++ w' ++ H ++ (v ++ S)) =
      a.signBit (B ++ w ++ H ++ (v ++ S)) := u1_signBit_window hA (by lenomega) hv
  have f2 : b.signBit (B ++ (w ++ (H ++ (v' ++ S)))) = b.signBit (B ++ w ++ H ++ (v ++ S)) := by
    rw [show B ++ w ++ H ++ (v ++ S) = B ++ (w ++ (H ++ (v ++ S))) by simp only [List.append_assoc]]
    exact u1_signBit_window' hB hB hw
  constructor
  · rw [u1_downCountFrom_cons s1, u1_downCountFrom_cons s2, u1_downCountFrom_nil,
      u1_downCountFrom_cons s1', u1_downCountFrom_cons s2', u1_downCountFrom_nil, e1, e2]
    ring
  · rw [u1_writheFrom_cons s1, u1_writheFrom_cons s2, u1_writheFrom_nil,
      u1_writheFrom_cons s1', u1_writheFrom_cons s2', u1_writheFrom_nil, f1, f2]
    ring

theorem u1_comm_below_local {a b : Letter} {c c' : Cuts} (hab : a.idx + a.coarity ≤ b.idx)
    (h : Word.run [a, b] c = some c') :
    Word.downCountFrom [a, b] c = Word.downCountFrom [b.reindex (b.idx + a.arity - a.coarity), a] c ∧
    Word.writheFrom [a, b] c = Word.writheFrom [b.reindex (b.idx + a.arity - a.coarity), a] c := by
  rw [run_two_iff] at h
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', ha1, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  obtain ⟨w, w', R, rfl, hw, hw', hw'len, rfl⟩ := act_window hL
  obtain ⟨B, M, M', hb1, hB, hc₁, hM, rfl⟩ := step_eq_some_iff.1 h2
  obtain ⟨B₁, H, rfl, hB₁⟩ := exists_split B (a.idx - 1 + a.coarity) (by omega)
  have hlen : (A ++ w').length = B₁.length := by simp only [List.length_append]; omega
  rw [← List.append_assoc, List.append_assoc B₁ H M] at hc₁
  obtain ⟨hB₁eq, hR⟩ := List.append_inj hc₁ hlen
  subst hB₁eq
  subst hR
  obtain ⟨u, u', T, rfl, hu, hu', hu'len, rfl⟩ := act_window hM
  have s1 : a.step (A ++ (w ++ (H ++ (u ++ T)))) = some (A ++ w' ++ H ++ (u ++ T)) := by
    rw [h1]; simp only [List.append_assoc]
  have s2 : b.step (A ++ w' ++ H ++ (u ++ T)) = some (A ++ w' ++ H ++ (u' ++ T)) :=
    step_of_prefix hb1 hB hM
  have s1' : (b.reindex (b.idx + a.arity - a.coarity)).step (A ++ (w ++ (H ++ (u ++ T)))) =
      some (A ++ w ++ H ++ (u' ++ T)) := by
    rw [show A ++ (w ++ (H ++ (u ++ T))) = A ++ w ++ H ++ (u ++ T) by simp only [List.append_assoc]]
    exact step_of_prefix (ℓ := b.reindex _) (A := A ++ w ++ H) (by lenomega) (by lenomega)
      (by rw [act_reindex]; exact hM)
  have s2' : a.step (A ++ w ++ H ++ (u' ++ T)) = some (A ++ w' ++ H ++ (u' ++ T)) := by
    rw [show A ++ w ++ H ++ (u' ++ T) = A ++ (w ++ (H ++ (u' ++ T))) by simp only [List.append_assoc],
      step_of_prefix ha1 hA (L' := w' ++ (H ++ (u' ++ T))) (by rw [act_append hw, hw']; rfl)]
    simp only [List.append_assoc]
  have e1 : a.downBit (A ++ w ++ H ++ (u' ++ T)) = a.downBit (A ++ (w ++ (H ++ (u ++ T)))) := by
    rw [show A ++ w ++ H ++ (u' ++ T) = A ++ (w ++ (H ++ (u' ++ T))) by simp only [List.append_assoc]]
    exact u1_downBit_window' hA hA hw
  have e2 : (b.reindex (b.idx + a.arity - a.coarity)).downBit (A ++ (w ++ (H ++ (u ++ T)))) =
      b.downBit (A ++ w' ++ H ++ (u ++ T)) := by
    rw [show A ++ (w ++ (H ++ (u ++ T))) = A ++ w ++ H ++ (u ++ T) by simp only [List.append_assoc]]
    exact u1_downBit_window hB (by lenomega) hu
  have f1 : a.signBit (A ++ w ++ H ++ (u' ++ T)) = a.signBit (A ++ (w ++ (H ++ (u ++ T)))) := by
    rw [show A ++ w ++ H ++ (u' ++ T) = A ++ (w ++ (H ++ (u' ++ T))) by simp only [List.append_assoc]]
    exact u1_signBit_window' hA hA hw
  have f2 : (b.reindex (b.idx + a.arity - a.coarity)).signBit (A ++ (w ++ (H ++ (u ++ T)))) =
      b.signBit (A ++ w' ++ H ++ (u ++ T)) := by
    rw [show A ++ (w ++ (H ++ (u ++ T))) = A ++ w ++ H ++ (u ++ T) by simp only [List.append_assoc]]
    exact u1_signBit_window hB (by lenomega) hu
  constructor
  · rw [u1_downCountFrom_cons s1, u1_downCountFrom_cons s2, u1_downCountFrom_nil,
      u1_downCountFrom_cons s1', u1_downCountFrom_cons s2', u1_downCountFrom_nil, e1, e2]
    ring
  · rw [u1_writheFrom_cons s1, u1_writheFrom_cons s2, u1_writheFrom_nil,
      u1_writheFrom_cons s1', u1_writheFrom_cons s2', u1_writheFrom_nil, f1, f2]
    ring

theorem u1_commStep_counts {V V' : Word} (h : IsCommStep V V') (hV : V.Closed) :
    V.downCountFrom [] = V'.downCountFrom [] ∧ V.writheFrom [] = V'.writheFrom [] := by
  obtain ⟨X, Y, a, b, rfl, hpat⟩ := h
  obtain ⟨c₀, c₁, hX, hP, -⟩ := hV.exists_run
  rcases hpat with ⟨hab, rfl⟩ | ⟨hab, rfl⟩
  · have hP' := run_comm_above hab hP
    obtain ⟨hD, hw⟩ := u1_comm_above_local hab hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_downCountFrom_append₃ X _ Y hX hP',
      u1_writheFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP', hD, hw]
    exact ⟨rfl, rfl⟩
  · have hP' := run_comm_below hab hP
    obtain ⟨hD, hw⟩ := u1_comm_below_local hab hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_downCountFrom_append₃ X _ Y hX hP',
      u1_writheFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP', hD, hw]
    exact ⟨rfl, rfl⟩

/-! ### the type-I target is never empty -/

theorem u1_typeI_target_ne_nil {W X Y : Word} {m : ℕ} {d : Bool}
    (hpat : (2 ≤ m ∧ W = X ++ [.l m d, .σ (m - 1), .r m] ++ Y) ∨
      (1 ≤ m ∧ W = X ++ [.l m d, .σ (m + 1), .r m] ++ Y))
    (hW : W.Closed) : X ++ Y ≠ [] := by
  intro hXY
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hXY
  rcases hpat with ⟨hm, rfl⟩ | ⟨hm, rfl⟩
  · simp only [List.nil_append, List.append_nil] at hW
    obtain ⟨c₁, h1, -⟩ := run_three_iff.1 hW
    obtain ⟨A, L, L', -, hA, hAL, -, -⟩ := step_eq_some_iff.1 h1
    have hA0 : A = [] := (List.append_eq_nil_iff.1 hAL.symm).1
    simp only [idx] at hA
    rw [hA0] at hA
    simp at hA; omega
  · simp only [List.nil_append, List.append_nil] at hW
    obtain ⟨c₁, h1, -⟩ := run_three_iff.1 hW
    obtain ⟨A, L, L', -, hA, hAL, -, -⟩ := step_eq_some_iff.1 h1
    have hA0 : A = [] := (List.append_eq_nil_iff.1 hAL.symm).1
    simp only [idx] at hA
    rw [hA0] at hA
    have : m = 1 := by simp at hA; omega
    subst this
    cases d <;> exact absurd hW (by decide)

end U1Infra

/-- LEAF (ng:commutation, sm-3:1929-1933 "The cusp directions and crossing signs are unchanged, so D and w
are unchanged as well"). -/
theorem comm_counts {W W' : OWord} (h : IsComm W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe := by
  have hne : W.letters ≠ [] := by
    rcases h with ⟨X, Y, a, b, hW, -⟩ | ⟨X, Y, a, b, -, hpat⟩
    · rw [hW]; simp
    · rcases hpat with ⟨-, hW⟩ | ⟨-, hW⟩ <;> rw [hW] <;> simp
  have hne' : W'.letters ≠ [] := by
    rcases h with ⟨X, Y, a, b, -, hpat⟩ | ⟨X, Y, a, b, hW', -⟩
    · rcases hpat with ⟨-, hW'⟩ | ⟨-, hW'⟩ <;> rw [hW'] <;> simp
    · rw [hW']; simp
  rw [realize_downCount W hne, realize_downCount W' hne', realize_writhe W hne, realize_writhe W' hne']
  unfold OWord.downCountSyn OWord.writheSyn
  rcases h with h | h
  · exact u1_commStep_counts h W.closed
  · obtain ⟨hD, hw⟩ := u1_commStep_counts h W'.closed
    exact ⟨hD.symm, hw.symm⟩

/-- LEAF (display ng:type-I-counts, sm-3:1964-1966, deletion direction: the curl carries exactly one downward
cusp — "Exactly one of the two cusps is downward and one is upward" — and one positive crossing — "Its
crossing is also positive"). -/
theorem typeI_counts {W W' : OWord} (h : IsTypeI W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount + 1 ∧ (realize W).writhe = (realize W').writhe + 1 := by
  obtain ⟨X, Y, m, d, hpat, hW'⟩ := h
  have hcl := W.closed
  have hne : W.letters ≠ [] := by rcases hpat with ⟨-, hW⟩ | ⟨-, hW⟩ <;> rw [hW] <;> simp
  have hne' : W'.letters ≠ [] := by rw [hW']; exact u1_typeI_target_ne_nil hpat hcl
  rw [realize_downCount W hne, realize_downCount W' hne', realize_writhe W hne, realize_writhe W' hne']
  unfold OWord.downCountSyn OWord.writheSyn
  rw [hW']
  rcases hpat with ⟨hm, hW⟩ | ⟨hm, hW⟩
  · rw [hW] at hcl ⊢
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    obtain rfl := run_typeI_left hm hP
    obtain ⟨hD, hw⟩ := u1_typeI_left_local hm hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append hX, u1_writheFrom_append hX, hD, hw]
    constructor <;> omega
  · rw [hW] at hcl ⊢
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    obtain rfl := run_typeI_right hm hP
    obtain ⟨hD, hw⟩ := u1_typeI_right_local hm hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append hX, u1_writheFrom_append hX, hD, hw]
    constructor <;> omega

/-- LEAF (ng:front-II, sm-3:1979-1987 "Their signs are opposite ... The same upper and lower cusp arms remain
after deletion.  Thus Δw = ΔD = 0"). -/
theorem typeII_counts {W W' : OWord} (h : IsTypeII W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe := by
  obtain ⟨X, Y, m, hpat⟩ := h
  have hcl := W.closed
  have hne : W.letters ≠ [] := by
    rcases hpat with ⟨d, -, hW, -⟩ | ⟨d, -, hW, -⟩ | ⟨-, hW, -⟩ | ⟨-, hW, -⟩ <;> rw [hW] <;> simp
  have hne' : W'.letters ≠ [] := by
    rcases hpat with ⟨d, -, -, hW'⟩ | ⟨d, -, -, hW'⟩ | ⟨-, -, hW'⟩ | ⟨-, -, hW'⟩ <;> rw [hW'] <;> simp
  rw [realize_downCount W hne, realize_downCount W' hne', realize_writhe W hne, realize_writhe W' hne']
  unfold OWord.downCountSyn OWord.writheSyn
  rcases hpat with ⟨d, hm, hW, hW'⟩ | ⟨d, hm, hW, hW'⟩ | ⟨hm, hW, hW'⟩ | ⟨hm, hW, hW'⟩
  · rw [hW] at hcl; rw [hW, hW']
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    have hP' := run_typeII_l_left hm hP
    obtain ⟨hD, hw⟩ := u1_typeII_l_left_local hm hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append₃ X _ Y hX hP', u1_writheFrom_append₃ X _ Y hX hP', hD, hw]
    exact ⟨rfl, rfl⟩
  · rw [hW] at hcl; rw [hW, hW']
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    have hP' := run_typeII_l_right hm hP
    obtain ⟨hD, hw⟩ := u1_typeII_l_right_local hm hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append₃ X _ Y hX hP', u1_writheFrom_append₃ X _ Y hX hP', hD, hw]
    exact ⟨rfl, rfl⟩
  · rw [hW] at hcl; rw [hW, hW']
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    have hP' := run_typeII_r_left hm hP
    obtain ⟨hD, hw⟩ := u1_typeII_r_left_local hm hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append₃ X _ Y hX hP', u1_writheFrom_append₃ X _ Y hX hP', hD, hw]
    exact ⟨rfl, rfl⟩
  · rw [hW] at hcl; rw [hW, hW']
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    have hP' := run_typeII_r_right hm hP
    obtain ⟨hD, hw⟩ := u1_typeII_r_right_local hm hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append₃ X _ Y hX hP', u1_writheFrom_append₃ X _ Y hX hP', hD, hw]
    exact ⟨rfl, rfl⟩

/-- LEAF (ng:front-III, sm-3:1997-2001 "Each physical pair crosses on both sides with the same over/under bit
and transported arrows" — no cusp letter, signs preserved). -/
theorem typeIII_counts {W W' : OWord} (h : IsTypeIII W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe := by
  obtain ⟨X, Y, m, hm, hpat⟩ := h
  have hcl := W.closed
  have hne : W.letters ≠ [] := by rcases hpat with ⟨hW, -⟩ | ⟨hW, -⟩ <;> rw [hW] <;> simp
  have hne' : W'.letters ≠ [] := by rcases hpat with ⟨-, hW'⟩ | ⟨-, hW'⟩ <;> rw [hW'] <;> simp
  rw [realize_downCount W hne, realize_downCount W' hne', realize_writhe W hne, realize_writhe W' hne']
  unfold OWord.downCountSyn OWord.writheSyn
  rcases hpat with ⟨hW, hW'⟩ | ⟨hW, hW'⟩
  · rw [hW] at hcl; rw [hW, hW']
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    obtain ⟨A, p, q, r, L, hA, rfl, rfl⟩ := run_typeIII_aux hm hP
    obtain ⟨hD₁, hD₂, hw⟩ := u1_typeIII_local (L := L) (p := p) (q := q) (r := r) hm hA
    rw [u1_downCountFrom_append₃ X _ Y hX (run_typeIII_of_split hm hA).1,
      u1_downCountFrom_append₃ X _ Y hX (run_typeIII_of_split hm hA).2,
      u1_writheFrom_append₃ X _ Y hX (run_typeIII_of_split hm hA).1,
      u1_writheFrom_append₃ X _ Y hX (run_typeIII_of_split hm hA).2, hD₁, hD₂, hw]
    exact ⟨rfl, rfl⟩
  · rw [hW] at hcl; rw [hW, hW']
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    obtain ⟨A, p, q, r, L, hA, rfl, rfl⟩ := run_typeIII_aux' hm hP
    obtain ⟨hD₁, hD₂, hw⟩ := u1_typeIII_local (L := L) (p := p) (q := q) (r := r) hm hA
    rw [u1_downCountFrom_append₃ X _ Y hX (run_typeIII_of_split hm hA).1,
      u1_downCountFrom_append₃ X _ Y hX (run_typeIII_of_split hm hA).2,
      u1_writheFrom_append₃ X _ Y hX (run_typeIII_of_split hm hA).1,
      u1_writheFrom_append₃ X _ Y hX (run_typeIII_of_split hm hA).2, hD₁, hD₂, hw]
    exact ⟨rfl, rfl⟩

/-- LEAF (display ng:zigzag-counts, sm-3:2020-2022: `Δw = 0`, `ΔD ∈ {0, −2}` — "Their directions are both
downward or both upward"). -/
theorem zigzag_counts {W W' : OWord} (h : IsZigzagDeletion W.letters W'.letters) :
    (realize W).writhe = (realize W').writhe ∧
    ((realize W).downCount = (realize W').downCount ∨ (realize W).downCount = (realize W').downCount + 2) := by
  have hne : W.letters ≠ [] := h.source_ne_nil
  have hne' : W'.letters ≠ [] := IsZigzagDeletion.ne_nil h W.closed
  have hcl := W.closed
  obtain ⟨X, Y, m, d, hm, hpat, hW'⟩ := h
  rw [realize_downCount W hne, realize_downCount W' hne', realize_writhe W hne, realize_writhe W' hne']
  unfold OWord.downCountSyn OWord.writheSyn
  rw [hW']
  rcases hpat with hW | hW
  · rw [hW] at hcl; rw [hW]
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    obtain rfl := run_zigzag_below hm hP
    obtain ⟨hD, hw⟩ := u1_zigzag_below_local hm hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append hX, u1_writheFrom_append hX, hD, hw]
    refine ⟨by omega, ?_⟩
    split_ifs <;> omega
  · rw [hW] at hcl; rw [hW]
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    obtain rfl := run_zigzag_above hm hP
    obtain ⟨hD, hw⟩ := u1_zigzag_above_local hm hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append hX, u1_writheFrom_append hX, hD, hw]
    refine ⟨by omega, ?_⟩
    split_ifs <;> omega

/-- LEAF (display ng:crossed-cusp-counts, sm-3:2030-2036 "the old crossing has sign −1.  Deletion raises w by
one and flips the cusp direction ... If the old cusp was downward, ΔD = −1; otherwise ΔD = 1"). -/
theorem crossedCusp_counts {W W' : OWord} (h : IsCrossedCuspShortcut W.letters W'.letters) :
    (realize W').writhe = (realize W).writhe + 1 ∧
    ((realize W').downCount + 1 = (realize W).downCount ∨ (realize W').downCount = (realize W).downCount + 1) := by
  obtain ⟨hne, hne'⟩ := h.ne_nil
  have hcl := W.closed
  obtain ⟨X, Y, i, hi, hpat⟩ := h
  rw [realize_downCount W hne, realize_downCount W' hne', realize_writhe W hne, realize_writhe W' hne']
  unfold OWord.downCountSyn OWord.writheSyn
  rcases hpat with ⟨d, hW, hW'⟩ | ⟨hW, hW'⟩
  · rw [hW] at hcl; rw [hW, hW']
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    have hP' := run_crossedCusp_l hi hP
    obtain ⟨hD, hw, hw'⟩ := u1_crossedCusp_l_local hi hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append₃ X _ Y hX hP', u1_writheFrom_append₃ X _ Y hX hP', hw, hw']
    refine ⟨by omega, ?_⟩
    rcases hD with hD | hD
    · left; omega
    · right; omega
  · rw [hW] at hcl; rw [hW, hW']
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    have hP' := run_crossedCusp_r hi hP
    obtain ⟨hD, hw, hw'⟩ := u1_crossedCusp_r_local hi hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append₃ X _ Y hX hP', u1_writheFrom_append₃ X _ Y hX hP', hw, hw']
    refine ⟨by omega, ?_⟩
    rcases hD with hD | hD
    · left; omega
    · right; omega

/-- LEAF (display ng:circle-counts, sm-3:2064-2068: `D_before = D_after + 1`, "The writhe is unchanged"). -/
theorem circleDeletion_counts {W W' : OWord} (h : IsCircleDeletion W.letters W'.letters) :
    (realize W).writhe = (realize W').writhe ∧ (realize W).downCount = (realize W').downCount + 1 := by
  have hcl := W.closed
  obtain ⟨X, Y, m, d, hm, hW, hW', hXY⟩ := h
  have hne : W.letters ≠ [] := by rw [hW]; simp
  have hne' : W'.letters ≠ [] := by rw [hW']; exact hXY
  rw [realize_downCount W hne, realize_downCount W' hne', realize_writhe W hne, realize_writhe W' hne']
  unfold OWord.downCountSyn OWord.writheSyn
  rw [hW] at hcl; rw [hW, hW']
  obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
  obtain rfl := run_circle hm hP
  obtain ⟨hD, hw⟩ := u1_circle_local hm hP
  rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
    u1_downCountFrom_append hX, u1_writheFrom_append hX, hD, hw]
  constructor <;> omega

/-- LEAF (the (t,u) table sm-3:2107-2126 "the same downward-cusp count in all three diagrams", and
sm-3:2129-2131 "Their writhes are w₀+1, w₀−1, w₀": the two principal branches carry opposite signs at the
one crossing, so `w_A + w_{A'} = 2 w_C`; which is which is fixed by the sign of the site, `skein_site`). -/
theorem skein_counts {A A' C : OWord} (h : IsCuspSkeinStep A.letters A'.letters C.letters) :
    (realize A).downCount = (realize C).downCount ∧ (realize A').downCount = (realize C).downCount ∧
    (realize A).writhe + (realize A').writhe = 2 * (realize C).writhe := by
  obtain ⟨hA, hA', hC⟩ := h.ne_nil
  rw [realize_downCount A hA, realize_downCount A' hA', realize_downCount C hC, realize_writhe A hA,
    realize_writhe A' hA', realize_writhe C hC]
  unfold OWord.downCountSyn OWord.writheSyn
  obtain ⟨X, Y, m, d, a, P, L, hm, hX, hP, hAe, hA'e, hCe⟩ := h
  rw [hAe, hA'e]
  rw [u1_downCountFrom_append₃ X _ Y hX (run_skein_A hm hP), u1_writheFrom_append₃ X _ Y hX (run_skein_A hm hP),
    u1_downCountFrom_append₃ X _ Y hX (run_skein_A' hm hP), u1_writheFrom_append₃ X _ Y hX (run_skein_A' hm hP)]
  obtain ⟨l1, l2, l3, l4, w12, w3, w4⟩ := u1_skein_local (d := d) (a := a) (L := L) hm hP
  rcases hCe with ⟨rfl, hCe⟩ | ⟨rfl, hCe⟩
  · rw [hCe, u1_downCountFrom_append₃ X _ Y hX (run_skein_Ctop hm hP),
      u1_writheFrom_append₃ X _ Y hX (run_skein_Ctop hm hP), l1, l2, l3, w3]
    refine ⟨rfl, rfl, ?_⟩
    omega
  · rw [hCe, u1_downCountFrom_append₃ X _ Y hX (run_skein_Cbottom hm hP),
      u1_writheFrom_append₃ X _ Y hX (run_skein_Cbottom hm hP), l1, l2, l4, w4]
    refine ⟨rfl, rfl, ?_⟩
    omega

/-! ### U2 infrastructure — the record core (unit U2; PLAN_FINAL.md §4 "L-rec", §5 "U2 record core")

The abstract named record of a closed word restricted to an *active set* of `σ` slots, `U2.slotRecord`,
and the isomorphisms that connect it to the records of the realization (`U2.realizeRecordIso`,
`U2.realizeAtRecordIso`) and of any diagram on the strands of the realization with the crossings of a
set of `σ` columns (`U2.diagramRecordIso`, for the vertex-moved diagrams of U6); the exterior
correspondence of two words agreeing outside a block (`U2.φE`, β2's `shiftIdx`/`extSlot`/`next_ext`),
reduced by the block-passage hypothesis `U2.Passage` to a conjugation of first returns
(`U2.conj_of_passage`, `U2.extRecordIso`, `U2.extRecordIsoAddFree`); a constructor for full slot
bijections (`U2.slotRecordIsoOfSlotEquiv`, commutation and skein switch); and the composed isomorphisms
`U2.vertexMovedRecordIso'`, `U2.realize_recordIso_of_ext`, `U2.realize_recordIso_addFree_of_ext`.
Consumers: U3 (`comm_recordIso`, `zigzag_recordIso`, `circle_recordIso_addFree`, `skein_site`) and U6
(`typeII_move`, `typeI_move`, `crossedCusp_move`).  Report: work/drafts/frontrows/U_U2_REPORT.md. -/

namespace U2

open SM.FrontRealize SM.FrontWord.Letter Equiv

/-! #### A. First-return lemmas (pure permutation theory, extending `SM.Link` §A) -/

section FirstReturnExtra

variable {α β : Type*} [Fintype α] [Fintype β] (f : Perm α) (g : Perm β)

/-- The first return to a subset factors through the first return to a superset: the `p`-return of `a`
along `f` is the `p`-return of `a` along the first-return permutation of the superset `E ⊇ p`
(strengthened `firstReturn_pow_of_pow`: the intermediate `E`-returns sit at intermediate times). -/
theorem firstReturn_pow_of_pow_strong (E : α → Prop) [DecidablePred E] (n : ℕ) :
    ∀ (m : {m // E m}), E ((f ^ n) m.1) →
      ∃ i : ℕ, ((firstReturn f E ^ i) m).1 = (f ^ n) m.1 ∧ (0 < n → 0 < i) ∧
        ∀ j, 0 < j → j < i → ∃ t, 0 < t ∧ t < n ∧ ((firstReturn f E ^ j) m).1 = (f ^ t) m.1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact ⟨0, by simp, fun h => absurd h (lt_irrefl 0), fun j hj hj' => absurd hj' (by omega)⟩
    set k := returnTime f E m.1 m.2 with hk
    have hkpos : 0 < k := returnTime_pos f E m.1 m.2
    rcases lt_trichotomy n k with hlt | heq | hgt
    · exact absurd hn (returnTime_min f E m.1 m.2 hpos hlt)
    · refine ⟨1, by rw [pow_one, firstReturn_apply, ← hk, heq], fun _ => Nat.one_pos, ?_⟩
      intro j hj hj'; omega
    · have hsplit : (f ^ n) m.1 = (f ^ (n - k)) (firstReturn f E m).1 := by
        rw [firstReturn_apply, ← hk, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hgt.le]
      obtain ⟨i, hi, hipos, hmid⟩ := ih (n - k) (by omega) (firstReturn f E m) (hsplit ▸ hn)
      refine ⟨i + 1, by rw [pow_succ, Perm.mul_apply, hi, hsplit], fun _ => Nat.succ_pos _, ?_⟩
      intro j hj hj'
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · have hj1 : j = 1 := by omega
        subst hj1
        exact ⟨k, hkpos, hgt, by rw [pow_one, firstReturn_apply, ← hk]⟩
      · obtain ⟨t, ht0, htn, ht⟩ := hmid (j - 1) (by omega) (by omega)
        refine ⟨t + k, by omega, by omega, ?_⟩
        have e : (firstReturn f E ^ j) m = (firstReturn f E ^ (j - 1)) (firstReturn f E m) := by
          rw [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel (by omega)]
        rw [e, ht, firstReturn_apply, ← hk, ← Perm.mul_apply, ← pow_add]

/-- The first return to `p ⊆ E` along `f` is the first return to `p` along the first-return permutation
of `E`. -/
theorem firstReturn_factor (E : α → Prop) [DecidablePred E] (p : α → Prop) [DecidablePred p]
    (hpE : ∀ a, p a → E a) (a : {a // p a}) :
    (firstReturn f p a).1 =
      (firstReturn (firstReturn f E) (fun b => p b.1) ⟨⟨a.1, hpE _ a.2⟩, a.2⟩).1.1 := by
  set r := returnTime f p a.1 a.2 with hr
  have hrpos : 0 < r := returnTime_pos f p a.1 a.2
  have hrp : p ((f ^ r) a.1) := returnTime_spec f p a.1 a.2
  set b : {m // E m} := ⟨a.1, hpE _ a.2⟩ with hb
  obtain ⟨i, hi, hipos, hmid⟩ := firstReturn_pow_of_pow_strong f E r b (hpE _ hrp)
  have hi0 : 0 < i := hipos hrpos
  have hret : returnTime (firstReturn f E) (fun b => p b.1) b a.2 = i := by
    rw [returnTime_eq_iff]
    refine ⟨⟨hi0, ?_⟩, ?_⟩
    · show p ((firstReturn f E ^ i) b).1
      rw [hi]; exact hrp
    · intro j hj ⟨hj0, hjp⟩
      obtain ⟨t, ht0, htr, ht⟩ := hmid j hj0 hj
      have : p ((f ^ t) a.1) := by
        have hjp' : p ((firstReturn f E ^ j) b).1 := hjp
        rwa [ht] at hjp'
      exact returnTime_min f p a.1 a.2 ht0 htr this
  show (f ^ r) a.1 = ((firstReturn f E ^ returnTime (firstReturn f E) (fun b => p b.1) b a.2) b).1
  rw [hret, hi]

/-- A bijection conjugating `f` to `g` and carrying `p` to `q` conjugates the first returns. -/
theorem firstReturn_conj (p : α → Prop) (q : β → Prop) [DecidablePred p] [DecidablePred q]
    (φ : α ≃ β) (hφ : ∀ a, φ (f a) = g (φ a)) (hpq : ∀ a, q (φ a) ↔ p a) (a : {a // p a}) :
    (firstReturn g q ⟨φ a.1, (hpq _).2 a.2⟩).1 = φ (firstReturn f p a).1 := by
  have hpow : ∀ n (x : α), φ ((f ^ n) x) = (g ^ n) (φ x) := by
    intro n; induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ', Perm.mul_apply, hφ, ih, pow_succ', Perm.mul_apply]
  set r := returnTime f p a.1 a.2 with hr
  have hret : returnTime g q (φ a.1) ((hpq _).2 a.2) = r := by
    rw [returnTime_eq_iff]
    refine ⟨⟨returnTime_pos f p a.1 a.2, ?_⟩, ?_⟩
    · rw [← hpow, hpq]; exact returnTime_spec f p a.1 a.2
    · intro j hj ⟨hj0, hjq⟩
      rw [← hpow, hpq] at hjq
      exact returnTime_min f p a.1 a.2 hj0 hj hjq
  show (g ^ returnTime g q (φ a.1) _) (φ a.1) = φ ((f ^ r) a.1)
  rw [hret, hpow]

/-- The first return of `f` to `E` is characterised by a path: `m` steps to an `E`-point, none before. -/
theorem firstReturn_eq_of_path (E : α → Prop) [DecidablePred E] (a : {a // E a}) {m : ℕ} (hm : 0 < m)
    (hE : E ((f ^ m) a.1)) (hmin : ∀ i, 0 < i → i < m → ¬ E ((f ^ i) a.1)) :
    (firstReturn f E a).1 = (f ^ m) a.1 := by
  have : returnTime f E a.1 a.2 = m :=
    (returnTime_eq_iff f E a.1 a.2).mpr ⟨⟨hm, hE⟩, fun j hj hj' => hmin j hj'.1 hj hj'.2⟩
  rw [firstReturn_apply, this]

/-- The return time is at most any positive period of the point. -/
theorem returnTime_le_of_pow_eq (E : α → Prop) [DecidablePred E] (a : α) (ha : E a) {k : ℕ} (hk : 0 < k)
    (h : (f ^ k) a = a) : returnTime f E a ha ≤ k :=
  Nat.find_min' (exists_return f E a ha) ⟨hk, by rw [h]; exact ha⟩

end FirstReturnExtra

/-! #### F. Conjugate first returns: transport of cycles (generic) -/

section ConjExtra

variable {α β : Type*} [Fintype α] [Fintype β] (f : Perm α) (g : Perm β)

omit [Fintype α] [Fintype β] in
theorem pow_conj {φ : α ≃ β} (hφ : ∀ a, φ (f a) = g (φ a)) (n : ℕ) (x : α) :
    φ ((f ^ n) x) = (g ^ n) (φ x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Perm.mul_apply, hφ, ih, pow_succ', Perm.mul_apply]

omit [Fintype β] in
theorem sameCycle_of_conj {φ : α ≃ β} (hφ : ∀ a, φ (f a) = g (φ a)) {x y : α} (h : f.SameCycle x y) :
    g.SameCycle (φ x) (φ y) := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  exact ⟨n, by rw [zpow_natCast, ← pow_conj f g hφ, hn]⟩

omit [Fintype α] [Fintype β] in
theorem conj_symm {φ : α ≃ β} (hφ : ∀ a, φ (f a) = g (φ a)) (b : β) : φ.symm (g b) = f (φ.symm b) := by
  apply φ.injective
  rw [Equiv.apply_symm_apply, hφ, Equiv.apply_symm_apply]

theorem sameCycle_iff_of_conj {φ : α ≃ β} (hφ : ∀ a, φ (f a) = g (φ a)) (x y : α) :
    g.SameCycle (φ x) (φ y) ↔ f.SameCycle x y := by
  refine ⟨fun h => ?_, sameCycle_of_conj f g hφ⟩
  have := sameCycle_of_conj g f (conj_symm f g hφ) h
  simpa using this

variable (E : α → Prop) (E' : β → Prop) [DecidablePred E] [DecidablePred E'] (φ : {a // E a} ≃ {b // E' b})

/-- Conjugate first returns: `E`-points lie on one `f`-cycle iff their images lie on one `g`-cycle. -/
theorem sameCycle_φ_iff (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a)) (a b : {a // E a}) :
    g.SameCycle (φ a).1 (φ b).1 ↔ f.SameCycle a.1 b.1 := by
  rw [← firstReturn_sameCycle_iff g E', ← firstReturn_sameCycle_iff f E]
  exact sameCycle_iff_of_conj (firstReturn f E) (firstReturn g E') (fun a => (conj a).symm) a b

theorem conj_symm' (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a)) (b : {b // E' b}) :
    firstReturn f E (φ.symm b) = φ.symm (firstReturn g E' b) :=
  (conj_symm (firstReturn f E) (firstReturn g E') (fun a => (conj a).symm) b).symm

/-- The first return to `p ⊆ E` is carried by a bijection conjugating the first returns to `E`, `E'`
(`firstReturn_factor` on both sides, then `firstReturn_conj`). -/
theorem firstReturn_conj_of_factor (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (p : α → Prop) (p' : β → Prop) [DecidablePred p] [DecidablePred p']
    (hpE : ∀ a, p a → E a) (hp'E' : ∀ b, p' b → E' b) (hpq : ∀ a : {a // E a}, p' (φ a).1 ↔ p a.1)
    (a : {a // p a}) :
    (firstReturn g p' ⟨(φ ⟨a.1, hpE _ a.2⟩).1, (hpq _).2 a.2⟩).1 =
      (φ ⟨(firstReturn f p a).1, hpE _ (firstReturn f p a).2⟩).1 := by
  have h1 := firstReturn_factor g E' p' hp'E' ⟨(φ ⟨a.1, hpE _ a.2⟩).1, (hpq _).2 a.2⟩
  have h2 := firstReturn_factor f E p hpE a
  have h3 := firstReturn_conj (firstReturn f E) (firstReturn g E') (fun a => p a.1) (fun b => p' b.1) φ
    (fun a => (conj a).symm) hpq ⟨⟨a.1, hpE _ a.2⟩, a.2⟩
  rw [h1]
  refine (congrArg Subtype.val h3).trans ?_
  exact congrArg (fun x => (φ x).1) (Subtype.ext h2.symm)

omit [Fintype α] [Fintype β] in
theorem sameCycle_pow (n : ℕ) (a : α) : f.SameCycle a ((f ^ n) a) := ⟨(n : ℤ), by rw [zpow_natCast]⟩

omit [Fintype α] [Fintype β] [DecidablePred E] in
/-- An `E`-point on the cycle of `a`. -/
noncomputable def repE (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (a : α) : {a // E a} :=
  ⟨(f ^ Classical.choose (hE a)) a, Classical.choose_spec (hE a)⟩

omit [Fintype α] [Fintype β] [DecidablePred E] in
theorem repE_sameCycle (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (a : α) : f.SameCycle a (repE f E hE a).1 :=
  sameCycle_pow f _ a

/-- The map of cycles induced by `φ`. -/
noncomputable def cycleMap (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) :
    Quotient (Perm.SameCycle.setoid f) → Quotient (Perm.SameCycle.setoid g) :=
  Quotient.lift (fun a => Quotient.mk (Perm.SameCycle.setoid g) (φ (repE f E hE a)).1) (by
    intro a b hab
    apply Quotient.sound
    have h : f.SameCycle (repE f E hE a).1 (repE f E hE b).1 :=
      (repE_sameCycle f E hE a).symm.trans ((show f.SameCycle a b from hab).trans (repE_sameCycle f E hE b))
    exact (sameCycle_φ_iff f g E E' φ conj _ _).2 h)

theorem cycleMap_mk (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (a : {a // E a}) :
    cycleMap f g E E' φ conj hE (Quotient.mk (Perm.SameCycle.setoid f) a.1) =
      Quotient.mk (Perm.SameCycle.setoid g) (φ a).1 := by
  apply Quotient.sound
  exact (sameCycle_φ_iff f g E E' φ conj _ _).2 (repE_sameCycle f E hE a.1).symm

theorem cycleMap_mk' (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (a : α) :
    cycleMap f g E E' φ conj hE (Quotient.mk (Perm.SameCycle.setoid f) a) =
      Quotient.mk (Perm.SameCycle.setoid g) (φ (repE f E hE a)).1 := rfl

/-- Conjugate first returns, every cycle meeting `E` resp. `E'`: the cycle sets correspond. -/
noncomputable def cycleEquiv (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (hE' : ∀ b : β, ∃ n : ℕ, E' ((g ^ n) b)) :
    Quotient (Perm.SameCycle.setoid f) ≃ Quotient (Perm.SameCycle.setoid g) where
  toFun := cycleMap f g E E' φ conj hE
  invFun := cycleMap g f E' E φ.symm (conj_symm' f g E E' φ conj) hE'
  left_inv o := by
    induction o using Quotient.inductionOn with
    | h a =>
      have h1 : Quotient.mk (Perm.SameCycle.setoid f) a =
          Quotient.mk (Perm.SameCycle.setoid f) (repE f E hE a).1 :=
        Quotient.sound (repE_sameCycle f E hE a)
      rw [h1, cycleMap_mk, cycleMap_mk, Equiv.symm_apply_apply]
  right_inv o := by
    induction o using Quotient.inductionOn with
    | h b =>
      have h1 : Quotient.mk (Perm.SameCycle.setoid g) b =
          Quotient.mk (Perm.SameCycle.setoid g) (repE g E' hE' b).1 :=
        Quotient.sound (repE_sameCycle g E' hE' b)
      rw [h1, cycleMap_mk, cycleMap_mk, Equiv.apply_symm_apply]

theorem cycleEquiv_mk (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (hE' : ∀ b : β, ∃ n : ℕ, E' ((g ^ n) b)) (a : {a // E a}) :
    cycleEquiv f g E E' φ conj hE hE' (Quotient.mk (Perm.SameCycle.setoid f) a.1) =
      Quotient.mk (Perm.SameCycle.setoid g) (φ a).1 :=
  cycleMap_mk f g E E' φ conj hE a

open Classical in
/-- The cycles of `f` when every `g`-cycle meets `E'` and exactly one `f`-cycle `c₀` misses `E`: the
`g`-cycles plus one (`Record.addFree`, the circle deletion). -/
noncomputable def cycleEquivOption (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE' : ∀ b : β, ∃ n : ℕ, E' ((g ^ n) b)) (c₀ : Quotient (Perm.SameCycle.setoid f))
    (hc₀ : ∀ a : α, (¬ ∃ n : ℕ, E ((f ^ n) a)) ↔ Quotient.mk (Perm.SameCycle.setoid f) a = c₀) :
    Quotient (Perm.SameCycle.setoid f) ≃ Option (Quotient (Perm.SameCycle.setoid g)) where
  toFun := Quotient.lift (fun a => if h : ∃ n : ℕ, E ((f ^ n) a) then
      some (Quotient.mk (Perm.SameCycle.setoid g)
        (φ ⟨(f ^ Classical.choose h) a, Classical.choose_spec h⟩).1) else none) (by
    intro a b hab
    have hab' : f.SameCycle a b := hab
    have hiff : (∃ n : ℕ, E ((f ^ n) a)) ↔ ∃ n : ℕ, E ((f ^ n) b) := by
      constructor
      · rintro ⟨n, hn⟩
        obtain ⟨m, hm⟩ := hab'.symm.exists_nat_pow_eq
        exact ⟨n + m, by rw [pow_add, Perm.mul_apply, hm]; exact hn⟩
      · rintro ⟨n, hn⟩
        obtain ⟨m, hm⟩ := hab'.exists_nat_pow_eq
        exact ⟨n + m, by rw [pow_add, Perm.mul_apply, hm]; exact hn⟩
    by_cases h : ∃ n : ℕ, E ((f ^ n) a)
    · have h' : ∃ n : ℕ, E ((f ^ n) b) := hiff.1 h
      simp only [h, h', ↓reduceDIte, Option.some.injEq]
      apply Quotient.sound
      apply (sameCycle_φ_iff f g E E' φ conj _ _).2
      show f.SameCycle ((f ^ Classical.choose h) a) ((f ^ Classical.choose h') b)
      exact (sameCycle_pow f (Classical.choose h) a).symm.trans
        (hab'.trans (sameCycle_pow f (Classical.choose h') b))
    · have h' : ¬ ∃ n : ℕ, E ((f ^ n) b) := fun hb => h (hiff.2 hb)
      simp only [h, h', ↓reduceDIte])
  invFun o := match o with
    | none => c₀
    | some o' => cycleMap g f E' E φ.symm (conj_symm' f g E E' φ conj) hE' o'
  left_inv o := by
    induction o using Quotient.inductionOn with
    | h a =>
      by_cases h : ∃ n : ℕ, E ((f ^ n) a)
      · simp only [Quotient.lift_mk, h, ↓reduceDIte]
        show cycleMap g f E' E φ.symm _ hE' (Quotient.mk _ (φ ⟨(f ^ Classical.choose h) a, _⟩).1) = _
        rw [cycleMap_mk, Equiv.symm_apply_apply]
        apply Quotient.sound
        exact (sameCycle_pow f (Classical.choose h) a).symm
      · simp only [Quotient.lift_mk, h, ↓reduceDIte]
        exact ((hc₀ a).1 h).symm
  right_inv o := by
    cases o with
    | none =>
      induction c₀ using Quotient.inductionOn with
      | h a₀ =>
        have : ¬ ∃ n : ℕ, E ((f ^ n) a₀) := (hc₀ a₀).2 rfl
        simp only [Quotient.lift_mk, this, ↓reduceDIte]
    | some o' =>
      induction o' using Quotient.inductionOn with
      | h b =>
        dsimp only
        rw [cycleMap_mk']
        set a : {a // E a} := φ.symm (repE g E' hE' b) with ha
        have h : ∃ n : ℕ, E ((f ^ n) a.1) := ⟨0, by simpa using a.2⟩
        simp only [Quotient.lift_mk, h, ↓reduceDIte, Option.some.injEq]
        apply Quotient.sound
        have h1 : f.SameCycle ((f ^ Classical.choose h) a.1) a.1 := (sameCycle_pow f (Classical.choose h) a.1).symm
        have h2 := (sameCycle_φ_iff f g E E' φ conj ⟨_, Classical.choose_spec h⟩ a).2 h1
        have h3 : (φ a).1 = (repE g E' hE' b).1 := by rw [ha, Equiv.apply_symm_apply]
        have h4 : g.SameCycle (φ a).1 b := by rw [h3]; exact (repE_sameCycle g E' hE' b).symm
        exact h2.trans h4

theorem cycleEquivOption_mk (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE' : ∀ b : β, ∃ n : ℕ, E' ((g ^ n) b)) (c₀ : Quotient (Perm.SameCycle.setoid f))
    (hc₀ : ∀ a : α, (¬ ∃ n : ℕ, E ((f ^ n) a)) ↔ Quotient.mk (Perm.SameCycle.setoid f) a = c₀)
    (a : {a // E a}) :
    cycleEquivOption f g E E' φ conj hE' c₀ hc₀ (Quotient.mk (Perm.SameCycle.setoid f) a.1) =
      some (Quotient.mk (Perm.SameCycle.setoid g) (φ a).1) := by
  have h : ∃ n : ℕ, E ((f ^ n) a.1) := ⟨0, by simpa using a.2⟩
  simp only [cycleEquivOption, Equiv.coe_fn_mk, Quotient.lift_mk, h, ↓reduceDIte, Option.some.injEq]
  apply Quotient.sound
  apply (sameCycle_φ_iff f g E E' φ conj _ _).2
  exact (sameCycle_pow f (Classical.choose h) a.1).symm


end ConjExtra


/-! #### B. The `σ` slots of a closed word: over bit, twin, sign -/

section SigmaSlots

variable {W : Word}

/-- A crossing letter is `σ` of its own index. -/
theorem letterAt_σ_of_isCrossing {k : ℕ} (h : (letterAt W k).isCrossing = true) :
    letterAt W k = .σ (letterAt W k).idx := by
  cases hℓ : letterAt W k with
  | l m d => rw [hℓ] at h; simp [isCrossing] at h
  | r m => rw [hℓ] at h; simp [isCrossing] at h
  | σ m => rfl

/-- The over bit of a slot: its piece is a descending pass (`pass p q` with `p < q`; the printed rule
"the branch with smaller dz/dx is over", `overStrand_crossingOf`). -/
def isDesc (u : Slot W) : Bool :=
  match shapeOf u with
  | .pass p q => decide (p < q)
  | _ => false

/-- A `σ` slot: the letter of its column is a crossing and its piece is one of the two crossing strands
(`pass m (m+1)` or `pass (m+1) m`).  These are exactly `σSlotA`/`σSlotB` (`isσSlot_iff`). -/
def IsσSlot (u : Slot W) : Prop :=
  (letterAt W (colOf u)).isCrossing = true ∧
    (shapeOf u = .pass (letterAt W (colOf u)).idx ((letterAt W (colOf u)).idx + 1) ∨
     shapeOf u = .pass ((letterAt W (colOf u)).idx + 1) (letterAt W (colOf u)).idx)

instance : DecidablePred (IsσSlot (W := W)) := fun u => by unfold IsσSlot; infer_instance

/-- The sign of the crossing letter of column `k` (the printed rule: positive iff the two bits agree,
`sign_crossingOf`). -/
def σsgnCol (W : Word) (k : ℕ) : SignType :=
  if bit W k (letterAt W k).idx = bit W k ((letterAt W k).idx + 1) then 1 else -1

/-- The sign carried by a `σ` slot: that of its column. -/
def σsgn (u : Slot W) : SignType := σsgnCol W (colOf u)

theorem σsgnCol_ne_zero (k : ℕ) : σsgnCol W k ≠ 0 := by
  unfold σsgnCol; split_ifs <;> decide

theorem σsgn_ne_zero (u : Slot W) : σsgn u ≠ 0 := σsgnCol_ne_zero _

theorem coe_σsgnCol (k : ℕ) :
    ((σsgnCol W k : SignType) : ℤ) =
      if bit W k (letterAt W k).idx = bit W k ((letterAt W k).idx + 1) then 1 else -1 := by
  unfold σsgnCol; split_ifs <;> rfl

variable (hW : W.Closed)
include hW

theorem isσSlot_σSlotA {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    IsσSlot (σSlotA hW hk hℓ) := by
  obtain ⟨hc, hs, -⟩ := σSlotA_spec hW hk hℓ
  refine ⟨?_, Or.inl ?_⟩
  · rw [hc, hℓ]; rfl
  · rw [hc, hℓ, hs]; rfl

theorem isσSlot_σSlotB {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    IsσSlot (σSlotB hW hk hℓ) := by
  obtain ⟨hc, hs, -⟩ := σSlotB_spec hW hk hℓ
  refine ⟨?_, Or.inr ?_⟩
  · rw [hc, hℓ]; rfl
  · rw [hc, hℓ, hs]; rfl

theorem isDesc_σSlotA {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    isDesc (σSlotA hW hk hℓ) = true := by
  unfold isDesc; rw [(σSlotA_spec hW hk hℓ).2.1]; simp

theorem isDesc_σSlotB {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    isDesc (σSlotB hW hk hℓ) = false := by
  unfold isDesc; rw [(σSlotB_spec hW hk hℓ).2.1]; simp

/-- The column of a slot is a real column. -/
theorem colOf_lt (u : Slot W) : colOf u < W.length := (piece_spec .std hW u).1

/-- A `σ` slot is `σSlotA` or `σSlotB` of its column. -/
theorem eq_σSlotA_or_σSlotB {u : Slot W} (hu : IsσSlot u) :
    u = σSlotA hW (colOf_lt hW u) (letterAt_σ_of_isCrossing hu.1) ∨
    u = σSlotB hW (colOf_lt hW u) (letterAt_σ_of_isCrossing hu.1) := by
  obtain ⟨hA1, hA2, -⟩ := σSlotA_spec hW (colOf_lt hW u) (letterAt_σ_of_isCrossing hu.1)
  obtain ⟨hB1, hB2, -⟩ := σSlotB_spec hW (colOf_lt hW u) (letterAt_σ_of_isCrossing hu.1)
  rcases hu.2 with h | h
  · left; exact slot_eq_of_piece_eq hW .std hA1.symm (h.trans hA2.symm)
  · right; exact slot_eq_of_piece_eq hW .std hB1.symm (h.trans hB2.symm)

theorem isσSlot_iff (u : Slot W) :
    IsσSlot u ↔ ∃ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
      u = σSlotA hW hk hℓ ∨ u = σSlotB hW hk hℓ := by
  constructor
  · intro hu
    exact ⟨_, _, colOf_lt hW u, letterAt_σ_of_isCrossing hu.1, eq_σSlotA_or_σSlotB hW hu⟩
  · rintro ⟨k, m, hk, hℓ, rfl | rfl⟩
    · exact isσSlot_σSlotA hW hk hℓ
    · exact isσSlot_σSlotB hW hk hℓ

/-- Two `σ` slots of one column with the same over bit coincide. -/
theorem σslot_ext {u v : Slot W} (hu : IsσSlot u) (hv : IsσSlot v) (hc : colOf u = colOf v)
    (hd : isDesc u = isDesc v) : u = v := by
  apply slot_eq_of_piece_eq hW .std hc
  have hu2 := hu.2
  have hv2 := hv.2
  rw [hc] at hu2
  rcases hu2 with h1 | h1 <;> rcases hv2 with h2 | h2 <;> simp [isDesc, h1, h2] at hd ⊢

omit hW in
theorem isDesc_eq_true_iff {u : Slot W} (hu : IsσSlot u) :
    isDesc u = true ↔ shapeOf u = .pass (letterAt W (colOf u)).idx ((letterAt W (colOf u)).idx + 1) := by
  unfold isDesc
  rcases hu.2 with h | h <;> rw [h] <;> simp

/-- The twin of a `σ` slot: the other crossing strand of its column (the identity on other slots). -/
noncomputable def σtwin (u : Slot W) : Slot W :=
  if h : (letterAt W (colOf u)).isCrossing = true then
    if isDesc u then σSlotB hW (colOf_lt hW u) (letterAt_σ_of_isCrossing h)
    else σSlotA hW (colOf_lt hW u) (letterAt_σ_of_isCrossing h)
  else u

theorem σtwin_spec {u : Slot W} (hu : IsσSlot u) :
    colOf (σtwin hW u) = colOf u ∧ IsσSlot (σtwin hW u) ∧ isDesc (σtwin hW u) = !isDesc u := by
  unfold σtwin
  simp only [hu.1, ↓reduceDIte]
  cases hd : isDesc u
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    exact ⟨(σSlotA_spec hW _ _).1, isσSlot_σSlotA hW _ _, isDesc_σSlotA hW _ _⟩
  · simp only [↓reduceIte, Bool.not_true]
    exact ⟨(σSlotB_spec hW _ _).1, isσSlot_σSlotB hW _ _, isDesc_σSlotB hW _ _⟩

theorem colOf_σtwin {u : Slot W} (hu : IsσSlot u) : colOf (σtwin hW u) = colOf u := (σtwin_spec hW hu).1

theorem isσSlot_σtwin {u : Slot W} (hu : IsσSlot u) : IsσSlot (σtwin hW u) := (σtwin_spec hW hu).2.1

theorem isDesc_σtwin {u : Slot W} (hu : IsσSlot u) : isDesc (σtwin hW u) = !isDesc u :=
  (σtwin_spec hW hu).2.2

theorem σtwin_σtwin {u : Slot W} (hu : IsσSlot u) : σtwin hW (σtwin hW u) = u := by
  have h1 := σtwin_spec hW hu
  have h2 := σtwin_spec hW h1.2.1
  apply σslot_ext hW h2.2.1 hu (h2.1.trans h1.1)
  rw [h2.2.2, h1.2.2, Bool.not_not]

theorem σtwin_ne {u : Slot W} (hu : IsσSlot u) : σtwin hW u ≠ u := by
  intro h
  have := isDesc_σtwin hW hu
  rw [h] at this
  cases isDesc u <;> simp at this

theorem σsgn_σtwin {u : Slot W} (hu : IsσSlot u) : σsgn (σtwin hW u) = σsgn u := by
  unfold σsgn; rw [colOf_σtwin hW hu]

theorem σtwin_σSlotA {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    σtwin hW (σSlotA hW hk hℓ) = σSlotB hW hk hℓ := by
  have hA := isσSlot_σSlotA hW hk hℓ
  apply σslot_ext hW (isσSlot_σtwin hW hA) (isσSlot_σSlotB hW hk hℓ)
  · rw [colOf_σtwin hW hA, (σSlotA_spec hW hk hℓ).1, (σSlotB_spec hW hk hℓ).1]
  · rw [isDesc_σtwin hW hA, isDesc_σSlotA hW hk hℓ, isDesc_σSlotB hW hk hℓ]; rfl

theorem σtwin_σSlotB {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    σtwin hW (σSlotB hW hk hℓ) = σSlotA hW hk hℓ := by
  rw [← σtwin_σSlotA hW hk hℓ, σtwin_σtwin hW (isσSlot_σSlotA hW hk hℓ)]

/-- The sign of a `σ` slot is β1's `signBit` of its letter at its cut. -/
theorem coe_σsgn_eq_signBit {u : Slot W} (hu : IsσSlot u) :
    ((σsgn u : SignType) : ℤ) = (letterAt W (colOf u)).signBit (cut W (colOf u)) := by
  unfold σsgn
  rw [coe_σsgnCol]
  have hℓ := letterAt_σ_of_isCrossing hu.1
  conv_rhs => rw [hℓ]
  rw [signBit_σ hW (colOf_lt hW u) hℓ]

/-- The sign of a `σ` slot is the geometric sign of its crossing. -/
theorem coe_σsgn_σSlotA (pl : Placement) (hne : W ≠ []) {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    ((σsgn (σSlotA hW hk hℓ) : SignType) : ℤ) =
      ((realizeAt pl hW hne).diagram.sign (crossingOf pl hW hne hk hℓ) : ℤ) := by
  rw [sign_crossingOf, σsgn, (σSlotA_spec hW hk hℓ).1, coe_σsgnCol, hℓ]; rfl

end SigmaSlots

/-! #### C. The slot record of a closed word restricted to an active set of `σ` slots -/

section SlotRecord

variable {W : Word} (hW : W.Closed)

/-- The component of a slot: the component index of its strand (the `comp` field). -/
noncomputable def slotComp (u : Slot W) : Fin (numComp hW) := ((idxEquiv hW).symm u).1

theorem slotComp_eq_iff (u v : Slot W) :
    slotComp hW u = slotComp hW v ↔ (nextPerm hW).SameCycle u v := by
  have := toSlot_fst_eq_iff hW ((idxEquiv hW).symm u) ((idxEquiv hW).symm v)
  rw [← idxEquiv_apply, ← idxEquiv_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  exact this

theorem slotComp_idxEquiv (s : Idx hW) : slotComp hW (idxEquiv hW s) = s.1 := by
  show ((idxEquiv hW).symm (idxEquiv hW s)).1 = s.1
  rw [Equiv.symm_apply_apply]

/-- The component of a slot is its orbit, numbered by `Fintype.equivFin`. -/
theorem slotComp_eq_equivFin (u : Slot W) :
    slotComp hW u = Fintype.equivFin (Orbit hW) (orbitOf hW u) := by
  obtain ⟨⟨i, j⟩, rfl⟩ := (idxEquiv hW).surjective u
  rw [slotComp_idxEquiv]
  have : orbitOf hW (idxEquiv hW ⟨i, j⟩) = orbitOf hW (rep hW i) := by
    rw [orbitOf_eq_iff]
    exact sameCycle_of_iterate hW (s := idxEquiv hW ⟨i, j⟩) (t := rep hW i) (a := 0) (b := j.val) rfl
  rw [this, orbitOf_rep, Equiv.apply_symm_apply]

/-- An *active set* of slots: `σ` slots, closed under the twin. -/
structure ActiveSet (S : Slot W → Prop) : Prop where
  isσ : ∀ u, S u → IsσSlot u
  twin : ∀ u, S u → S (σtwin hW u)

variable (S : Slot W → Prop) [DecidablePred S] (hS : ActiveSet hW S)

/-- The pairing of the active slots: the twin. -/
noncomputable def slotPair : Perm {u : Slot W // S u} where
  toFun u := ⟨σtwin hW u.1, hS.twin _ u.2⟩
  invFun u := ⟨σtwin hW u.1, hS.twin _ u.2⟩
  left_inv u := Subtype.ext (σtwin_σtwin hW (hS.isσ _ u.2))
  right_inv u := Subtype.ext (σtwin_σtwin hW (hS.isσ _ u.2))

/-- THE ABSTRACT NAMED RECORD of a closed word `W` restricted to the active set `S` of `σ` slots
(def:gauss-record read on the slot cycle of the realization):
* `comps := Fin (numComp hW)` — the components (cycles of `next`), crossing-free ones included;
* `M := {u // S u}` — the active slots (one occurrence per crossing strand);
* `comp` — the component of the slot's strand;
* `succ := firstReturn (nextPerm hW) S` — the next active slot along the slot cycle `next`;
* `pair := σtwin` — the other crossing strand of the column;
* `isOver := isDesc` — the descending strand is over;
* `sgn := σsgn` — positive iff the two bits of the column agree (β1's `signBit`). -/
noncomputable def slotRecord : Record where
  comps := Fin (numComp hW)
  M := {u : Slot W // S u}
  comp u := slotComp hW u.1
  succ := firstReturn (nextPerm hW) S
  pair := slotPair hW S hS
  isOver u := isDesc u.1
  sgn u := σsgn u.1
  succ_comp u := (slotComp_eq_iff hW _ _).2 (sameCycle_firstReturn_apply (nextPerm hW) S u).symm
  succ_cycle _ _ h := firstReturn_sameCycle_of_sameCycle _ _ ((slotComp_eq_iff hW _ _).1 h)
  pair_ne u h := σtwin_ne hW (hS.isσ _ u.2) (congrArg Subtype.val h)
  pair_invol u := Subtype.ext (σtwin_σtwin hW (hS.isσ _ u.2))
  bit_pair u := isDesc_σtwin hW (hS.isσ _ u.2)
  sgn_pair u := σsgn_σtwin hW (hS.isσ _ u.2)
  sgn_ne u := σsgn_ne_zero u.1

@[simp] theorem slotRecord_comps : (slotRecord hW S hS).comps = Fin (numComp hW) := rfl
@[simp] theorem slotRecord_M : (slotRecord hW S hS).M = {u : Slot W // S u} := rfl
theorem slotRecord_comp (u : {u : Slot W // S u}) : (slotRecord hW S hS).comp u = slotComp hW u.1 := rfl
theorem slotRecord_succ : (slotRecord hW S hS).succ = firstReturn (nextPerm hW) S := rfl
theorem slotRecord_succ_val (u : {u : Slot W // S u}) :
    ((slotRecord hW S hS).succ u).1 = ((nextPerm hW) ^ returnTime (nextPerm hW) S u.1 u.2) u.1 := rfl
theorem slotRecord_pair_val (u : {u : Slot W // S u}) :
    ((slotRecord hW S hS).pair u).1 = σtwin hW u.1 := rfl
theorem slotRecord_isOver (u : {u : Slot W // S u}) : (slotRecord hW S hS).isOver u = isDesc u.1 := rfl
theorem slotRecord_sgn (u : {u : Slot W // S u}) : (slotRecord hW S hS).sgn u = σsgn u.1 := rfl

/-- Two pointwise-equivalent active sets give isomorphic slot records. -/
noncomputable def slotRecordCongr (S' : Slot W → Prop) [DecidablePred S'] (hS' : ActiveSet hW S')
    (h : ∀ u, S u ↔ S' u) : RecordIso (slotRecord hW S hS) (slotRecord hW S' hS') where
  e := Equiv.refl _
  Φ := Equiv.subtypeEquivRight h
  comp_eq _ := rfl
  succ_eq u := by
    apply Subtype.ext
    exact (firstReturn_conj (nextPerm hW) (nextPerm hW) S S' (Equiv.refl _) (fun _ => rfl) (fun a => (h a).symm) u).symm
  pair_eq _ := rfl
  bit_eq _ := rfl
  sgn_eq _ := rfl

end SlotRecord

/-! #### D. The record of a diagram on the strands of a realization -/

section DiagramIso

/-- Visits are determined by their crossing and their strand. -/
theorem visit_ext {Γ : Shadow} {v w : Γ.Visit} (h1 : v.1 = w.1) (h2 : v.2.val = w.2.val) : v = w := by
  obtain ⟨x, s, hs⟩ := v
  obtain ⟨y, t, ht⟩ := w
  cases h1
  cases (Subtype.ext h2 : (⟨s, hs⟩ : {s // s ∈ x.val}) = ⟨t, ht⟩)
  rfl

theorem signType_ext_int {a b : SignType} (h : ((a : SignType) : ℤ) = b) : a = b := by
  cases a <;> cases b <;> first | rfl | (exfalso; revert h; decide)

/-- Real cyclic betweenness of integer parts plus fractional parts in `[0,1)` is cyclic betweenness of the
integer parts (distinct integers). -/
theorem cycBetween_nat_add {A B C : ℕ} (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) {α β γ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    cycBetween (A + α) (B + β) (C + γ) ↔ ((A < B ∧ B < C) ∨ (B < C ∧ C < A) ∨ (C < A ∧ A < B)) := by
  have key : ∀ (x y : ℕ) (ξ η : ℝ), x ≠ y → 0 ≤ ξ → ξ < 1 → 0 ≤ η → η < 1 →
      ((x : ℝ) + ξ < y + η ↔ x < y) := by
    intro x y ξ η hxy hξ0 hξ1 hη0 hη1
    rcases lt_or_gt_of_ne hxy with h | h
    · have : (x : ℝ) + 1 ≤ y := by exact_mod_cast h
      exact iff_of_true (by linarith) h
    · have : (y : ℝ) + 1 ≤ x := by exact_mod_cast h
      exact iff_of_false (by linarith) (by omega)
  unfold cycBetween
  rw [key A B α β hAB hα0 hα1 hβ0 hβ1, key B C β γ hBC hβ0 hβ1 hγ0 hγ1, key C A γ α hAC.symm hγ0 hγ1 hα0 hα1]

variable (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ [])

/-- The active set of an admissible set `K` of columns: the `σ` slots whose column lies in `K`. -/
def colActive (K : ℕ → Prop) (u : Slot W) : Prop := IsσSlot u ∧ K (colOf u)

instance (K : ℕ → Prop) [DecidablePred K] : DecidablePred (colActive (W := W) K) := fun _ => by
  unfold colActive; infer_instance

theorem colActive_activeSet (K : ℕ → Prop) : ActiveSet hW (colActive K) where
  isσ _ hu := hu.1
  twin u hu := ⟨isσSlot_σtwin hW hu.1, by rw [colOf_σtwin hW hu.1]; exact hu.2⟩

theorem colActive_σSlotA {K : ℕ → Prop} {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) (hK : K k) :
    colActive K (σSlotA hW hk hℓ) := ⟨isσSlot_σSlotA hW hk hℓ, by rw [(σSlotA_spec hW hk hℓ).1]; exact hK⟩

theorem colActive_σSlotB {K : ℕ → Prop} {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) (hK : K k) :
    colActive K (σSlotB hW hk hℓ) := ⟨isσSlot_σSlotB hW hk hℓ, by rw [(σSlotB_spec hW hk hℓ).1]; exact hK⟩

variable (V : (shadowOf pl hW hne).Vertices)

/-- A slot as a strand of the re-vertexed shadow (`Idx hW` is its strand type). -/
noncomputable def stStrand (u : Slot W) : ((shadowOf pl hW hne).withVertices V).Strand := (idxEquiv hW).symm u

@[simp] theorem idxEquiv_stStrand (u : Slot W) : idxEquiv hW (stStrand pl hW hne V u) = u :=
  Equiv.apply_symm_apply _ _

@[simp] theorem stStrand_idxEquiv (s : ((shadowOf pl hW hne).withVertices V).Strand) :
    stStrand pl hW hne V (idxEquiv hW s) = s := Equiv.symm_apply_apply _ _

theorem stStrand_injective : Function.Injective (stStrand pl hW hne V) := (idxEquiv hW).symm.injective

/-- A strand of the re-vertexed shadow as a strand index (the identity, typed). -/
def strIdx (s : ((shadowOf pl hW hne).withVertices V).Strand) : Idx hW := s

theorem idxEquiv_strIdx (s : ((shadowOf pl hW hne).withVertices V).Strand) :
    idxEquiv hW (strIdx pl hW hne V s) = idxEquiv hW s := rfl

theorem strIdx_stStrand (u : Slot W) : strIdx pl hW hne V (stStrand pl hW hne V u) = (idxEquiv hW).symm u := rfl

theorem eq_stStrand_iff (s : ((shadowOf pl hW hne).withVertices V).Strand) (u : Slot W) :
    s = stStrand pl hW hne V u ↔ idxEquiv hW s = u := Equiv.eq_symm_apply _

variable (hgen : ((shadowOf pl hW hne).withVertices V).Generic)
  (ov : ((shadowOf pl hW hne).withVertices V).Crossing → ((shadowOf pl hW hne).withVertices V).Strand)
  (hov : ∀ x, ov x ∈ x.val)

/-- A diagram on the re-vertexed shadow of a realization (the vertex-moved diagrams of the geometric rows;
the realization itself is `V := vertices`). -/
noncomputable abbrev mkDiagram : Diagram := ⟨(shadowOf pl hW hne).withVertices V, hgen, ov, hov⟩

local notation "𝔇" => mkDiagram pl hW hne V hgen ov hov

/-- The crossing pair of the `σ` letter at column `k`, as strands (`Idx hW` is the strand type of every
re-vertexed shadow of the realization). -/
noncomputable abbrev σpair {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    Finset ((shadowOf pl hW hne).withVertices V).Strand :=
  {stStrand pl hW hne V (σSlotA hW hk hℓ), stStrand pl hW hne V (σSlotB hW hk hℓ)}

theorem mem_σpair_A {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    stStrand pl hW hne V (σSlotA hW hk hℓ) ∈ σpair pl hW hne V hk hℓ := Finset.mem_insert_self _ _

theorem mem_σpair_B {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    stStrand pl hW hne V (σSlotB hW hk hℓ) ∈ σpair pl hW hne V hk hℓ :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem mem_σpair_iff {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m)
    (s : ((shadowOf pl hW hne).withVertices V).Strand) :
    s ∈ σpair pl hW hne V hk hℓ ↔ idxEquiv hW s = σSlotA hW hk hℓ ∨ idxEquiv hW s = σSlotB hW hk hℓ := by
  simp only [σpair, Finset.mem_insert, Finset.mem_singleton, eq_stStrand_iff]

theorem colOf_of_mem_σpair {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m)
    {s : ((shadowOf pl hW hne).withVertices V).Strand} (hs : s ∈ σpair pl hW hne V hk hℓ) :
    colOf (idxEquiv hW s) = k := by
  rcases (mem_σpair_iff pl hW hne V hk hℓ s).1 hs with h | h <;> rw [h]
  · exact (σSlotA_spec hW hk hℓ).1
  · exact (σSlotB_spec hW hk hℓ).1

variable (K : ℕ → Prop)

/-- The data making `mkDiagram` a diagram "with the shadow structure of `realize W` and the crossings of
the active columns `K`": its crossings are exactly the `σ` pairs of the columns in `K`, the over strand
of each is the descending strand, and the sign is the printed sign of the letter. -/
structure SlotDiagramData : Prop where
  cross : ∀ x : Finset ((shadowOf pl hW hne).withVertices V).Strand,
    ((shadowOf pl hW hne).withVertices V).IsCrossing x ↔
      ∃ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m), K k ∧ x = σpair pl hW hne V hk hℓ
  overStrand : ∀ (x : ((shadowOf pl hW hne).withVertices V).Crossing) (k m : ℕ) (hk : k < W.length)
    (hℓ : letterAt W k = .σ m), x.val = σpair pl hW hne V hk hℓ → ov x = stStrand pl hW hne V (σSlotA hW hk hℓ)
  sgn : ∀ (x : ((shadowOf pl hW hne).withVertices V).Crossing) (k m : ℕ) (hk : k < W.length)
    (hℓ : letterAt W k = .σ m), x.val = σpair pl hW hne V hk hℓ →
    ((mkDiagram pl hW hne V hgen ov hov).sign x : ℤ) = if bit W k m = bit W k (m + 1) then 1 else -1

variable (data : SlotDiagramData pl hW hne V hgen ov hov K)
include data

/-- The crossing of an active column. -/
noncomputable def σcross {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) (hK : K k) :
    (mkDiagram pl hW hne V hgen ov hov).Γ.Crossing :=
  ⟨σpair pl hW hne V hk hℓ, (data.cross _).2 ⟨k, m, hk, hℓ, hK, rfl⟩⟩

theorem σcross_val {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) (hK : K k) :
    (σcross pl hW hne V hgen ov hov K data hk hℓ hK).val = σpair pl hW hne V hk hℓ := rfl

/-- The strand of a visit is an active `σ` slot. -/
theorem visit_active (v : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    colActive K (idxEquiv hW v.2.val) := by
  obtain ⟨k, m, hk, hℓ, hK, hx⟩ := (data.cross v.1.val).1 v.1.2
  have hs : v.2.val ∈ σpair pl hW hne V hk hℓ := hx ▸ v.2.2
  rcases (mem_σpair_iff pl hW hne V hk hℓ _).1 hs with h | h <;> rw [h]
  · exact colActive_σSlotA hW hk hℓ hK
  · exact colActive_σSlotB hW hk hℓ hK

/-- A strand lies in at most one crossing. -/
theorem crossing_eq_of_mem {x y : (mkDiagram pl hW hne V hgen ov hov).Γ.Crossing}
    {s : (mkDiagram pl hW hne V hgen ov hov).Γ.Strand} (hx : s ∈ x.val) (hy : s ∈ y.val) : x = y := by
  obtain ⟨k, m, hk, hℓ, -, ex⟩ := (data.cross x.val).1 x.2
  obtain ⟨k', m', hk', hℓ', -, ey⟩ := (data.cross y.val).1 y.2
  have hkk : k = k' :=
    (colOf_of_mem_σpair pl hW hne V hk hℓ (ex ▸ hx)).symm.trans (colOf_of_mem_σpair pl hW hne V hk' hℓ' (ey ▸ hy))
  subst hkk
  have hmm : m = m' := Letter.σ.inj (hℓ.symm.trans hℓ')
  subst hmm
  exact Subtype.ext (ex.trans ey.symm)

/-- The visit of an active slot. -/
noncomputable def toVisit (u : {u : Slot W // colActive K u}) : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit :=
  ⟨σcross pl hW hne V hgen ov hov K data (colOf_lt hW u.1) (letterAt_σ_of_isCrossing u.2.1.1) u.2.2,
    ⟨stStrand pl hW hne V u.1, by
      rw [σcross_val, mem_σpair_iff, idxEquiv_stStrand]
      exact eq_σSlotA_or_σSlotB hW u.2.1⟩⟩

theorem toVisit_strand (u : {u : Slot W // colActive K u}) :
    (toVisit pl hW hne V hgen ov hov K data u).2.val = stStrand pl hW hne V u.1 := rfl

/-- The visits of the diagram are the active slots. -/
noncomputable def visitEquiv : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit ≃ {u : Slot W // colActive K u} where
  toFun v := ⟨idxEquiv hW v.2.val, visit_active pl hW hne V hgen ov hov K data v⟩
  invFun := toVisit pl hW hne V hgen ov hov K data
  left_inv v := by
    apply visit_ext
    · refine crossing_eq_of_mem pl hW hne V hgen ov hov K data (s := v.2.val) ?_ v.2.2
      have h := (toVisit pl hW hne V hgen ov hov K data
        ⟨idxEquiv hW v.2.val, visit_active pl hW hne V hgen ov hov K data v⟩).2.2
      rwa [toVisit_strand, stStrand_idxEquiv] at h
    · rw [toVisit_strand, stStrand_idxEquiv]
  right_inv u := Subtype.ext (by
    show idxEquiv hW (toVisit pl hW hne V hgen ov hov K data u).2.val = u.1
    rw [toVisit_strand, idxEquiv_stStrand])

theorem visitEquiv_apply_val (v : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    (visitEquiv pl hW hne V hgen ov hov K data v).1 = idxEquiv hW v.2.val := rfl

theorem visitEquiv_symm_apply (u : {u : Slot W // colActive K u}) :
    (visitEquiv pl hW hne V hgen ov hov K data).symm u = toVisit pl hW hne V hgen ov hov K data u := rfl

/-- The other strand of a crossing is the twin slot. -/
theorem slot_other {x : (mkDiagram pl hW hne V hgen ov hov).Γ.Crossing}
    {s : (mkDiagram pl hW hne V hgen ov hov).Γ.Strand} (hs : s ∈ x.val) :
    idxEquiv hW (((shadowOf pl hW hne).withVertices V).other x hs) = σtwin hW (idxEquiv hW s) := by
  obtain ⟨k, m, hk, hℓ, -, ex⟩ := (data.cross x.val).1 x.2
  have hs' : s ∈ σpair pl hW hne V hk hℓ := ex ▸ hs
  have hAB : stStrand pl hW hne V (σSlotA hW hk hℓ) ≠ stStrand pl hW hne V (σSlotB hW hk hℓ) :=
    fun h => σSlotA_ne_σSlotB hW hk hℓ (stStrand_injective pl hW hne V h)
  rcases (mem_σpair_iff pl hW hne V hk hℓ s).1 hs' with h | h
  · have hsA : s = stStrand pl hW hne V (σSlotA hW hk hℓ) := (eq_stStrand_iff pl hW hne V _ _).2 h
    have : stStrand pl hW hne V (σSlotB hW hk hℓ) = ((shadowOf pl hW hne).withVertices V).other x hs :=
      ((shadowOf pl hW hne).withVertices V).eq_other_of_mem_of_ne x hs
        (by rw [ex]; exact mem_σpair_B pl hW hne V hk hℓ) (by rw [hsA]; exact hAB.symm)
    rw [← this, idxEquiv_stStrand, h, σtwin_σSlotA]
  · have hsB : s = stStrand pl hW hne V (σSlotB hW hk hℓ) := (eq_stStrand_iff pl hW hne V _ _).2 h
    have : stStrand pl hW hne V (σSlotA hW hk hℓ) = ((shadowOf pl hW hne).withVertices V).other x hs :=
      ((shadowOf pl hW hne).withVertices V).eq_other_of_mem_of_ne x hs
        (by rw [ex]; exact mem_σpair_A pl hW hne V hk hℓ) (by rw [hsB]; exact hAB)
    rw [← this, idxEquiv_stStrand, h, σtwin_σSlotB]

/-- The over bit of a visit is the descent bit of its slot. -/
theorem overBit_eq (v : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    (mkDiagram pl hW hne V hgen ov hov).overBit v = isDesc (idxEquiv hW v.2.val) := by
  obtain ⟨k, m, hk, hℓ, -, ex⟩ := (data.cross v.1.val).1 v.1.2
  have hs : v.2.val ∈ σpair pl hW hne V hk hℓ := ex ▸ v.2.2
  have hover : (mkDiagram pl hW hne V hgen ov hov).overStrand v.1 = stStrand pl hW hne V (σSlotA hW hk hℓ) :=
    data.overStrand v.1 k m hk hℓ ex
  unfold Diagram.overBit
  rw [hover]
  rcases (mem_σpair_iff pl hW hne V hk hℓ _).1 hs with h | h
  · rw [h, isDesc_σSlotA]
    exact decide_eq_true ((eq_stStrand_iff pl hW hne V _ _).2 h)
  · rw [h, isDesc_σSlotB]
    refine decide_eq_false (fun e => σSlotA_ne_σSlotB hW hk hℓ ?_)
    rw [← h, e, idxEquiv_stStrand]

/-- The sign of a visit is the `σ` sign of its slot. -/
theorem sign_eq (v : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    (mkDiagram pl hW hne V hgen ov hov).sign v.1 = σsgn (idxEquiv hW v.2.val) := by
  obtain ⟨k, m, hk, hℓ, -, ex⟩ := (data.cross v.1.val).1 v.1.2
  have hcol : colOf (idxEquiv hW v.2.val) = k := colOf_of_mem_σpair pl hW hne V hk hℓ (ex ▸ v.2.2)
  apply signType_ext_int
  rw [data.sgn v.1 k m hk hℓ ex, σsgn, hcol, coe_σsgnCol, hℓ]; rfl

/-- Two visits with the same strand coincide (a strand lies in at most one crossing). -/
theorem visit_eq_of_strand_eq {w w' : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit}
    (h : w.2.val = w'.2.val) : w = w' :=
  visit_ext (crossing_eq_of_mem pl hW hne V hgen ov hov K data (h ▸ w.2.2) w'.2.2) h

omit data in
/-- Moving `n` steps along a component is `n` applications of `next`. -/
theorem idxEquiv_add (i : Fin (numComp hW)) (a : ZMod (period hW (rep hW i))) (n : ℕ) :
    idxEquiv hW ⟨i, a + n⟩ = (next hW)^[n] (idxEquiv hW ⟨i, a⟩) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih, Nat.cast_succ, ← add_assoc]
    exact toSlot_succ hW i (a + n)

omit data in
theorem nextPerm_pow_apply (n : ℕ) (u : Slot W) : ((nextPerm hW) ^ n) u = (next hW)^[n] u := by
  rw [Equiv.Perm.coe_pow]; rfl

omit data in
/-- The traversal coordinate of a visit: its strand's label plus its crossing parameter. -/
theorem visitCoord_eq (w : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    (mkDiagram pl hW hne V hgen ov hov).visitCoord w =
      ((w.2.val.2.val : ℕ) : ℝ) + ((mkDiagram pl hW hne V hgen ov hov).visitPt w).2.2.val := rfl

omit data in
/-- The traversal coordinate of a visit whose strand is `⟨i, b⟩` (as a strand index). -/
theorem visitCoord_eq_of (w : (𝔇).Γ.Visit) {i : Fin (numComp hW)} {b : ZMod (period hW (rep hW i))}
    (h : strIdx pl hW hne V w.2.val = ⟨i, b⟩) :
    (𝔇).visitCoord w = ((b.val : ℕ) : ℝ) + ((𝔇).visitPt w).2.2.val := by
  have e : (w.2.val.2.val : ℕ) = b.val := by
    have := congrArg (fun s : Idx hW => s.2.val) h
    exact this
  rw [visitCoord_eq, e]

omit data in
/-- The component of a visit whose strand is `⟨i, b⟩`. -/
theorem compOf_eq_of (w : (𝔇).Γ.Visit) {i : Fin (numComp hW)} {b : ZMod (period hW (rep hW i))}
    (h : strIdx pl hW hne V w.2.val = ⟨i, b⟩) : (𝔇).compOf w = i := by
  have := congrArg Sigma.fst h
  exact this

/-- THE SUCCESSOR LAW: the forward successor of a visit is the first return of the slot cycle `next` to
the active slots (each strand carries at most one visit, so the traversal order of the visits on a
component is the cyclic order of their strands). -/
theorem nextVisit_eq [DecidablePred K] (v : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    (mkDiagram pl hW hne V hgen ov hov).nextVisit v =
      toVisit pl hW hne V hgen ov hov K data
        (firstReturn (nextPerm hW) (colActive K) (visitEquiv pl hW hne V hgen ov hov K data v)) := by
  set S : Slot W → Prop := colActive (W := W) K with hSdef
  set u₀ : {u : Slot W // S u} := visitEquiv pl hW hne V hgen ov hov K data v with hu₀
  obtain ⟨i, a, hva⟩ : ∃ (i : Fin (numComp hW)) (a : ZMod (period hW (rep hW i))),
      strIdx pl hW hne V v.2.val = ⟨i, a⟩ := ⟨_, _, rfl⟩
  have hu₀v : u₀.1 = idxEquiv hW ⟨i, a⟩ := by
    show idxEquiv hW (strIdx pl hW hne V v.2.val) = _
    rw [hva]
  set n := returnTime (nextPerm hW) S u₀.1 u₀.2 with hn
  have hn0 : 0 < n := returnTime_pos _ _ _ _
  have hmin : ∀ j, 0 < j → j < n → ¬ S (((nextPerm hW) ^ j) u₀.1) :=
    fun j hj hjn => returnTime_min _ _ _ _ hj hjn
  have hfr : (firstReturn (nextPerm hW) S u₀).1 = ((nextPerm hW) ^ n) u₀.1 := rfl
  have hk3 : 3 ≤ period hW (rep hW i) := three_le_period hW _
  have hkpos : 0 < period hW (rep hW i) := by omega
  have hpow : ∀ j : ℕ, ((nextPerm hW) ^ j) u₀.1 = idxEquiv hW ⟨i, a + j⟩ := by
    intro j; rw [nextPerm_pow_apply, idxEquiv_add, hu₀v]
  have hnk : n ≤ period hW (rep hW i) := by
    apply returnTime_le_of_pow_eq (nextPerm hW) S u₀.1 u₀.2 hkpos
    rw [hpow, hu₀v, ZMod.natCast_self, add_zero]
  set w := toVisit pl hW hne V hgen ov hov K data (firstReturn (nextPerm hW) S u₀) with hw
  have hw2 : strIdx pl hW hne V w.2.val = ⟨i, a + n⟩ := by
    show strIdx pl hW hne V (stStrand pl hW hne V (firstReturn (nextPerm hW) S u₀).1) = _
    rw [strIdx_stStrand, hfr, hpow]
    exact Equiv.symm_apply_apply _ _
  -- every visit of the component sits `j` steps after `v`, at an active slot
  have hcomp : ∀ (b : ZMod (period hW (rep hW i))), ∃ j : ℕ, j < period hW (rep hW i) ∧ b = a + j := by
    intro b
    exact ⟨(b - a).val, ZMod.val_lt _, by rw [ZMod.natCast_zmod_val, add_sub_cancel]⟩
  have hno : ∀ (u' : (𝔇).Γ.Visit) (b : ZMod (period hW (rep hW i))), strIdx pl hW hne V u'.2.val = ⟨i, b⟩ →
      ∀ j : ℕ, b = a + j → 0 < j → j < n → False := by
    intro u' b hub j hb hj hjn
    apply hmin j hj hjn
    rw [hpow, ← hb, ← hub, idxEquiv_strIdx]
    exact visit_active pl hW hne V hgen ov hov K data u'
  have hcast_ne : ∀ j : ℕ, 0 < j → j < period hW (rep hW i) → (j : ZMod (period hW (rep hW i))) ≠ 0 := by
    intro j hj hjk h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact absurd (Nat.le_of_dvd hj h) (not_le.2 hjk)
  have hcast_inj : ∀ j j' : ℕ, j < period hW (rep hW i) → j' < period hW (rep hW i) →
      (j : ZMod (period hW (rep hW i))) = j' → j = j' := by
    intro j j' hj hj' h
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at this
  have hvisit_eq : ∀ (u' u'' : (𝔇).Γ.Visit) (b : ZMod (period hW (rep hW i))),
      strIdx pl hW hne V u'.2.val = ⟨i, b⟩ → strIdx pl hW hne V u''.2.val = ⟨i, b⟩ → u' = u'' := by
    intro u' u'' b h1 h2
    apply visit_eq_of_strand_eq pl hW hne V hgen ov hov K data
    exact h1.trans h2.symm
  have hcompv : ∀ u' : (𝔇).Γ.Visit, (𝔇).compOf u' = (𝔇).compOf v →
      ∃ b : ZMod (period hW (rep hW i)), strIdx pl hW hne V u'.2.val = ⟨i, b⟩ := by
    intro u' hu'
    obtain ⟨i', b, hub⟩ : ∃ (i' : Fin (numComp hW)) (b : ZMod (period hW (rep hW i'))),
      strIdx pl hW hne V u'.2.val = ⟨i', b⟩ := ⟨_, _, rfl⟩
    have hi' : i = i' := by
      rw [← compOf_eq_of pl hW hne V hgen ov hov u' hub, ← compOf_eq_of pl hW hne V hgen ov hov v hva, hu']
    subst hi'
    exact ⟨b, hub⟩
  rcases lt_or_eq_of_le hnk with hlt | heq
  · -- `n < k`: the candidate differs from `v`; uniqueness of the cyclic successor
    have hwv : w ≠ v := by
      intro h
      have h2 : strIdx pl hW hne V w.2.val = strIdx pl hW hne V v.2.val := by rw [h]
      rw [hw2, hva] at h2
      have h3 : a + (n : ZMod (period hW (rep hW i))) = a := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
      exact hcast_ne n hn0 hlt (add_eq_left.1 h3)
    have hwc : (𝔇).compOf w = (𝔇).compOf v := by
      rw [compOf_eq_of pl hW hne V hgen ov hov w hw2, compOf_eq_of pl hW hne V hgen ov hov v hva]
    apply cycNext_unique_on (p := fun w' => (𝔇).compOf w' = (𝔇).compOf v) (k := (𝔇).visitCoord)
      (fun a b ha hb h => (𝔇).visitCoord_injOn (ha.trans hb.symm) h) rfl ((𝔇).compOf_nextVisit v) hwc
      ((𝔇).nextVisit_ne_self v w hwc hwv) hwv (fun u' hu' => (𝔇).nextVisit_no_between v u' hu')
    intro u' hu'
    obtain ⟨b, hub⟩ := hcompv u' hu'
    obtain ⟨j, hjk, hb⟩ := hcomp b
    rw [hb] at hub
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hvisit_eq u' v _ hub (by rw [hva, Nat.cast_zero, add_zero])]
      exact not_cycBetween_self_left _ _
    rcases lt_trichotomy j n with hjn | hjn | hnj
    · exact (hno u' _ hub j rfl hj0 hjn).elim
    · rw [hvisit_eq u' w _ hub (by rw [hw2, hjn])]
      exact not_cycBetween_self_mid _ _
    · -- `n < j`: the coordinates are in the wrong cyclic order
      rw [visitCoord_eq_of pl hW hne V hgen ov hov v hva, visitCoord_eq_of pl hW hne V hgen ov hov u' hub,
        visitCoord_eq_of pl hW hne V hgen ov hov w hw2]
      have hAB : a.val ≠ (a + (j : ZMod (period hW (rep hW i)))).val := by
        intro h
        have := ZMod.val_injective _ h
        exact hcast_ne j hj0 hjk (add_eq_left.1 this.symm)
      have hBC : (a + (j : ZMod (period hW (rep hW i)))).val ≠ (a + (n : ZMod (period hW (rep hW i)))).val := by
        intro h
        have := hcast_inj j n hjk hlt (add_left_cancel (ZMod.val_injective _ h))
        omega
      have hAC : a.val ≠ (a + (n : ZMod (period hW (rep hW i)))).val := by
        intro h
        have := ZMod.val_injective _ h
        exact hcast_ne n hn0 hlt (add_eq_left.1 this.symm)
      rw [cycBetween_nat_add hAB hBC hAC ((𝔇).visitPt v).2.2.2.1 ((𝔇).visitPt v).2.2.2.2
        ((𝔇).visitPt u').2.2.2.1 ((𝔇).visitPt u').2.2.2.2 ((𝔇).visitPt w).2.2.2.1 ((𝔇).visitPt w).2.2.2.2]
      have hb' : (a + (j : ZMod (period hW (rep hW i)))).val = a.val + j ∨
          (a + (j : ZMod (period hW (rep hW i)))).val + period hW (rep hW i) = a.val + j := by
        rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hjk]
        exact add_mod_cases _ _ _ (ZMod.val_lt a) hjk
      have hc' : (a + (n : ZMod (period hW (rep hW i)))).val = a.val + n ∨
          (a + (n : ZMod (period hW (rep hW i)))).val + period hW (rep hW i) = a.val + n := by
        rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
        exact add_mod_cases _ _ _ (ZMod.val_lt a) hlt
      rw [cycIdx_iff (period hW (rep hW i)) j n a.val _ _ hkpos (ZMod.val_lt _) (ZMod.val_lt _) hj0 hn0 hjk hlt
        hb' hc']
      omega
  · -- `n = k`: `v` is the only visit of its component, and the candidate is `v`
    have hwv : w = v := by
      apply hvisit_eq w v _ hw2
      rw [hva, heq, ZMod.natCast_self, add_zero]
    rw [hwv]
    apply (𝔇).nextVisit_eq_self v
    intro u' hu'
    obtain ⟨b, hub⟩ := hcompv u' hu'
    obtain ⟨j, hjk, hb⟩ := hcomp b
    rw [hb] at hub
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hvisit_eq u' v _ hub (by rw [hva, Nat.cast_zero, add_zero])
    · exact (hno u' _ hub j rfl hj0 (heq ▸ hjk)).elim

/-- THE RECORD OF A DIAGRAM ON THE STRANDS OF A REALIZATION is the slot record of the active columns. -/
noncomputable def diagramRecordIso [DecidablePred K] :
    RecordIso (mkDiagram pl hW hne V hgen ov hov).record (slotRecord hW (colActive K) (colActive_activeSet hW K)) where
  e := Equiv.refl _
  Φ := visitEquiv pl hW hne V hgen ov hov K data
  comp_eq v := by
    show slotComp hW (idxEquiv hW v.2.val) = v.2.val.1
    exact slotComp_idxEquiv hW _
  succ_eq v := by
    show visitEquiv pl hW hne V hgen ov hov K data ((mkDiagram pl hW hne V hgen ov hov).nextVisit v) = _
    rw [nextVisit_eq pl hW hne V hgen ov hov K data]
    exact (visitEquiv pl hW hne V hgen ov hov K data).apply_symm_apply _
  pair_eq v := by
    apply Subtype.ext
    show idxEquiv hW ((mkDiagram pl hW hne V hgen ov hov).twin v).2.val = σtwin hW (idxEquiv hW v.2.val)
    exact slot_other pl hW hne V hgen ov hov K data v.2.2
  bit_eq v := (overBit_eq pl hW hne V hgen ov hov K data v).symm
  sgn_eq v := (sign_eq pl hW hne V hgen ov hov K data v).symm

end DiagramIso

/-! #### E. The realization itself -/

section Realize

variable (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ [])

/-- All `σ` slots form an active set. -/
theorem allActive : ActiveSet hW (IsσSlot (W := W)) where
  isσ _ hu := hu
  twin _ hu := isσSlot_σtwin hW hu

/-- The realization is the diagram with all `σ` columns active. -/
theorem realizeAt_data :
    SlotDiagramData pl hW hne (shadowOf pl hW hne).vertices (realizeAt pl hW hne).generic
      (realizeAt pl hW hne).overStrand (realizeAt pl hW hne).overStrand_mem (fun _ => True) where
  cross x := by
    constructor
    · intro h
      have e := congrArg Subtype.val (eq_crossingOf pl hW hne ⟨x, h⟩)
      rw [crossingOf_val] at e
      exact ⟨_, _, _, _, trivial, e⟩
    · rintro ⟨k, m, hk, hℓ, -, rfl⟩
      exact (crossingOf pl hW hne hk hℓ).2
  overStrand x k m hk hℓ hx := by
    have : x = crossingOf pl hW hne hk hℓ := Subtype.ext hx
    rw [this]
    exact overStrand_crossingOf pl hW hne hk hℓ
  sgn x k m hk hℓ hx := by
    have : x = crossingOf pl hW hne hk hℓ := Subtype.ext hx
    rw [this]
    exact sign_crossingOf pl hW hne hk hℓ

/-- `realizeRecordIso` for `realizeAt`: the named record of the realization is the slot record of all
`σ` slots. -/
noncomputable def realizeAtRecordIso :
    RecordIso (realizeAt pl hW hne).diagram.record (slotRecord hW IsσSlot (allActive hW)) :=
  (diagramRecordIso pl hW hne (shadowOf pl hW hne).vertices (realizeAt pl hW hne).generic
    (realizeAt pl hW hne).overStrand (realizeAt pl hW hne).overStrand_mem (fun _ => True)
    (realizeAt_data pl hW hne)).trans
    (slotRecordCongr hW _ _ IsσSlot (allActive hW) (fun _ => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩))

end Realize



/-! #### G. The exterior correspondence of `X ++ P ++ Y` and `X ++ P' ++ Y` (β2's `shiftIdx`/`extSlot`/`next_ext`) -/

section Exterior

variable (X P Y P' : Word)

instance instDecidableExtCol (k : ℕ) : Decidable (ExtCol X P k) := by unfold ExtCol; infer_instance
instance instDecidablePredExtCol : DecidablePred (ExtCol X P) := fun k => instDecidableExtCol X P k

/-- A slot whose piece lies in an exterior column. -/
def ExtPiece (u : Slot (X ++ P ++ Y)) : Prop := ExtCol X P (colOf u)

instance : DecidablePred (ExtPiece X P Y) := fun u => by unfold ExtPiece; infer_instance

theorem extPiece_σtwin (hW : (X ++ P ++ Y).Closed) {u : Slot (X ++ P ++ Y)} (hu : IsσSlot u)
    (h : ExtPiece X P Y u) : ExtPiece X P Y (σtwin hW u) := by
  show ExtCol X P (colOf _); rw [colOf_σtwin hW hu]; exact h

theorem shiftIdx_injOn (hP : P ≠ []) {k k' : ℕ} (hk : ExtCol X P k) (hk' : ExtCol X P k')
    (h : shiftIdx X P P' k = shiftIdx X P P' k') : k = k' := by
  have := P_length_pos P hP
  unfold ExtCol at hk hk'
  unfold shiftIdx at h
  split_ifs at h <;> omega

/-- The inverse index shift on exterior columns of `W'`. -/
def unshiftCol (k' : ℕ) : ℕ := if k' < X.length then k' else k' + P.length - P'.length

theorem unshiftCol_spec (hP : P ≠ []) {k' : ℕ} (h : ExtCol X P' k') :
    ExtCol X P (unshiftCol X P P' k') ∧ shiftIdx X P P' (unshiftCol X P P' k') = k' := by
  have := P_length_pos P hP
  unfold ExtCol at h ⊢
  unfold unshiftCol shiftIdx
  split_ifs <;> omega

theorem colOf_mk {V : Word} (k p : ℕ) (hs : IsSlot V (k, p)) :
    colOf (⟨(k, p), hs⟩ : Slot V) = if p = 0 then k else if bit V k p then k else k - 1 := rfl

variable (hP : P ≠ []) (hE : SameEffect X P P') (hW : (X ++ P ++ Y).Closed) (hW' : (X ++ P' ++ Y).Closed)
include hP hE hW

/-- The slot of `W'` corresponding to an exterior-piece slot of `W` (β2's `extSlot`). -/
noncomputable def extF (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    {u' : Slot (X ++ P' ++ Y) // ExtPiece X P' Y u'} :=
  ⟨extSlot X P Y P' hP hE ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩, by
    show ExtCol X P' (colOf _)
    rw [colOf_ext X P Y P' hP hE hW ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩ u.2]
    exact extCol_shift X P P' hP u.2⟩

theorem extF_val (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    (extF X P Y P' hP hE hW u).1.1 = extPair X P P' u.1.1 := rfl

theorem extF_eq (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    (extF X P Y P' hP hE hW u).1 = extSlot X P Y P' hP hE ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩ := rfl

theorem extF_injective : Function.Injective (extF X P Y P' hP hE hW) := by
  rintro ⟨⟨⟨k, p⟩, hs⟩, hu⟩ ⟨⟨⟨k', p'⟩, hs'⟩, hv⟩ h
  have h1 : extPair X P P' (k, p) = extPair X P P' (k', p') := congrArg (fun x => x.1.1) h
  simp only [extPair, Prod.mk.injEq] at h1
  obtain ⟨hsh, rfl⟩ := h1
  have hext : IsExtSlot X P (k, p) := isExtSlot_of_extCol X P Y P' hP hE ⟨(k, p), hs⟩ hu
  have hext' : IsExtSlot X P (k', p) := isExtSlot_of_extCol X P Y P' hP hE ⟨(k', p), hs'⟩ hv
  have hu' := hu; have hv' := hv
  unfold ExtPiece at hu' hv'
  rw [colOf_mk] at hu' hv'
  suffices hkk : k = k' by subst hkk; rfl
  by_cases hp : p = 0
  · simp only [hp, ↓reduceIte] at hu' hv'
    exact shiftIdx_injOn X P P' hP hu' hv' hsh
  · simp only [hp, ↓reduceIte] at hu' hv'
    unfold IsExtSlot at hext hext'
    simp only [hp, ↓reduceIte] at hext hext'
    have hb : bit (X ++ P ++ Y) k p = bit (X ++ P ++ Y) k' p := by
      rw [bit_ext X P Y P' hP hE hext, bit_ext X P Y P' hP hE hext', hsh]
    cases hbk : bit (X ++ P ++ Y) k p
    · rw [hbk] at hu' hb
      rw [← hb] at hv'
      simp only [Bool.false_eq_true, ↓reduceIte] at hu' hv'
      have hk1 : 1 ≤ k := (cutSlot_pos hW (by
        rcases hs with ⟨h0, -⟩ | ⟨h1, -, -⟩
        · exact absurd h0 hp
        · exact h1) (by
        rcases hs with ⟨h0, -⟩ | ⟨-, h2, -⟩
        · exact absurd h0 hp
        · exact h2)).1
      have hk1' : 1 ≤ k' := (cutSlot_pos hW (by
        rcases hs' with ⟨h0, -⟩ | ⟨h1, -, -⟩
        · exact absurd h0 hp
        · exact h1) (by
        rcases hs' with ⟨h0, -⟩ | ⟨-, h2, -⟩
        · exact absurd h0 hp
        · exact h2)).1
      have e1 := shiftIdx_pred X P P' hP hu' hk1
      have e2 := shiftIdx_pred X P P' hP hv' hk1'
      have := shiftIdx_injOn X P P' hP hu' hv' (by rw [e1, e2, hsh])
      omega
    · rw [hbk] at hu' hb
      rw [← hb] at hv'
      simp only [↓reduceIte] at hu' hv'
      exact shiftIdx_injOn X P P' hP hu' hv' hsh

omit hP hE hW in
theorem length_W' : (X ++ P' ++ Y).length = X.length + P'.length + Y.length := by
  simp only [List.length_append]
omit hP hE hW in
theorem length_W : (X ++ P ++ Y).length = X.length + P.length + Y.length := by
  simp only [List.length_append]

theorem extF_surjective : Function.Surjective (extF X P Y P' hP hE hW) := by
  rintro ⟨⟨⟨j', p⟩, hs'⟩, hu'⟩
  have hu'' := hu'
  unfold ExtPiece at hu''
  rw [colOf_mk] at hu''
  have hPpos := P_length_pos P hP
  have hlen := length_W X P Y
  have hlen' := length_W' X Y P'
  by_cases hp : p = 0
  · subst hp
    simp only [↓reduceIte] at hu''
    obtain ⟨hk, hsh⟩ := unshiftCol_spec X P P' hP hu''
    set k := unshiftCol X P P' j' with hkdef
    have hj' : j' < (X ++ P' ++ Y).length := by
      rcases hs' with ⟨-, h, -⟩ | ⟨h, -, -⟩
      · exact h
      · omega
    have hkW : k < (X ++ P ++ Y).length := by
      unfold unshiftCol at hkdef; unfold ExtCol at hu''; split_ifs at hkdef <;> omega
    have hslot : IsSlot (X ++ P ++ Y) (k, 0) := by
      left
      refine ⟨rfl, hkW, ?_⟩
      rw [letterAt_ext X P Y P' hP hk, hsh]
      rcases hs' with ⟨-, -, h⟩ | ⟨h, -, -⟩
      · exact h
      · omega
    refine ⟨⟨⟨(k, 0), hslot⟩, ?_⟩, ?_⟩
    · show ExtCol X P (colOf _); rw [colOf_mk]; simpa using hk
    · apply Subtype.ext; apply Subtype.ext
      rw [extF_val]; simp only [extPair]; rw [hsh]
  · simp only [hp, ↓reduceIte] at hu''
    have hs'' : 1 ≤ p ∧ p ≤ (cut (X ++ P' ++ Y) j').length ∧ j' ≤ (X ++ P' ++ Y).length := by
      rcases hs' with ⟨h0, -⟩ | h
      · exact absurd h0 hp
      · exact h
    cases hb : bit (X ++ P' ++ Y) j' p
    · -- leftward: the piece is in column `j' - 1`
      rw [hb] at hu''
      simp only [Bool.false_eq_true, ↓reduceIte] at hu''
      have hj1 : 1 ≤ j' := by
        rcases Nat.eq_zero_or_pos j' with rfl | h
        · exfalso
          have := hs''.2.1
          rw [cut_zero] at this
          simp at this
          omega
        · exact h
      obtain ⟨hk, hsh⟩ := unshiftCol_spec X P P' hP hu''
      set k := unshiftCol X P P' (j' - 1) with hkdef
      have hsh1 : shiftIdx X P P' (k + 1) = j' := by rw [shiftIdx_succ X P P' hP hk, hsh]; omega
      have hkW : k + 1 ≤ (X ++ P ++ Y).length := by
        unfold unshiftCol at hkdef; unfold ExtCol at hu''; split_ifs at hkdef <;> omega
      have hcut : cut (X ++ P ++ Y) (k + 1) = cut (X ++ P' ++ Y) j' := by
        rw [cut_ext X P Y P' hP hE hk.extCut_succ, hsh1]
      have hslot : IsSlot (X ++ P ++ Y) (k + 1, p) := by
        right; exact ⟨hs''.1, by rw [hcut]; exact hs''.2.1, hkW⟩
      have hbit : bit (X ++ P ++ Y) (k + 1) p = false := by
        rw [bit_ext X P Y P' hP hE hk.extCut_succ, hsh1, hb]
      refine ⟨⟨⟨(k + 1, p), hslot⟩, ?_⟩, ?_⟩
      · show ExtCol X P (colOf _); rw [colOf_mk]; simp only [hp, ↓reduceIte, hbit, Bool.false_eq_true]
        simpa using hk
      · apply Subtype.ext; apply Subtype.ext
        rw [extF_val]; simp only [extPair]; rw [hsh1]
    · -- rightward: the piece is in column `j'`
      rw [hb] at hu''
      simp only [↓reduceIte] at hu''
      obtain ⟨hk, hsh⟩ := unshiftCol_spec X P P' hP hu''
      set k := unshiftCol X P P' j' with hkdef
      have hkW : k ≤ (X ++ P ++ Y).length := by
        unfold unshiftCol at hkdef; unfold ExtCol at hu''; split_ifs at hkdef <;> omega
      have hcut : cut (X ++ P ++ Y) k = cut (X ++ P' ++ Y) j' := by
        rw [cut_ext X P Y P' hP hE hk.extCut, hsh]
      have hslot : IsSlot (X ++ P ++ Y) (k, p) := by
        right; exact ⟨hs''.1, by rw [hcut]; exact hs''.2.1, hkW⟩
      have hbit : bit (X ++ P ++ Y) k p = true := by
        rw [bit_ext X P Y P' hP hE hk.extCut, hsh, hb]
      refine ⟨⟨⟨(k, p), hslot⟩, ?_⟩, ?_⟩
      · show ExtCol X P (colOf _); rw [colOf_mk]; simp only [hp, ↓reduceIte, hbit]; exact hk
      · apply Subtype.ext; apply Subtype.ext
        rw [extF_val]; simp only [extPair]; rw [hsh]

/-- THE EXTERIOR SLOT CORRESPONDENCE: the exterior-piece slots of the two words are in bijection by the
index shift (`shiftIdx`); `P'` may be empty. -/
noncomputable def φE : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u} ≃ {u' : Slot (X ++ P' ++ Y) // ExtPiece X P' Y u'} :=
  Equiv.ofBijective (extF X P Y P' hP hE hW) ⟨extF_injective X P Y P' hP hE hW, extF_surjective X P Y P' hP hE hW⟩

theorem φE_apply (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    φE X P Y P' hP hE hW u = extF X P Y P' hP hE hW u := rfl

theorem φE_val (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    (φE X P Y P' hP hE hW u).1.1 = extPair X P P' u.1.1 := rfl

theorem colOf_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    colOf (φE X P Y P' hP hE hW u).1 = shiftIdx X P P' (colOf u.1) :=
  colOf_ext X P Y P' hP hE hW ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩ u.2

/-- THE BLOCK PASSAGE HYPOTHESIS (verified by the rows on their concrete patterns): from every *entry slot*
`b` of the block of `W` (an exterior slot whose piece lies in the block: cut `|X|` heading right or cut
`|X|+|P|` heading left) the traversal exits the block after `m` steps at the exterior-piece slot `c`, and
in `W'` the slot `b'` corresponding to `b` reaches the slot corresponding to `c` after `m'` block steps
(`m' = 0` allowed: the case `P' = []`). -/
structure Passage : Prop where
  pass : ∀ b : Slot (X ++ P ++ Y), IsExtSlot X P b.1 → ¬ ExtCol X P (colOf b) →
    ∃ (m : ℕ) (c : Slot (X ++ P ++ Y)), (next hW)^[m] b = c ∧ ExtCol X P (colOf c) ∧
      (∀ i < m, ¬ ExtCol X P (colOf ((next hW)^[i] b))) ∧
      ∃ (m' : ℕ) (b' : Slot (X ++ P' ++ Y)), b'.1 = extPair X P P' b.1 ∧
        ((next hW')^[m'] b').1 = extPair X P P' c.1 ∧
        ∀ i < m', ¬ ExtCol X P' (colOf ((next hW')^[i] b'))

/-- The passage hypothesis makes the first returns to the exterior-piece slots conjugate under `φE`. -/
theorem conj_of_passage (hpass : Passage X P Y P' hW hW') (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    firstReturn (nextPerm hW') (ExtPiece X P' Y) (φE X P Y P' hP hE hW u) =
      φE X P Y P' hP hE hW (firstReturn (nextPerm hW) (ExtPiece X P Y) u) := by
  set φ := φE X P Y P' hP hE hW with hφ
  obtain ⟨hnext_ext, hnext_eq⟩ :=
    next_ext X P Y P' hP hE hW hW' ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩ u.2
  have hφu : (φ u).1 = extSlot X P Y P' hP hE ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩ := rfl
  by_cases hE1 : ExtPiece X P Y (next hW u.1)
  · -- one exterior step on both sides
    have h1 : (firstReturn (nextPerm hW) (ExtPiece X P Y) u).1 = next hW u.1 :=
      firstReturn_apply_of_mem _ _ u hE1
    have h2 : next hW' (φ u).1 = (φ ⟨next hW u.1, hE1⟩).1 := by
      apply Subtype.ext
      rw [hφu, hnext_eq]; rfl
    have hE1' : ExtPiece X P' Y (next hW' (φ u).1) := by rw [h2]; exact (φ _).2
    apply Subtype.ext
    rw [firstReturn_apply_of_mem _ _ (φ u) hE1', nextPerm_apply, h2]
    exact congrArg (fun x => (φ x).1) (Subtype.ext h1.symm)
  · -- a block passage
    obtain ⟨m, c, hmc, hc, hint, m', b', hb', hm', hint'⟩ := hpass.pass (next hW u.1) hnext_ext hE1
    have hW1 : (firstReturn (nextPerm hW) (ExtPiece X P Y) u).1 = c := by
      rw [firstReturn_eq_of_path (nextPerm hW) (ExtPiece X P Y) u (m := m + 1) (Nat.succ_pos _) ?_ ?_]
      · rw [nextPerm_pow_apply, Function.iterate_succ_apply, hmc]
      · show ExtCol X P (colOf _)
        rw [nextPerm_pow_apply, Function.iterate_succ_apply, hmc]; exact hc
      · intro i hi him
        show ¬ ExtCol X P (colOf _)
        rw [nextPerm_pow_apply]
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [Function.iterate_succ_apply]
        exact hint i' (by omega)
    have hb'' : next hW' (φ u).1 = b' := by
      apply Subtype.ext
      rw [hb', hφu, hnext_eq]
    have hcφ : (φ ⟨c, hc⟩).1 = (next hW')^[m'] b' := by
      apply Subtype.ext
      rw [hm']; rfl
    have hW2 : (firstReturn (nextPerm hW') (ExtPiece X P' Y) (φ u)).1 = (φ ⟨c, hc⟩).1 := by
      rw [firstReturn_eq_of_path (nextPerm hW') (ExtPiece X P' Y) (φ u) (m := m' + 1) (Nat.succ_pos _) ?_ ?_]
      · rw [nextPerm_pow_apply, Function.iterate_succ_apply, hb'', hcφ]
      · show ExtCol X P' (colOf _)
        rw [nextPerm_pow_apply, Function.iterate_succ_apply, hb'', ← hcφ]; exact (φ ⟨c, hc⟩).2
      · intro i hi him
        show ¬ ExtCol X P' (colOf _)
        rw [nextPerm_pow_apply]
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [Function.iterate_succ_apply, hb'']
        exact hint' i' (by omega)
    apply Subtype.ext
    rw [hW2]
    exact congrArg (fun x => (φ x).1) (Subtype.ext hW1.symm)

omit hE in
/-- The entry slots of the block, concretely: cut `|X|` heading right, or cut `|X|+|P|` heading left. -/
theorem entry_iff (b : Slot (X ++ P ++ Y)) :
    IsExtSlot X P b.1 ∧ ¬ ExtCol X P (colOf b) ↔
      (∃ p, b.1 = (X.length, p) ∧ p ≠ 0 ∧ bit (X ++ P ++ Y) X.length p = true) ∨
      (∃ p, b.1 = (X.length + P.length, p) ∧ p ≠ 0 ∧ bit (X ++ P ++ Y) (X.length + P.length) p = false) := by
  have hPpos := P_length_pos P hP
  obtain ⟨⟨k, p⟩, hs⟩ := b
  rw [colOf_mk]
  by_cases hp : p = 0
  · subst hp
    simp only [IsExtSlot, ↓reduceIte]
    constructor
    · rintro ⟨h1, h2⟩; exact absurd h1 h2
    · rintro (⟨p', h, hp', -⟩ | ⟨p', h, hp', -⟩) <;> simp only [Prod.mk.injEq] at h <;> exact absurd h.2.symm hp'
  · have hk1 : 1 ≤ k := (cutSlot_pos hW (by
        rcases hs with ⟨h0, -⟩ | ⟨h1, -, -⟩
        · exact absurd h0 hp
        · exact h1) (by
        rcases hs with ⟨h0, -⟩ | ⟨-, h2, -⟩
        · exact absurd h0 hp
        · exact h2)).1
    simp only [IsExtSlot, hp, ↓reduceIte]
    cases hb : bit (X ++ P ++ Y) k p
    · simp only [Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro ⟨h1, h2⟩
        have hk : k = X.length + P.length := by unfold ExtCut at h1; unfold ExtCol at h2; omega
        subst hk
        exact Or.inr ⟨p, rfl, hp, hb⟩
      · rintro (⟨p', h, -, hb'⟩ | ⟨p', h, -, -⟩)
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact absurd (hb'.symm.trans hb) (by decide)
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, ?_⟩ <;> (try unfold ExtCut) <;> (try unfold ExtCol) <;> omega
    · simp only [↓reduceIte]
      constructor
      · rintro ⟨h1, h2⟩
        have hk : k = X.length := by unfold ExtCut at h1; unfold ExtCol at h2; omega
        subst hk
        exact Or.inl ⟨p, rfl, hp, hb⟩
      · rintro (⟨p', h, -, -⟩ | ⟨p', h, -, hb'⟩)
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, ?_⟩ <;> (try unfold ExtCut) <;> (try unfold ExtCol) <;> omega
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact absurd (hb'.symm.trans hb) (by decide)

/-- The piece shape is preserved by the exterior correspondence. -/
theorem shapeOf_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    shapeOf (φE X P Y P' hP hE hW u).1 = shapeOf u.1 := by
  obtain ⟨⟨⟨k, p⟩, hs⟩, hu⟩ := u
  have hext : IsExtSlot X P (k, p) := isExtSlot_of_extCol X P Y P' hP hE ⟨(k, p), hs⟩ hu
  have hval : (φE X P Y P' hP hE hW ⟨⟨(k, p), hs⟩, hu⟩).1.1 = (shiftIdx X P P' k, p) := rfl
  have hu' := hu
  unfold ExtPiece at hu'
  rw [colOf_mk] at hu'
  unfold shapeOf
  rw [hval]
  simp only
  by_cases hp : p = 0
  · subst hp
    simp only [↓reduceIte] at hu' ⊢
    simp only [← letterAt_ext X P Y P' hP hu', ← bit_ext X P Y P' hP hE hu'.extCut]
  · simp only [hp, ↓reduceIte] at hu' ⊢
    simp only [IsExtSlot, hp, ↓reduceIte] at hext
    rw [← bit_ext X P Y P' hP hE hext p]
    cases hb : bit (X ++ P ++ Y) k p
    · rw [hb] at hu'
      simp only [Bool.false_eq_true, ↓reduceIte] at hu' ⊢
      have hk1 : 1 ≤ k := (cutSlot_pos hW (by
        rcases hs with ⟨h0, -⟩ | ⟨h1, -, -⟩
        · exact absurd h0 hp
        · exact h1) (by
        rcases hs with ⟨h0, -⟩ | ⟨-, h2, -⟩
        · exact absurd h0 hp
        · exact h2)).1
      rw [← shiftIdx_pred X P P' hP hu' hk1, ← letterAt_ext X P Y P' hP hu']
    · rw [hb] at hu'
      simp only [↓reduceIte] at hu' ⊢
      rw [← letterAt_ext X P Y P' hP hu']

theorem letterAt_colOf_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    letterAt (X ++ P' ++ Y) (colOf (φE X P Y P' hP hE hW u).1) = letterAt (X ++ P ++ Y) (colOf u.1) := by
  rw [colOf_φE, ← letterAt_ext X P Y P' hP u.2]

theorem bit_colOf_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) (p : ℕ) :
    bit (X ++ P' ++ Y) (colOf (φE X P Y P' hP hE hW u).1) p = bit (X ++ P ++ Y) (colOf u.1) p := by
  rw [colOf_φE, ← bit_ext X P Y P' hP hE u.2.extCut]

/-- `σ` slots correspond to `σ` slots. -/
theorem isσSlot_φE_iff (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    IsσSlot (φE X P Y P' hP hE hW u).1 ↔ IsσSlot u.1 := by
  unfold IsσSlot
  rw [letterAt_colOf_φE, shapeOf_φE]

theorem isDesc_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    isDesc (φE X P Y P' hP hE hW u).1 = isDesc u.1 := by
  unfold isDesc; rw [shapeOf_φE]

theorem σsgn_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    σsgn (φE X P Y P' hP hE hW u).1 = σsgn u.1 := by
  unfold σsgn σsgnCol
  rw [letterAt_colOf_φE, bit_colOf_φE, bit_colOf_φE]

theorem φE_σtwin (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) (hu : IsσSlot u.1) :
    (φE X P Y P' hP hE hW ⟨σtwin hW u.1, extPiece_σtwin X P Y hW hu u.2⟩).1 = σtwin hW' (φE X P Y P' hP hE hW u).1 := by
  have hu' : IsσSlot (φE X P Y P' hP hE hW u).1 := (isσSlot_φE_iff X P Y P' hP hE hW u).2 hu
  apply σslot_ext hW' ((isσSlot_φE_iff X P Y P' hP hE hW _).2 (isσSlot_σtwin hW hu)) (isσSlot_σtwin hW' hu')
  · rw [colOf_φE, colOf_σtwin hW' hu', colOf_φE]
    show shiftIdx X P P' (colOf (σtwin hW u.1)) = _
    rw [colOf_σtwin hW hu]
  · rw [isDesc_φE, isDesc_σtwin hW' hu', isDesc_φE]
    show isDesc (σtwin hW u.1) = _
    rw [isDesc_σtwin hW hu]

/-- The active sets correspond. -/
theorem colActive_φE_iff (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    colActive (ExtCol X P') (φE X P Y P' hP hE hW u).1 ↔ colActive (ExtCol X P) u.1 := by
  constructor
  · rintro ⟨h1, -⟩; exact ⟨(isσSlot_φE_iff X P Y P' hP hE hW u).1 h1, u.2⟩
  · rintro ⟨h1, -⟩; exact ⟨(isσSlot_φE_iff X P Y P' hP hE hW u).2 h1, (φE X P Y P' hP hE hW u).2⟩

/-- The active slots of the two words correspond. -/
noncomputable def extActiveEquiv :
    {u : Slot (X ++ P ++ Y) // colActive (ExtCol X P) u} ≃ {u' : Slot (X ++ P' ++ Y) // colActive (ExtCol X P') u'} where
  toFun u := ⟨(φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1, (colActive_φE_iff X P Y P' hP hE hW _).2 u.2⟩
  invFun u' := ⟨((φE X P Y P' hP hE hW).symm ⟨u'.1, u'.2.2⟩).1, by
    have h := (colActive_φE_iff X P Y P' hP hE hW ((φE X P Y P' hP hE hW).symm ⟨u'.1, u'.2.2⟩)).1
    rw [Equiv.apply_symm_apply] at h
    exact h u'.2⟩
  left_inv u := Subtype.ext (by
    show ((φE X P Y P' hP hE hW).symm ⟨(φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1, _⟩).1 = u.1
    rw [show (⟨(φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1, _⟩ : {u' // ExtPiece X P' Y u'}) =
      φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩ from rfl, Equiv.symm_apply_apply])
  right_inv u' := Subtype.ext (by
    show (φE X P Y P' hP hE hW ⟨((φE X P Y P' hP hE hW).symm ⟨u'.1, u'.2.2⟩).1, _⟩).1 = u'.1
    rw [show (⟨((φE X P Y P' hP hE hW).symm ⟨u'.1, u'.2.2⟩).1, _⟩ : {u // ExtPiece X P Y u}) =
      (φE X P Y P' hP hE hW).symm ⟨u'.1, u'.2.2⟩ from rfl, Equiv.apply_symm_apply])

theorem extActiveEquiv_val (u : {u : Slot (X ++ P ++ Y) // colActive (ExtCol X P) u}) :
    (extActiveEquiv X P Y P' hP hE hW u).1 = (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1 := rfl

/-- THE EXTERIOR RECORD ISOMORPHISM: two words agreeing outside a block, with corresponding block passages
and every component meeting the exterior, have isomorphic slot records on their exterior `σ` slots. -/
noncomputable def extRecordIso (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u')) :
    RecordIso (slotRecord hW (colActive (ExtCol X P)) (colActive_activeSet hW _))
      (slotRecord hW' (colActive (ExtCol X P')) (colActive_activeSet hW' _)) :=
  let φ := φE X P Y P' hP hE hW
  let conj := conj_of_passage X P Y P' hP hE hW hW' hpass
  let hexitP : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y (((nextPerm hW) ^ n) u) := fun u => by
    obtain ⟨n, hn⟩ := hexit u; exact ⟨n, by rw [nextPerm_pow_apply]; exact hn⟩
  let hexitP' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y (((nextPerm hW') ^ n) u') := fun u => by
    obtain ⟨n, hn⟩ := hexit' u; exact ⟨n, by rw [nextPerm_pow_apply]; exact hn⟩
  let oe : Orbit hW ≃ Orbit hW' :=
    cycleEquiv (nextPerm hW) (nextPerm hW') (ExtPiece X P Y) (ExtPiece X P' Y) φ conj hexitP hexitP'
  { e := (Fintype.equivFin (Orbit hW)).symm.trans (oe.trans (Fintype.equivFin (Orbit hW')))
    Φ := extActiveEquiv X P Y P' hP hE hW
    comp_eq := fun u => by
      show slotComp hW' (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1 =
        ((Fintype.equivFin (Orbit hW)).symm.trans (oe.trans (Fintype.equivFin (Orbit hW')))) (slotComp hW u.1)
      rw [slotComp_eq_equivFin, slotComp_eq_equivFin]
      simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
      congr 1
      show orbitOf hW' _ = cycleEquiv (nextPerm hW) (nextPerm hW') (ExtPiece X P Y) (ExtPiece X P' Y) φ conj
        hexitP hexitP' (orbitOf hW u.1)
      exact (cycleEquiv_mk (nextPerm hW) (nextPerm hW') (ExtPiece X P Y) (ExtPiece X P' Y) φ conj hexitP hexitP'
        ⟨u.1, u.2.2⟩).symm
    succ_eq := fun u => by
      apply Subtype.ext
      show (φE X P Y P' hP hE hW ⟨(firstReturn (nextPerm hW) (colActive (ExtCol X P)) u).1, _⟩).1 =
        (firstReturn (nextPerm hW') (colActive (ExtCol X P')) ⟨(φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1, _⟩).1
      exact (firstReturn_conj_of_factor (nextPerm hW) (nextPerm hW') (ExtPiece X P Y) (ExtPiece X P' Y) φ conj
        (colActive (ExtCol X P)) (colActive (ExtCol X P')) (fun _ h => h.2) (fun _ h => h.2)
        (colActive_φE_iff X P Y P' hP hE hW) u).symm
    pair_eq := fun u => by
      apply Subtype.ext
      show (φE X P Y P' hP hE hW ⟨σtwin hW u.1, _⟩).1 = σtwin hW' (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1
      exact φE_σtwin X P Y P' hP hE hW hW' ⟨u.1, u.2.2⟩ u.2.1
    bit_eq := fun u => by
      show isDesc (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1 = isDesc u.1
      exact isDesc_φE X P Y P' hP hE hW _
    sgn_eq := fun u => by
      show σsgn (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1 = σsgn u.1
      exact σsgn_φE X P Y P' hP hE hW _ }

end Exterior



/-! #### H. Consequences: realizations, full slot bijections, the composed isomorphisms -/

section Consequences

/-- `realizeRecordIso` (PLAN_FINAL §5 "U2"): the named record of `realize W` is the slot record of all `σ`
slots of `W` (nonempty words; the empty word realizes to the standard circle). -/
noncomputable def realizeRecordIso (W : OWord) (h : W.letters ≠ []) :
    RecordIso (realize W).diagram.record (slotRecord W.closed IsσSlot (allActive W.closed)) := by
  rw [realize_eq_realizeAt W h]
  exact realizeAtRecordIso .std W.closed h

/-- Blocks without crossing letters: the exterior `σ` slots are all `σ` slots. -/
theorem colActive_extCol_iff (X P Y : Word)
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P.length → (letterAt (X ++ P ++ Y) k).isCrossing = false)
    (u : Slot (X ++ P ++ Y)) : colActive (ExtCol X P) u ↔ IsσSlot u := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    by_contra hc
    unfold ExtCol at hc
    have h1 := h.1
    rw [hnoσ (colOf u) (by omega) (by omega)] at h1
    exact Bool.false_ne_true h1

variable {W W' : Word} (hW : W.Closed) (hW' : W'.Closed) (S : Slot W → Prop) (S' : Slot W' → Prop)
  [DecidablePred S] [DecidablePred S'] (hS : ActiveSet hW S) (hS' : ActiveSet hW' S')

/-- The cycle bijection induced by a slot bijection commuting with `next`. -/
noncomputable def orbitEquivOfSlotEquiv (ψ : Slot W ≃ Slot W') (hnext : ∀ u, ψ (next hW u) = next hW' (ψ u)) :
    Orbit hW ≃ Orbit hW' :=
  Quotient.congr ψ (fun a b => (sameCycle_iff_of_conj (nextPerm hW) (nextPerm hW') hnext a b).symm)

/-- A bijection of ALL slots commuting with `next`, carrying the active set onto the active set and
preserving twins, over bits and signs, is a record isomorphism (the commutation, PLAN_FINAL §4 L-rec; the
cusp-skein switch record after `Record.switch`). -/
noncomputable def slotRecordIsoOfSlotEquiv (ψ : Slot W ≃ Slot W') (hnext : ∀ u, ψ (next hW u) = next hW' (ψ u))
    (hact : ∀ u, S' (ψ u) ↔ S u) (htwin : ∀ u, S u → ψ (σtwin hW u) = σtwin hW' (ψ u))
    (hdesc : ∀ u, S u → isDesc (ψ u) = isDesc u) (hsgn : ∀ u, S u → σsgn (ψ u) = σsgn u) :
    RecordIso (slotRecord hW S hS) (slotRecord hW' S' hS') where
  e := (Fintype.equivFin (Orbit hW)).symm.trans
    ((orbitEquivOfSlotEquiv hW hW' ψ hnext).trans (Fintype.equivFin (Orbit hW')))
  Φ := Equiv.subtypeEquiv ψ (fun u => (hact u).symm)
  comp_eq u := by
    show slotComp hW' (ψ u.1) = ((Fintype.equivFin (Orbit hW)).symm.trans
      ((orbitEquivOfSlotEquiv hW hW' ψ hnext).trans (Fintype.equivFin (Orbit hW')))) (slotComp hW u.1)
    rw [slotComp_eq_equivFin, slotComp_eq_equivFin]
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  succ_eq u := by
    apply Subtype.ext
    show ψ (firstReturn (nextPerm hW) S u).1 = (firstReturn (nextPerm hW') S' ⟨ψ u.1, (hact u.1).2 u.2⟩).1
    exact (firstReturn_conj (nextPerm hW) (nextPerm hW') S S' ψ hnext hact u).symm
  pair_eq u := Subtype.ext (htwin u.1 u.2)
  bit_eq u := hdesc u.1 u.2
  sgn_eq u := hsgn u.1 u.2

end Consequences

section Composed

variable (X P Y P' : Word) (hP : P ≠ []) (hE : SameEffect X P P')
  (hW : (X ++ P ++ Y).Closed) (hW' : (X ++ P' ++ Y).Closed)
include hP hE

/-- THE RECORD OF THE VERTEX-MOVED DIAGRAM (U6): a diagram on the re-vertexed shadow of `realize (X ++ P ++ Y)`
whose crossings are the exterior `σ` pairs, with corresponding block passages, every component meeting the
exterior, and no crossing letter in `P'`, has the named record of `realize (X ++ P' ++ Y)` (any placement). -/
noncomputable def vertexMovedRecordIso (pl : Placement) (hne : X ++ P ++ Y ≠ []) (hne' : X ++ P' ++ Y ≠ [])
    (V : (shadowOf pl hW hne).Vertices) (hgen : ((shadowOf pl hW hne).withVertices V).Generic)
    (ov : ((shadowOf pl hW hne).withVertices V).Crossing → ((shadowOf pl hW hne).withVertices V).Strand)
    (hov : ∀ x, ov x ∈ x.val) (data : SlotDiagramData pl hW hne V hgen ov hov (ExtCol X P))
    (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (pl' : Placement) :
    RecordIso (mkDiagram pl hW hne V hgen ov hov).record (realizeAt pl' hW' hne').diagram.record :=
  ((diagramRecordIso pl hW hne V hgen ov hov (ExtCol X P) data).trans
    (extRecordIso X P Y P' hP hE hW hW' hpass hexit hexit')).trans
    ((slotRecordCongr hW' _ _ IsσSlot (allActive hW') (colActive_extCol_iff X P' Y hnoσ)).trans
      (realizeAtRecordIso pl' hW' hne').symm)

/-- The same with the target `realize W'` for a closed oriented word `W'` with letters `X ++ P' ++ Y`. -/
noncomputable def vertexMovedRecordIso' (pl : Placement) (hne : X ++ P ++ Y ≠ [])
    (V : (shadowOf pl hW hne).Vertices) (hgen : ((shadowOf pl hW hne).withVertices V).Generic)
    (ov : ((shadowOf pl hW hne).withVertices V).Crossing → ((shadowOf pl hW hne).withVertices V).Strand)
    (hov : ∀ x, ov x ∈ x.val) (data : SlotDiagramData pl hW hne V hgen ov hov (ExtCol X P))
    (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (W' : OWord) (hW'eq : W'.letters = X ++ P' ++ Y) (hne' : X ++ P' ++ Y ≠ []) :
    RecordIso (mkDiagram pl hW hne V hgen ov hov).record (realize W').diagram.record := by
  obtain ⟨L, hL⟩ := W'
  simp only at hW'eq
  subst hW'eq
  rw [realize_eq_realizeAt ⟨_, hL⟩ hne']
  exact vertexMovedRecordIso X P Y P' hP hE hW hL pl hne hne' V hgen ov hov data hpass hexit hexit' hnoσ .std

/-- TWO REALIZATIONS agreeing outside a block without crossing letters on either side (the zigzag deletion
and, with `P' = []`, every deletion with an empty factor), with corresponding passages and every component
meeting the exterior, have isomorphic named records. -/
noncomputable def realizeAtRecordIsoOfExt (hne : X ++ P ++ Y ≠ []) (hne' : X ++ P' ++ Y ≠ [])
    (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P.length → (letterAt (X ++ P ++ Y) k).isCrossing = false)
    (hnoσ' : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (pl pl' : Placement) :
    RecordIso (realizeAt pl hW hne).diagram.record (realizeAt pl' hW' hne').diagram.record :=
  (((realizeAtRecordIso pl hW hne).trans
    (slotRecordCongr hW IsσSlot (allActive hW) _ (colActive_activeSet hW _)
      (fun u => (colActive_extCol_iff X P Y hnoσ u).symm))).trans
    (extRecordIso X P Y P' hP hE hW hW' hpass hexit hexit')).trans
    ((slotRecordCongr hW' _ _ IsσSlot (allActive hW') (colActive_extCol_iff X P' Y hnoσ')).trans
      (realizeAtRecordIso pl' hW' hne').symm)

/-- The same for closed oriented words `W`, `W'` with letters `X ++ P ++ Y`, `X ++ P' ++ Y`. -/
theorem realize_recordIso_of_ext (hne : X ++ P ++ Y ≠ []) (hne' : X ++ P' ++ Y ≠ [])
    (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P.length → (letterAt (X ++ P ++ Y) k).isCrossing = false)
    (hnoσ' : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (W W' : OWord) (hWeq : W.letters = X ++ P ++ Y) (hW'eq : W'.letters = X ++ P' ++ Y) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := by
  obtain ⟨L, hL⟩ := W
  obtain ⟨L', hL'⟩ := W'
  simp only at hWeq hW'eq
  subst hWeq hW'eq
  rw [realize_eq_realizeAt ⟨_, hL⟩ hne, realize_eq_realizeAt ⟨_, hL'⟩ hne']
  exact ⟨realizeAtRecordIsoOfExt X P Y P' hP hE hL hL' hne hne' hpass hexit hexit' hnoσ hnoσ' .std .std⟩

end Composed


/-! #### I. The circle deletion: one interior component on the left (`Record.addFree`) -/

section AddFree

/-- `Record.addFree` is functorial in named record isomorphisms. -/
noncomputable def addFreeCongr {ρ ρ' : Record} (ι : RecordIso ρ ρ') : RecordIso ρ.addFree ρ'.addFree where
  e := Equiv.optionCongr ι.e
  Φ := ι.Φ
  comp_eq v := congrArg some (ι.comp_eq v)
  succ_eq := ι.succ_eq
  pair_eq := ι.pair_eq
  bit_eq := ι.bit_eq
  sgn_eq := ι.sgn_eq

variable (X P Y P' : Word) (hP : P ≠ []) (hE : SameEffect X P P')
  (hW : (X ++ P ++ Y).Closed) (hW' : (X ++ P' ++ Y).Closed)
include hP hE

/-- THE EXTERIOR RECORD ISOMORPHISM WITH ONE FREE CIRCLE (ng:circle, `circle_recordIso_addFree`): as
`extRecordIso`, but exactly one component `c₀` of `W` misses the exterior (the separated circle) — the slot
record of `W` is the slot record of `W'` with one crossing-free circle added. -/
noncomputable def extRecordIsoAddFree (hpass : Passage X P Y P' hW hW')
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (c₀ : Orbit hW)
    (hc₀ : ∀ u : Slot (X ++ P ++ Y), (¬ ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u)) ↔ orbitOf hW u = c₀) :
    RecordIso (slotRecord hW (colActive (ExtCol X P)) (colActive_activeSet hW _))
      (slotRecord hW' (colActive (ExtCol X P')) (colActive_activeSet hW' _)).addFree :=
  let φ := φE X P Y P' hP hE hW
  let conj := conj_of_passage X P Y P' hP hE hW hW' hpass
  let hexitP' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y (((nextPerm hW') ^ n) u') := fun u => by
    obtain ⟨n, hn⟩ := hexit' u; exact ⟨n, by rw [nextPerm_pow_apply]; exact hn⟩
  let hc₀' : ∀ u : Slot (X ++ P ++ Y), (¬ ∃ n : ℕ, ExtPiece X P Y (((nextPerm hW) ^ n) u)) ↔
      Quotient.mk (Perm.SameCycle.setoid (nextPerm hW)) u = c₀ := fun u => by
    simp only [nextPerm_pow_apply]; exact hc₀ u
  let oe : Orbit hW ≃ Option (Orbit hW') :=
    cycleEquivOption (nextPerm hW) (nextPerm hW') (ExtPiece X P Y) (ExtPiece X P' Y) φ conj hexitP' c₀ hc₀'
  { e := (Fintype.equivFin (Orbit hW)).symm.trans (oe.trans (Equiv.optionCongr (Fintype.equivFin (Orbit hW'))))
    Φ := extActiveEquiv X P Y P' hP hE hW
    comp_eq := fun u => by
      show some (slotComp hW' (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1) =
        ((Fintype.equivFin (Orbit hW)).symm.trans (oe.trans (Equiv.optionCongr (Fintype.equivFin (Orbit hW')))))
          (slotComp hW u.1)
      rw [slotComp_eq_equivFin, slotComp_eq_equivFin]
      simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
      have h := cycleEquivOption_mk (nextPerm hW) (nextPerm hW') (ExtPiece X P Y) (ExtPiece X P' Y) φ conj
        hexitP' c₀ hc₀' ⟨u.1, u.2.2⟩
      show _ = Equiv.optionCongr (Fintype.equivFin (Orbit hW')) (oe (orbitOf hW u.1))
      rw [show oe (orbitOf hW u.1) = some (orbitOf hW' (φ ⟨u.1, u.2.2⟩).1) from h, Equiv.optionCongr_apply,
        Option.map_some]
      try rfl
    succ_eq := fun u => by
      apply Subtype.ext
      show (φE X P Y P' hP hE hW ⟨(firstReturn (nextPerm hW) (colActive (ExtCol X P)) u).1, _⟩).1 =
        (firstReturn (nextPerm hW') (colActive (ExtCol X P')) ⟨(φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1, _⟩).1
      exact (firstReturn_conj_of_factor (nextPerm hW) (nextPerm hW') (ExtPiece X P Y) (ExtPiece X P' Y) φ conj
        (colActive (ExtCol X P)) (colActive (ExtCol X P')) (fun _ h => h.2) (fun _ h => h.2)
        (colActive_φE_iff X P Y P' hP hE hW) u).symm
    pair_eq := fun u => by
      apply Subtype.ext
      show (φE X P Y P' hP hE hW ⟨σtwin hW u.1, _⟩).1 = σtwin hW' (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1
      exact φE_σtwin X P Y P' hP hE hW hW' ⟨u.1, u.2.2⟩ u.2.1
    bit_eq := fun u => by
      show isDesc (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1 = isDesc u.1
      exact isDesc_φE X P Y P' hP hE hW _
    sgn_eq := fun u => by
      show σsgn (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1 = σsgn u.1
      exact σsgn_φE X P Y P' hP hE hW _ }

/-- The circle deletion on realizations: `W = X ++ P ++ Y` with a separated crossing-free block `P` forming
one component `c₀`, `W' = X ++ P' ++ Y` (`P' = []`), corresponding passages, every component of `W'` meeting
the exterior: the named record of `realize W` is that of `realize W'` with one free circle added. -/
theorem realize_recordIso_addFree_of_ext (hne : X ++ P ++ Y ≠ []) (hne' : X ++ P' ++ Y ≠ [])
    (hpass : Passage X P Y P' hW hW')
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (c₀ : Orbit hW)
    (hc₀ : ∀ u : Slot (X ++ P ++ Y), (¬ ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u)) ↔ orbitOf hW u = c₀)
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P.length → (letterAt (X ++ P ++ Y) k).isCrossing = false)
    (hnoσ' : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (W W' : OWord) (hWeq : W.letters = X ++ P ++ Y) (hW'eq : W'.letters = X ++ P' ++ Y) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record.addFree) := by
  obtain ⟨L, hL⟩ := W
  obtain ⟨L', hL'⟩ := W'
  simp only at hWeq hW'eq
  subst hWeq hW'eq
  rw [realize_eq_realizeAt ⟨_, hL⟩ hne, realize_eq_realizeAt ⟨_, hL'⟩ hne']
  exact ⟨(((realizeAtRecordIso .std hL hne).trans
    (slotRecordCongr hL IsσSlot (allActive hL) _ (colActive_activeSet hL _)
      (fun u => (colActive_extCol_iff X P Y hnoσ u).symm))).trans
    (extRecordIsoAddFree X P Y P' hP hE hL hL' hpass hexit' c₀ hc₀)).trans
    (addFreeCongr ((slotRecordCongr hL' _ _ IsσSlot (allActive hL') (colActive_extCol_iff X P' Y hnoσ')).trans
      (realizeAtRecordIso .std hL' hne').symm))⟩

end AddFree


end U2

/-! ### L-rec (unit U3, on the record core U2) — named-record isomorphisms (rp:record-polynomial
`presentations`, lp:split-circle in record form `P_addFree`, the accepted smoothing gate
`exists_smoothing_record_visit`).  Record of a realization: visits = the two slots of each `σ` letter,
successor = the next `σ` slot along the slot cycle `next` (`toSlot_succ`, `crossingParam_eq_half`), twin = the
other slot of the column, over = the descending strand (`overStrand_crossingOf`), sign = `sign_crossingOf`;
exterior slots of two words correspond by the index shift (`shiftIdx`, `next_ext`). -/

/-- LEAF (ng:commutation, sm-3:1929-1933 "After cusp rounding this is a positive page isotopy; equivalently,
the full named records are the same"). -/
theorem comm_recordIso {W W' : OWord} (h : IsComm W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := sorry

/-- LEAF (ng:deletions, sm-3:2017-2019: after rounding the zigzag "is a simple ordinary arc, positively page
isotopic relative to its endpoints to the straightened arc" — no crossing is touched; every strand passes
through the block, the exterior visits and their cyclic orders are unchanged). -/
theorem zigzag_recordIso {W W' : OWord} (h : IsZigzagDeletion W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := sorry

/-- LEAF (ng:circle, sm-3:2054-2059 "A standard circle separated by the word procedure has no mixed crossings
... Lemma lp:split-circle permits this nesting"): the record of the word with the circle is the record of the
remainder with one free (crossing-free) component added. -/
theorem circle_recordIso_addFree {W W' : OWord} (h : IsCircleDeletion W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record.addFree) := sorry

/-- The data one principal direction of the interchange supplies for its earlier branch `A` (sm-3:2091-2099
"Exchanging over and under at that crossing makes their local ordered crossing records identical, including
the boundary attachments.  After gluing any same actual exterior, the full named records are identical.  Thus
their polynomial values are the two crossing choices at one ordinary skein site"; sm-3:2119-2126 "Only the one
compatible smoothing is used"): the crossing `x` of the `σ` letter of `A`'s factor; the named record of
`realize A'` is that of the switch of `realize A` at `x`; an oriented smoothing of `realize A` at `x` (the
accepted `exists_smoothing_record_visit` supplies one with record `(realize A).record.smooth v`) carries the
named record of `realize C`; and the sign of `x` is the writhe difference `w_A − w_C` (the exterior writhe
`w₀` is `w_C`). -/
def SkeinSite (A A' C : OWord) : Prop :=
  ∃ x : (realize A).diagram.Γ.Crossing,
    Nonempty (RecordIso (realize A').diagram.record ((realize A).diagram.switch x).record) ∧
    (∃ D₀ : Diagram, IsOrientedSmoothing (realize A).diagram x D₀ ∧
      Nonempty (RecordIso D₀.record (realize C).diagram.record)) ∧
    ((realize A).diagram.sign x : ℤ) = (realize A).writhe - (realize C).writhe

/-- LEAF (ng:cusp-skein, the site for the printed direction `A = l_{m+1} σ_m`, `A' = l_m σ_{m+1}`, smoothing
`C_top`/`C_bottom` by the (t,u) table).  The other principal direction is the same leaf applied to
`IsCuspSkeinStep A' A C` (glue `skein_ineq_backward`). -/
theorem skein_site {A A' C : OWord} (h : IsCuspSkeinStep A.letters A'.letters C.letters) : SkeinSite A A' C :=
  sorry

/-- LEAF (ng:cusp-skein "the unique compatible smoothing", FR-12): the interchange determines `C` — the two
principal words differ first at the cusp letter, which fixes `X`, `m`, `d`, `Y`; the through-strand bit is
read from `run X []`; the reverse-direction case is contradictory (`l (m+1) = l m'`, `l m = l (m'+1)`). -/
theorem skein_unique {A A' C C' : Word} (h : IsCuspSkein A A' C) (h' : IsCuspSkein A A' C') : C = C' :=
  sorry

/-! ### L-geo (units U5, U6 on the geometry core U4) — the disc-local moves through the accepted
`RIData`/`RIIData`/`RIIIData` (`P_reidemeister_I/II/III`).  The move disc is a convex polygon hugging the
active strands (spectator strands run parallel one unit away, so such a disc exists; the full-height block
rectangle is NOT admissible: `ArcCover` forbids spectators).  For the length-changing patterns the comparison
diagram is a vertex-moved copy `D` of `realize W` (same shadow structure, the active strand's interior vertices
moved inside the disc, the removed crossings gone, everything else literally equal: `MoveMatch` with the
identity), whose named record is that of `realize W'` (record core U2, "active set" variant). -/

/-- LEAF (ng:front-III, sm-3:1995-2003 "an actual ordinary Reidemeister-III configuration ... The three
over/under choices give one strict height order ... Each physical pair crosses on both sides with the same
over/under bit and transported arrows"): the two standard realizations (same length, no cusp letter, so the
spectators are literally identical horizontal pieces) form an `RIII` site in the band disc
`[x_k, x_{k+3}] × [−(m+2)−ε, −m+ε]`; the arcs are the three strands entering at positions `m, m+1, m+2`,
named by height, the visit order along each arc reversed.  Either direction of `IsTypeIII` (the data are
symmetric in the two diagrams). -/
theorem typeIII_site {W W' : OWord} (h : IsTypeIII W.letters W'.letters) :
    ∃ U : Set Plane, Nonempty (RIIIData U (realize W).diagram (realize W').diagram) := sorry

/-- LEAF (ng:front-II, sm-3:1979-1984 "the through-strand is under at both crossings [or over at both] ...
After rounding the cusp, the arcs bound an empty ordinary bigon with one common over-strand: an oriented
Reidemeister-II site"): a diagram `D` — `realize W` with the through-strand's two interior vertices in the
block lifted past the cusp arms — related to `realize W` by `RII` (the bigon disappears) and carrying the
named record of `realize W'` (no crossing left in the block; exterior visits and the block's connections of
the boundary slots agree).  All four variants of `IsTypeII` (right-cusp versions: the same strands backwards). -/
theorem typeII_move {W W' : OWord} (h : IsTypeII W.letters W'.letters) :
    ∃ D : Diagram, RII D (realize W).diagram ∧
      Nonempty (RecordIso D.record (realize W').diagram.record) := sorry

/-- LEAF (ng:front-I, sm-3:1955-1963 "After rounding its two cusps, the unique crossing bounds an empty
ordinary monogon"): a diagram `D` — `realize W` with the curl's vertices moved so that the strand runs
through the block crossing-free — related to `realize W` by `RI` (the kink) and carrying the named record of
`realize W' = realize (X ++ Y)`. -/
theorem typeI_move {W W' : OWord} (h : IsTypeI W.letters W'.letters) :
    ∃ D : Diagram, RI D (realize W).diagram ∧
      Nonempty (RecordIso D.record (realize W').diagram.record) := sorry

/-- LEAF (ng:deletions, sm-3:2027-2033 "a cusp whose own arms cross once.  Replace it by the uncrossed cusp
with the same two oriented boundary attachments.  After rounding, ordinary Reidemeister I deletes its empty
monogon"): a diagram `D` — `realize W` with the arms' interior vertices exchanged so that they no longer
cross — related to `realize W` by `RI` (a kink of sign −1) and carrying the named record of `realize W'`
(`l_i (!d)`: the bit flip is the arms' exchange of exits). -/
theorem crossedCusp_move {W W' : OWord} (h : IsCrossedCuspShortcut W.letters W'.letters) :
    ∃ D : Diagram, RI D (realize W).diagram ∧
      Nonempty (RecordIso D.record (realize W').diagram.record) := sorry

/-! ### L-PL (unit U7) — the planarity fact for an arbitrary PL union of standard circles -/

section u7_helpers

/-! ### U7 helpers: PL chains as graphs of continuous functions -/

/-- The closed segment from `x` to `y`, as the image of `[0,1]`. -/
def u7_seg (x y : Plane) : Set Plane := (fun t : ℝ => x + t • (y - x)) '' Set.Icc (0 : ℝ) 1

theorem u7_mem_seg_iff {x y p : Plane} :
    p ∈ u7_seg x y ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = x + t • (y - x) := by
  simp only [u7_seg, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩; exact ⟨t, h0, h1, rfl⟩
  · rintro ⟨t, h0, h1, rfl⟩; exact ⟨t, ⟨h0, h1⟩, rfl⟩

theorem u7_seg_symm (x y : Plane) : u7_seg x y = u7_seg y x := by
  ext p
  simp only [u7_mem_seg_iff]
  constructor
  · rintro ⟨t, h0, h1, rfl⟩
    refine ⟨1 - t, by linarith, by linarith, ?_⟩
    ext <;> simp <;> ring
  · rintro ⟨t, h0, h1, rfl⟩
    refine ⟨1 - t, by linarith, by linarith, ?_⟩
    ext <;> simp <;> ring

theorem u7_seg_isCompact (x y : Plane) : IsCompact (u7_seg x y) :=
  isCompact_Icc.image (by fun_prop)

theorem u7_left_mem_seg (x y : Plane) : x ∈ u7_seg x y :=
  u7_mem_seg_iff.2 ⟨0, le_rfl, zero_le_one, by simp⟩

theorem u7_right_mem_seg (x y : Plane) : y ∈ u7_seg x y :=
  u7_mem_seg_iff.2 ⟨1, zero_le_one, le_rfl, by simp⟩

/-- The x-range of a segment whose endpoints are ordered by `x`. -/
theorem u7_seg_fst_mem {x y p : Plane} (hxy : x.1 ≤ y.1) (hp : p ∈ u7_seg x y) :
    x.1 ≤ p.1 ∧ p.1 ≤ y.1 := by
  obtain ⟨t, h0, h1, rfl⟩ := u7_mem_seg_iff.1 hp
  simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
  constructor <;> nlinarith

/-- On a nonvertical segment the x-coordinate determines the point. -/
theorem u7_seg_eq_of_fst_eq {x y p q : Plane} (hxy : x.1 ≠ y.1) (hp : p ∈ u7_seg x y)
    (hq : q ∈ u7_seg x y) (h : p.1 = q.1) : p = q := by
  obtain ⟨t, -, -, rfl⟩ := u7_mem_seg_iff.1 hp
  obtain ⟨u, -, -, rfl⟩ := u7_mem_seg_iff.1 hq
  simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul] at h
  have hne : y.1 - x.1 ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  have : t = u := mul_right_cancel₀ hne (by linarith)
  rw [this]

/-- The polygonal chain through `v 0, …, v n`. -/
def u7_chain (v : ℕ → Plane) (n : ℕ) : Set Plane := ⋃ j ∈ Set.Iio n, u7_seg (v j) (v (j + 1))

theorem u7_mem_chain_iff {v : ℕ → Plane} {n : ℕ} {p : Plane} :
    p ∈ u7_chain v n ↔ ∃ j, j < n ∧ p ∈ u7_seg (v j) (v (j + 1)) := by
  simp only [u7_chain, Set.mem_iUnion, Set.mem_Iio, exists_prop]

theorem u7_chain_isCompact (v : ℕ → Plane) (n : ℕ) : IsCompact (u7_chain v n) :=
  (Set.finite_Iio n).isCompact_biUnion fun _ _ => u7_seg_isCompact _ _

theorem u7_chain_lt {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1)
    {a b : ℕ} (hab : a < b) (hb : b ≤ n) : (v a).1 < (v b).1 := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d + 1 := ⟨b - a - 1, by omega⟩
  induction d with
  | zero => exact hv a (by omega)
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := hv (a + d + 1) (by omega)
    rw [show a + (d + 1) + 1 = a + d + 1 + 1 by ring]
    exact h1.trans h2

theorem u7_chain_strictMono {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1) :
    StrictMonoOn (fun j => (v j).1) (Set.Iic n) := fun _ _ _ hb hab =>
  u7_chain_lt hv hab (Set.mem_Iic.1 hb)

theorem u7_chain_mono {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) : (v a).1 ≤ (v b).1 := by
  rcases hab.lt_or_eq with h | rfl
  · exact (u7_chain_lt hv h hb).le
  · exact le_rfl

theorem u7_chain_injOn {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1) :
    Set.InjOn Prod.fst (u7_chain v n) := by
  intro p hp q hq hpq
  obtain ⟨j, hj, hpj⟩ := u7_mem_chain_iff.1 hp
  obtain ⟨j', hj', hqj⟩ := u7_mem_chain_iff.1 hq
  wlog hle : j ≤ j' generalizing p q j j'
  · exact (this hq hp hpq.symm j' hj' hqj j hj hpj (by omega)).symm
  rcases hle.lt_or_eq with hlt | rfl
  · have h1 := u7_seg_fst_mem (hv j hj).le hpj
    have h2 := u7_seg_fst_mem (hv j' hj').le hqj
    have h3 : (v (j + 1)).1 ≤ (v j').1 := u7_chain_mono hv hlt hj'.le
    have e1 : p.1 = (v (j + 1)).1 := by linarith
    have e2 : q.1 = (v j').1 := by linarith
    have hp' : p = v (j + 1) := u7_seg_eq_of_fst_eq (hv j hj).ne hpj (u7_right_mem_seg _ _) e1
    have hq' : q = v j' := u7_seg_eq_of_fst_eq (hv j' hj').ne hqj (u7_left_mem_seg _ _) e2
    have hjj : j + 1 = j' := by
      by_contra hne
      have hlt' : j + 1 < j' := by omega
      have := (u7_chain_strictMono hv) (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 hj'.le) hlt'
      simp only at this
      linarith
    rw [hp', hq', hjj]
  · exact u7_seg_eq_of_fst_eq (hv j hj).ne hpj hqj hpq

theorem u7_chain_fst_subset {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1) :
    Prod.fst '' u7_chain v n ⊆ Set.Icc (v 0).1 (v n).1 := by
  rintro x ⟨p, hp, rfl⟩
  obtain ⟨j, hj, hpj⟩ := u7_mem_chain_iff.1 hp
  have h1 := u7_seg_fst_mem (hv j hj).le hpj
  have h2 := u7_chain_mono hv (Nat.zero_le j) hj.le
  have h3 := u7_chain_mono hv (Nat.succ_le_of_lt hj) le_rfl
  exact ⟨by linarith, by linarith⟩

theorem u7_chain_exists_piece {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1)
    (hn : 0 < n) {x : ℝ} (hx : x ∈ Set.Icc (v 0).1 (v n).1) :
    ∃ j, j < n ∧ (v j).1 ≤ x ∧ x ≤ (v (j + 1)).1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hxn : x ≤ (v n).1
    · rcases Nat.eq_zero_or_pos n with rfl | hn'
      · exact ⟨0, by omega, hx.1, hx.2⟩
      · obtain ⟨j, hj, h1, h2⟩ := ih (fun j hj => hv j (by omega)) hn' ⟨hx.1, hxn⟩
        exact ⟨j, by omega, h1, h2⟩
    · exact ⟨n, by omega, (not_le.1 hxn).le, hx.2⟩

theorem u7_chain_fst_image {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1)
    (hn : 0 < n) : Prod.fst '' u7_chain v n = Set.Icc (v 0).1 (v n).1 := by
  refine Set.Subset.antisymm (u7_chain_fst_subset hv) ?_
  intro x hx
  obtain ⟨j, hj, h1, h2⟩ := u7_chain_exists_piece hv hn hx
  have hd : 0 < (v (j + 1)).1 - (v j).1 := sub_pos.2 (hv j hj)
  refine ⟨v j + ((x - (v j).1) / ((v (j + 1)).1 - (v j).1)) • (v (j + 1) - v j), ?_, ?_⟩
  · exact u7_mem_chain_iff.2 ⟨j, hj, u7_mem_seg_iff.2
      ⟨_, div_nonneg (by linarith) hd.le, (div_le_one hd).2 (by linarith), rfl⟩⟩
  · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
    field_simp
    ring

/-- A compact set that is the graph of a function over `Icc a b` is the graph of a continuous
function (compact → Hausdorff bijections are homeomorphisms). -/
theorem u7_exists_graphFun {K : Set Plane} {a b : ℝ} (hab : a ≤ b) (hK : IsCompact K)
    (hinj : Set.InjOn Prod.fst K) (himg : Prod.fst '' K = Set.Icc a b) :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∀ x ∈ Set.Icc a b, (x, f x) ∈ K) ∧ (∀ p ∈ K, f p.1 = p.2) := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let φ : K → Set.Icc a b := fun p => ⟨p.1.1, himg ▸ Set.mem_image_of_mem Prod.fst p.2⟩
  have hφc : Continuous φ := Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _
  have hφinj : Function.Injective φ := by
    intro p q hpq
    exact Subtype.ext (hinj p.2 q.2 (congrArg Subtype.val hpq))
  have hφsurj : Function.Surjective φ := by
    intro x
    have hx : (x : ℝ) ∈ Prod.fst '' K := by rw [himg]; exact x.2
    obtain ⟨p, hp, hpx⟩ := hx
    exact ⟨⟨p, hp⟩, Subtype.ext hpx⟩
  let e : K ≃ Set.Icc a b := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hec : Continuous e := hφc
  let h : K ≃ₜ Set.Icc a b := hec.homeoOfEquivCompactToT2
  have h1 : ∀ p : K, ((h p : Set.Icc a b) : ℝ) = (p.1).1 := fun p => rfl
  have hkey : ∀ x ∈ Set.Icc a b, ((h.symm (Set.projIcc a b hab x)).1).1 = x := by
    intro x hx
    have := h1 (h.symm (Set.projIcc a b hab x))
    rw [h.apply_symm_apply] at this
    rw [← this]
    exact congrArg Subtype.val (Set.projIcc_of_mem hab hx)
  have hmem : ∀ x ∈ Set.Icc a b, (x, ((h.symm (Set.projIcc a b hab x)).1).2) ∈ K := by
    intro x hx
    have hp := (h.symm (Set.projIcc a b hab x)).2
    rw [show (x, ((h.symm (Set.projIcc a b hab x)).1).2) = (h.symm (Set.projIcc a b hab x)).1 from
      Prod.ext (hkey x hx).symm rfl]
    exact hp
  refine ⟨fun x => ((h.symm (Set.projIcc a b hab x)).1).2, ?_, hmem, ?_⟩
  · exact continuous_snd.comp (continuous_subtype_val.comp (h.symm.continuous.comp continuous_projIcc))
  · intro p hp
    have hx : p.1 ∈ Set.Icc a b := himg ▸ ⟨p, hp, rfl⟩
    have := hinj (hmem p.1 hx) hp rfl
    have h2 : ((p.1, ((h.symm (Set.projIcc a b hab p.1)).1).2) : Plane).2 = p.2 := congrArg Prod.snd this
    exact h2


/-! ### U7 helpers: PL-front facts -/

variable (F : PLFront)

/-- The segment of a strand `⟨i, m⟩` as `u7_seg` between its two vertices. -/
theorem u7_seg_eq (i : Fin F.Γ.c) (m : ZMod (F.Γ.comp i).k) :
    F.Γ.seg ⟨i, m⟩ = u7_seg ((F.Γ.comp i).P m) ((F.Γ.comp i).P (m + 1)) := by
  ext p
  rw [Shadow.seg_mk, u7_mem_seg_iff]
  simp only [edgeSegment, edgePoint, edge, Set.mem_ofPred_eq]

/-- Along a run of vertices none of which is a cusp, the rightward bit is constant. -/
theorem u7_xdir_run (i : Fin F.Γ.c) (a : ZMod (F.Γ.comp i).k) (n : ℕ)
    (hno : ∀ j : ℕ, 0 < j → j < n → ¬ F.IsCusp ⟨i, a + j⟩) :
    ∀ j : ℕ, j < n → F.xdir ⟨i, a + j⟩ = F.xdir ⟨i, a⟩ := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hnc := hno (j + 1) (Nat.succ_pos j) hj
    have h := F.xdir_prev_eq_of_not_isCusp hnc
    have hprev : F.prev ⟨i, a + ((j + 1 : ℕ) : ZMod (F.Γ.comp i).k)⟩ = ⟨i, a + j⟩ := by
      simp only [PLFront.prev, Nat.cast_succ]
      congr 1
      ring
    rw [hprev] at h
    rw [← h]
    exact ih (by omega)

/-- A vertex at which the rightward bit changes is a cusp. -/
theorem u7_isCusp_of_xdir_ne {s : F.Γ.Strand} (h : F.xdir (F.prev s) ≠ F.xdir s) : F.IsCusp s := by
  by_contra hc
  exact h (F.xdir_prev_eq_of_not_isCusp hc)

/-- The two arms of a cusp meet only at the cusp vertex (they are not collinear). -/
theorem u7_seg_prev_inter_cusp {s : F.Γ.Strand} (h : F.IsCusp s) {p : Plane}
    (hp : p ∈ F.Γ.seg (F.prev s)) (hq : p ∈ F.Γ.seg s) : p = F.Γ.tail s := by
  obtain ⟨i, m⟩ := s
  have hprev : F.prev ⟨i, m⟩ = ⟨i, m - 1⟩ := rfl
  rw [hprev, u7_seg_eq, sub_add_cancel] at hp
  rw [u7_seg_eq] at hq
  obtain ⟨t₁, -, -, hp'⟩ := u7_mem_seg_iff.1 hp
  obtain ⟨t₂, -, -, hq'⟩ := u7_mem_seg_iff.1 hq
  set P := (F.Γ.comp i).P with hP
  have hIn : F.eIn ⟨i, m⟩ = P m - P (m - 1) := by
    show F.Γ.dir ⟨i, m - 1⟩ = P m - P (m - 1)
    rw [Shadow.dir_mk]
    simp only [edge, hP]
    rw [sub_add_cancel]
  have hOut : F.eOut ⟨i, m⟩ = P (m + 1) - P m := rfl
  have hdet := F.cusp_det_ne_zero h
  rw [hIn, hOut] at hdet
  have hrel : (t₁ - 1) • (P m - P (m - 1)) = t₂ • (P (m + 1) - P m) := by
    have e := hp'.symm.trans hq'
    ext
    · have := congrArg Prod.fst e
      simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul] at this ⊢
      linarith
    · have := congrArg Prod.snd e
      simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul] at this ⊢
      linarith
  have hdet0 : t₂ * det (P m - P (m - 1)) (P (m + 1) - P m) = 0 := by
    have h3 : det (P m - P (m - 1)) (t₂ • (P (m + 1) - P m)) =
        t₂ * det (P m - P (m - 1)) (P (m + 1) - P m) := by
      simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [← h3, ← hrel]
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
    ring
  have ht₂ : t₂ = 0 := by
    rcases mul_eq_zero.1 hdet0 with h0 | h0
    · exact h0
    · exact absurd h0 hdet
  rw [hq', ht₂, zero_smul, add_zero]
  rfl


/-- The planarity fact on one component: with a unique left cusp `⟨i, ℓ⟩`, a unique right cusp `⟨i, r⟩`
and no crossing, the left cusp is downward iff the right cusp is not.  The two x-monotone arcs are graphs
of continuous functions over `[a, b]` whose difference never vanishes inside, so its sign at the two
ends agrees; the sign at each end is read off the arm heights (`isDownCusp_iff_armIn_above`). -/
theorem u7_down_iff_not_down (h : F.IsStandardCircles) (i : Fin F.Γ.c) (ℓ r : ZMod (F.Γ.comp i).k)
    (hL : F.IsLeftCusp ⟨i, ℓ⟩) (hR : F.IsRightCusp ⟨i, r⟩)
    (hLu : ∀ m, F.IsLeftCusp ⟨i, m⟩ → m = ℓ) (hRu : ∀ m, F.IsRightCusp ⟨i, m⟩ → m = r) :
    (F.IsDownCusp ⟨i, ℓ⟩ ↔ ¬ F.IsDownCusp ⟨i, r⟩) := by
  classical
  have hcusp : ∀ m, F.IsCusp ⟨i, m⟩ → m = ℓ ∨ m = r := fun m hm => by
    rcases (F.isCusp_iff _).1 hm with hl | hr
    · exact Or.inl (hLu m hl)
    · exact Or.inr (hRu m hr)
  have hℓr : ℓ ≠ r := by
    intro e
    subst e
    exact F.not_isLeftCusp_and_isRightCusp _ ⟨hL, hR⟩
  -- the number of rightward strands `n` and of leftward strands `m`
  set n := (r - ℓ).val with hn
  have hnk : n < (F.Γ.comp i).k := ZMod.val_lt _
  have hn0 : 0 < n := ZMod.val_pos.2 (sub_ne_zero.2 hℓr.symm)
  have hncast : (n : ZMod (F.Γ.comp i).k) = r - ℓ := ZMod.natCast_zmod_val _
  set m := (F.Γ.comp i).k - n with hm
  have hm0 : 0 < m := by omega
  have hmcast : (m : ZMod (F.Γ.comp i).k) = ℓ - r := by
    rw [hm, Nat.cast_sub hnk.le, ZMod.natCast_self, hncast]; ring
  have hcast_inj : ∀ j j' : ℕ, j < (F.Γ.comp i).k → j' < (F.Γ.comp i).k →
      (j : ZMod (F.Γ.comp i).k) = j' → j = j' := fun j j' hj hj' e => by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at e
    exact e
  -- the rightward bits along the two runs
  have hA : ∀ j : ℕ, j < n → F.xdir ⟨i, ℓ + j⟩ = true := by
    have hrun := u7_xdir_run F i ℓ n (fun j hj0 hjn hc => by
      rcases hcusp _ hc with e | e
      · have e' : (j : ZMod (F.Γ.comp i).k) = ((0 : ℕ) : ZMod (F.Γ.comp i).k) := by
          rw [Nat.cast_zero]; exact (add_eq_left).1 e
        have := hcast_inj j 0 (by omega) (by omega) e'
        omega
      · have e' : (j : ZMod (F.Γ.comp i).k) = (n : ZMod (F.Γ.comp i).k) := by
          rw [hncast]; exact eq_sub_of_add_eq' e
        have := hcast_inj j n (by omega) hnk e'
        omega)
    intro j hj
    rw [hrun j hj]
    exact (F.xdir_eq_true_iff _).2 hL.2
  have hB : ∀ j : ℕ, j < m → F.xdir ⟨i, r + j⟩ = false := by
    have hrun := u7_xdir_run F i r m (fun j hj0 hjm hc => by
      rcases hcusp _ hc with e | e
      · have e' : (j : ZMod (F.Γ.comp i).k) = (m : ZMod (F.Γ.comp i).k) := by
          rw [hmcast]; exact eq_sub_of_add_eq' e
        have := hcast_inj j m (by omega) (by omega) e'
        omega
      · have e' : (j : ZMod (F.Γ.comp i).k) = ((0 : ℕ) : ZMod (F.Γ.comp i).k) := by
          rw [Nat.cast_zero]; exact (add_eq_left).1 e
        have := hcast_inj j 0 (by omega) (by omega) e'
        omega)
    intro j hj
    rw [hrun j hj]
    exact (F.xdir_eq_false_iff _).2 hR.2
  -- the two vertex chains
  set vA : ℕ → Plane := fun j => (F.Γ.comp i).P (ℓ + j) with hvAdef
  set vB : ℕ → Plane := fun j => (F.Γ.comp i).P (r + ((m - j : ℕ) : ZMod (F.Γ.comp i).k)) with hvBdef
  have hdirA : ∀ j : ℕ, F.Γ.dir ⟨i, ℓ + j⟩ = (F.Γ.comp i).P (ℓ + j + 1) - (F.Γ.comp i).P (ℓ + j) :=
    fun j => rfl
  have hdirB : ∀ j : ℕ, F.Γ.dir ⟨i, r + j⟩ = (F.Γ.comp i).P (r + j + 1) - (F.Γ.comp i).P (r + j) :=
    fun j => rfl
  have hvA : ∀ j, j < n → (vA j).1 < (vA (j + 1)).1 := fun j hj => by
    have hx := (F.xdir_eq_true_iff ⟨i, ℓ + j⟩).1 (hA j hj)
    rw [hdirA] at hx
    simp only [hvAdef, Nat.cast_succ, ← add_assoc]
    simp only [Prod.fst_sub] at hx
    linarith
  have hvB : ∀ j, j < m → (vB j).1 < (vB (j + 1)).1 := fun j hj => by
    have e1 : m - j = (m - (j + 1)) + 1 := by omega
    have hx := (F.xdir_eq_false_iff ⟨i, r + ((m - (j + 1) : ℕ) : ZMod (F.Γ.comp i).k)⟩).1
      (hB _ (by omega))
    rw [hdirB] at hx
    simp only [hvBdef]
    rw [e1, Nat.cast_succ, ← add_assoc]
    simp only [Prod.fst_sub] at hx
    linarith
  -- the strands' segments are the chain pieces
  have hsegA : ∀ j : ℕ, F.Γ.seg ⟨i, ℓ + j⟩ = u7_seg (vA j) (vA (j + 1)) := fun j => by
    rw [u7_seg_eq]
    simp only [hvAdef, Nat.cast_succ, ← add_assoc]
  have hsegB : ∀ j : ℕ, j < m →
      F.Γ.seg ⟨i, r + ((m - (j + 1) : ℕ) : ZMod (F.Γ.comp i).k)⟩ = u7_seg (vB j) (vB (j + 1)) :=
    fun j hj => by
    rw [u7_seg_eq, u7_seg_symm]
    simp only [hvBdef]
    rw [show m - j = (m - (j + 1)) + 1 by omega, Nat.cast_succ, ← add_assoc]
  set KA := u7_chain vA n with hKA
  set KB := u7_chain vB m with hKB
  have hKA_mem : ∀ p ∈ KA, ∃ j, j < n ∧ p ∈ F.Γ.seg ⟨i, ℓ + j⟩ := fun p hp => by
    obtain ⟨j, hj, hpj⟩ := u7_mem_chain_iff.1 hp
    exact ⟨j, hj, by rw [hsegA j]; exact hpj⟩
  have hKB_mem : ∀ p ∈ KB, ∃ j, j < m ∧ p ∈ F.Γ.seg ⟨i, r + j⟩ := fun p hp => by
    obtain ⟨j, hj, hpj⟩ := u7_mem_chain_iff.1 hp
    exact ⟨m - (j + 1), by omega, by rw [hsegB j hj]; exact hpj⟩
  -- endpoints
  have hvA0 : vA 0 = (F.Γ.comp i).P ℓ := by simp [hvAdef]
  have hvAn : vA n = (F.Γ.comp i).P r := by
    simp only [hvAdef]; rw [hncast]; congr 1; ring
  have hvB0 : vB 0 = (F.Γ.comp i).P ℓ := by
    simp only [hvBdef, Nat.sub_zero]; rw [hmcast]; congr 1; ring
  have hvBm : vB m = (F.Γ.comp i).P r := by simp [hvBdef]
  set a := ((F.Γ.comp i).P ℓ).1 with ha
  set b := ((F.Γ.comp i).P r).1 with hb
  have hab : a < b := by
    have := u7_chain_lt hvA hn0 le_rfl
    rwa [hvA0, hvAn] at this
  obtain ⟨fA, hfAc, hfA1, hfA2⟩ := u7_exists_graphFun hab.le (u7_chain_isCompact vA n)
    (u7_chain_injOn hvA) (by rw [u7_chain_fst_image hvA hn0, hvA0, hvAn])
  obtain ⟨fB, hfBc, hfB1, hfB2⟩ := u7_exists_graphFun hab.le (u7_chain_isCompact vB m)
    (u7_chain_injOn hvB) (by rw [u7_chain_fst_image hvB hm0, hvB0, hvBm])
  set g : ℝ → ℝ := fun x => fB x - fA x with hg
  have hgc : Continuous g := hfBc.sub hfAc
  -- (B) the two arcs never meet strictly between the cusps: no crossing, and adjacent strands of
  -- opposite bits meet at a cusp vertex only
  have hg0 : ∀ x ∈ Set.Ioo a b, g x ≠ 0 := by
    intro x hx hgx
    have hxI : x ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hx
    have hpA := hfA1 x hxI
    have hpB := hfB1 x hxI
    have heq : fB x = fA x := sub_eq_zero.1 hgx
    rw [heq] at hpB
    obtain ⟨j, hj, hpj⟩ := hKA_mem _ hpA
    obtain ⟨j', hj', hpj'⟩ := hKB_mem _ hpB
    have hs : F.xdir ⟨i, ℓ + j⟩ = true := hA j hj
    have ht : F.xdir ⟨i, r + j'⟩ = false := hB j' hj'
    have hvertex : ∀ q : ZMod (F.Γ.comp i).k, ((x, fA x) : Plane) = (F.Γ.comp i).P q →
        F.IsCusp ⟨i, q⟩ → False := by
      intro q hpq hc
      have hx1 : x = ((F.Γ.comp i).P q).1 := congrArg Prod.fst hpq
      rcases hcusp q hc with e | e
      · rw [e] at hx1
        exact absurd hx1 (ne_of_gt hx.1)
      · rw [e] at hx1
        exact absurd hx1 (ne_of_lt hx.2)
    by_cases hadj : F.Γ.Adjacent ⟨i, ℓ + j⟩ ⟨i, r + j'⟩
    · rw [Shadow.adjacent_mk_iff] at hadj
      rcases hadj with h1 | h1 | h1
      · have e : r + (j' : ZMod (F.Γ.comp i).k) = ℓ + j - 1 := by linear_combination h1
        have hts : (⟨i, r + j'⟩ : F.Γ.Strand) = F.prev ⟨i, ℓ + j⟩ := by
          show _ = (⟨i, ℓ + j - 1⟩ : F.Γ.Strand)
          rw [e]
        have hc : F.IsCusp ⟨i, ℓ + j⟩ := u7_isCusp_of_xdir_ne F (by rw [← hts, ht, hs]; decide)
        have hp := u7_seg_prev_inter_cusp F hc (by rw [← hts]; exact hpj') hpj
        exact hvertex _ hp hc
      · have e : r + (j' : ZMod (F.Γ.comp i).k) = ℓ + j := by linear_combination h1
        rw [e, hs] at ht
        exact Bool.noConfusion ht
      · have e : ℓ + (j : ZMod (F.Γ.comp i).k) = r + j' - 1 := by
          linear_combination (-1 : ZMod (F.Γ.comp i).k) * h1
        have hst : (⟨i, ℓ + j⟩ : F.Γ.Strand) = F.prev ⟨i, r + j'⟩ := by
          show _ = (⟨i, r + j' - 1⟩ : F.Γ.Strand)
          rw [e]
        have hc : F.IsCusp ⟨i, r + j'⟩ := u7_isCusp_of_xdir_ne F (by rw [← hst, ht, hs]; decide)
        have hp := u7_seg_prev_inter_cusp F hc (by rw [← hst]; exact hpj) hpj'
        exact hvertex _ hp hc
    · have hcr : F.Γ.IsCrossing {⟨i, ℓ + j⟩, ⟨i, r + j'⟩} :=
        F.Γ.isCrossing_pair hadj ⟨_, hpj, hpj'⟩
      exact h.1.elim (⟨_, hcr⟩ : F.Γ.Crossing)
  -- (C) hence `g` has constant sign on `(a, b)` (intermediate value theorem)
  have hsign : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, 0 < g x → 0 < g y := by
    intro x hx y hy hgx
    by_contra hgy
    have hgy' : g y < 0 := lt_of_le_of_ne (not_lt.1 hgy) (hg0 y hy)
    obtain ⟨z, hz, hz0⟩ :=
      isPreconnected_Ioo.intermediate_value hy hx hgc.continuousOn ⟨hgy'.le, hgx.le⟩
    exact hg0 z hz hz0
  -- (D) the sign near the left cusp reads the arm heights there
  have hLc := hL.isCusp
  set e₁ := F.eOut ⟨i, ℓ⟩ with he₁
  set e₂ := F.armIn ⟨i, ℓ⟩ with he₂
  have he₁1 : 0 < e₁.1 := hL.2
  have he₂1 : 0 < e₂.1 := by
    have := hL.1
    simp only [he₂, PLFront.armIn, Prod.fst_neg]
    linarith
  have he₁def : e₁ = (F.Γ.comp i).P (ℓ + 1) - (F.Γ.comp i).P ℓ := rfl
  have he₂def : e₂ = (F.Γ.comp i).P (ℓ - 1) - (F.Γ.comp i).P ℓ := by
    show -(F.Γ.dir ⟨i, ℓ - 1⟩) = _
    rw [Shadow.dir_mk]
    simp only [edge]
    rw [sub_add_cancel, neg_sub]
  set δ := min e₁.1 e₂.1 / 2 with hδ
  have hmin : 0 < min e₁.1 e₂.1 := lt_min he₁1 he₂1
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ < e₁.1 := by have := min_le_left e₁.1 e₂.1; rw [hδ]; linarith
  have hδ2 : δ < e₂.1 := by have := min_le_right e₁.1 e₂.1; rw [hδ]; linarith
  have hpA : ((F.Γ.comp i).P ℓ + (δ / e₁.1) • e₁) ∈ KA := by
    refine u7_mem_chain_iff.2 ⟨0, hn0, ?_⟩
    rw [← hsegA 0, Nat.cast_zero, add_zero, u7_seg_eq]
    exact u7_mem_seg_iff.2 ⟨δ / e₁.1, div_nonneg hδ0.le he₁1.le, (div_le_one he₁1).2 hδ1.le, rfl⟩
  have hpB : ((F.Γ.comp i).P ℓ + (δ / e₂.1) • e₂) ∈ KB := by
    refine u7_mem_chain_iff.2 ⟨0, hm0, ?_⟩
    rw [← hsegB 0 hm0]
    have e : r + ((m - (0 + 1) : ℕ) : ZMod (F.Γ.comp i).k) = ℓ - 1 := by
      rw [Nat.zero_add, Nat.cast_pred hm0, hmcast]; ring
    rw [e, u7_seg_eq, sub_add_cancel, u7_seg_symm]
    exact u7_mem_seg_iff.2 ⟨δ / e₂.1, div_nonneg hδ0.le he₂1.le, (div_le_one he₂1).2 hδ2.le,
      by rw [he₂def]⟩
  have hfAδ : fA (a + δ) = ((F.Γ.comp i).P ℓ).2 + (δ / e₁.1) * e₁.2 := by
    have h1 := hfA2 _ hpA
    have hx : ((F.Γ.comp i).P ℓ + (δ / e₁.1) • e₁).1 = a + δ := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [div_mul_cancel₀ _ he₁1.ne']
    rw [hx] at h1
    rw [h1]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have hfBδ : fB (a + δ) = ((F.Γ.comp i).P ℓ).2 + (δ / e₂.1) * e₂.2 := by
    have h1 := hfB2 _ hpB
    have hx : ((F.Γ.comp i).P ℓ + (δ / e₂.1) • e₂).1 = a + δ := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [div_mul_cancel₀ _ he₂1.ne']
    rw [hx] at h1
    rw [h1]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have hgδ : g (a + δ) = δ * (PLFront.armHeight e₂ - PLFront.armHeight e₁) := by
    simp only [hg, hfAδ, hfBδ, PLFront.armHeight, abs_of_pos he₁1, abs_of_pos he₂1]
    ring
  have hL_iff : F.IsDownCusp ⟨i, ℓ⟩ ↔ 0 < g (a + δ) := by
    rw [F.isDownCusp_iff_armIn_above hLc, hgδ]
    show PLFront.armHeight e₁ < PLFront.armHeight e₂ ↔ _
    constructor
    · intro hlt
      exact mul_pos hδ0 (sub_pos.2 hlt)
    · intro hpos
      by_contra hle
      have := mul_nonneg hδ0.le (sub_nonneg.2 (not_lt.1 hle))
      linarith
  have haδ : a + δ ∈ Set.Ioo a b := by
    refine ⟨by linarith, ?_⟩
    have h1 : (vA 1).1 = a + e₁.1 := by
      simp only [hvAdef, Nat.cast_one, he₁def, Prod.fst_sub]
      rw [ha]; ring
    have h2 := u7_chain_mono hvA (show 1 ≤ n from hn0) le_rfl
    rw [hvAn] at h2
    linarith [hb]
  -- (E) the sign near the right cusp reads the arm heights there
  have hRc := hR.isCusp
  set e₃ := F.eOut ⟨i, r⟩ with he₃
  set e₄ := F.armIn ⟨i, r⟩ with he₄
  have he₃1 : e₃.1 < 0 := hR.2
  have he₄1 : e₄.1 < 0 := by
    have := hR.1
    simp only [he₄, PLFront.armIn, Prod.fst_neg]
    linarith
  have he₃def : e₃ = (F.Γ.comp i).P (r + 1) - (F.Γ.comp i).P r := rfl
  have he₄def : e₄ = (F.Γ.comp i).P (r - 1) - (F.Γ.comp i).P r := by
    show -(F.Γ.dir ⟨i, r - 1⟩) = _
    rw [Shadow.dir_mk]
    simp only [edge]
    rw [sub_add_cancel, neg_sub]
  set δ' := min (-e₃.1) (-e₄.1) / 2 with hδ'
  have hmin' : 0 < min (-e₃.1) (-e₄.1) := lt_min (by linarith) (by linarith)
  have hδ'0 : 0 < δ' := by rw [hδ']; linarith
  have hδ'3 : δ' < -e₃.1 := by have := min_le_left (-e₃.1) (-e₄.1); rw [hδ']; linarith
  have hδ'4 : δ' < -e₄.1 := by have := min_le_right (-e₃.1) (-e₄.1); rw [hδ']; linarith
  have hpB' : ((F.Γ.comp i).P r + (δ' / (-e₃.1)) • e₃) ∈ KB := by
    refine u7_mem_chain_iff.2 ⟨m - 1, by omega, ?_⟩
    rw [← hsegB (m - 1) (by omega)]
    have e : r + ((m - (m - 1 + 1) : ℕ) : ZMod (F.Γ.comp i).k) = r := by
      rw [show m - (m - 1 + 1) = 0 by omega, Nat.cast_zero, add_zero]
    rw [e, u7_seg_eq]
    exact u7_mem_seg_iff.2 ⟨δ' / (-e₃.1), div_nonneg hδ'0.le (by linarith),
      (div_le_one (by linarith)).2 hδ'3.le, rfl⟩
  have hpA' : ((F.Γ.comp i).P r + (δ' / (-e₄.1)) • e₄) ∈ KA := by
    refine u7_mem_chain_iff.2 ⟨n - 1, by omega, ?_⟩
    rw [← hsegA (n - 1)]
    have e : ℓ + ((n - 1 : ℕ) : ZMod (F.Γ.comp i).k) = r - 1 := by
      rw [Nat.cast_pred hn0, hncast]; ring
    rw [e, u7_seg_eq, sub_add_cancel, u7_seg_symm]
    exact u7_mem_seg_iff.2 ⟨δ' / (-e₄.1), div_nonneg hδ'0.le (by linarith),
      (div_le_one (by linarith)).2 hδ'4.le, by rw [he₄def]⟩
  have hfBδ' : fB (b - δ') = ((F.Γ.comp i).P r).2 + (δ' / (-e₃.1)) * e₃.2 := by
    have h1 := hfB2 _ hpB'
    have hx : ((F.Γ.comp i).P r + (δ' / (-e₃.1)) • e₃).1 = b - δ' := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [div_neg, neg_mul, div_mul_cancel₀ _ he₃1.ne, ← sub_eq_add_neg]
    rw [hx] at h1
    rw [h1]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have hfAδ' : fA (b - δ') = ((F.Γ.comp i).P r).2 + (δ' / (-e₄.1)) * e₄.2 := by
    have h1 := hfA2 _ hpA'
    have hx : ((F.Γ.comp i).P r + (δ' / (-e₄.1)) • e₄).1 = b - δ' := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [div_neg, neg_mul, div_mul_cancel₀ _ he₄1.ne, ← sub_eq_add_neg]
    rw [hx] at h1
    rw [h1]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have hgδ' : g (b - δ') = δ' * (PLFront.armHeight e₃ - PLFront.armHeight e₄) := by
    simp only [hg, hfAδ', hfBδ', PLFront.armHeight, abs_of_neg he₃1, abs_of_neg he₄1]
    ring
  have hR_iff : F.IsDownCusp ⟨i, r⟩ ↔ g (b - δ') < 0 := by
    rw [F.isDownCusp_iff_armIn_above hRc, hgδ']
    show PLFront.armHeight e₃ < PLFront.armHeight e₄ ↔ _
    constructor
    · intro hlt
      exact mul_neg_of_pos_of_neg hδ'0 (sub_neg.2 hlt)
    · intro hneg
      by_contra hle
      have := mul_nonneg hδ'0.le (sub_nonneg.2 (not_lt.1 hle))
      linarith
  have hbδ' : b - δ' ∈ Set.Ioo a b := by
    refine ⟨?_, by linarith⟩
    have h1 : (vA (n - 1)).1 = b + e₄.1 := by
      simp only [hvAdef]
      rw [Nat.cast_pred hn0, hncast, he₄def, Prod.fst_sub,
        show ℓ + (r - ℓ - 1) = r - 1 by ring, hb]
      ring
    have h2 := u7_chain_mono hvA (Nat.zero_le (n - 1)) (Nat.sub_le n 1)
    rw [hvA0] at h2
    linarith [ha]
  -- (F) conclusion: `L` down ↔ `g > 0` on `(a, b)` ↔ `R` not down
  constructor
  · intro hdL hdR
    have h1 := hL_iff.1 hdL
    have h2 := hR_iff.1 hdR
    have := hsign _ haδ _ hbδ' h1
    linarith
  · intro hndR
    have h2 : 0 < g (b - δ') :=
      lt_of_le_of_ne (not_lt.1 (fun hlt => hndR (hR_iff.2 hlt))) (hg0 _ hbδ').symm
    exact hL_iff.2 (hsign _ hbδ' _ haδ h2)


/-- Each component of a union of standard circles has exactly one downward cusp: its two cusps are the
unique left and right cusps, and `u7_down_iff_not_down` says exactly one of them is downward. -/
theorem u7_card_down_eq_one (h : F.IsStandardCircles) (i : Fin F.Γ.c) :
    Nat.card {s : F.Γ.Strand // s.1 = i ∧ F.IsDownCusp s} = 1 := by
  obtain ⟨hLc, hRc⟩ := h.2 i
  rw [Nat.card_eq_one_iff_unique] at hLc hRc
  obtain ⟨⟨hLsub⟩, ⟨⟨L, hLi, hL⟩⟩⟩ := hLc
  obtain ⟨⟨hRsub⟩, ⟨⟨R, hRi, hR⟩⟩⟩ := hRc
  have hLu : ∀ s, s.1 = i → F.IsLeftCusp s → s = L := fun s hs hsl =>
    congrArg Subtype.val (hLsub ⟨s, hs, hsl⟩ ⟨L, hLi, hL⟩)
  have hRu : ∀ s, s.1 = i → F.IsRightCusp s → s = R := fun s hs hsr =>
    congrArg Subtype.val (hRsub ⟨s, hs, hsr⟩ ⟨R, hRi, hR⟩)
  obtain ⟨iL, ℓ⟩ := L
  obtain ⟨iR, r⟩ := R
  simp only at hLi hRi
  subst hLi
  subst hRi
  have hiff := u7_down_iff_not_down F h iR ℓ r hL hR
    (fun q hq => by have := hLu ⟨iR, q⟩ rfl hq; simpa using this)
    (fun q hq => by have := hRu ⟨iR, q⟩ rfl hq; simpa using this)
  have hcusp : ∀ s : F.Γ.Strand, s.1 = iR → F.IsCusp s → s = ⟨iR, ℓ⟩ ∨ s = ⟨iR, r⟩ :=
    fun s hs hc => by
    rcases (F.isCusp_iff s).1 hc with hl | hr
    · exact Or.inl (hLu s hs hl)
    · exact Or.inr (hRu s hs hr)
  rw [Nat.card_eq_one_iff_unique]
  by_cases hdL : F.IsDownCusp ⟨iR, ℓ⟩
  · have hdR : ¬ F.IsDownCusp ⟨iR, r⟩ := hiff.1 hdL
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨⟨iR, ℓ⟩, rfl, hdL⟩⟩⟩
    have ha : a.1 = ⟨iR, ℓ⟩ := by
      rcases hcusp a.1 a.2.1 a.2.2.isCusp with e | e
      · exact e
      · exact absurd (e ▸ a.2.2) hdR
    have hb : b.1 = ⟨iR, ℓ⟩ := by
      rcases hcusp b.1 b.2.1 b.2.2.isCusp with e | e
      · exact e
      · exact absurd (e ▸ b.2.2) hdR
    exact Subtype.ext (ha.trans hb.symm)
  · have hdR : F.IsDownCusp ⟨iR, r⟩ := by
      by_contra hc
      exact hdL (hiff.2 hc)
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨⟨iR, r⟩, rfl, hdR⟩⟩⟩
    have ha : a.1 = ⟨iR, r⟩ := by
      rcases hcusp a.1 a.2.1 a.2.2.isCusp with e | e
      · exact absurd (e ▸ a.2.2) hdL
      · exact e
    have hb : b.1 = ⟨iR, r⟩ := by
      rcases hcusp b.1 b.2.1 b.2.2.isCusp with e | e
      · exact absurd (e ▸ b.2.2) hdL
      · exact e
    exact Subtype.ext (ha.trans hb.symm)

end u7_helpers

/-- LEAF (ng:circle, sm-3:2053-2054 "A simple crossing-free component with exactly one left and one right
cusp has D = 1"): on a `PLFront`, the two x-monotone PL arcs between the cusps of a component never meet, so
one lies above the other and exactly one cusp is traversed upper arm → lower arm.  (Accepted for
realizations: `FrontRealizeStandard.IsStandardCircles.downCount_eq_c`; word-layer fallback FR-11.) -/
theorem PLFront.IsStandardCircles.downCount_eq_c_general (F : PLFront) (h : F.IsStandardCircles) :
    F.downCount = F.Γ.c := by
  unfold PLFront.downCount
  rw [PLFront.card_subtype_eq_sum_comp]
  rw [Finset.sum_congr rfl fun i _ => u7_card_down_eq_one F h i]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  exact Finset.card_fin _

/-! ### L-smooth (unit U8) — the smooth clauses of row 76 -/

/-! ### U8D infrastructure -/

namespace U8D

open Filter Topology Set Metric Classical
open scoped NNReal

noncomputable section


/-! #### Part A: real-line toolbox — integer separation, `Int.fract`, stability of `cycBetween` -/

/-- `x` is at distance at least `2ε` from every integer -/
def Sep (ε x : ℝ) : Prop := ∀ m : ℤ, 2 * ε ≤ |x + m|

theorem Sep.neg {ε x : ℝ} (h : Sep ε x) : Sep ε (-x) := by
  intro m
  have := h (-m)
  rw [← abs_neg] at this
  push_cast at this ⊢
  convert this using 2; ring

theorem Sep.symm_sub {ε a b : ℝ} (h : Sep ε (a - b)) : Sep ε (b - a) := by
  have := h.neg; rwa [neg_sub] at this

theorem Sep.pos {ε x : ℝ} (h : Sep ε x) (hε : 0 < ε) : x ≠ 0 := by
  intro hx; have := h 0; simp [hx] at this; linarith

theorem fract_eq_add_int (x : ℝ) : Int.fract x = x + ((-⌊x⌋ : ℤ) : ℝ) := by
  rw [← Int.self_sub_floor]; push_cast; ring

/-- moving by less than the separation does not cross an integer -/
theorem fract_add_of_sep {ε x h : ℝ} (hs : Sep ε x) (hh : |h| < 2 * ε) :
    Int.fract (x + h) = Int.fract x + h := by
  have h1 : 2 * ε ≤ Int.fract x := by
    have := hs (-⌊x⌋)
    rwa [← fract_eq_add_int, abs_of_nonneg (Int.fract_nonneg x)] at this
  have h2 : 2 * ε ≤ 1 - Int.fract x := by
    have := hs (-⌊x⌋ - 1)
    have e : x + ((-⌊x⌋ - 1 : ℤ) : ℝ) = Int.fract x - 1 := by
      rw [fract_eq_add_int]; push_cast; ring
    rw [e, abs_of_nonpos (by linarith [Int.fract_lt_one x])] at this; linarith
  rw [abs_lt] at hh
  have e : Int.fract x + h = (x + h) + ((-⌊x⌋ : ℤ) : ℝ) := by rw [fract_eq_add_int]; ring
  calc Int.fract (x + h) = Int.fract ((x + h) + ((-⌊x⌋ : ℤ) : ℝ)) := (Int.fract_add_intCast _ _).symm
    _ = Int.fract (Int.fract x + h) := by rw [e]
    _ = Int.fract x + h := Int.fract_eq_self.2 ⟨by linarith, by linarith⟩

/-- two points within `ε` of separated points (mod 1) have distinct `Int.fract` -/
theorem fract_ne_of_sep {ε a b a' b' : ℝ} (hs : Sep ε (a - b)) (ha : |a' - a| < ε) (hb : |b' - b| < ε) :
    Int.fract a' ≠ Int.fract b' := by
  intro h
  obtain ⟨m, hm⟩ := Int.fract_eq_fract.1 h
  have := hs (-m)
  have e : a - b + ((-m : ℤ) : ℝ) = -((a' - a) - (b' - b)) := by push_cast; linarith
  rw [e, abs_neg] at this
  have h2 : |(a' - a) - (b' - b)| < 2 * ε := by
    calc |(a' - a) - (b' - b)| ≤ |a' - a| + |b' - b| := abs_sub _ _
      _ < ε + ε := add_lt_add ha hb
      _ = 2 * ε := by ring
  linarith

theorem not_cycBetween_self_mid (a b : ℝ) : ¬ cycBetween a b b := by
  unfold cycBetween
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith

theorem fract_sub_of_mem_Ico {a b : ℝ} (ha : a ∈ Ico (0 : ℝ) 1) (hb : b ∈ Ico (0 : ℝ) 1)
    (hab : a ≠ b) : Int.fract (b - a) = if a < b then b - a else b - a + 1 := by
  split_ifs with h
  · exact Int.fract_eq_self.2 ⟨by linarith, by linarith [hb.2, ha.1]⟩
  · have hba : b < a := lt_of_le_of_ne (not_lt.1 h) (Ne.symm hab)
    rw [← Int.fract_add_one]
    exact Int.fract_eq_self.2 ⟨by linarith [hb.1, ha.2], by linarith⟩

/-- the cyclic order of three distinct points of the fundamental period: from `a` in the positive
direction, `b` is met before `c` -/
theorem cycBetween_iff_fract {a b c : ℝ} (ha : a ∈ Ico (0 : ℝ) 1) (hb : b ∈ Ico (0 : ℝ) 1)
    (hc : c ∈ Ico (0 : ℝ) 1) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cycBetween a b c ↔ Int.fract (b - a) < Int.fract (c - a) := by
  rw [fract_sub_of_mem_Ico ha hb hab, fract_sub_of_mem_Ico ha hc hac]
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
    rcases lt_or_gt_of_ne hac with h3 | h3 <;>
    (first | rw [ite_eq_left_of_eq_true _ _ (eq_true h1)] | rw [ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 h1.le))]) <;>
    (first | rw [ite_eq_left_of_eq_true _ _ (eq_true h3)] | rw [ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 h3.le))]) <;>
    unfold cycBetween <;>
    constructor <;>
    first
    | (rintro (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> linarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2])
    | (intro h; first
        | exact Or.inl ⟨by linarith, by linarith⟩
        | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
        | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
        | (exfalso; linarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]))

/-- `Int.fract (Int.fract x - Int.fract y) = Int.fract (x - y)` -/
theorem fract_fract_sub_fract (x y : ℝ) : Int.fract (Int.fract x - Int.fract y) = Int.fract (x - y) := by
  have e : Int.fract x - Int.fract y = (x - y) + ((⌊y⌋ - ⌊x⌋ : ℤ) : ℝ) := by
    rw [fract_eq_add_int x, fract_eq_add_int y]; push_cast; ring
  rw [e, Int.fract_add_intCast]

theorem fract_sub_fract_eq_add_int (x y : ℝ) : ∃ m : ℤ, Int.fract x - Int.fract y = (x - y) + m :=
  ⟨⌊y⌋ - ⌊x⌋, by rw [fract_eq_add_int x, fract_eq_add_int y]; push_cast; ring⟩

/-- **Stability of the cyclic order.**  Three parameters `a b c` of the fundamental period, pairwise
separated (mod 1) by more than `2ε` when distinct, and perturbations `a' b' c'` within `ε` (equal
parameters perturbed equally): the cyclic order of the `Int.fract` of the perturbations is that of
the originals. -/
theorem cycBetween_fract_of_sep {ε a b c a' b' c' : ℝ} (ha : a ∈ Ico (0 : ℝ) 1)
    (hb : b ∈ Ico (0 : ℝ) 1) (hc : c ∈ Ico (0 : ℝ) 1)
    (hab : a ≠ b → Sep ε (a - b)) (hbc : b ≠ c → Sep ε (b - c)) (hac : a ≠ c → Sep ε (a - c))
    (hab' : a = b → a' = b') (hbc' : b = c → b' = c') (hac' : a = c → a' = c')
    (ha' : |a' - a| < ε) (hb' : |b' - b| < ε) (hc' : |c' - c| < ε) :
    cycBetween a b c ↔ cycBetween (Int.fract a') (Int.fract b') (Int.fract c') := by
  by_cases e1 : a = b
  · subst e1; rw [hab' rfl]
    exact ⟨fun h => (not_cycBetween_self_left _ _ h).elim, fun h => (not_cycBetween_self_left _ _ h).elim⟩
  by_cases e2 : b = c
  · subst e2; rw [hbc' rfl]
    exact ⟨fun h => (not_cycBetween_self_mid _ _ h).elim, fun h => (not_cycBetween_self_mid _ _ h).elim⟩
  by_cases e3 : a = c
  · subst e3; rw [hac' rfl]
    exact ⟨fun h => (not_cycBetween_self_right _ _ h).elim, fun h => (not_cycBetween_self_right _ _ h).elim⟩
  have sab := hab e1
  have sbc := hbc e2
  have sac := hac e3
  have fa : Int.fract a' ∈ Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have fb : Int.fract b' ∈ Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have fc : Int.fract c' ∈ Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  rw [cycBetween_iff_fract ha hb hc e1 e2 e3,
    cycBetween_iff_fract fa fb fc (fract_ne_of_sep sab ha' hb') (fract_ne_of_sep sbc hb' hc')
      (fract_ne_of_sep sac ha' hc'),
    fract_fract_sub_fract, fract_fract_sub_fract]
  -- the perturbed differences
  have hε : 0 < ε := lt_of_le_of_lt (abs_nonneg _) ha'
  have eb : b' - a' = (b - a) + ((b' - b) - (a' - a)) := by ring
  have ec : c' - a' = (c - a) + ((c' - c) - (a' - a)) := by ring
  have hhb : |(b' - b) - (a' - a)| < 2 * ε := by
    calc |(b' - b) - (a' - a)| ≤ |b' - b| + |a' - a| := abs_sub _ _
      _ < ε + ε := add_lt_add hb' ha'
      _ = 2 * ε := by ring
  have hhc : |(c' - c) - (a' - a)| < 2 * ε := by
    calc |(c' - c) - (a' - a)| ≤ |c' - c| + |a' - a| := abs_sub _ _
      _ < ε + ε := add_lt_add hc' ha'
      _ = 2 * ε := by ring
  rw [eb, ec, fract_add_of_sep sab.symm_sub hhb, fract_add_of_sep sac.symm_sub hhc]
  -- the two originals are separated by at least `2ε`
  obtain ⟨m, hm⟩ := fract_sub_fract_eq_add_int (b - a) (c - a)
  have hsep : 2 * ε ≤ |Int.fract (b - a) - Int.fract (c - a)| := by
    rw [hm]; have := sbc m; convert this using 2; ring
  have hdiff : |((b' - b) - (a' - a)) - ((c' - c) - (a' - a))| < 2 * ε := by
    calc |((b' - b) - (a' - a)) - ((c' - c) - (a' - a))| = |(b' - b) - (c' - c)| := by ring_nf
      _ ≤ |b' - b| + |c' - c| := abs_sub _ _
      _ < ε + ε := add_lt_add hb' hc'
      _ = 2 * ε := by ring
  rw [abs_lt] at hdiff
  constructor
  · intro h
    rw [abs_of_neg (by linarith)] at hsep
    linarith
  · intro h
    by_contra h'
    rw [abs_of_nonneg (by linarith)] at hsep
    linarith


/-- the parameters within `ε` (mod 1) of `a` -/
def near (ε a : ℝ) : Set ℝ := {u | ∃ m : ℤ, u + m ∈ Ioo (a - ε) (a + ε)}

theorem isOpen_near (ε a : ℝ) : IsOpen (near ε a) := by
  have : near ε a = ⋃ m : ℤ, Ioo (a - ε - m) (a + ε - m) := by
    ext u
    constructor
    · rintro ⟨m, h1, h2⟩
      exact mem_iUnion.2 ⟨m, by constructor <;> linarith⟩
    · intro h
      obtain ⟨m, h1, h2⟩ := mem_iUnion.1 h
      exact ⟨m, by constructor <;> linarith⟩
  rw [this]; exact isOpen_iUnion fun m => isOpen_Ioo

/-- as `ε → 0⁺`, `ε` separates a non-integer from the integers -/
theorem eventually_sep {x : ℝ} (hx : Int.fract x ≠ 0) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Sep ε x := by
  have h1 : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hx)
  have h2 : Int.fract x < 1 := Int.fract_lt_one x
  have hpos : (0 : ℝ) < min (Int.fract x) (1 - Int.fract x) / 2 := by
    apply half_pos; exact lt_min h1 (by linarith)
  refine Filter.eventually_of_mem (Ioo_mem_nhdsGT hpos) ?_
  intro ε hε m
  have hε2 : 2 * ε < min (Int.fract x) (1 - Int.fract x) := by linarith [hε.2]
  have hmin1 := min_le_left (Int.fract x) (1 - Int.fract x)
  have hmin2 := min_le_right (Int.fract x) (1 - Int.fract x)
  have e : x + m = Int.fract x + ((⌊x⌋ + m : ℤ) : ℝ) := by rw [fract_eq_add_int]; push_cast; ring
  rw [e]
  rcases le_or_gt 0 (⌊x⌋ + m) with hk | hk
  · have : (0 : ℝ) ≤ ((⌊x⌋ + m : ℤ) : ℝ) := by exact_mod_cast hk
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : ((⌊x⌋ + m : ℤ) : ℝ) ≤ -1 := by
      have : ⌊x⌋ + m ≤ -1 := by omega
      exact_mod_cast this
    rw [abs_of_neg (by linarith)]; linarith

theorem fract_sub_ne_zero {a b : ℝ} (ha : a ∈ Ico (0 : ℝ) 1) (hb : b ∈ Ico (0 : ℝ) 1) (hne : a ≠ b) :
    Int.fract (a - b) ≠ 0 := by
  intro h
  obtain ⟨-, -, z, hz⟩ := Int.fract_eq_iff.1 h
  have h1 : (z : ℝ) < 1 := by linarith [ha.2, hb.1]
  have h2 : (-1 : ℝ) < z := by linarith [ha.1, hb.2]
  have h3 : z < 1 := by exact_mod_cast h1
  have h4 : -1 < z := by exact_mod_cast h2
  have hz0 : z = 0 := by omega
  subst hz0
  simp at hz
  exact hne (by linarith)


/-! #### Part C: persistence of a nondegenerate zero, uniformly in a parameter -/

/-- **Persistence of a nondegenerate zero.**  `Φ x` has a zero `y₀` at `x = x₀` with invertible
derivative `L`; `Φ` and its derivative are jointly continuous.  Then for every small radius `ε`,
and all `x` near `x₀`, `Φ x` has exactly one zero in the open ball of radius `ε` about `y₀`.
No implicit-function theorem in the parameter is used (the parameter space is arbitrary): the
mean-value inequality makes `Φ x` a linear approximation of `L` on the ball, which is injective
there and onto a ball about `Φ x y₀` (Mathlib's `ApproximatesLinearOn`). -/
theorem persist {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [Nontrivial E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {X : Type*} [TopologicalSpace X]
    (Φ : X → E → G) (DΦ : X → E → E →L[ℝ] G)
    (hderiv : ∀ x y, HasFDerivAt (Φ x) (DΦ x y) y)
    (hΦ : Continuous (fun p : X × E => Φ p.1 p.2))
    (hDΦ : Continuous (fun p : X × E => DΦ p.1 p.2))
    (x₀ : X) (y₀ : E) (h0 : Φ x₀ y₀ = 0) (L : E ≃L[ℝ] G) (hL : DΦ x₀ y₀ = L) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ᶠ x in 𝓝 x₀, ∃! y, y ∈ ball y₀ ε ∧ Φ x y = 0 := by
  set N : ℝ≥0 := ‖(L.symm : G →L[ℝ] E)‖₊ with hNdef
  have hLs : (L.symm : G →L[ℝ] E) ≠ 0 := by
    intro h
    obtain ⟨y, hy⟩ := exists_ne (0 : E)
    apply hy
    have h1 := L.symm_apply_apply y
    rw [show L.symm (L y) = (L.symm : G →L[ℝ] E) (L y) from rfl, h] at h1
    simpa using h1.symm
  have hN : 0 < N := nnnorm_pos.2 hLs
  have hNi : 0 < N⁻¹ := inv_pos.2 hN
  set c : ℝ≥0 := N⁻¹ / 2 with hcdef
  have hc : c < N⁻¹ := by
    rw [hcdef]; exact NNReal.half_lt_self hNi.ne'
  have hcpos : (0 : ℝ) < (N⁻¹ : ℝ≥0) - c := by
    rw [sub_pos]; exact_mod_cast hc
  -- the derivative is within `c` of `L` on a product neighbourhood
  have h1 : ∀ᶠ p : X × E in 𝓝 (x₀, y₀), ‖DΦ p.1 p.2 - (L : E →L[ℝ] G)‖ < c := by
    have hcont : Continuous (fun p : X × E => ‖DΦ p.1 p.2 - (L : E →L[ℝ] G)‖) :=
      (hDΦ.sub continuous_const).norm
    have := hcont.continuousAt (x := (x₀, y₀))
    simp only [ContinuousAt, hL, sub_self, norm_zero] at this
    exact this.eventually_lt_const (by exact_mod_cast (half_pos hNi : 0 < N⁻¹ / 2))
  rw [nhds_prod_eq, Filter.eventually_prod_iff] at h1
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := h1
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp hpb
  refine ⟨ε₀ / 2, half_pos hε₀, fun ε hε hεε₀ => ?_⟩
  have hbound : ∀ x, pa x → ∀ y ∈ closedBall y₀ ε, ‖DΦ x y - (L : E →L[ℝ] G)‖ ≤ c := by
    intro x hx y hy
    have hy' : dist y y₀ < ε₀ := by
      rw [mem_closedBall] at hy; linarith
    exact (hab hx (hball hy')).le
  have happrox : ∀ x, pa x → ∀ r, 0 < r → r ≤ ε →
      ApproximatesLinearOn (Φ x) (L : E →L[ℝ] G) (closedBall y₀ r) c := by
    intro x hx r hr hrε y hy z hz
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun w _ => (hderiv x w).hasFDerivWithinAt)
      (fun w hw => hbound x hx w (closedBall_subset_closedBall hrε hw))
      (convex_closedBall y₀ r) hz hy
  -- existence: `Φ x y₀` is small for `x` near `x₀`
  have h2 : ∀ᶠ x in 𝓝 x₀, ‖Φ x y₀‖ < ((N⁻¹ : ℝ≥0) - c) * (ε / 2) := by
    have hcont : Continuous (fun x : X => ‖Φ x y₀‖) :=
      (hΦ.comp (continuous_id.prodMk continuous_const)).norm
    have := hcont.continuousAt (x := x₀)
    simp only [ContinuousAt, h0, norm_zero] at this
    exact this.eventually_lt_const (by positivity)
  filter_upwards [hpa, h2] with x hx hx2
  have hinj : InjOn (Φ x) (closedBall y₀ ε) :=
    (happrox x hx ε hε le_rfl).injOn (Or.inr hc)
  have hsurj := (happrox x hx (ε / 2) (half_pos hε) (half_le_self hε.le)).surjOn_closedBall_of_nonlinearRightInverse
    L.toNonlinearRightInverse (half_pos hε).le subset_rfl
  have hmem : (0 : G) ∈ closedBall (Φ x y₀) (((L.toNonlinearRightInverse.nnnorm : ℝ)⁻¹ - c) * (ε / 2)) := by
    rw [mem_closedBall, dist_zero_left]
    exact hx2.le
  obtain ⟨y, hy, hΦy⟩ := hsurj hmem
  refine ⟨y, ⟨?_, hΦy⟩, ?_⟩
  · rw [mem_ball]; rw [mem_closedBall] at hy; linarith
  · rintro z ⟨hz, hΦz⟩
    exact hinj (ball_subset_closedBall hz) (ball_subset_closedBall (by rw [mem_ball]; rw [mem_closedBall] at hy; linarith)) (hΦz.trans hΦy.symm)

/-! #### Part B: the jointly smooth family and its `u`-derivatives -/

/-- the parameter interval of a deformation, as a (preconnected) space -/
abbrev I : Type := Set.Icc (0 : ℝ) 1

instance : PreconnectedSpace I := Subtype.preconnectedSpace isPreconnected_Icc

/-- the region of joint smoothness -/
def dom : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.univ

theorem uniqueDiffOn_dom : UniqueDiffOn ℝ dom := UniqueDiffOn.prod (uniqueDiffOn_Icc zero_lt_one) uniqueDiffOn_univ

theorem mem_dom {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ) : (t, u) ∈ dom := ⟨ht, trivial⟩

variable {F F' : SmoothFront} (d : F.NonsingularDeformation F')

/-- the `i`-th component of `path t`, indexed by `Fin F.c` -/
def comp (t : ℝ) (i : Fin F.c) : SmoothLoop := (d.path t).comp (Fin.cast (d.c_eq t).symm i)

/-- the family, as a function of `(t, u)` -/
def Γ (i : Fin F.c) : ℝ × ℝ → Plane := fun p => (comp d p.1 i).γ p.2

theorem contDiffOn_Γ (i : Fin F.c) : ContDiffOn ℝ ∞ (Γ d i) dom := d.smooth i

/-- the `k`-th partial derivative in `u`, taken within `dom` -/
def pd (i : Fin F.c) : ℕ → ℝ × ℝ → Plane
  | 0 => Γ d i
  | k + 1 => fun p => fderivWithin ℝ (pd i k) dom p ((0 : ℝ), (1 : ℝ))

theorem contDiffOn_pd (i : Fin F.c) (k : ℕ) : ContDiffOn ℝ ∞ (pd d i k) dom := by
  induction k with
  | zero => exact contDiffOn_Γ d i
  | succ k ih =>
    show ContDiffOn ℝ ∞ (fun p => fderivWithin ℝ (pd d i k) dom p ((0 : ℝ), (1 : ℝ))) dom
    exact (((contDiffOn_infty_iff_fderivWithin uniqueDiffOn_dom).1 ih).2).clm_apply contDiffOn_const

theorem continuousOn_pd (i : Fin F.c) (k : ℕ) : ContinuousOn (pd d i k) dom :=
  (contDiffOn_pd d i k).continuousOn

/-- on the smooth region the partial derivatives are the iterated derivatives of the components -/
theorem pd_eq (i : Fin F.c) (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ) :
    pd d i k (t, u) = iteratedDeriv k (comp d t i).γ u := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv k (comp d t i).γ = fun u => pd d i k (t, u) :=
      funext fun u => (ih u).symm
    rw [hfun]
    show fderivWithin ℝ (pd d i k) dom (t, u) ((0 : ℝ), (1 : ℝ)) = deriv (fun u => pd d i k (t, u)) u
    have hd : HasFDerivWithinAt (pd d i k) (fderivWithin ℝ (pd d i k) dom (t, u)) dom (t, u) :=
      ((contDiffOn_pd d i k).differentiableOn (by decide) (t, u) (mem_dom ht u)).hasFDerivWithinAt
    have hl : HasDerivAt (fun u : ℝ => ((t, u) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) u :=
      (hasDerivAt_const u t).prodMk (hasDerivAt_id u)
    have := hd.comp_hasDerivWithinAt u (hl.hasDerivWithinAt (s := Set.univ)) (fun u _ => mem_dom ht u)
    rw [hasDerivWithinAt_univ] at this
    exact this.deriv.symm

/-- the partial derivatives as continuous functions on `I × ℝ` -/
def pdI (i : Fin F.c) (k : ℕ) : I × ℝ → Plane := fun p => pd d i k (p.1.1, p.2)

theorem continuous_pdI (i : Fin F.c) (k : ℕ) : Continuous (pdI d i k) :=
  (continuousOn_pd d i k).comp_continuous (by fun_prop) (fun p => mem_dom p.1.2 p.2)

theorem pdI_eq (i : Fin F.c) (k : ℕ) (t : I) (u : ℝ) :
    pdI d i k (t, u) = iteratedDeriv k (comp d t.1 i).γ u := pd_eq d i k t.2 u

/-- the components of `path t` are the reindexed components -/
theorem path_comp_eq (t : ℝ) (j : Fin (d.path t).c) :
    (d.path t).comp j = comp d t (Fin.cast (d.c_eq t) j) := by
  rfl

/-! The front notions of `path t` in terms of the family. -/

theorem eval_eq (t : I) (j : Fin (d.path t.1).c) (u : ℝ) :
    (d.path t.1).eval (j, u) = pdI d (Fin.cast (d.c_eq t.1) j) 0 (t, u) := by
  rw [pdI_eq, iteratedDeriv_zero, SmoothFront.eval_def, path_comp_eq]

theorem vel_eq (t : I) (j : Fin (d.path t.1).c) (u : ℝ) :
    (d.path t.1).vel (j, u) = pdI d (Fin.cast (d.c_eq t.1) j) 1 (t, u) := by
  rw [pdI_eq, iteratedDeriv_one, SmoothFront.vel_def, path_comp_eq]

theorem acc_eq (t : I) (j : Fin (d.path t.1).c) (u : ℝ) :
    (d.path t.1).acc (j, u) = pdI d (Fin.cast (d.c_eq t.1) j) 2 (t, u) := by
  rw [pdI_eq, SmoothFront.acc_def, path_comp_eq]

theorem jerk_eq (t : I) (j : Fin (d.path t.1).c) (u : ℝ) :
    (d.path t.1).jerk (j, u) = pdI d (Fin.cast (d.c_eq t.1) j) 3 (t, u) := by
  rw [pdI_eq, SmoothFront.jerk_def, path_comp_eq]

/-- derivative of the `k`-th partial in `u` for fixed `t` -/
theorem hasDerivAt_pdI (i : Fin F.c) (k : ℕ) (t : I) (u : ℝ) :
    HasDerivAt (fun u => pdI d i k (t, u)) (pdI d i (k + 1) (t, u)) u := by
  have hf : (fun u => pdI d i k (t, u)) = iteratedDeriv k (comp d t.1 i).γ :=
    funext fun u => pdI_eq d i k t u
  rw [hf, pdI_eq, iteratedDeriv_succ]
  exact (((comp d t.1 i).contDiff_iteratedDeriv k).differentiable (by decide) u).hasDerivAt

/-- reindexing the components between two members of the family -/
def ρ (t t' : ℝ) : Fin (d.path t).c ≃ Fin (d.path t').c :=
  finCongr (by rw [d.c_eq, d.c_eq])

@[simp] theorem cast_ρ (t t' : ℝ) (j : Fin (d.path t).c) :
    Fin.cast (d.c_eq t') (ρ d t t' j) = Fin.cast (d.c_eq t) j := by
  ext; simp [ρ]

@[simp] theorem ρ_symm_apply_cast (t t' : ℝ) (j : Fin (d.path t).c) :
    (ρ d t t').symm (ρ d t t' j) = j := Equiv.symm_apply_apply _ _

theorem ρ_val (t t' : ℝ) (j : Fin (d.path t).c) : ((ρ d t t' j : Fin _) : ℕ) = j := rfl
/-! #### Part D: cusps — local hypotheses, counting, and the analysis producing them -/

/-- a cusp is a zero of the `x`-velocity alone (`no_vertical`) -/
theorem isCusp_iff_fst (A : SmoothFront) (p : Param A.c) : A.IsCusp p ↔ (A.vel p).1 = 0 := by
  constructor
  · intro h; rw [show A.vel p = 0 from h]; rfl
  · intro h; by_contra hne; exact A.no_vertical p.1 p.2 hne h

/-- **Local cusp hypotheses** between a front `A` and a nearby front `B` (circles reindexed by `ρ`):
distinct cusps of `A` on one circle are separated by more than `2ε` (mod 1); each cusp of `A` has
exactly one cusp of `B` within `ε`, of the same direction; every cusp of `B` lies within `ε` (mod 1)
of a cusp of `A`. -/
structure CuspHyp (A B : SmoothFront) (ρ : Fin A.c ≃ Fin B.c) (ε : ℝ) : Prop where
  pos : 0 < ε
  sep : ∀ p ∈ A.cuspSet, ∀ q ∈ A.cuspSet, p.1 = q.1 → p ≠ q → Sep ε (p.2 - q.2)
  exu : ∀ p ∈ A.cuspSet, ∃! u, u ∈ Ioo (p.2 - ε) (p.2 + ε) ∧ B.IsCusp (ρ p.1, u)
  down : ∀ p ∈ A.cuspSet, ∀ u ∈ Ioo (p.2 - ε) (p.2 + ε), B.IsCusp (ρ p.1, u) →
    (B.IsDownCusp (ρ p.1, u) ↔ A.IsDownCusp p)
  nonew : ∀ q ∈ B.cuspSet, ∃ p ∈ A.cuspSet, ∃ m : ℤ, q.1 = ρ p.1 ∧ q.2 + m ∈ Ioo (p.2 - ε) (p.2 + ε)

namespace CuspHyp

variable {A B : SmoothFront} {ρ : Fin A.c ≃ Fin B.c} {ε : ℝ} (h : CuspHyp A B ρ ε)
include h

/-- the cusp of `B` near the cusp `p` of `A` -/
def φ (p : Param A.c) (hp : p ∈ A.cuspSet) : ℝ := Classical.choose (h.exu p hp).exists

theorem φ_mem (p : Param A.c) (hp : p ∈ A.cuspSet) : h.φ p hp ∈ Ioo (p.2 - ε) (p.2 + ε) :=
  (Classical.choose_spec (h.exu p hp).exists).1

theorem φ_cusp (p : Param A.c) (hp : p ∈ A.cuspSet) : B.IsCusp (ρ p.1, h.φ p hp) :=
  (Classical.choose_spec (h.exu p hp).exists).2

theorem φ_unique (p : Param A.c) (hp : p ∈ A.cuspSet) {u : ℝ} (hu : u ∈ Ioo (p.2 - ε) (p.2 + ε))
    (hc : B.IsCusp (ρ p.1, u)) : u = h.φ p hp :=
  (h.exu p hp).unique ⟨hu, hc⟩ ⟨h.φ_mem p hp, h.φ_cusp p hp⟩

theorem φ_abs (p : Param A.c) (hp : p ∈ A.cuspSet) : |h.φ p hp - p.2| < ε := by
  have := h.φ_mem p hp
  rw [abs_sub_lt_iff]; constructor <;> linarith [this.1, this.2]

/-- the image cusp, in the fundamental period -/
def f (p : Param A.c) (hp : p ∈ A.cuspSet) : Param B.c := (ρ p.1, Int.fract (h.φ p hp))

theorem sameParam_f (p : Param A.c) (hp : p ∈ A.cuspSet) :
    SameParam (ρ p.1, h.φ p hp) (h.f p hp) :=
  ⟨rfl, -⌊h.φ p hp⌋, fract_eq_add_int _⟩

theorem f_mem (p : Param A.c) (hp : p ∈ A.cuspSet) : h.f p hp ∈ B.cuspSet :=
  B.mem_cuspSet.2 ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩,
    (B.isCusp_iff_of_sameParam (h.sameParam_f p hp)).2 (h.φ_cusp p hp)⟩

theorem f_injective (p : Param A.c) (hp : p ∈ A.cuspSet) (q : Param A.c) (hq : q ∈ A.cuspSet)
    (heq : h.f p hp = h.f q hq) : p = q := by
  have h1 : ρ p.1 = ρ q.1 := congrArg Prod.fst heq
  have h1' : p.1 = q.1 := ρ.injective h1
  have h2 : Int.fract (h.φ p hp) = Int.fract (h.φ q hq) := congrArg Prod.snd heq
  by_contra hne
  exact fract_ne_of_sep (h.sep p hp q hq h1' hne) (h.φ_abs p hp) (h.φ_abs q hq) h2

theorem f_surjective (q : Param B.c) (hq : q ∈ B.cuspSet) :
    ∃ p, ∃ hp : p ∈ A.cuspSet, h.f p hp = q := by
  obtain ⟨p, hp, m, h1, hm⟩ := h.nonew q hq
  refine ⟨p, hp, ?_⟩
  have hqc : B.IsCusp q := B.isCusp_of_mem_cuspSet hq
  have hsp : SameParam q (ρ p.1, q.2 + m) := ⟨h1, m, rfl⟩
  have hc : B.IsCusp (ρ p.1, q.2 + m) := (B.isCusp_iff_of_sameParam hsp).2 hqc
  have := h.φ_unique p hp hm hc
  unfold f
  rw [← this, Int.fract_add_intCast, Int.fract_eq_self.2 (B.mem_cuspSet.1 hq).1]
  exact Prod.ext h1.symm rfl

theorem f_down (p : Param A.c) (hp : p ∈ A.cuspSet) : B.IsDownCusp (h.f p hp) ↔ A.IsDownCusp p := by
  rw [B.isDownCusp_iff_of_sameParam (h.sameParam_f p hp)]
  exact h.down p hp _ (h.φ_mem p hp) (h.φ_cusp p hp)

/-- the down-cusp counts agree -/
theorem downCount_eq : A.downCount = B.downCount := by
  unfold SmoothFront.downCount
  refine Finset.card_bij (fun p hp => h.f p (Finset.mem_filter.1 hp).1) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨h.f_mem p hp.1, (h.f_down p hp.1).2 hp.2⟩
  · intro p hp q hq heq
    exact h.f_injective p _ q _ heq
  · intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨p, hp, rfl⟩ := h.f_surjective q hq.1
    exact ⟨p, Finset.mem_filter.2 ⟨hp, (h.f_down p hp).1 hq.2⟩, rfl⟩

end CuspHyp

/-! ##### The analysis for cusps -/

section CuspAnalysis

include d

/-- the `x`-velocity of the family on component `i` -/
def gx (i : Fin F.c) : I × ℝ → ℝ := fun z => (pdI d i 1 z).1
/-- its `u`-derivative, the `x`-acceleration -/
def gxx (i : Fin F.c) : I × ℝ → ℝ := fun z => (pdI d i 2 z).1
/-- the cusp discriminant `x''·det(γ'', γ''')` of the family -/
def disc (i : Fin F.c) : I × ℝ → ℝ :=
  fun z => (pdI d i 2 z).1 * det (pdI d i 2 z) (pdI d i 3 z)

theorem continuous_gx (i : Fin F.c) : Continuous (gx d i) := (continuous_pdI d i 1).fst
theorem continuous_gxx (i : Fin F.c) : Continuous (gxx d i) := (continuous_pdI d i 2).fst
theorem continuous_disc (i : Fin F.c) : Continuous (disc d i) := by
  have h2 := continuous_pdI d i 2
  have h3 := continuous_pdI d i 3
  unfold disc det
  fun_prop

theorem isCusp_iff_gx (t : I) (p : Param (d.path t.1).c) :
    (d.path t.1).IsCusp p ↔ gx d (Fin.cast (d.c_eq t.1) p.1) (t, p.2) = 0 := by
  rw [isCusp_iff_fst, vel_eq]; rfl

theorem cuspDisc_eq (t : I) (p : Param (d.path t.1).c) :
    (d.path t.1).cuspDisc p = disc d (Fin.cast (d.c_eq t.1) p.1) (t, p.2) := by
  unfold SmoothFront.cuspDisc disc; rw [acc_eq, jerk_eq]

theorem hasDerivAt_gx (i : Fin F.c) (t : I) (u : ℝ) :
    HasDerivAt (fun u => gx d i (t, u)) (gxx d i (t, u)) u :=
  (hasDerivAt_pdI d i 1 t u).fst

variable (t₀ : I)

/-- persistence of a cusp along the family (1-D case of `persist`) -/
theorem cusp_persist (i : Fin F.c) (u₀ : ℝ) (h0 : gx d i (t₀, u₀) = 0) (h2 : gxx d i (t₀, u₀) ≠ 0) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ᶠ t in 𝓝 t₀, ∃! u, u ∈ Ioo (u₀ - ε) (u₀ + ε) ∧ gx d i (t, u) = 0 := by
  have := persist (X := I) (E := ℝ) (G := ℝ) (fun t u => gx d i (t, u))
    (fun t u => (1 : ℝ →L[ℝ] ℝ).smulRight (gxx d i (t, u)))
    (fun t u => (hasDerivAt_gx d i t u).hasFDerivAt)
    (continuous_gx d i)
    ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous.comp (continuous_gxx d i))
    t₀ u₀ h0 (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ h2)) rfl
  simpa only [Real.ball_eq_Ioo] using this

theorem cusp_exu (p : Param (d.path t₀.1).c) (hp : p ∈ (d.path t₀.1).cuspSet) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ᶠ t in 𝓝 t₀, ∃! u, u ∈ Ioo (p.2 - ε) (p.2 + ε) ∧
      (d.path t.1).IsCusp (ρ d t₀.1 t.1 p.1, u) := by
  have hc : (d.path t₀.1).IsCusp p := (d.path t₀.1).isCusp_of_mem_cuspSet hp
  have h0 : gx d (Fin.cast (d.c_eq t₀.1) p.1) (t₀, p.2) = 0 := (isCusp_iff_gx d t₀ p).1 hc
  have h2 : gxx d (Fin.cast (d.c_eq t₀.1) p.1) (t₀, p.2) ≠ 0 := by
    have := (d.path t₀.1).acc_fst_ne_zero_of_isCusp hc
    rwa [acc_eq] at this
  obtain ⟨ε₀, hε₀, H⟩ := cusp_persist d t₀ _ p.2 h0 h2
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => (H ε hε hεε₀).mono fun t ht => ?_⟩
  simpa only [isCusp_iff_gx, cast_ρ] using ht

theorem cusp_down (p : Param (d.path t₀.1).c) (hp : p ∈ (d.path t₀.1).cuspSet) :
    ∃ ε₁ > 0, ∀ᶠ t in 𝓝 t₀, ∀ u ∈ Ioo (p.2 - ε₁) (p.2 + ε₁),
      (d.path t.1).IsCusp (ρ d t₀.1 t.1 p.1, u) →
      ((d.path t.1).IsDownCusp (ρ d t₀.1 t.1 p.1, u) ↔ (d.path t₀.1).IsDownCusp p) := by
  set i := Fin.cast (d.c_eq t₀.1) p.1 with hi
  have hc := (d.path t₀.1).isCusp_of_mem_cuspSet hp
  have hne : disc d i (t₀, p.2) ≠ 0 := by
    have := (d.path t₀.1).cuspDisc_ne_zero_of_isCusp hc
    rwa [cuspDisc_eq] at this
  have hev : ∀ᶠ z : I × ℝ in 𝓝 (t₀, p.2), (disc d i z < 0 ↔ disc d i (t₀, p.2) < 0) := by
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact (Filter.Tendsto.eventually_lt_const hneg (continuous_disc d i).continuousAt).mono
        fun z hz => ⟨fun _ => hneg, fun _ => hz⟩
    · exact (Filter.Tendsto.eventually_const_lt hpos (continuous_disc d i).continuousAt).mono
        fun z hz => ⟨fun h => absurd hz (not_lt.2 h.le), fun h => absurd hpos (not_lt.2 h.le)⟩
  rw [nhds_prod_eq, eventually_prod_iff] at hev
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := hev
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.eventually_nhds_iff.mp hpb
  refine ⟨ε₁, hε₁, hpa.mono fun t ht u hu hcu => ?_⟩
  have hu' : dist u p.2 < ε₁ := by
    rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith [hu.1, hu.2]
  have key := hab ht (hball hu')
  unfold SmoothFront.IsDownCusp
  rw [cuspDisc_eq, cuspDisc_eq, cast_ρ]
  exact ⟨fun h => ⟨hc, key.1 h.2⟩, fun h => ⟨hcu, key.2 h.2⟩⟩

/-- no new cusps: eventually every cusp of `path t` is within `ε` (mod 1) of a cusp of `path t₀` -/
theorem cusp_nonew (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ (t : I) in 𝓝 t₀, ∀ q : Param (d.path t.1).c, q ∈ (d.path t.1).cuspSet →
      ∃ p ∈ (d.path t₀.1).cuspSet, ∃ m : ℤ,
        q.1 = ρ d t₀.1 t.1 p.1 ∧ q.2 + m ∈ Ioo (p.2 - ε) (p.2 + ε) := by
  have key : ∀ i : Fin F.c, ∀ᶠ t in 𝓝 t₀, ∀ u ∈ Icc (0 : ℝ) 1, gx d i (t, u) = 0 →
      ∃ p ∈ (d.path t₀.1).cuspSet, Fin.cast (d.c_eq t₀.1) p.1 = i ∧ u ∈ near ε p.2 := by
    intro i
    set T := (d.path t₀.1).cuspSet.filter (fun p => Fin.cast (d.c_eq t₀.1) p.1 = i) with hT
    set K : Set ℝ := Icc 0 1 \ ⋃ p ∈ T, near ε p.2 with hK
    have hKc : IsCompact K :=
      isCompact_Icc.diff (isOpen_iUnion fun p => isOpen_iUnion fun _ => isOpen_near ε p.2)
    have hK0 : ∀ u ∈ K, gx d i (t₀, u) ≠ 0 := by
      rintro u ⟨hu1, hu2⟩ h0
      apply hu2
      set j : Fin (d.path t₀.1).c := Fin.cast (d.c_eq t₀.1).symm i with hj
      have hc : (d.path t₀.1).IsCusp (j, u) := (isCusp_iff_gx d t₀ (j, u)).2 h0
      have hmem := (d.path t₀.1).rep_mem_cuspSet hc
      refine mem_iUnion₂.2 ⟨SameParam.rep (j, u), Finset.mem_filter.2 ⟨hmem, Fin.ext rfl⟩, -⌊u⌋, ?_⟩
      show u + ((-⌊u⌋ : ℤ) : ℝ) ∈ Ioo (Int.fract u - ε) (Int.fract u + ε)
      rw [← fract_eq_add_int]
      exact ⟨by linarith, by linarith⟩
    have hev := hKc.eventually_forall_of_forall_eventually (x₀ := t₀) (P := fun t u => gx d i (t, u) ≠ 0)
      (fun u hu => (continuous_gx d i).continuousAt.eventually_ne (hK0 u hu))
    refine hev.mono fun t ht u hu h0 => ?_
    have hnK : u ∉ K := fun hK' => ht u hK' h0
    have hu' : u ∈ ⋃ p ∈ T, near ε p.2 := by
      by_contra hc; exact hnK ⟨hu, hc⟩
    obtain ⟨p, hp, hnear⟩ := mem_iUnion₂.1 hu'
    rw [Finset.mem_filter] at hp
    exact ⟨p, hp.1, hp.2, hnear⟩
  refine (Filter.eventually_all.2 key).mono fun t ht q hq => ?_
  have hqc := (d.path t.1).isCusp_of_mem_cuspSet hq
  have hq2 := ((d.path t.1).mem_cuspSet.1 hq).1
  have h0 : gx d (Fin.cast (d.c_eq t.1) q.1) (t, q.2) = 0 := (isCusp_iff_gx d t q).1 hqc
  obtain ⟨p, hp, hcast, m, hm⟩ := ht _ q.2 (Ico_subset_Icc_self hq2) h0
  refine ⟨p, hp, m, ?_, hm⟩
  apply Fin.ext
  have := congrArg Fin.val hcast
  simpa [ρ] using this.symm

/-- **the local cusp hypotheses hold near every parameter** -/
theorem eventually_cuspHyp :
    ∃ ε, ∀ᶠ t in 𝓝 t₀, CuspHyp (d.path t₀.1) (d.path t.1) (ρ d t₀.1 t.1) ε := by
  set A := d.path t₀.1 with hA
  have E1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := eventually_mem_nhdsWithin
  have E2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ A.cuspSet, ∀ q ∈ A.cuspSet, p.1 = q.1 → p ≠ q →
      Sep ε (p.2 - q.2) := by
    refine (Finset.eventually_all A.cuspSet).2 fun p hp => (Finset.eventually_all A.cuspSet).2 fun q hq => ?_
    by_cases hc : p.1 = q.1 ∧ p ≠ q
    · have hne : p.2 ≠ q.2 := fun h => hc.2 (Prod.ext hc.1 h)
      exact (eventually_sep (fract_sub_ne_zero (A.mem_cuspSet.1 hp).1 (A.mem_cuspSet.1 hq).1 hne)).mono
        fun ε h _ _ => h
    · exact Filter.Eventually.of_forall fun ε h1 h2 => absurd ⟨h1, h2⟩ hc
  have E3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ A.cuspSet, ∀ᶠ t in 𝓝 t₀, ∃! u, u ∈ Ioo (p.2 - ε) (p.2 + ε) ∧
      (d.path t.1).IsCusp (ρ d t₀.1 t.1 p.1, u) := by
    refine (Finset.eventually_all A.cuspSet).2 fun p hp => ?_
    obtain ⟨ε₀, hε₀, H⟩ := cusp_exu d t₀ p hp
    exact Filter.eventually_of_mem (Ioo_mem_nhdsGT hε₀) fun ε hε => H ε hε.1 hε.2.le
  have E4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ A.cuspSet, ∀ᶠ t in 𝓝 t₀, ∀ u ∈ Ioo (p.2 - ε) (p.2 + ε),
      (d.path t.1).IsCusp (ρ d t₀.1 t.1 p.1, u) →
      ((d.path t.1).IsDownCusp (ρ d t₀.1 t.1 p.1, u) ↔ A.IsDownCusp p) := by
    refine (Finset.eventually_all A.cuspSet).2 fun p hp => ?_
    obtain ⟨ε₁, hε₁, H⟩ := cusp_down d t₀ p hp
    exact Filter.eventually_of_mem (Ioo_mem_nhdsGT hε₁) fun ε hε => H.mono fun t ht u hu =>
      ht u (Ioo_subset_Ioo (by linarith [hε.2]) (by linarith [hε.2]) hu)
  obtain ⟨ε, hε1, hε2, hε3, hε4⟩ := (E1.and (E2.and (E3.and E4))).exists
  refine ⟨ε, ?_⟩
  have T3 := (Finset.eventually_all A.cuspSet).2 hε3
  have T4 := (Finset.eventually_all A.cuspSet).2 hε4
  have T5 := cusp_nonew d t₀ ε hε1
  filter_upwards [T3, T4, T5] with t h3 h4 h5
  exact ⟨hε1, hε2, h3, h4, h5⟩

/-- **`D` is invariant** under a nonsingular deformation. -/
theorem downCount_eq_of_deformation : F.downCount = F'.downCount := by
  have hlc : IsLocallyConstant (fun t : I => (d.path t.1).downCount) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    obtain ⟨ε, hε⟩ := eventually_cuspHyp d t₀
    exact hε.mono fun t ht => ht.downCount_eq.symm
  have h := hlc.apply_eq_of_preconnectedSpace (⟨0, by norm_num⟩ : I) (⟨1, by norm_num⟩ : I)
  have h0 : d.path (⟨0, by norm_num⟩ : I).1 = F := d.start
  have h1 : d.path (⟨1, by norm_num⟩ : I).1 = F' := d.stop
  simp only [h0, h1] at h
  exact h

end CuspAnalysis
/-! #### Part G: the record of a front, its transport, and the local double-point hypotheses -/

/-- **The named record of a front transported to another front**: a bijection of circles and of
crossing occurrences preserving circles, the cyclic order of the occurrences along each circle,
meeting (the pairing), the over rule (smaller slope) and the over-first signs. -/
structure FrontRecEquiv (A B : SmoothFront) where
  e : Fin A.c ≃ Fin B.c
  Φ : A.Occ ≃ B.Occ
  comp_eq : ∀ p : A.Occ, (Φ p).1.1 = e p.1.1
  between_iff : ∀ p q r : A.Occ, p.1.1 = q.1.1 → q.1.1 = r.1.1 →
    (cycBetween p.1.2 q.1.2 r.1.2 ↔ cycBetween (Φ p).1.2 (Φ q).1.2 (Φ r).1.2)
  meet_iff : ∀ p q : A.Occ, p ≠ q → (A.eval p = A.eval q ↔ B.eval (Φ p) = B.eval (Φ q))
  slope_iff : ∀ p q : A.Occ, p ≠ q → A.eval p = A.eval q →
    (A.slope p < A.slope q ↔ B.slope (Φ p) < B.slope (Φ q))
  sign_eq : ∀ p q : A.Occ, p ≠ q → A.eval p = A.eval q → A.crossSign p q = B.crossSign (Φ p) (Φ q)

theorem fst_mem_occSet_of_mem_crossingPairs {A : SmoothFront} {a : Param A.c × Param A.c} (ha : a ∈ A.crossingPairs) :
    a.1 ∈ A.occSet :=
  A.fst_mem_occSet_of_mem_doubleSet (A.crossingPairs_subset_doubleSet ha)

theorem snd_mem_occSet_of_mem_crossingPairs {A : SmoothFront} {a : Param A.c × Param A.c} (ha : a ∈ A.crossingPairs) :
    a.2 ∈ A.occSet :=
  A.snd_mem_occSet_of_mem_doubleSet (A.crossingPairs_subset_doubleSet ha)

namespace FrontRecEquiv

variable {A B : SmoothFront} (ι : FrontRecEquiv A B)
include ι

theorem comp_eq_iff (p q : A.Occ) : (ι.Φ p).1.1 = (ι.Φ q).1.1 ↔ p.1.1 = q.1.1 := by
  rw [ι.comp_eq, ι.comp_eq, ι.e.apply_eq_iff_eq]

/-- the inverse transport -/
def symm : FrontRecEquiv B A where
  e := ι.e.symm
  Φ := ι.Φ.symm
  comp_eq p := by
    have := ι.comp_eq (ι.Φ.symm p)
    rw [Equiv.apply_symm_apply] at this
    rw [this, Equiv.symm_apply_apply]
  between_iff p q r hpq hqr := by
    have h1 : (ι.Φ.symm p).1.1 = (ι.Φ.symm q).1.1 := by
      rw [← ι.comp_eq_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hpq
    have h2 : (ι.Φ.symm q).1.1 = (ι.Φ.symm r).1.1 := by
      rw [← ι.comp_eq_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hqr
    have := ι.between_iff _ _ _ h1 h2
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm
  meet_iff p q hne := by
    have hne' : ι.Φ.symm p ≠ ι.Φ.symm q := fun h => hne (ι.Φ.symm.injective h)
    have := ι.meet_iff _ _ hne'
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm
  slope_iff p q hne he := by
    have hne' : ι.Φ.symm p ≠ ι.Φ.symm q := fun h => hne (ι.Φ.symm.injective h)
    have hm := ι.meet_iff _ _ hne'
    simp only [Equiv.apply_symm_apply] at hm
    have := ι.slope_iff _ _ hne' (hm.2 he)
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm
  sign_eq p q hne he := by
    have hne' : ι.Φ.symm p ≠ ι.Φ.symm q := fun h => hne (ι.Φ.symm.injective h)
    have hm := ι.meet_iff _ _ hne'
    simp only [Equiv.apply_symm_apply] at hm
    have := ι.sign_eq _ _ hne' (hm.2 he)
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm

/-- **the writhe is carried by the record** -/
theorem writhe_eq : A.writhe = B.writhe := by
  unfold SmoothFront.writhe
  refine Finset.sum_bij (fun a ha => ((ι.Φ ⟨a.1, fst_mem_occSet_of_mem_crossingPairs ha⟩).1,
    (ι.Φ ⟨a.2, snd_mem_occSet_of_mem_crossingPairs ha⟩).1)) ?_ ?_ ?_ ?_
  · intro a ha
    have h := A.mem_crossingPairs'.1 ha
    have hPQ : (⟨a.1, fst_mem_occSet_of_mem_crossingPairs ha⟩ : A.Occ) ≠
        ⟨a.2, snd_mem_occSet_of_mem_crossingPairs ha⟩ :=
      fun h' => h.1.2.2.1 (congrArg Subtype.val h')
    have hev : A.eval (⟨a.1, fst_mem_occSet_of_mem_crossingPairs ha⟩ : A.Occ) =
        A.eval (⟨a.2, snd_mem_occSet_of_mem_crossingPairs ha⟩ : A.Occ) := h.1.2.2.2
    rw [B.mem_crossingPairs']
    refine ⟨⟨(ι.Φ _).2.1, (ι.Φ _).2.1, ?_, (ι.meet_iff _ _ hPQ).1 hev⟩, (ι.slope_iff _ _ hPQ hev).1 h.2⟩
    intro h'; exact hPQ (ι.Φ.injective (Subtype.ext h'))
  · intro a ha a' ha' heq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    have e1 := congrArg Subtype.val (ι.Φ.injective (Subtype.ext h1))
    have e2 := congrArg Subtype.val (ι.Φ.injective (Subtype.ext h2))
    exact Prod.ext e1 e2
  · intro b hb
    have h := B.mem_crossingPairs'.1 hb
    set P' : B.Occ := ⟨b.1, fst_mem_occSet_of_mem_crossingPairs hb⟩ with hP'
    set Q' : B.Occ := ⟨b.2, snd_mem_occSet_of_mem_crossingPairs hb⟩ with hQ'
    have hPQ' : P' ≠ Q' := fun h' => h.1.2.2.1 (congrArg Subtype.val h')
    have hev' : B.eval P' = B.eval Q' := h.1.2.2.2
    have hne : ι.Φ.symm P' ≠ ι.Φ.symm Q' := fun h' => hPQ' (ι.Φ.symm.injective h')
    have hm := ι.meet_iff _ _ hne
    simp only [Equiv.apply_symm_apply] at hm
    have hs := ι.slope_iff _ _ hne (hm.2 hev')
    simp only [Equiv.apply_symm_apply] at hs
    have hmem : ((ι.Φ.symm P').1, (ι.Φ.symm Q').1) ∈ A.crossingPairs := by
      rw [A.mem_crossingPairs']
      exact ⟨⟨(ι.Φ.symm P').2.1, (ι.Φ.symm Q').2.1, fun h' => hne (Subtype.ext h'), hm.2 hev'⟩, hs.2 h.2⟩
    refine ⟨((ι.Φ.symm P').1, (ι.Φ.symm Q').1), hmem, ?_⟩
    have e1 : (⟨((ι.Φ.symm P').1, (ι.Φ.symm Q').1).1, fst_mem_occSet_of_mem_crossingPairs hmem⟩ : A.Occ) =
        ι.Φ.symm P' := Subtype.ext rfl
    have e2 : (⟨((ι.Φ.symm P').1, (ι.Φ.symm Q').1).2, snd_mem_occSet_of_mem_crossingPairs hmem⟩ : A.Occ) =
        ι.Φ.symm Q' := Subtype.ext rfl
    simp only [e1, e2, Equiv.apply_symm_apply]
    rfl
  · intro a ha
    have h := A.mem_crossingPairs'.1 ha
    exact ι.sign_eq ⟨a.1, fst_mem_occSet_of_mem_crossingPairs ha⟩ ⟨a.2, snd_mem_occSet_of_mem_crossingPairs ha⟩
      (fun h' => h.1.2.2.1 (congrArg Subtype.val h')) h.1.2.2.2

end FrontRecEquiv

/-- **transport of a polygonal reading**: a diagram carrying the record of `A` carries the record of `B`
once the record of `B` is transported to that of `A` -/
def transportMarking {A B : SmoothFront} (κ : FrontRecEquiv B A) {S : Diagram} (m : A.Marking S) :
    B.Marking S where
  e := κ.e.trans m.e
  Φ := κ.Φ.trans m.Φ
  comp_eq p := by
    show S.compOf (m.Φ (κ.Φ p)) = m.e (κ.e p.1.1)
    rw [m.comp_eq, κ.comp_eq]
  between_iff p q r hpq hqr := by
    show cycBetween p.1.2 q.1.2 r.1.2 ↔
      cycBetween (S.visitCoord (m.Φ (κ.Φ p))) (S.visitCoord (m.Φ (κ.Φ q))) (S.visitCoord (m.Φ (κ.Φ r)))
    rw [κ.between_iff p q r hpq hqr]
    exact m.between_iff _ _ _ ((κ.comp_eq_iff p q).2 hpq) ((κ.comp_eq_iff q r).2 hqr)
  pair_eq p q hne he := m.pair_eq _ _ (fun h' => hne (κ.Φ.injective h')) ((κ.meet_iff p q hne).1 he)
  over_iff p q hne he := by
    show S.overBit (m.Φ (κ.Φ p)) = true ↔ B.slope p < B.slope q
    rw [m.over_iff _ _ (fun h' => hne (κ.Φ.injective h')) ((κ.meet_iff p q hne).1 he)]
    exact (κ.slope_iff p q hne he).symm
  sgn_eq p q hne he hs := by
    show ((S.sign (m.Φ (κ.Φ p)).1 : ℤ)) = B.crossSign p q
    rw [m.sgn_eq _ _ (fun h' => hne (κ.Φ.injective h')) ((κ.meet_iff p q hne).1 he)
      ((κ.slope_iff p q hne he).1 hs)]
    exact (κ.sign_eq p q hne he).symm

/-! ##### Partners of occurrences -/

/-- the partner of an occurrence is unique (`no_triple`) -/
theorem partner_unique (A : SmoothFront) {p q q' : Param A.c} (hp : p.2 ∈ Ico (0 : ℝ) 1)
    (hq : q.2 ∈ Ico (0 : ℝ) 1) (hq' : q'.2 ∈ Ico (0 : ℝ) 1) (hpq : p ≠ q) (hpq' : p ≠ q')
    (he : A.eval p = A.eval q) (he' : A.eval p = A.eval q') : q = q' := by
  by_contra hne
  exact A.no_triple p q q' (fun hs => hpq (SameParam.eq_of_mem_Ico hp hq hs))
    (fun hs => hne (SameParam.eq_of_mem_Ico hq hq' hs))
    (fun hs => hpq' (SameParam.eq_of_mem_Ico hp hq' hs)) he (he.symm.trans he')

/-- the partner of an occurrence: the other branch of its double point -/
def partner (A : SmoothFront) (p : A.Occ) : A.Occ :=
  Classical.choose (SmoothFront.Marking.exists_partner p)

theorem partner_ne (A : SmoothFront) (p : A.Occ) : p ≠ partner A p :=
  (Classical.choose_spec (SmoothFront.Marking.exists_partner p)).1

theorem eval_partner (A : SmoothFront) (p : A.Occ) : A.eval p = A.eval (partner A p) :=
  (Classical.choose_spec (SmoothFront.Marking.exists_partner p)).2

theorem eq_partner (A : SmoothFront) {p q : A.Occ} (hne : p ≠ q) (he : A.eval p = A.eval q) :
    q = partner A p :=
  Subtype.ext (partner_unique A p.2.1 q.2.1 (partner A p).2.1 (fun h => hne (Subtype.ext h))
    (fun h => partner_ne A p (Subtype.ext h)) he (eval_partner A p))

theorem partner_partner (A : SmoothFront) (p : A.Occ) : partner A (partner A p) = p :=
  (eq_partner A (partner_ne A p).symm (eval_partner A p).symm).symm

theorem mem_doubleSet_partner (A : SmoothFront) (p : A.Occ) : (p.1, (partner A p).1) ∈ A.doubleSet :=
  A.mem_doubleSet.2 ⟨p.2.1, (partner A p).2.1, fun h => partner_ne A p (Subtype.ext h), eval_partner A p⟩

/-! ##### The local double-point hypotheses -/

/-- the `ε`-box about a double point -/
def box (ε : ℝ) {c : ℕ} (a : Param c × Param c) : Set (ℝ × ℝ) :=
  Ioo (a.1.2 - ε) (a.1.2 + ε) ×ˢ Ioo (a.2.2 - ε) (a.2.2 + ε)

theorem mem_box {ε : ℝ} {c : ℕ} {a : Param c × Param c} {uv : ℝ × ℝ} :
    uv ∈ box ε a ↔ uv.1 ∈ Ioo (a.1.2 - ε) (a.1.2 + ε) ∧ uv.2 ∈ Ioo (a.2.2 - ε) (a.2.2 + ε) := Iff.rfl

/-- **Local double-point hypotheses** between `A` and a nearby front `B` (circles reindexed by `ρ`):
distinct occurrences of `A` on one circle are separated by more than `2ε` (mod 1); each double point
of `A` has exactly one double point of `B` in its `ε`-box, with the same over rule and sign; every
double point of `B` lies (mod 1) in the `ε`-box of a double point of `A`. -/
structure OccHyp (A B : SmoothFront) (ρ : Fin A.c ≃ Fin B.c) (ε : ℝ) : Prop where
  pos : 0 < ε
  sep : ∀ p ∈ A.occSet, ∀ q ∈ A.occSet, p.1 = q.1 → p ≠ q → Sep ε (p.2 - q.2)
  exu : ∀ a ∈ A.doubleSet, ∃! uv : ℝ × ℝ, uv ∈ box ε a ∧ B.eval (ρ a.1.1, uv.1) = B.eval (ρ a.2.1, uv.2)
  pres : ∀ a ∈ A.doubleSet, ∀ uv ∈ box ε a,
    (B.slope (ρ a.1.1, uv.1) < B.slope (ρ a.2.1, uv.2) ↔ A.slope a.1 < A.slope a.2) ∧
    B.crossSign (ρ a.1.1, uv.1) (ρ a.2.1, uv.2) = A.crossSign a.1 a.2
  nonew : ∀ b ∈ B.doubleSet, ∃ a ∈ A.doubleSet, ∃ m n : ℤ, b.1.1 = ρ a.1.1 ∧ b.2.1 = ρ a.2.1 ∧
    (b.1.2 + m, b.2.2 + n) ∈ box ε a

namespace OccHyp

variable {A B : SmoothFront} {ρ : Fin A.c ≃ Fin B.c} {ε : ℝ} (h : OccHyp A B ρ ε)
include h

/-- the double point of `B` in the box of the double point `a` of `A` -/
def sol (a : Param A.c × Param A.c) (ha : a ∈ A.doubleSet) : ℝ × ℝ :=
  Classical.choose (h.exu a ha).exists

theorem sol_mem (a : Param A.c × Param A.c) (ha : a ∈ A.doubleSet) : h.sol a ha ∈ box ε a :=
  (Classical.choose_spec (h.exu a ha).exists).1

theorem sol_eval (a : Param A.c × Param A.c) (ha : a ∈ A.doubleSet) :
    B.eval (ρ a.1.1, (h.sol a ha).1) = B.eval (ρ a.2.1, (h.sol a ha).2) :=
  (Classical.choose_spec (h.exu a ha).exists).2

theorem sol_unique (a : Param A.c × Param A.c) (ha : a ∈ A.doubleSet) {uv : ℝ × ℝ} (hmem : uv ∈ box ε a)
    (heq : B.eval (ρ a.1.1, uv.1) = B.eval (ρ a.2.1, uv.2)) : uv = h.sol a ha :=
  (h.exu a ha).unique ⟨hmem, heq⟩ ⟨h.sol_mem a ha, h.sol_eval a ha⟩

/-- the parameter of the image of the occurrence `p` -/
def φ (p : A.Occ) : ℝ := (h.sol (p.1, (partner A p).1) (mem_doubleSet_partner A p)).1

theorem φ_mem (p : A.Occ) : h.φ p ∈ Ioo (p.1.2 - ε) (p.1.2 + ε) :=
  (h.sol_mem (p.1, (partner A p).1) (mem_doubleSet_partner A p)).1

theorem φ_abs (p : A.Occ) : |h.φ p - p.1.2| < ε := by
  have := h.φ_mem p
  rw [abs_sub_lt_iff]; constructor <;> linarith [this.1, this.2]

/-- the image of the partner is the second coordinate of the solution -/
theorem φ_partner (p : A.Occ) :
    h.φ (partner A p) = (h.sol (p.1, (partner A p).1) (mem_doubleSet_partner A p)).2 := by
  unfold φ
  have hsw : h.sol ((partner A p).1, (partner A (partner A p)).1) (mem_doubleSet_partner A (partner A p)) =
      (h.sol (p.1, (partner A p).1) (mem_doubleSet_partner A p)).swap := by
    symm
    apply h.sol_unique
    · rw [mem_box]
      have hm := h.sol_mem (p.1, (partner A p).1) (mem_doubleSet_partner A p)
      rw [mem_box] at hm
      rw [partner_partner]
      exact ⟨hm.2, hm.1⟩
    · rw [partner_partner]
      exact (h.sol_eval (p.1, (partner A p).1) (mem_doubleSet_partner A p)).symm
  rw [hsw]; rfl

/-- the image occurrence, as a parameter of the fundamental period -/
def Φ₀ (p : A.Occ) : Param B.c := (ρ p.1.1, Int.fract (h.φ p))

theorem sameParam_Φ₀ (p : A.Occ) : SameParam (ρ p.1.1, h.φ p) (h.Φ₀ p) :=
  ⟨rfl, -⌊h.φ p⌋, fract_eq_add_int _⟩

theorem eval_Φ₀ (p : A.Occ) : B.eval (h.Φ₀ p) = B.eval (ρ p.1.1, h.φ p) :=
  SmoothFront.eval_of_sameParam (h.sameParam_Φ₀ p)

theorem slope_Φ₀ (p : A.Occ) : B.slope (h.Φ₀ p) = B.slope (ρ p.1.1, h.φ p) :=
  B.slope_of_sameParam (h.sameParam_Φ₀ p)

theorem crossSign_Φ₀ (p q : A.Occ) :
    B.crossSign (h.Φ₀ p) (h.Φ₀ q) = B.crossSign (ρ p.1.1, h.φ p) (ρ q.1.1, h.φ q) :=
  B.crossSign_of_sameParam (h.sameParam_Φ₀ p) (h.sameParam_Φ₀ q)

theorem Φ₀_ne (p q : A.Occ) (hne : p ≠ q) : h.Φ₀ p ≠ h.Φ₀ q := by
  intro heq
  have h1 : ρ p.1.1 = ρ q.1.1 := congrArg Prod.fst heq
  have h1' : p.1.1 = q.1.1 := ρ.injective h1
  have h2 : Int.fract (h.φ p) = Int.fract (h.φ q) := congrArg Prod.snd heq
  have hne' : p.1 ≠ q.1 := fun h' => hne (Subtype.ext h')
  exact fract_ne_of_sep (h.sep p.1 p.2 q.1 q.2 h1' hne') (h.φ_abs p) (h.φ_abs q) h2

theorem eval_Φ₀_partner (p : A.Occ) : B.eval (h.Φ₀ p) = B.eval (h.Φ₀ (partner A p)) := by
  rw [eval_Φ₀, eval_Φ₀, φ_partner]
  exact h.sol_eval (p.1, (partner A p).1) (mem_doubleSet_partner A p)

theorem Φ₀_mem (p : A.Occ) : h.Φ₀ p ∈ B.occSet :=
  B.mem_occSet.2 ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, h.Φ₀ (partner A p),
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, h.Φ₀_ne _ _ (partner_ne A p), h.eval_Φ₀_partner p⟩

/-- the occurrence map -/
def Φ (p : A.Occ) : B.Occ := ⟨h.Φ₀ p, h.Φ₀_mem p⟩

theorem Φ_injective : Function.Injective h.Φ := fun p q heq =>
  by_contra fun hne => h.Φ₀_ne p q hne (congrArg Subtype.val heq)

theorem Φ_surjective : Function.Surjective h.Φ := by
  intro p'
  have hb : (p'.1, (partner B p').1) ∈ B.doubleSet := mem_doubleSet_partner B p'
  obtain ⟨a, ha, m, n, h1, h2, hmn⟩ := h.nonew _ hb
  have haocc : a.1 ∈ A.occSet := A.fst_mem_occSet_of_mem_doubleSet ha
  have ha' := A.mem_doubleSet.1 ha
  have hQ : (partner A ⟨a.1, haocc⟩).1 = a.2 := by
    have := eq_partner A (p := ⟨a.1, haocc⟩) (q := ⟨a.2, A.snd_mem_occSet_of_mem_doubleSet ha⟩)
      (fun h' => ha'.2.2.1 (congrArg Subtype.val h')) ha'.2.2.2
    exact congrArg Subtype.val this.symm
  have hdp : ((⟨a.1, haocc⟩ : A.Occ).1, (partner A ⟨a.1, haocc⟩).1) = a := Prod.ext rfl hQ
  have hsol : ((p'.1.2 + m, (partner B p').1.2 + n) : ℝ × ℝ) =
      h.sol ((⟨a.1, haocc⟩ : A.Occ).1, (partner A ⟨a.1, haocc⟩).1) (mem_doubleSet_partner A _) := by
    apply h.sol_unique
    · rw [hdp]; exact hmn
    · rw [hdp]
      have e1 : B.eval (ρ a.1.1, p'.1.2 + m) = B.eval p'.1 :=
        SmoothFront.eval_of_sameParam (⟨h1, m, rfl⟩ : SameParam p'.1 (ρ a.1.1, p'.1.2 + m))
      have e2 : B.eval (ρ a.2.1, (partner B p').1.2 + n) = B.eval (partner B p').1 :=
        SmoothFront.eval_of_sameParam
          (⟨h2, n, rfl⟩ : SameParam (partner B p').1 (ρ a.2.1, (partner B p').1.2 + n))
      show B.eval (ρ a.1.1, p'.1.2 + m) = B.eval (ρ a.2.1, (partner B p').1.2 + n)
      rw [e1, e2]; exact eval_partner B p'
  refine ⟨⟨a.1, haocc⟩, Subtype.ext ?_⟩
  show (ρ a.1.1, Int.fract (h.φ ⟨a.1, haocc⟩)) = p'.1
  have hφ : h.φ ⟨a.1, haocc⟩ = p'.1.2 + m := by
    unfold φ; rw [← hsol]
  rw [hφ, Int.fract_add_intCast, Int.fract_eq_self.2 p'.2.1]
  exact Prod.ext h1.symm rfl

/-- the occurrence bijection -/
def toEquiv : A.Occ ≃ B.Occ := Equiv.ofBijective h.Φ ⟨h.Φ_injective, h.Φ_surjective⟩

theorem toEquiv_val (p : A.Occ) : (h.toEquiv p).1 = h.Φ₀ p := rfl

/-- **the local hypotheses transport the record** -/
def toFrontRecEquiv : FrontRecEquiv A B where
  e := ρ
  Φ := h.toEquiv
  comp_eq p := rfl
  between_iff p q r hpq hqr := by
    show cycBetween p.1.2 q.1.2 r.1.2 ↔
      cycBetween (Int.fract (h.φ p)) (Int.fract (h.φ q)) (Int.fract (h.φ r))
    apply cycBetween_fract_of_sep p.2.1 q.2.1 r.2.1
    · intro hne; exact h.sep p.1 p.2 q.1 q.2 hpq (fun h' => hne (congrArg Prod.snd h'))
    · intro hne; exact h.sep q.1 q.2 r.1 r.2 hqr (fun h' => hne (congrArg Prod.snd h'))
    · intro hne; exact h.sep p.1 p.2 r.1 r.2 (hpq.trans hqr) (fun h' => hne (congrArg Prod.snd h'))
    · intro heq; have : p = q := Subtype.ext (Prod.ext hpq heq); rw [this]
    · intro heq; have : q = r := Subtype.ext (Prod.ext hqr heq); rw [this]
    · intro heq; have : p = r := Subtype.ext (Prod.ext (hpq.trans hqr) heq); rw [this]
    · exact h.φ_abs p
    · exact h.φ_abs q
    · exact h.φ_abs r
  meet_iff p q hne := by
    constructor
    · intro he
      have hq : q = partner A p := eq_partner A hne he
      rw [hq]; exact h.eval_Φ₀_partner p
    · intro he
      have h1 : h.toEquiv q = partner B (h.toEquiv p) :=
        eq_partner B (fun h' => hne (h.toEquiv.injective h')) he
      have h2 : h.toEquiv (partner A p) = partner B (h.toEquiv p) :=
        eq_partner B (fun h' => partner_ne A p (h.toEquiv.injective h')) (h.eval_Φ₀_partner p)
      have : q = partner A p := h.toEquiv.injective (h1.trans h2.symm)
      rw [this]; exact eval_partner A p
  slope_iff p q hne he := by
    have hq : q = partner A p := eq_partner A hne he
    subst hq
    have := (h.pres (p.1, (partner A p).1) (mem_doubleSet_partner A p) _
      (h.sol_mem (p.1, (partner A p).1) (mem_doubleSet_partner A p))).1
    show A.slope p.1 < A.slope (partner A p).1 ↔ B.slope (h.Φ₀ p) < B.slope (h.Φ₀ (partner A p))
    rw [slope_Φ₀, slope_Φ₀, φ_partner]
    exact this.symm
  sign_eq p q hne he := by
    have hq : q = partner A p := eq_partner A hne he
    subst hq
    have := (h.pres (p.1, (partner A p).1) (mem_doubleSet_partner A p) _
      (h.sol_mem (p.1, (partner A p).1) (mem_doubleSet_partner A p))).2
    show A.crossSign p.1 (partner A p).1 = B.crossSign (h.Φ₀ p) (h.Φ₀ (partner A p))
    rw [crossSign_Φ₀, φ_partner]
    exact this.symm

end OccHyp
/-! #### Part F: the analysis for double points -/

/-- the sign of a continuous function is locally constant where it is nonzero -/
theorem eventually_sign_iff {X : Type*} [TopologicalSpace X] {f : X → ℝ} {x₀ : X}
    (hf : ContinuousAt f x₀) (h0 : f x₀ ≠ 0) :
    ∀ᶠ x in 𝓝 x₀, (f x < 0 ↔ f x₀ < 0) ∧ (0 < f x ↔ 0 < f x₀) := by
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · exact (Filter.Tendsto.eventually_lt_const hneg hf).mono fun z hz =>
      ⟨⟨fun _ => hneg, fun _ => hz⟩, ⟨fun h => absurd hz (not_lt.2 h.le), fun h => absurd hneg (not_lt.2 h.le)⟩⟩
  · exact (Filter.Tendsto.eventually_const_lt hpos hf).mono fun z hz =>
      ⟨⟨fun h => absurd hz (not_lt.2 h.le), fun h => absurd hpos (not_lt.2 h.le)⟩, ⟨fun _ => hpos, fun _ => hz⟩⟩

/-! ##### The linear equivalence `(s, r) ↦ s • a - r • b` of two independent vectors -/

/-- the linear map `(s, r) ↦ s • a - r • b` -/
def planeMap (a b : Plane) : ℝ × ℝ →L[ℝ] Plane :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight a - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight b

theorem planeMap_apply (a b : Plane) (x : ℝ × ℝ) : planeMap a b x = x.1 • a - x.2 • b := rfl

/-- its inverse (Cramer) when `D = det a b ≠ 0` -/
def planeInv (a b : Plane) (D : ℝ) : Plane →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight ((b.2 / D, a.2 / D) : ℝ × ℝ) +
  (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight ((-b.1 / D, -a.1 / D) : ℝ × ℝ)

theorem planeInv_apply (a b : Plane) (D : ℝ) (w : Plane) :
    planeInv a b D w = w.1 • ((b.2 / D, a.2 / D) : ℝ × ℝ) + w.2 • ((-b.1 / D, -a.1 / D) : ℝ × ℝ) := rfl

/-- `(s, r) ↦ s • a - r • b` is a linear equivalence when `det a b ≠ 0` -/
def planeEquiv (a b : Plane) (hD : det a b ≠ 0) : (ℝ × ℝ) ≃L[ℝ] Plane :=
  ContinuousLinearEquiv.equivOfInverse (planeMap a b) (planeInv a b (det a b))
    (fun x => by
      rw [planeInv_apply, planeMap_apply]
      unfold det at hD ⊢
      have hinv := mul_inv_cancel₀ hD
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
        linear_combination x.1 * hinv
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, smul_eq_mul]
        linear_combination x.2 * hinv)
    (fun y => by
      rw [planeInv_apply, planeMap_apply]
      unfold det at hD ⊢
      have hinv := mul_inv_cancel₀ hD
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        linear_combination y.1 * hinv
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        linear_combination y.2 * hinv)

theorem coe_planeEquiv (a b : Plane) (hD : det a b ≠ 0) :
    (planeEquiv a b hD : ℝ × ℝ →L[ℝ] Plane) = planeMap a b := rfl

theorem box_mono {ε ε' : ℝ} (h : ε ≤ ε') {c : ℕ} (a : Param c × Param c) : box ε a ⊆ box ε' a :=
  Set.prod_mono (Ioo_subset_Ioo (by linarith) (by linarith)) (Ioo_subset_Ioo (by linarith) (by linarith))

/-! ##### Calculus: strict monotonicity from a nonvanishing third derivative -/

/-- if `f' φ = f'' φ = 0` and `f''' > 0` on an open interval containing `φ`, `f` is strictly
increasing there -/
theorem strictMonoOn_of_third_deriv_pos {f f₁ f₂ f₃ : ℝ → ℝ} (h1 : ∀ u, HasDerivAt f (f₁ u) u)
    (h2 : ∀ u, HasDerivAt f₁ (f₂ u) u) (h3 : ∀ u, HasDerivAt f₂ (f₃ u) u)
    {α β φ : ℝ} (hφ : φ ∈ Ioo α β) (hf1 : f₁ φ = 0) (hf2 : f₂ φ = 0)
    (hpos : ∀ u ∈ Ioo α β, 0 < f₃ u) : StrictMonoOn f (Ioo α β) := by
  have c0 : Continuous f := continuous_iff_continuousAt.2 fun u => (h1 u).continuousAt
  have c1 : Continuous f₁ := continuous_iff_continuousAt.2 fun u => (h2 u).continuousAt
  have c2 : Continuous f₂ := continuous_iff_continuousAt.2 fun u => (h3 u).continuousAt
  have d1 : deriv f = f₁ := funext fun u => (h1 u).deriv
  have d2 : deriv f₁ = f₂ := funext fun u => (h2 u).deriv
  have d3 : deriv f₂ = f₃ := funext fun u => (h3 u).deriv
  have m2 : StrictMonoOn f₂ (Ioo α β) :=
    strictMonoOn_of_deriv_pos (convex_Ioo α β) c2.continuousOn
      (by rw [interior_Ioo]; intro u hu; rw [d3]; exact hpos u hu)
  have f2neg : ∀ u ∈ Ioo α φ, f₂ u < 0 := fun u hu => by
    have := m2 ⟨hu.1, hu.2.trans hφ.2⟩ hφ hu.2; rwa [hf2] at this
  have f2pos : ∀ u ∈ Ioo φ β, 0 < f₂ u := fun u hu => by
    have := m2 hφ ⟨hφ.1.trans hu.1, hu.2⟩ hu.1; rwa [hf2] at this
  have a1 : StrictAntiOn f₁ (Ioc α φ) :=
    strictAntiOn_of_deriv_neg (convex_Ioc α φ) c1.continuousOn
      (by rw [interior_Ioc]; intro u hu; rw [d2]; exact f2neg u hu)
  have m1 : StrictMonoOn f₁ (Ico φ β) :=
    strictMonoOn_of_deriv_pos (convex_Ico φ β) c1.continuousOn
      (by rw [interior_Ico]; intro u hu; rw [d2]; exact f2pos u hu)
  have f1pos : ∀ u ∈ Ioo α β, u ≠ φ → 0 < f₁ u := by
    intro u hu hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := a1 ⟨hu.1, hlt.le⟩ ⟨hφ.1, le_rfl⟩ hlt; rwa [hf1] at this
    · have := m1 ⟨le_rfl, hφ.2⟩ ⟨hgt.le, hu.2⟩ hgt; rwa [hf1] at this
  have mL : StrictMonoOn f (Ioc α φ) :=
    strictMonoOn_of_deriv_pos (convex_Ioc α φ) c0.continuousOn
      (by rw [interior_Ioc]; intro u hu; rw [d1]; exact f1pos u ⟨hu.1, hu.2.trans hφ.2⟩ hu.2.ne)
  have mR : StrictMonoOn f (Ico φ β) :=
    strictMonoOn_of_deriv_pos (convex_Ico φ β) c0.continuousOn
      (by rw [interior_Ico]; intro u hu; rw [d1]; exact f1pos u ⟨hφ.1.trans hu.1, hu.2⟩ hu.1.ne')
  intro u hu v hv huv
  rcases le_or_gt u φ with hu' | hu'
  · rcases le_or_gt v φ with hv' | hv'
    · exact mL ⟨hu.1, hu'⟩ ⟨hv.1, hv'⟩ huv
    · calc f u ≤ f φ := by
            rcases eq_or_lt_of_le hu' with h | h
            · rw [h]
            · exact (mL ⟨hu.1, hu'⟩ ⟨hφ.1, le_rfl⟩ h).le
        _ < f v := mR ⟨le_rfl, hφ.2⟩ ⟨hv'.le, hv.2⟩ hv'
  · exact mR ⟨hu'.le, hu.2⟩ ⟨(hu'.trans huv).le, hv.2⟩ huv

/-- the same with either sign of `f'''`, as injectivity -/
theorem injOn_of_third_deriv {f f₁ f₂ f₃ : ℝ → ℝ} (h1 : ∀ u, HasDerivAt f (f₁ u) u)
    (h2 : ∀ u, HasDerivAt f₁ (f₂ u) u) (h3 : ∀ u, HasDerivAt f₂ (f₃ u) u)
    {α β φ : ℝ} (hφ : φ ∈ Ioo α β) (hf1 : f₁ φ = 0) (hf2 : f₂ φ = 0)
    (hsign : (∀ u ∈ Ioo α β, 0 < f₃ u) ∨ (∀ u ∈ Ioo α β, f₃ u < 0)) : InjOn f (Ioo α β) := by
  rcases hsign with hpos | hneg
  · exact (strictMonoOn_of_third_deriv_pos h1 h2 h3 hφ hf1 hf2 hpos).injOn
  · have := strictMonoOn_of_third_deriv_pos (f := fun u => -f u) (f₁ := fun u => -f₁ u)
      (f₂ := fun u => -f₂ u) (f₃ := fun u => -f₃ u) (fun u => (h1 u).neg) (fun u => (h2 u).neg)
      (fun u => (h3 u).neg) hφ (by simp [hf1]) (by simp [hf2]) (fun u hu => by simp; exact hneg u hu)
    intro u hu v hv huv
    exact this.injOn hu hv (by simp only [huv])

section DoubleAnalysis

include d

/-- the double-point map of the pair of components `(i, i')` -/
def Φ2 (i i' : Fin F.c) (t : I) (uv : ℝ × ℝ) : Plane := pdI d i 0 (t, uv.1) - pdI d i' 0 (t, uv.2)

/-- its derivative in `(u, v)` -/
def DΦ2 (i i' : Fin F.c) (t : I) (uv : ℝ × ℝ) : ℝ × ℝ →L[ℝ] Plane :=
  planeMap (pdI d i 1 (t, uv.1)) (pdI d i' 1 (t, uv.2))

theorem hasFDerivAt_Φ2 (i i' : Fin F.c) (t : I) (uv : ℝ × ℝ) :
    HasFDerivAt (Φ2 d i i' t) (DΦ2 d i i' t uv) uv := by
  have h1 : HasFDerivAt (fun uv : ℝ × ℝ => pdI d i 0 (t, uv.1))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (pdI d i 1 (t, uv.1))) uv := by
    have := (hasDerivAt_pdI d i 0 t uv.1).hasFDerivAt.comp uv hasFDerivAt_fst
    refine this.congr_fderiv ?_
    ext <;> simp
  have h2 : HasFDerivAt (fun uv : ℝ × ℝ => pdI d i' 0 (t, uv.2))
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (pdI d i' 1 (t, uv.2))) uv := by
    have := (hasDerivAt_pdI d i' 0 t uv.2).hasFDerivAt.comp uv hasFDerivAt_snd
    refine this.congr_fderiv ?_
    ext <;> simp
  exact h1.sub h2

theorem continuous_Φ2 (i i' : Fin F.c) : Continuous (fun p : I × (ℝ × ℝ) => Φ2 d i i' p.1 p.2) := by
  have h1 := continuous_pdI d i 0
  have h2 := continuous_pdI d i' 0
  unfold Φ2; fun_prop

theorem continuous_DΦ2 (i i' : Fin F.c) : Continuous (fun p : I × (ℝ × ℝ) => DΦ2 d i i' p.1 p.2) := by
  have h1 := continuous_pdI d i 1
  have h2 := continuous_pdI d i' 1
  unfold DΦ2 planeMap
  refine Continuous.sub ?_ ?_
  · exact (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) Plane
      (ContinuousLinearMap.fst ℝ ℝ ℝ)).continuous.comp (by fun_prop)
  · exact (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) Plane
      (ContinuousLinearMap.snd ℝ ℝ ℝ)).continuous.comp (by fun_prop)

variable (t₀ : I)

/-- persistence of a transverse double point along the family (2-D case of `persist`) -/
theorem double_persist (a : Param (d.path t₀.1).c × Param (d.path t₀.1).c)
    (ha : a ∈ (d.path t₀.1).doubleSet) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ᶠ t in 𝓝 t₀, ∃! uv : ℝ × ℝ, uv ∈ box ε a ∧
      (d.path t.1).eval (ρ d t₀.1 t.1 a.1.1, uv.1) = (d.path t.1).eval (ρ d t₀.1 t.1 a.2.1, uv.2) := by
  have hd : (d.path t₀.1).IsDouble a.1 a.2 := (d.path t₀.1).isDouble_of_mem_doubleSet ha
  have h0 : Φ2 d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1) t₀ (a.1.2, a.2.2) = 0 := by
    unfold Φ2; rw [sub_eq_zero]
    have := hd.2
    rwa [eval_eq, eval_eq] at this
  have hdet : det (pdI d (Fin.cast (d.c_eq t₀.1) a.1.1) 1 (t₀, a.1.2))
      (pdI d (Fin.cast (d.c_eq t₀.1) a.2.1) 1 (t₀, a.2.2)) ≠ 0 := by
    have := (d.path t₀.1).det_vel_ne_zero_of_isDouble hd
    rwa [vel_eq, vel_eq] at this
  obtain ⟨ε₀, hε₀, H⟩ := persist (X := I) (E := ℝ × ℝ) (G := Plane) (Φ2 d _ _) (DΦ2 d _ _)
    (hasFDerivAt_Φ2 d _ _) (continuous_Φ2 d _ _) (continuous_DΦ2 d _ _) t₀ (a.1.2, a.2.2) h0
    (planeEquiv _ _ hdet) rfl
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => (H ε hε hεε₀).mono fun t ht => ?_⟩
  have hbox : ∀ uv : ℝ × ℝ, uv ∈ ball (a.1.2, a.2.2) ε ↔ uv ∈ box ε a := by
    intro uv; rw [← ball_prod_same, Real.ball_eq_Ioo, Real.ball_eq_Ioo]; rfl
  have heq : ∀ uv : ℝ × ℝ, Φ2 d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1) t uv = 0 ↔
      (d.path t.1).eval (ρ d t₀.1 t.1 a.1.1, uv.1) = (d.path t.1).eval (ρ d t₀.1 t.1 a.2.1, uv.2) := by
    intro uv; simp only [Φ2, sub_eq_zero, eval_eq, cast_ρ]
  simpa only [hbox, heq] using ht

/-- the slope difference of the family at a pair of parameters -/
def slDiff (i i' : Fin F.c) : I × (ℝ × ℝ) → ℝ := fun z =>
  (pdI d i 1 (z.1, z.2.1)).2 / (pdI d i 1 (z.1, z.2.1)).1 -
    (pdI d i' 1 (z.1, z.2.2)).2 / (pdI d i' 1 (z.1, z.2.2)).1

/-- the tangent determinant of the family at a pair of parameters -/
def dtFun (i i' : Fin F.c) : I × (ℝ × ℝ) → ℝ := fun z =>
  det (pdI d i 1 (z.1, z.2.1)) (pdI d i' 1 (z.1, z.2.2))

theorem continuous_dtFun (i i' : Fin F.c) : Continuous (dtFun d i i') := by
  have h1 := continuous_pdI d i 1
  have h2 := continuous_pdI d i' 1
  unfold dtFun det; fun_prop

/-- the over rule and the sign at a double point persist on a box -/
theorem double_pres (a : Param (d.path t₀.1).c × Param (d.path t₀.1).c)
    (ha : a ∈ (d.path t₀.1).doubleSet) :
    ∃ ε₁ > 0, ∀ᶠ t in 𝓝 t₀, ∀ uv ∈ box ε₁ a,
      ((d.path t.1).slope (ρ d t₀.1 t.1 a.1.1, uv.1) < (d.path t.1).slope (ρ d t₀.1 t.1 a.2.1, uv.2) ↔
        (d.path t₀.1).slope a.1 < (d.path t₀.1).slope a.2) ∧
      (d.path t.1).crossSign (ρ d t₀.1 t.1 a.1.1, uv.1) (ρ d t₀.1 t.1 a.2.1, uv.2) =
        (d.path t₀.1).crossSign a.1 a.2 := by
  have hd : (d.path t₀.1).IsDouble a.1 a.2 := (d.path t₀.1).isDouble_of_mem_doubleSet ha
  have hc1 := continuous_pdI d (Fin.cast (d.c_eq t₀.1) a.1.1) 1
  have hc2 := continuous_pdI d (Fin.cast (d.c_eq t₀.1) a.2.1) 1
  have hx1 : (pdI d (Fin.cast (d.c_eq t₀.1) a.1.1) 1 (t₀, a.1.2)).1 ≠ 0 := by
    have := (d.path t₀.1).vel_fst_ne_zero_of_isDouble hd; rwa [vel_eq] at this
  have hx2 : (pdI d (Fin.cast (d.c_eq t₀.1) a.2.1) 1 (t₀, a.2.2)).1 ≠ 0 := by
    have := (d.path t₀.1).vel_fst_ne_zero_of_isDouble hd.symm; rwa [vel_eq] at this
  have hsl : ContinuousAt (slDiff d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1)) (t₀, (a.1.2, a.2.2)) := by
    unfold slDiff
    apply ContinuousAt.sub
    · exact ContinuousAt.div (by fun_prop) (by fun_prop) hx1
    · exact ContinuousAt.div (by fun_prop) (by fun_prop) hx2
  have hsl0 : slDiff d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1) (t₀, (a.1.2, a.2.2)) ≠ 0 := by
    have := (d.path t₀.1).slope_ne_of_isDouble hd
    unfold SmoothFront.slope at this
    rw [vel_eq, vel_eq] at this
    exact sub_ne_zero.2 this
  have hdt0 : dtFun d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1) (t₀, (a.1.2, a.2.2)) ≠ 0 := by
    have := (d.path t₀.1).det_vel_ne_zero_of_isDouble hd; rwa [vel_eq, vel_eq] at this
  have ev := (eventually_sign_iff hsl hsl0).and
    (eventually_sign_iff (continuous_dtFun d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1)).continuousAt hdt0)
  rw [nhds_prod_eq, eventually_prod_iff] at ev
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := ev
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.eventually_nhds_iff.mp hpb
  refine ⟨ε₁, hε₁, hpa.mono fun t ht uv huv => ?_⟩
  have huv' : dist uv (a.1.2, a.2.2) < ε₁ := by
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := huv
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_sub_lt_iff, abs_sub_lt_iff]
    dsimp only
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨⟨k1, -⟩, ⟨-, k2⟩⟩ := hab ht (hball huv')
  constructor
  · have e : ∀ s : I, ∀ w : ℝ × ℝ,
        ((d.path s.1).slope (ρ d t₀.1 s.1 a.1.1, w.1) < (d.path s.1).slope (ρ d t₀.1 s.1 a.2.1, w.2) ↔
          slDiff d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1) (s, w) < 0) := by
      intro s w
      unfold SmoothFront.slope slDiff
      simp only [vel_eq, cast_ρ]
      rw [sub_neg]
    rw [e t uv, k1]
    unfold SmoothFront.slope slDiff
    rw [vel_eq, vel_eq, sub_neg]
  · have e2 : ∀ s : I, ∀ w : ℝ × ℝ,
        (d.path s.1).crossSign (ρ d t₀.1 s.1 a.1.1, w.1) (ρ d t₀.1 s.1 a.2.1, w.2) =
          if 0 < dtFun d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1) (s, w) then 1 else -1 := by
      intro s w
      unfold SmoothFront.crossSign dtFun
      simp only [vel_eq, cast_ρ]
    have e3 : (d.path t₀.1).crossSign a.1 a.2 = if 0 < dtFun d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1) (t₀, (a.1.2, a.2.2)) then 1 else -1 := by
      unfold SmoothFront.crossSign dtFun
      rw [vel_eq, vel_eq]
    rw [e2 t uv, e3]
    exact if_congr k2 rfl rfl

/-! ##### Uniform local injectivity of the components -/

theorem hasDerivAt_det_pdI (a : Plane) (i : Fin F.c) (k : ℕ) (t : I) (u : ℝ) :
    HasDerivAt (fun u => det a (pdI d i k (t, u))) (det a (pdI d i (k + 1) (t, u))) u := by
  have h := hasDerivAt_pdI d i k t u
  have hs : HasDerivAt (fun u => (pdI d i k (t, u)).2) (pdI d i (k + 1) (t, u)).2 u := h.snd
  have hf : HasDerivAt (fun u => (pdI d i k (t, u)).1) (pdI d i (k + 1) (t, u)).1 u := h.fst
  unfold det
  exact (hs.const_mul a.1).sub (hf.const_mul a.2)

/-- the determinant `det(γ''(t, v), γ'''(t, u))` of component `i` (third-derivative test) -/
def Wfun (i : Fin F.c) : I × (ℝ × ℝ) → ℝ := fun z =>
  det (pdI d i 2 (z.1, z.2.2)) (pdI d i 3 (z.1, z.2.1))

theorem continuous_Wfun (i : Fin F.c) : Continuous (Wfun d i) := by
  have h2 := continuous_pdI d i 2
  have h3 := continuous_pdI d i 3
  unfold Wfun det; fun_prop

/-- near every parameter, the component `i` of `path t` is injective, uniformly for `t` near `t₀` -/
theorem injOn_near (i : Fin F.c) (u₀ : ℝ) :
    ∃ r > 0, ∀ᶠ t in 𝓝 t₀, InjOn (fun u => pdI d i 0 (t, u)) (Ioo (u₀ - r) (u₀ + r)) := by
  by_cases hreg : gx d i (t₀, u₀) = 0
  · -- a cusp of `path t₀`: the third-derivative argument
    have hc : (d.path t₀.1).IsCusp (Fin.cast (d.c_eq t₀.1).symm i, u₀) :=
      (isCusp_iff_gx d t₀ (Fin.cast (d.c_eq t₀.1).symm i, u₀)).2 hreg
    have hne : det (pdI d i 2 (t₀, u₀)) (pdI d i 3 (t₀, u₀)) ≠ 0 := by
      have := (d.path t₀.1).det_acc_jerk_ne_zero_of_isCusp hc; rwa [acc_eq, jerk_eq] at this
    have h2 : gxx d i (t₀, u₀) ≠ 0 := by
      have := (d.path t₀.1).acc_fst_ne_zero_of_isCusp hc; rwa [acc_eq] at this
    have hW0 : Wfun d i (t₀, (u₀, u₀)) ≠ 0 := hne
    have ev := eventually_sign_iff (continuous_Wfun d i).continuousAt hW0
    rw [nhds_prod_eq, eventually_prod_iff] at ev
    obtain ⟨pa, hpa, pb, hpb, hab⟩ := ev
    obtain ⟨r₁, hr₁, hball⟩ := Metric.eventually_nhds_iff.mp hpb
    obtain ⟨ε₀, hε₀, H⟩ := cusp_persist d t₀ i u₀ hreg h2
    refine ⟨min r₁ ε₀, lt_min hr₁ hε₀, ?_⟩
    filter_upwards [hpa, H (min r₁ ε₀) (lt_min hr₁ hε₀) (min_le_right _ _)] with t ht hex
    obtain ⟨φ, ⟨hφ, hφ0⟩, -⟩ := hex
    have hWbox : ∀ u ∈ Ioo (u₀ - min r₁ ε₀) (u₀ + min r₁ ε₀), ∀ v ∈ Ioo (u₀ - min r₁ ε₀) (u₀ + min r₁ ε₀),
        (Wfun d i (t, (u, v)) < 0 ↔ Wfun d i (t₀, (u₀, u₀)) < 0) ∧
        (0 < Wfun d i (t, (u, v)) ↔ 0 < Wfun d i (t₀, (u₀, u₀))) := by
      intro u hu v hv
      apply hab ht; apply hball
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_sub_lt_iff, abs_sub_lt_iff]
      dsimp only
      have := min_le_left r₁ ε₀
      exact ⟨⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩, ⟨by linarith [hv.1, hv.2], by linarith [hv.1, hv.2]⟩⟩
    -- the velocity vanishes at the cusp `φ` of `path t`
    have hv0 : pdI d i 1 (t, φ) = 0 := by
      have hcusp : (d.path t.1).IsCusp (Fin.cast (d.c_eq t.1).symm i, φ) :=
        (isCusp_iff_fst _ _).2 (by rw [vel_eq]; exact hφ0)
      have : (d.path t.1).vel (Fin.cast (d.c_eq t.1).symm i, φ) = 0 := hcusp
      rw [vel_eq] at this
      exact this
    have hinj : InjOn (fun u => det (pdI d i 2 (t, φ)) (pdI d i 0 (t, u)))
        (Ioo (u₀ - min r₁ ε₀) (u₀ + min r₁ ε₀)) := by
      refine injOn_of_third_deriv (hasDerivAt_det_pdI d (pdI d i 2 (t, φ)) i 0 t)
        (hasDerivAt_det_pdI d (pdI d i 2 (t, φ)) i 1 t)
        (hasDerivAt_det_pdI d (pdI d i 2 (t, φ)) i 2 t) hφ ?_ ?_ ?_
      · show det (pdI d i 2 (t, φ)) (pdI d i 1 (t, φ)) = 0
        rw [hv0]; unfold det; simp
      · show det (pdI d i 2 (t, φ)) (pdI d i 2 (t, φ)) = 0
        unfold det; ring
      · rcases lt_or_gt_of_ne hW0 with hneg | hpos
        · right; intro u hu; exact (hWbox u hu φ hφ).1.2 hneg
        · left; intro u hu; exact (hWbox u hu φ hφ).2.2 hpos
    intro u hu v hv huv
    exact hinj hu hv (by simp only [huv])
  · -- a regular point: `x` is strictly monotone nearby
    have ev := eventually_sign_iff (continuous_gx d i).continuousAt hreg
    rw [nhds_prod_eq, eventually_prod_iff] at ev
    obtain ⟨pa, hpa, pb, hpb, hab⟩ := ev
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hpb
    refine ⟨r, hr, hpa.mono fun t ht => ?_⟩
    have hx : ∀ u ∈ Ioo (u₀ - r) (u₀ + r),
        (gx d i (t, u) < 0 ↔ gx d i (t₀, u₀) < 0) ∧ (0 < gx d i (t, u) ↔ 0 < gx d i (t₀, u₀)) :=
      fun u hu => hab ht (hball (by rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith [hu.1, hu.2]))
    have hderiv : ∀ u, HasDerivAt (fun u => (pdI d i 0 (t, u)).1) (gx d i (t, u)) u :=
      fun u => (hasDerivAt_pdI d i 0 t u).fst
    have hcont : Continuous (fun u => (pdI d i 0 (t, u)).1) :=
      continuous_iff_continuousAt.2 fun u => (hderiv u).continuousAt
    have hd : deriv (fun u => (pdI d i 0 (t, u)).1) = fun u => gx d i (t, u) :=
      funext fun u => (hderiv u).deriv
    have hinj : InjOn (fun u => (pdI d i 0 (t, u)).1) (Ioo (u₀ - r) (u₀ + r)) := by
      rcases lt_or_gt_of_ne hreg with hneg | hpos
      · refine (strictAntiOn_of_deriv_neg (convex_Ioo _ _) hcont.continuousOn ?_).injOn
        rw [interior_Ioo]; intro u hu; rw [hd]; exact (hx u hu).1.2 hneg
      · refine (strictMonoOn_of_deriv_pos (convex_Ioo _ _) hcont.continuousOn ?_).injOn
        rw [interior_Ioo]; intro u hu; rw [hd]; exact (hx u hu).2.2 hpos
    intro u hu v hv huv
    exact hinj hu hv (congrArg Prod.fst huv)

/-- **uniform local injectivity**: eventually, two parameters of `[-1, 2]` closer than `η` with the
same image on component `i` coincide -/
theorem uniform_injOn (i : Fin F.c) :
    ∃ η > 0, ∀ᶠ t in 𝓝 t₀, ∀ u v : ℝ, u ∈ Icc (-1 : ℝ) 2 → v ∈ Icc (-1 : ℝ) 2 → |u - v| < η →
      pdI d i 0 (t, u) = pdI d i 0 (t, v) → u = v := by
  choose r hr using injOn_near d t₀ i
  have hK : IsCompact (Icc (-1 : ℝ) 2) := isCompact_Icc
  obtain ⟨T, -, hcover⟩ := hK.elim_nhds_subcover
    (fun u₀ => Ioo (u₀ - r u₀ / 2) (u₀ + r u₀ / 2))
    (fun u₀ _ => Ioo_mem_nhds (by linarith [(hr u₀).1]) (by linarith [(hr u₀).1]))
  have hTne : T.Nonempty := by
    have : (-1 : ℝ) ∈ ⋃ u₀ ∈ T, Ioo (u₀ - r u₀ / 2) (u₀ + r u₀ / 2) := hcover ⟨le_rfl, by norm_num⟩
    obtain ⟨u₀, hu₀, -⟩ := mem_iUnion₂.1 this
    exact ⟨u₀, hu₀⟩
  obtain ⟨u₁, hu₁, hmin⟩ := T.exists_min_image (fun u₀ => r u₀ / 2) hTne
  refine ⟨r u₁ / 2, half_pos (hr u₁).1, ?_⟩
  have hall : ∀ᶠ t in 𝓝 t₀, ∀ u₀ ∈ T, InjOn (fun u => pdI d i 0 (t, u)) (Ioo (u₀ - r u₀) (u₀ + r u₀)) :=
    (Finset.eventually_all T).2 fun u₀ _ => (hr u₀).2
  refine hall.mono fun t ht u v hu hv huv heq => ?_
  obtain ⟨u₀, hu₀, hu'⟩ := mem_iUnion₂.1 (hcover hu)
  have hle := hmin u₀ hu₀
  have hu'' : u ∈ Ioo (u₀ - r u₀) (u₀ + r u₀) := by
    constructor <;> linarith [hu'.1, hu'.2, (hr u₀).1]
  have hv'' : v ∈ Ioo (u₀ - r u₀) (u₀ + r u₀) := by
    rw [abs_sub_lt_iff] at huv
    constructor <;> linarith [hu'.1, hu'.2, huv.1, huv.2]
  exact ht u₀ hu₀ hu'' hv'' heq

/-- the parameters within `η` (mod 1) of the diagonal -/
def nearDiag (η : ℝ) : Set (ℝ × ℝ) := {uv | ∃ m : ℤ, |uv.1 - uv.2 - m| < η}

omit d in
theorem isOpen_nearDiag (η : ℝ) : IsOpen (nearDiag η) := by
  have : nearDiag η = ⋃ m : ℤ, {uv : ℝ × ℝ | |uv.1 - uv.2 - m| < η} := by
    ext uv; simp [nearDiag]
  rw [this]
  exact isOpen_iUnion fun m => isOpen_lt (by fun_prop) continuous_const

/-- no new double points: eventually every double point of `path t` lies (mod 1) in the `ε`-box of a
double point of `path t₀` -/
theorem double_nonew (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ (t : I) in 𝓝 t₀, ∀ b : Param (d.path t.1).c × Param (d.path t.1).c, b ∈ (d.path t.1).doubleSet →
      ∃ a ∈ (d.path t₀.1).doubleSet, ∃ m n : ℤ, b.1.1 = ρ d t₀.1 t.1 a.1.1 ∧ b.2.1 = ρ d t₀.1 t.1 a.2.1 ∧
        (b.1.2 + m, b.2.2 + n) ∈ box ε a := by
  have key : ∀ i i' : Fin F.c, ∀ᶠ t in 𝓝 t₀, ∀ u v : ℝ, u ∈ Icc (0 : ℝ) 1 → v ∈ Icc (0 : ℝ) 1 →
      pdI d i 0 (t, u) = pdI d i' 0 (t, v) →
      (i = i' ∧ ∃ m : ℤ, u = v + m) ∨
      ∃ a ∈ (d.path t₀.1).doubleSet, Fin.cast (d.c_eq t₀.1) a.1.1 = i ∧ Fin.cast (d.c_eq t₀.1) a.2.1 = i' ∧
        ∃ m n : ℤ, (u + m, v + n) ∈ box ε a := by
    intro i i'
    obtain ⟨η, hη, hULI⟩ := uniform_injOn d t₀ i
    set T := (d.path t₀.1).doubleSet.filter
      (fun a => Fin.cast (d.c_eq t₀.1) a.1.1 = i ∧ Fin.cast (d.c_eq t₀.1) a.2.1 = i') with hT
    set Ω : Set (ℝ × ℝ) := ⋃ a ∈ T, near ε a.1.2 ×ˢ near ε a.2.2 with hΩ_def
    set Δ : Set (ℝ × ℝ) := {uv | i = i' ∧ uv ∈ nearDiag (min η 1)} with hΔ_def
    have hΩ : IsOpen Ω :=
      isOpen_iUnion fun a => isOpen_iUnion fun _ => (isOpen_near _ _).prod (isOpen_near _ _)
    have hΔ : IsOpen Δ := by
      by_cases hii : i = i'
      · have : Δ = nearDiag (min η 1) := by ext; simp [hΔ_def, hii]
        rw [this]; exact isOpen_nearDiag _
      · have : Δ = ∅ := by ext; simp [hΔ_def, hii]
        rw [this]; exact isOpen_empty
    set K : Set (ℝ × ℝ) := (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) \ (Ω ∪ Δ) with hK_def
    have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).diff (hΩ.union hΔ)
    have hK0 : ∀ uv ∈ K, Φ2 d i i' t₀ uv ≠ 0 := by
      rintro ⟨u, v⟩ ⟨⟨hu, hv⟩, hnot⟩ h0
      apply hnot
      set j : Fin (d.path t₀.1).c := Fin.cast (d.c_eq t₀.1).symm i with hj
      set j' : Fin (d.path t₀.1).c := Fin.cast (d.c_eq t₀.1).symm i' with hj'
      have he : (d.path t₀.1).eval (j, u) = (d.path t₀.1).eval (j', v) := by
        rw [eval_eq, eval_eq]; exact sub_eq_zero.1 h0
      by_cases hsp : SameParam (j, u) (j', v)
      · right
        obtain ⟨hjj, m, hm⟩ := hsp
        have hii : i = i' := by
          have h1 : j = j' := hjj
          rw [hj, hj'] at h1
          exact Fin.ext (by have := congrArg Fin.val h1; simpa using this)
        refine ⟨hii, -m, ?_⟩
        show |u - v - ((-m : ℤ) : ℝ)| < min η 1
        have hm' : v = u + m := hm
        have e : u - v - ((-m : ℤ) : ℝ) = 0 := by rw [hm']; push_cast; ring
        rw [e, abs_zero]; exact lt_min hη one_pos
      · left
        have hd : ((j, Int.fract u), (j', Int.fract v)) ∈ (d.path t₀.1).doubleSet := by
          rw [(d.path t₀.1).mem_doubleSet]
          refine ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_, ?_⟩
          · intro heq
            apply hsp
            have h1 : j = j' := congrArg Prod.fst heq
            have h2 : Int.fract u = Int.fract v := congrArg Prod.snd heq
            obtain ⟨z, hz⟩ := Int.fract_eq_fract.1 h2
            exact ⟨h1, -z, by push_cast; linarith⟩
          · show (d.path t₀.1).eval (j, Int.fract u) = (d.path t₀.1).eval (j', Int.fract v)
            rw [SmoothFront.eval_of_sameParam (⟨rfl, -⌊u⌋, fract_eq_add_int u⟩ : SameParam (j, u) (j, Int.fract u)),
              SmoothFront.eval_of_sameParam (⟨rfl, -⌊v⌋, fract_eq_add_int v⟩ : SameParam (j', v) (j', Int.fract v))]
            exact he
        refine mem_iUnion₂.2 ⟨_, Finset.mem_filter.2 ⟨hd, Fin.ext rfl, Fin.ext rfl⟩, ⟨-⌊u⌋, ?_⟩, ⟨-⌊v⌋, ?_⟩⟩
        · show u + ((-⌊u⌋ : ℤ) : ℝ) ∈ Ioo (Int.fract u - ε) (Int.fract u + ε)
          rw [← fract_eq_add_int]; exact ⟨by linarith, by linarith⟩
        · show v + ((-⌊v⌋ : ℤ) : ℝ) ∈ Ioo (Int.fract v - ε) (Int.fract v + ε)
          rw [← fract_eq_add_int]; exact ⟨by linarith, by linarith⟩
    have hev := hK.eventually_forall_of_forall_eventually (x₀ := t₀) (P := fun t uv => Φ2 d i i' t uv ≠ 0)
      (fun uv huv => (continuous_Φ2 d i i').continuousAt.eventually_ne (hK0 uv huv))
    filter_upwards [hev, hULI] with t ht hU u v hu hv heq
    by_cases hΔm : (u, v) ∈ Δ
    · left
      obtain ⟨hii, m, hm⟩ := hΔm
      refine ⟨hii, m, ?_⟩
      subst hii
      have hm1 : |u - v - m| < 1 := lt_of_lt_of_le hm (min_le_right _ _)
      have hmη : |u - v - m| < η := lt_of_lt_of_le hm (min_le_left _ _)
      have hvm : v + m ∈ Icc (-1 : ℝ) 2 := by
        rw [abs_sub_lt_iff] at hm1
        constructor <;> linarith [hu.1, hu.2, hv.1, hv.2, hm1.1, hm1.2]
      have hper : pdI d i 0 (t, v + m) = pdI d i 0 (t, v) := by
        rw [pdI_eq, pdI_eq, iteratedDeriv_zero]
        exact (comp d t.1 i).eq_add_int m v
      exact hU u (v + m) (Icc_subset_Icc (by norm_num) (by norm_num) hu) hvm
        (by rw [show u - (v + m) = u - v - m by ring]; exact hmη) (heq.trans hper.symm)
    · by_cases hΩm : (u, v) ∈ Ω
      · right
        obtain ⟨a, ha, hm⟩ := mem_iUnion₂.1 hΩm
        rw [Finset.mem_filter] at ha
        obtain ⟨⟨m, hm1⟩, ⟨n, hn1⟩⟩ := hm
        exact ⟨a, ha.1, ha.2.1, ha.2.2, m, n, hm1, hn1⟩
      · exfalso
        have hK' : (u, v) ∈ K := ⟨⟨hu, hv⟩, fun h => h.elim hΩm hΔm⟩
        exact ht (u, v) hK' (by unfold Φ2; rw [sub_eq_zero]; exact heq)
  have hall := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun i' => key i i'
  refine hall.mono fun t ht b hb => ?_
  have hb' := (d.path t.1).mem_doubleSet.1 hb
  have hne : ¬ SameParam b.1 b.2 := fun hs => hb'.2.2.1 (SameParam.eq_of_mem_Ico hb'.1 hb'.2.1 hs)
  have heq : pdI d (Fin.cast (d.c_eq t.1) b.1.1) 0 (t, b.1.2) =
      pdI d (Fin.cast (d.c_eq t.1) b.2.1) 0 (t, b.2.2) := by
    rw [← eval_eq, ← eval_eq]; exact hb'.2.2.2
  rcases ht _ _ b.1.2 b.2.2 (Ico_subset_Icc_self hb'.1) (Ico_subset_Icc_self hb'.2.1) heq with
    ⟨hii, m, hm⟩ | ⟨a, ha, h1, h2, m, n, hmn⟩
  · exfalso
    apply hne
    refine ⟨Fin.ext (by have := congrArg Fin.val hii; simpa using this), -m, ?_⟩
    push_cast; linarith
  · refine ⟨a, ha, m, n, ?_, ?_, hmn⟩
    · apply Fin.ext; have := congrArg Fin.val h1; simpa [ρ] using this.symm
    · apply Fin.ext; have := congrArg Fin.val h2; simpa [ρ] using this.symm

/-- **the local double-point hypotheses hold near every parameter** -/
theorem eventually_occHyp :
    ∃ ε, ∀ᶠ t in 𝓝 t₀, OccHyp (d.path t₀.1) (d.path t.1) (ρ d t₀.1 t.1) ε := by
  have E1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := eventually_mem_nhdsWithin
  have E2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ (d.path t₀.1).occSet, ∀ q ∈ (d.path t₀.1).occSet, p.1 = q.1 → p ≠ q →
      Sep ε (p.2 - q.2) := by
    have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ (d.path t₀.1).occSet_finite.toFinset, ∀ q ∈ (d.path t₀.1).occSet_finite.toFinset,
        p.1 = q.1 → p ≠ q → Sep ε (p.2 - q.2) := by
      refine (Finset.eventually_all _).2 fun p hp => (Finset.eventually_all _).2 fun q hq => ?_
      rw [Set.Finite.mem_toFinset] at hp hq
      by_cases hc : p.1 = q.1 ∧ p ≠ q
      · have hne : p.2 ≠ q.2 := fun h => hc.2 (Prod.ext hc.1 h)
        exact (eventually_sep (fract_sub_ne_zero hp.1 hq.1 hne)).mono fun ε h _ _ => h
      · exact Filter.Eventually.of_forall fun ε h1 h2 => absurd ⟨h1, h2⟩ hc
    exact this.mono fun ε h p hp q hq =>
      h p ((d.path t₀.1).occSet_finite.mem_toFinset.2 hp) q ((d.path t₀.1).occSet_finite.mem_toFinset.2 hq)
  have E3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a ∈ (d.path t₀.1).doubleSet, ∀ᶠ t in 𝓝 t₀, ∃! uv : ℝ × ℝ, uv ∈ box ε a ∧
      (d.path t.1).eval (ρ d t₀.1 t.1 a.1.1, uv.1) = (d.path t.1).eval (ρ d t₀.1 t.1 a.2.1, uv.2) := by
    refine (Finset.eventually_all (d.path t₀.1).doubleSet).2 fun a ha => ?_
    obtain ⟨ε₀, hε₀, H⟩ := double_persist d t₀ a ha
    exact Filter.eventually_of_mem (Ioo_mem_nhdsGT hε₀) fun ε hε => H ε hε.1 hε.2.le
  have E4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a ∈ (d.path t₀.1).doubleSet, ∀ᶠ t in 𝓝 t₀, ∀ uv ∈ box ε a,
      ((d.path t.1).slope (ρ d t₀.1 t.1 a.1.1, uv.1) < (d.path t.1).slope (ρ d t₀.1 t.1 a.2.1, uv.2) ↔
        (d.path t₀.1).slope a.1 < (d.path t₀.1).slope a.2) ∧
      (d.path t.1).crossSign (ρ d t₀.1 t.1 a.1.1, uv.1) (ρ d t₀.1 t.1 a.2.1, uv.2) =
        (d.path t₀.1).crossSign a.1 a.2 := by
    refine (Finset.eventually_all (d.path t₀.1).doubleSet).2 fun a ha => ?_
    obtain ⟨ε₁, hε₁, H⟩ := double_pres d t₀ a ha
    exact Filter.eventually_of_mem (Ioo_mem_nhdsGT hε₁) fun ε hε => H.mono fun t ht uv huv =>
      ht uv (box_mono hε.2.le a huv)
  obtain ⟨ε, hε1, hε2, hε3, hε4⟩ := (E1.and (E2.and (E3.and E4))).exists
  refine ⟨ε, ?_⟩
  filter_upwards [(Finset.eventually_all (d.path t₀.1).doubleSet).2 hε3, (Finset.eventually_all (d.path t₀.1).doubleSet).2 hε4,
    double_nonew d t₀ ε hε1] with t h3 h4 h5
  exact ⟨hε1, hε2, h3, h4, h5⟩

/-- **`w` is invariant** under a nonsingular deformation. -/
theorem writhe_eq_of_deformation : F.writhe = F'.writhe := by
  have hlc : IsLocallyConstant (fun t : I => (d.path t.1).writhe) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    obtain ⟨ε, hε⟩ := eventually_occHyp d t₀
    exact hε.mono fun t ht => ht.toFrontRecEquiv.writhe_eq.symm
  have h := hlc.apply_eq_of_preconnectedSpace (⟨0, by norm_num⟩ : I) (⟨1, by norm_num⟩ : I)
  have h0 : d.path (⟨0, by norm_num⟩ : I).1 = F := d.start
  have h1 : d.path (⟨1, by norm_num⟩ : I).1 = F' := d.stop
  simp only [h0, h1] at h
  exact h

/-- **the polygonal readings transport** along a nonsingular deformation. -/
theorem marking_nonempty_of_deformation (S : Diagram) (hS : Nonempty (F.Marking S)) :
    Nonempty (F'.Marking S) := by
  have hlc : IsLocallyConstant (fun t : I => decide (Nonempty ((d.path t.1).Marking S))) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    obtain ⟨ε, hε⟩ := eventually_occHyp d t₀
    refine hε.mono fun t ht => ?_
    have ι := ht.toFrontRecEquiv
    apply decide_eq_decide.2
    exact ⟨fun ⟨m⟩ => ⟨transportMarking ι m⟩, fun ⟨m⟩ => ⟨transportMarking ι.symm m⟩⟩
  have h := hlc.apply_eq_of_preconnectedSpace (⟨0, by norm_num⟩ : I) (⟨1, by norm_num⟩ : I)
  have h0 : d.path (⟨0, by norm_num⟩ : I).1 = F := d.start
  have h1 : d.path (⟨1, by norm_num⟩ : I).1 = F' := d.stop
  simp only [h0, h1] at h
  exact (decide_eq_decide.1 h).1 hS

/-- **`P` of the roundings is invariant** under a nonsingular deformation. -/
theorem P_eq_of_deformation (S S' : Diagram) (hS : F.IsRounding S) (hS' : F'.IsRounding S') :
    P S = P S' := by
  obtain ⟨m⟩ := marking_nonempty_of_deformation d S hS.marking_nonempty
  obtain ⟨ρ'⟩ := hS'
  have hS'' : F'.IsRounding S := ⟨⟨ρ'.G, ρ'.geom, m⟩⟩
  exact hS''.P_eq ⟨ρ'⟩

end DoubleAnalysis

end

end U8D

/-- LEAF (ng:commutation, sm-3:1934-1936 "A deformation without a singular event preserves the records, D and
w: signs, cusp directions and cyclic attachments cannot change"): `D`.  Along a jointly smooth family inside
the class, the cusp set `{x' = 0}` is a covering of `[0,1]` (`x'' ≠ 0` at every zero, vertical tangencies
excluded), on which the discriminant `x''·det(γ'', γ''')` is continuous and nonzero. -/
theorem deform_downCount (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) :
    F.downCount = F'.downCount := h.elim fun d => U8D.downCount_eq_of_deformation d

/-- LEAF: the same for `w` (the transverse double points form a covering of `[0,1]`, no accumulation at a
semicubical cusp, `crossSign` continuous and nonzero). -/
theorem deform_writhe (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) :
    F.writhe = F'.writhe := h.elim fun d => U8D.writhe_eq_of_deformation d

/-- LEAF: the same for the records of the roundings, hence (sm-3:1936-1937 "Lemma rp:record-polynomial gives
scalar equality") the polynomial: the `Marking` of `F` transports along the family to a `Marking` of `F'`. -/
theorem deform_P (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) (S S' : Diagram)
    (hS : F.IsRounding S) (hS' : F'.IsRounding S') : P S = P S' :=
  h.elim fun d => U8D.P_eq_of_deformation d S S' hS hS'

/-- LEAF = THE REPRESENTATION THEOREM (ng:commutation sm-3:1924-1925, proof 1938-1947 "separate them by small
local x translations ... Reading successive vertical cuts then gives the finite elementary word"): the
block's analytic bridge (FINAL §8 risk 1; 7.5-11k lines; attacked last; rows 76 and 83 wait for it). -/
theorem represent (F : SmoothFront) : ∃ W : OWord,
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧ F.sCount = (realize W).sCount ∧
    ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record) := sorry

end Leaves

/-! ## Glue (all proved) -/

/-! ### Degrees -/

/-- `deg_a δ^n = n` (`degAZ_mul` in the domain `R`). -/
theorem degAZ_delta_pow (n : ℕ) : degAZ (R.delta ^ n) = n := by
  induction n with
  | zero => simp [degAZ, degA_one]
  | succ n ih =>
    rw [pow_succ, degAZ_mul (pow_ne_zero _ delta_ne_zero) delta_ne_zero, ih, degAZ_delta]
    push_cast; ring

/-- "Solving the skein relation separately in the two directions" (sm-3:2132-2142): the recursion at a
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

/-! ### Polynomial equalities from the leaves -/

/-- ng:commutation: `Δd = 0` (T-rec + rp:record-polynomial). -/
theorem P_comm {W W' : OWord} (h : IsComm W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram :=
  presentations _ _ (comm_recordIso h)

/-- ng:deletions, zigzag: `Δd = 0`. -/
theorem P_zigzag {W W' : OWord} (h : IsZigzagDeletion W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram :=
  presentations _ _ (zigzag_recordIso h)

/-- ng:circle (sm-3:2059 "For nonempty remainder, P_before = δ P_after"): lp:split-circle in record form. -/
theorem P_circleDeletion {W W' : OWord} (h : IsCircleDeletion W.letters W'.letters) :
    P (realize W).diagram = R.delta * P (realize W').diagram :=
  P_addFree _ _ (circle_recordIso_addFree h)

/-- ng:front-III: `Δd = 0` (`P_reidemeister_III` on the site). -/
theorem P_typeIII {W W' : OWord} (h : IsTypeIII W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨U, hU⟩ := typeIII_site h
  exact P_reidemeister_III ⟨U, Or.inl hU⟩

/-- ng:front-II: `Δd = 0` (`P_reidemeister_II` to the vertex-moved diagram, then its record). -/
theorem P_typeII {W W' : OWord} (h : IsTypeII W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨D, hR, hrec⟩ := typeII_move h
  exact (P_reidemeister_II hR).symm.trans (presentations _ _ hrec)

/-- ng:front-I: `Δd = 0` (`P_reidemeister_I`, then the record). -/
theorem P_typeI {W W' : OWord} (h : IsTypeI W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨D, hR, hrec⟩ := typeI_move h
  exact (P_reidemeister_I hR).symm.trans (presentations _ _ hrec)

/-- ng:deletions, crossed cusp: `Δd = 0`. -/
theorem P_crossedCusp {W W' : OWord} (h : IsCrossedCuspShortcut W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨D, hR, hrec⟩ := crossedCusp_move h
  exact (P_reidemeister_I hR).symm.trans (presentations _ _ hrec)


/-! ### The base and the standard circles -/

/-- ng:circle's second sentence for an arbitrary PL union of standard circles: `D = c` (L-PL), `w = 0`,
`P = δ^{c−1}` (lp:split-circle's crossing-free clause), so `B = c − (c − 1) − 1 = 0`. -/
theorem PLFront.IsStandardCircles.defect_eq_zero (F : PLFront) (h : F.IsStandardCircles) : F.defect = 0 := by
  rw [h.defect_eq, PLFront.IsStandardCircles.downCount_eq_c_general F h, P_crossingFree h.1, degAZ_delta_pow]
  have hc := F.Γ.hc
  have hcc : F.diagram.componentCount = F.Γ.c := rfl
  omega

/-- The base clause of the descent on the syntactic base of `SM.ng_finite_word` (ng:circle's `B = 0` for the
base, with the accepted planarity fact for realizations — independent of L-PL). -/
theorem base_defect_nonneg (W : OWord) (hW : W.IsStandardCircleBase) : 0 ≤ (realize W).defect := by
  have hstd := realize_isStandardCircles_of_base W hW
  have hD := realize_downCount_eq_c_of_base W hW
  rw [hstd.defect_eq, hD, P_crossingFree hstd.1, degAZ_delta_pow]
  have hc := (realize W).Γ.hc
  have hcc : (realize W).diagram.componentCount = (realize W).Γ.c := rfl
  omega

/-! ### The cusp-skein inequality from a site (display ng:skein-defect, sm-3:2127-2163) -/

/-- Display ng:skein-defect, first line, for the earlier branch `A` of the printed direction: the site lives
in `A`; positive `x` uses ng:skein-plus/degree-plus, negative `x` ng:skein-minus/degree-minus. -/
theorem skein_ineq_forward {A A' C : OWord} (h : IsCuspSkeinStep A.letters A'.letters C.letters) :
    min (realize A').defect (realize C).defect ≤ (realize A).defect := by
  obtain ⟨x, hrec, ⟨D₀, hsm, hrec₀⟩, hsign⟩ := skein_site h
  obtain ⟨hDA, hDA', hw⟩ := skein_counts h
  have hPA' : P (realize A').diagram = P ((realize A).diagram.switch x) := presentations _ _ hrec
  have hP₀ : P D₀ = P (realize C).diagram := presentations _ _ hrec₀
  unfold PLFront.defect
  rw [hDA, hDA']
  rcases (realize A).diagram.sign_eq_one_or_neg_one x with h1 | h1
  · have hpos : (realize A).diagram.IsPositive x := ((realize A).diagram.isPositive_iff_sign_eq_one x).2 h1
    have e := P_recursion_pos hsm hpos
    rw [← hPA', hP₀] at e
    have hb := degAZ_le_of_eq_pos (P_ne_zero _) (P_ne_zero _) e (P_ne_zero _)
    rw [h1] at hsign
    simp at hsign
    rcases le_max_iff.1 hb with h2 | h2
    · exact le_trans (min_le_left _ _) (by omega)
    · exact le_trans (min_le_right _ _) (by omega)
  · have hneg : ¬ (realize A).diagram.IsPositive x := by
      intro hp
      have := ((realize A).diagram.isPositive_iff_sign_eq_one x).1 hp
      rw [this] at h1; exact absurd h1 (by decide)
    have e := P_recursion_neg hsm hneg
    rw [← hPA', hP₀] at e
    have hb := degAZ_le_of_eq_neg (P_ne_zero _) (P_ne_zero _) e (P_ne_zero _)
    rw [h1] at hsign
    simp at hsign
    rcases le_max_iff.1 hb with h2 | h2
    · exact le_trans (min_le_left _ _) (by omega)
    · exact le_trans (min_le_right _ _) (by omega)

/-- Display ng:skein-defect, second line ("the other principal direction", sm-3:2164-2166 "Reflected ...
templates follow by relabeling their actual attachments and arrows in this local calculation"): the site
lives in `A'`, and the recursion is solved the other way (`switch_of_recursion_pos/neg`). -/
theorem skein_ineq_backward {A A' C : OWord} (h : IsCuspSkeinStep A'.letters A.letters C.letters) :
    min (realize A').defect (realize C).defect ≤ (realize A).defect := by
  obtain ⟨x, hrec, ⟨D₀, hsm, hrec₀⟩, hsign⟩ := skein_site h
  obtain ⟨hDA', hDA, hw⟩ := skein_counts h
  have hPA : P (realize A).diagram = P ((realize A').diagram.switch x) := presentations _ _ hrec
  have hP₀ : P D₀ = P (realize C).diagram := presentations _ _ hrec₀
  unfold PLFront.defect
  rw [hDA, hDA']
  rcases (realize A').diagram.sign_eq_one_or_neg_one x with h1 | h1
  · have hpos : (realize A').diagram.IsPositive x := ((realize A').diagram.isPositive_iff_sign_eq_one x).2 h1
    have e := P_recursion_pos hsm hpos
    rw [← hPA, hP₀] at e
    have e' := switch_of_recursion_pos e
    have hb := degAZ_le_of_eq_neg (P_ne_zero _) (P_ne_zero _) e' (P_ne_zero _)
    rw [h1] at hsign
    simp at hsign
    rcases le_max_iff.1 hb with h2 | h2
    · exact le_trans (min_le_left _ _) (by omega)
    · exact le_trans (min_le_right _ _) (by omega)
  · have hneg : ¬ (realize A').diagram.IsPositive x := by
      intro hp
      have := ((realize A').diagram.isPositive_iff_sign_eq_one x).1 hp
      rw [this] at h1; exact absurd h1 (by decide)
    have e := P_recursion_neg hsm hneg
    rw [← hPA, hP₀] at e
    have e' := switch_of_recursion_neg e
    have hb := degAZ_le_of_eq_pos (P_ne_zero _) (P_ne_zero _) e' (P_ne_zero _)
    rw [h1] at hsign
    simp at hsign
    rcases le_max_iff.1 hb with h2 | h2
    · exact le_trans (min_le_left _ _) (by omega)
    · exact le_trans (min_le_right _ _) (by omega)

end FrontRows

open FrontRows

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

/-- **ng:front-I** (row 77), assembled: display ng:type-I-counts and `Δd = 0` give `ΔB = 0` (sm-3:1967). -/
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
`realize_sCount` (both words nonempty), the `B` clauses from the count displays and the polynomial leaves. -/
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

/-- **ng:circle** (row 81), assembled: display ng:circle-counts with `deg_a (δ P) = deg_a P + 1` ("Its
product with the leading coefficient of P_after is nonzero because the coefficient ring is an integral
domain", sm-3:2061-2063: `degAZ_mul` in the domain `R`). -/
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

/-- Both displayed inequalities of ng:skein-defect (sm-3:2158-2163) from the row (the interchange is
symmetric in its principal branches). -/
theorem ng_cusp_skein_both {A A' C : OWord} (h : IsCuspSkein A.letters A'.letters C.letters) :
    min (realize A').defect (realize C).defect ≤ (realize A).defect ∧
    min (realize A).defect (realize C).defect ≤ (realize A').defect :=
  ⟨ng_cusp_skein.earlier_branch A A' C h, ng_cusp_skein.earlier_branch A' A C h.symm⟩

namespace FrontRows

/-! ## Row 83: the word bound, then the smooth front -/

/-- The seven laws of the descent (`Moves.Laws`) for the moves of `SM.ng_finite_word` with the geometric
`s`, `B` of the realization and the axiom's syntactic base: `pres_B` = rows 76(1), 77, 78, 79; `del_B` =
rows 80, 81(1); `skein_B` = row 82; `base_B` = row 81(2-3) on the syntactic base (`base_defect_nonneg`);
the three `s` laws are the accepted `wordMoves_pres_s/del_s/skein_s` (definitionally the same fields). -/
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

/-- ng:local-front-bound on words (sm-3:2313-2343, the degree induction along the principal chains of
Literature input ng:finite-word): `B ≥ 0` on every closed oriented word's realization.  Consumes
`SM.ng_finite_word`.  The named companion of row 83 (not a field: the printed clause is on the smooth
class). -/
theorem word_bound : ∀ W : OWord, 0 ≤ (realize W).defect :=
  ng_finite_word_bound _ _ certificate_laws

end FrontRows

/-- **ng:local-front-bound** (row 83), assembled: the representation clause of ng:commutation carries `D`,
`w` and the rounding's record to a word; rp:record-polynomial (`presentations`) carries `P`; the word
bound gives `B ≥ 0`; display ng:defect converts (sm-3:2343). -/
theorem ng_local_front_bound : NgLocalFrontBoundClauses where
  front_inequality := fun F S hS => by
    obtain ⟨W, hD, hw, -, hrec⟩ := ng_commutation.represent F
    have hP : P S = P (realize W).diagram := presentations S _ (hrec S hS)
    have h0 := FrontRows.word_bound W
    rw [← F.defect_nonneg_iff S]
    unfold SmoothFront.defect SmoothFront.dOf
    rw [hD, hw, hP]
    exact h0

end SM
