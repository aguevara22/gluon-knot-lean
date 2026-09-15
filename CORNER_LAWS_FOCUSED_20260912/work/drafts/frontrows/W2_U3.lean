import SM.FrontRealizeGeometry
import SM.FrontRealizeBase
import SM.FrontRealizeDeform
import SM.FrontInterfaces
import SM.FrontWordsBase
import SM.FrontGeomModel
import SM.PolynomialBlock

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

/-! ### U3 infrastructure — the record rows (unit U3; PLAN_FINAL.md §4 "L-rec", §5 "U3 record rows")

Tools for the five L-rec leaves, on the record core U2: (A) the word combinatorics of `skein_unique`; (B) a
record isomorphism of the full `σ`-slot records from conjugate first returns to any active supersets
(`U3.recordIsoOfConj`, the generalisation of `U2.extRecordIso` needed when the block itself carries `σ`
letters — the commutation and the cusp-skein switch), the glue of two subtype bijections
(`U3.glueEquiv`), and conjugation from explicit paths (`U3.conj_of_paths`); (C) the letter-local
successor computations on a block (straight passes, the three letter kinds); (D)-(G) the concrete block
passages of the zigzag, the circle, the commutation and the cusp skein. -/

namespace U3

open SM.FrontRealize SM.FrontWord.Letter Equiv U2

/-! #### A. Word combinatorics for `skein_unique` -/

/-- Two pairs of lists, each pair differing at the end of its common prefix and agreeing on the prefix,
have the same prefix and correspond letter by letter. -/
theorem two_appends_eq {X X₂ Y₁ Y₂ Y₃ Y₄ : Word} {a b a₂ b₂ : Letter} (hab : a ≠ b) (hab₂ : a₂ ≠ b₂)
    (h1 : X ++ a :: Y₁ = X₂ ++ a₂ :: Y₃) (h2 : X ++ b :: Y₂ = X₂ ++ b₂ :: Y₄) :
    X = X₂ ∧ a = a₂ ∧ b = b₂ ∧ Y₁ = Y₃ ∧ Y₂ = Y₄ := by
  induction X generalizing X₂ with
  | nil =>
    cases X₂ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h1 h2
      exact ⟨rfl, h1.1, h2.1, h1.2, h2.2⟩
    | cons x X₂ =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h1 h2
      exact absurd (h1.1.trans h2.1.symm) hab
  | cons x X ih =>
    cases X₂ with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h1 h2
      exact absurd (h1.1.symm.trans h2.1) hab₂
    | cons x₂ X₂ =>
      simp only [List.cons_append, List.cons.injEq] at h1 h2
      obtain ⟨rfl, h1⟩ := h1
      obtain ⟨-, h2⟩ := h2
      obtain ⟨rfl, h3, h4, h5, h6⟩ := ih h1 h2
      exact ⟨rfl, h3, h4, h5, h6⟩

/-- The same principal direction twice: the interchange data agree, so the smoothings agree. -/
theorem skeinStep_unique {A A' C C' : Word} (h : IsCuspSkeinStep A A' C) (h' : IsCuspSkeinStep A A' C') :
    C = C' := by
  obtain ⟨X, Y, m, d, a, P, L, hm, hX, hP, hA, hA', hC⟩ := h
  obtain ⟨X₂, Y₂, m₂, d₂, a₂, P₂, L₂, hm₂, hX₂, hP₂, hA₂, hA'₂, hC₂⟩ := h'
  have e1 : X ++ (Letter.l (m + 1) d) :: (Letter.σ m :: Y) = X₂ ++ (Letter.l (m₂ + 1) d₂) :: (Letter.σ m₂ :: Y₂) := by
    simpa using hA.symm.trans hA₂
  have e2 : X ++ (Letter.l m d) :: (Letter.σ (m + 1) :: Y) = X₂ ++ (Letter.l m₂ d₂) :: (Letter.σ (m₂ + 1) :: Y₂) := by
    simpa using hA'.symm.trans hA'₂
  have hab : Letter.l (m + 1) d ≠ Letter.l m d := by intro h; injection h with h1; omega
  have hab₂ : Letter.l (m₂ + 1) d₂ ≠ Letter.l m₂ d₂ := by intro h; injection h with h1; omega
  obtain ⟨rfl, hl, -, hY, -⟩ := two_appends_eq hab hab₂ e1 e2
  simp only [Letter.l.injEq, List.cons.injEq, Letter.σ.injEq] at hl hY
  obtain ⟨hmm, rfl⟩ := hl
  obtain ⟨-, rfl⟩ := hY
  have hmm' : m = m₂ := by omega
  subst hmm'
  rw [hX] at hX₂
  have hPP : P ++ a :: L = P₂ ++ a₂ :: L₂ := Option.some.inj hX₂
  obtain ⟨-, hal⟩ := List.append_inj hPP (hP.trans hP₂.symm)
  obtain ⟨rfl, -⟩ := List.cons.inj hal
  rcases hC with ⟨had, rfl⟩ | ⟨had, rfl⟩ <;> rcases hC₂ with ⟨had₂, rfl⟩ | ⟨had₂, rfl⟩
  · rfl
  · exact absurd (had.symm.trans had₂) (by cases d <;> simp)
  · exact absurd (had.symm.trans had₂) (by cases d <;> simp)
  · rfl

/-- The two principal directions cannot both hold for one pair `(A, A')`: the cusp letters would satisfy
`l (m+1) = l m'` and `l m = l (m'+1)`. -/
theorem skeinStep_not_both {A A' C C' : Word} (h : IsCuspSkeinStep A A' C) (h' : IsCuspSkeinStep A' A C') :
    False := by
  obtain ⟨X, Y, m, d, a, P, L, hm, hX, hP, hA, hA', -⟩ := h
  obtain ⟨X₂, Y₂, m₂, d₂, a₂, P₂, L₂, hm₂, hX₂, hP₂, hA'₂, hA₂, -⟩ := h'
  have e1 : X ++ (Letter.l (m + 1) d) :: (Letter.σ m :: Y) = X₂ ++ (Letter.l m₂ d₂) :: (Letter.σ (m₂ + 1) :: Y₂) := by
    simpa using hA.symm.trans hA₂
  have e2 : X ++ (Letter.l m d) :: (Letter.σ (m + 1) :: Y) = X₂ ++ (Letter.l (m₂ + 1) d₂) :: (Letter.σ m₂ :: Y₂) := by
    simpa using hA'.symm.trans hA'₂
  have hab : Letter.l (m + 1) d ≠ Letter.l m d := by intro h; injection h with h1; omega
  have hab₂ : Letter.l m₂ d₂ ≠ Letter.l (m₂ + 1) d₂ := by intro h; injection h with h1; omega
  obtain ⟨rfl, hl, hl', -, -⟩ := two_appends_eq hab hab₂ e1 e2
  injection hl with hl1 hl2
  injection hl' with hl3 hl4
  omega

/-! #### B. Records from conjugate first returns to active supersets (generic) -/

section Generic

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Glueing two subtype bijections along disjoint predicates. -/
noncomputable def glueEquiv (p q : α → Prop) (p' q' : β → Prop) [DecidablePred p] [DecidablePred p']
    (hpq : ∀ a, p a → ¬ q a) (hpq' : ∀ b, p' b → ¬ q' b)
    (φ₁ : {a // p a} ≃ {b // p' b}) (φ₂ : {a // q a} ≃ {b // q' b}) : {a // p a ∨ q a} ≃ {b // p' b ∨ q' b} where
  toFun a := if h : p a.1 then ⟨(φ₁ ⟨a.1, h⟩).1, Or.inl (φ₁ ⟨a.1, h⟩).2⟩
    else ⟨(φ₂ ⟨a.1, a.2.resolve_left h⟩).1, Or.inr (φ₂ ⟨a.1, a.2.resolve_left h⟩).2⟩
  invFun b := if h : p' b.1 then ⟨(φ₁.symm ⟨b.1, h⟩).1, Or.inl (φ₁.symm ⟨b.1, h⟩).2⟩
    else ⟨(φ₂.symm ⟨b.1, b.2.resolve_left h⟩).1, Or.inr (φ₂.symm ⟨b.1, b.2.resolve_left h⟩).2⟩
  left_inv a := by
    apply Subtype.ext
    by_cases h : p a.1
    · simp only [h, ↓reduceDIte, (φ₁ ⟨a.1, h⟩).2]
      rw [show (⟨(φ₁ ⟨a.1, h⟩).1, (φ₁ ⟨a.1, h⟩).2⟩ : {b // p' b}) = φ₁ ⟨a.1, h⟩ from rfl, Equiv.symm_apply_apply]
    · have hq := a.2.resolve_left h
      have h' : ¬ p' (φ₂ ⟨a.1, hq⟩).1 := fun hp' => hpq' _ hp' (φ₂ ⟨a.1, hq⟩).2
      simp only [h, ↓reduceDIte, h']
      rw [show (⟨(φ₂ ⟨a.1, hq⟩).1, _⟩ : {b // q' b}) = φ₂ ⟨a.1, hq⟩ from rfl, Equiv.symm_apply_apply]
  right_inv b := by
    apply Subtype.ext
    by_cases h : p' b.1
    · simp only [h, ↓reduceDIte, (φ₁.symm ⟨b.1, h⟩).2]
      rw [show (⟨(φ₁.symm ⟨b.1, h⟩).1, (φ₁.symm ⟨b.1, h⟩).2⟩ : {a // p a}) = φ₁.symm ⟨b.1, h⟩ from rfl,
        Equiv.apply_symm_apply]
    · have hq := b.2.resolve_left h
      have h' : ¬ p (φ₂.symm ⟨b.1, hq⟩).1 := fun hp => hpq _ hp (φ₂.symm ⟨b.1, hq⟩).2
      simp only [h, ↓reduceDIte, h']
      rw [show (⟨(φ₂.symm ⟨b.1, hq⟩).1, _⟩ : {a // q a}) = φ₂.symm ⟨b.1, hq⟩ from rfl, Equiv.apply_symm_apply]

omit [Fintype α] [Fintype β] in
theorem glueEquiv_val_left (p q : α → Prop) (p' q' : β → Prop) [DecidablePred p] [DecidablePred p']
    (hpq : ∀ a, p a → ¬ q a) (hpq' : ∀ b, p' b → ¬ q' b)
    (φ₁ : {a // p a} ≃ {b // p' b}) (φ₂ : {a // q a} ≃ {b // q' b}) (a : {a // p a ∨ q a}) (h : p a.1) :
    (glueEquiv p q p' q' hpq hpq' φ₁ φ₂ a).1 = (φ₁ ⟨a.1, h⟩).1 := by
  simp only [glueEquiv, Equiv.coe_fn_mk, h, ↓reduceDIte]

omit [Fintype α] [Fintype β] in
theorem glueEquiv_val_right (p q : α → Prop) (p' q' : β → Prop) [DecidablePred p] [DecidablePred p']
    (hpq : ∀ a, p a → ¬ q a) (hpq' : ∀ b, p' b → ¬ q' b)
    (φ₁ : {a // p a} ≃ {b // p' b}) (φ₂ : {a // q a} ≃ {b // q' b}) (a : {a // p a ∨ q a}) (h : ¬ p a.1) :
    (glueEquiv p q p' q' hpq hpq' φ₁ φ₂ a).1 = (φ₂ ⟨a.1, a.2.resolve_left h⟩).1 := by
  simp only [glueEquiv, Equiv.coe_fn_mk, h, ↓reduceDIte]

variable (f : Perm α) (g : Perm β) (E : α → Prop) (E' : β → Prop) [DecidablePred E] [DecidablePred E']
  (φ : {a // E a} ≃ {b // E' b})

/-- Conjugation of the first returns from explicit paths on both sides. -/
theorem conj_of_paths
    (h : ∀ u : {a // E a}, ∃ (m m' : ℕ) (_ : 0 < m) (_ : 0 < m') (hE : E ((f ^ m) u.1)),
      (∀ i, 0 < i → i < m → ¬ E ((f ^ i) u.1)) ∧ (∀ i, 0 < i → i < m' → ¬ E' ((g ^ i) (φ u).1)) ∧
      (g ^ m') (φ u).1 = (φ ⟨(f ^ m) u.1, hE⟩).1) :
    ∀ u, firstReturn g E' (φ u) = φ (firstReturn f E u) := by
  intro u
  obtain ⟨m, m', hm, hm', hE, hmin, hmin', heq⟩ := h u
  have h1 : firstReturn f E u = ⟨(f ^ m) u.1, hE⟩ := Subtype.ext (firstReturn_eq_of_path f E u hm hE hmin)
  rw [h1]
  apply Subtype.ext
  have hE' : E' ((g ^ m') (φ u).1) := by rw [heq]; exact (φ _).2
  rw [firstReturn_eq_of_path g E' (φ u) hm' hE' hmin']
  exact heq

end Generic

section RecIso

variable {W W' : Word} (hW : W.Closed) (hW' : W'.Closed)
  (E : Slot W → Prop) (E' : Slot W' → Prop) [DecidablePred E] [DecidablePred E']
  (φ : {u // E u} ≃ {u' // E' u'})

/-- `conj_of_paths` for the slot successor, with iterates. -/
theorem conj_of_paths_next
    (h : ∀ u : {u // E u}, ∃ (m m' : ℕ) (_ : 0 < m) (_ : 0 < m') (hE : E ((next hW)^[m] u.1)),
      (∀ i, 0 < i → i < m → ¬ E ((next hW)^[i] u.1)) ∧ (∀ i, 0 < i → i < m' → ¬ E' ((next hW')^[i] (φ u).1)) ∧
      (next hW')^[m'] (φ u).1 = (φ ⟨(next hW)^[m] u.1, hE⟩).1) :
    ∀ u, firstReturn (nextPerm hW') E' (φ u) = φ (firstReturn (nextPerm hW) E u) := by
  apply conj_of_paths
  intro u
  obtain ⟨m, m', hm, hm', hE, hmin, hmin', heq⟩ := h u
  refine ⟨m, m', hm, hm', by rw [nextPerm_pow_apply]; exact hE, ?_, ?_, ?_⟩
  · intro i hi him; rw [nextPerm_pow_apply]; exact hmin i hi him
  · intro i hi him; rw [nextPerm_pow_apply]; exact hmin' i hi him
  · have e1 : (nextPerm hW' ^ m') (φ u).1 = (next hW')^[m'] (φ u).1 := nextPerm_pow_apply hW' m' _
    rw [e1, heq]
    exact congrArg (fun x : {u // E u} => (φ x).1) (Subtype.ext (nextPerm_pow_apply hW m u.1).symm)

/-- THE RECORD ISOMORPHISM FROM CONJUGATE FIRST RETURNS: active supersets `E ⊇ IsσSlot`, `E' ⊇ IsσSlot`
of the two words, conjugate first returns under `φ`, every component meeting `E` resp. `E'`, and `φ`
carrying `σ` slots to `σ` slots with twins, over bits and signs — the full `σ`-slot records are
isomorphic (`U2.extRecordIso` is the case `E = ExtPiece`). -/
noncomputable def recordIsoOfConj
    (conj : ∀ u, firstReturn (nextPerm hW') E' (φ u) = φ (firstReturn (nextPerm hW) E u))
    (hexit : ∀ u : Slot W, ∃ n : ℕ, E ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot W', ∃ n : ℕ, E' ((next hW')^[n] u'))
    (hσE : ∀ u, IsσSlot u → E u) (hσE' : ∀ u', IsσSlot u' → E' u')
    (hσ : ∀ u : {u // E u}, IsσSlot (φ u).1 ↔ IsσSlot u.1)
    (htwin : ∀ (u : {u // E u}) (hu : IsσSlot u.1),
      (φ ⟨σtwin hW u.1, hσE _ (isσSlot_σtwin hW hu)⟩).1 = σtwin hW' (φ u).1)
    (hdesc : ∀ u : {u // E u}, IsσSlot u.1 → isDesc (φ u).1 = isDesc u.1)
    (hsgn : ∀ u : {u // E u}, IsσSlot u.1 → σsgn (φ u).1 = σsgn u.1) :
    RecordIso (slotRecord hW IsσSlot (allActive hW)) (slotRecord hW' IsσSlot (allActive hW')) :=
  let hexitP : ∀ u : Slot W, ∃ n : ℕ, E (((nextPerm hW) ^ n) u) := fun u => by
    obtain ⟨n, hn⟩ := hexit u; exact ⟨n, by rw [nextPerm_pow_apply]; exact hn⟩
  let hexitP' : ∀ u' : Slot W', ∃ n : ℕ, E' (((nextPerm hW') ^ n) u') := fun u => by
    obtain ⟨n, hn⟩ := hexit' u; exact ⟨n, by rw [nextPerm_pow_apply]; exact hn⟩
  let oe : Orbit hW ≃ Orbit hW' := cycleEquiv (nextPerm hW) (nextPerm hW') E E' φ conj hexitP hexitP'
  { e := (Fintype.equivFin (Orbit hW)).symm.trans (oe.trans (Fintype.equivFin (Orbit hW')))
    Φ := { toFun := fun u => ⟨(φ ⟨u.1, hσE _ u.2⟩).1, (hσ _).2 u.2⟩
           invFun := fun u' => ⟨(φ.symm ⟨u'.1, hσE' _ u'.2⟩).1, by
             have h := (hσ (φ.symm ⟨u'.1, hσE' _ u'.2⟩)).1
             rw [Equiv.apply_symm_apply] at h
             exact h u'.2⟩
           left_inv := fun u => Subtype.ext (by
             show (φ.symm ⟨(φ ⟨u.1, hσE _ u.2⟩).1, _⟩).1 = u.1
             rw [show (⟨(φ ⟨u.1, hσE _ u.2⟩).1, _⟩ : {u' // E' u'}) = φ ⟨u.1, hσE _ u.2⟩ from rfl,
               Equiv.symm_apply_apply])
           right_inv := fun u' => Subtype.ext (by
             show (φ ⟨(φ.symm ⟨u'.1, hσE' _ u'.2⟩).1, _⟩).1 = u'.1
             rw [show (⟨(φ.symm ⟨u'.1, hσE' _ u'.2⟩).1, _⟩ : {u // E u}) = φ.symm ⟨u'.1, hσE' _ u'.2⟩ from rfl,
               Equiv.apply_symm_apply]) }
    comp_eq := fun u => by
      show slotComp hW' (φ ⟨u.1, hσE _ u.2⟩).1 =
        ((Fintype.equivFin (Orbit hW)).symm.trans (oe.trans (Fintype.equivFin (Orbit hW')))) (slotComp hW u.1)
      rw [slotComp_eq_equivFin, slotComp_eq_equivFin]
      simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
      congr 1
      show orbitOf hW' _ = cycleEquiv (nextPerm hW) (nextPerm hW') E E' φ conj hexitP hexitP' (orbitOf hW u.1)
      exact (cycleEquiv_mk (nextPerm hW) (nextPerm hW') E E' φ conj hexitP hexitP' ⟨u.1, hσE _ u.2⟩).symm
    succ_eq := fun u => by
      apply Subtype.ext
      show (φ ⟨(firstReturn (nextPerm hW) IsσSlot u).1, _⟩).1 =
        (firstReturn (nextPerm hW') IsσSlot ⟨(φ ⟨u.1, _⟩).1, _⟩).1
      exact (firstReturn_conj_of_factor (nextPerm hW) (nextPerm hW') E E' φ conj IsσSlot IsσSlot hσE hσE' hσ u).symm
    pair_eq := fun u => by
      apply Subtype.ext
      show (φ ⟨σtwin hW u.1, _⟩).1 = σtwin hW' (φ ⟨u.1, _⟩).1
      exact htwin ⟨u.1, hσE _ u.2⟩ u.2
    bit_eq := fun u => hdesc ⟨u.1, hσE _ u.2⟩ u.2
    sgn_eq := fun u => hsgn ⟨u.1, hσE _ u.2⟩ u.2 }

end RecIso

/-! #### C. Letter-local successor computations on a block -/

section Local

variable {V : Word} (hV : V.Closed)

omit hV in
theorem colOf_val {s : Slot V} {k p : ℕ} (hs : s.1 = (k, p)) :
    colOf s = if p = 0 then k else if bit V k p then k else k - 1 := by
  obtain ⟨⟨k', p'⟩, hs'⟩ := s
  simp only [Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  rfl

include hV

/-- every slot's column is a real column -/
theorem slot_col_lt {s : Slot V} {k p : ℕ} (hs : s.1 = (k, p)) : k < V.length := by
  have h := s.2
  rw [hs] at h
  rcases h with ⟨-, hk, -⟩ | ⟨h1, h2, -⟩
  · exact hk
  · exact (cutSlot_pos hV h1 h2).2

theorem cutSlot_facts {s : Slot V} {k p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) :
    1 ≤ p ∧ p ≤ (cut V k).length ∧ 0 < k ∧ k < V.length := by
  have h := s.2
  rw [hs] at h
  rcases h with ⟨h0, -, -⟩ | ⟨h1, h2, -⟩
  · exact absurd h0 hp
  · obtain ⟨hk0, hk⟩ := cutSlot_pos hV h1 h2
    exact ⟨h1, h2, hk0, hk⟩

omit hV in
theorem vertex_lt {s : Slot V} {k : ℕ} (hs : s.1 = (k, 0)) : k < V.length := by
  have h := s.2
  rw [hs] at h
  rcases h with ⟨-, hk, -⟩ | ⟨h1, -, -⟩
  · exact hk
  · simp at h1

omit hV in
theorem vertex_not_crossing {s : Slot V} {k : ℕ} (hs : s.1 = (k, 0)) : (letterAt V k).isCrossing = false := by
  have h := s.2
  rw [hs] at h
  rcases h with ⟨-, -, hσ⟩ | ⟨h1, -, -⟩
  · exact hσ
  · simp at h1

theorem letter_idx_pos {k : ℕ} (hk : k < V.length) : 1 ≤ (letterAt V k).idx := by
  obtain ⟨D⟩ := decomp hV k hk
  exact D.hm

/-- bits above a letter are unchanged across its column -/
theorem bit_succ_of_lt {k p : ℕ} (hk : k < V.length) (hp1 : 1 ≤ p) (hp : p < (letterAt V k).idx) :
    bit V (k + 1) p = bit V k p := by
  obtain ⟨D⟩ := decomp hV k hk
  rw [bit_eq, bit_eq]
  exact D.getD_above hp1 hp

/-- bits below a letter are unchanged across its column, shifted by its strand-count change -/
theorem bit_succ_of_ge {k p : ℕ} (hk : k < V.length) (hp : (letterAt V k).idx + (letterAt V k).arity ≤ p) :
    bit V (k + 1) (p + (letterAt V k).coarity - (letterAt V k).arity) = bit V k p := by
  obtain ⟨D⟩ := decomp hV k hk
  rw [bit_eq, bit_eq]
  exact D.getD_below hp

/-- (1) a rightward strand above the letter passes the column -/
theorem next_right_lt {s : Slot V} {k p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) (hb : bit V k p = true)
    (hlt : p < (letterAt V k).idx) :
    (next hV s).1 = (k + 1, p) ∧ bit V (k + 1) p = true := by
  obtain ⟨hp1, -, -, hk⟩ := cutSlot_facts hV hs hp
  refine ⟨?_, ?_⟩
  · rw [next_val, hs, nextPair_right V hp hb (posR_of_lt hlt)]
  · rw [bit_succ_of_lt hV hk hp1 hlt, hb]

/-- (2) a rightward strand below the letter passes the column, shifted -/
theorem next_right_ge {s : Slot V} {k p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) (hb : bit V k p = true)
    (hge : (letterAt V k).idx + (letterAt V k).arity ≤ p) :
    (next hV s).1 = (k + 1, p + (letterAt V k).coarity - (letterAt V k).arity) ∧
      bit V (k + 1) (p + (letterAt V k).coarity - (letterAt V k).arity) = true := by
  obtain ⟨-, -, -, hk⟩ := cutSlot_facts hV hs hp
  refine ⟨?_, ?_⟩
  · rw [next_val, hs, nextPair_right V hp hb (posR_of_ge hge)]
  · rw [bit_succ_of_ge hV hk hge, hb]

/-- (3) a leftward strand above the letter of the previous column passes it -/
theorem next_left_lt {s : Slot V} {k q : ℕ} (hs : s.1 = (k, q)) (hq : q ≠ 0) (hb : bit V k q = false)
    (hlt : q < (letterAt V (k - 1)).idx) :
    (next hV s).1 = (k - 1, q) ∧ bit V (k - 1) q = false := by
  obtain ⟨hq1, -, hk0, hk⟩ := cutSlot_facts hV hs hq
  refine ⟨?_, ?_⟩
  · rw [next_val, hs, nextPair_left V hq hb (posL_of_lt hlt)]
  · have := bit_succ_of_lt hV (k := k - 1) (by omega) hq1 hlt
    rw [Nat.sub_add_cancel hk0] at this
    rw [← this, hb]

/-- (4) a leftward strand below the letter of the previous column passes it, shifted -/
theorem next_left_ge {s : Slot V} {k q : ℕ} (hs : s.1 = (k, q)) (hq : q ≠ 0) (hb : bit V k q = false)
    (hge : (letterAt V (k - 1)).idx + (letterAt V (k - 1)).coarity ≤ q) :
    (next hV s).1 = (k - 1, q + (letterAt V (k - 1)).arity - (letterAt V (k - 1)).coarity) ∧
      bit V (k - 1) (q + (letterAt V (k - 1)).arity - (letterAt V (k - 1)).coarity) = false := by
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hV hs hq
  refine ⟨?_, ?_⟩
  · rw [next_val, hs, nextPair_left V hq hb (posL_of_ge hge)]
  · have := bit_succ_of_ge hV (k := k - 1) (p := q + (letterAt V (k - 1)).arity - (letterAt V (k - 1)).coarity)
      (by omega) (by omega)
    rw [Nat.sub_add_cancel hk0, show q + (letterAt V (k - 1)).arity - (letterAt V (k - 1)).coarity +
      (letterAt V (k - 1)).coarity - (letterAt V (k - 1)).arity = q by omega] at this
    rw [← this, hb]

/-! the crossing letter -/

omit hV in
theorem lt_length_of_letterAt_σ {k j : ℕ} (hℓ : letterAt V k = .σ j) : k < V.length := by
  by_contra h
  rw [not_lt] at h
  unfold letterAt at hℓ
  rw [List.getD_eq_default _ _ h] at hℓ
  cases hℓ

theorem σ_idx_pos {k j : ℕ} (hℓ : letterAt V k = .σ j) : 1 ≤ j :=
  (σ_facts hV (lt_length_of_letterAt_σ hℓ) hℓ).1

theorem next_σ_right_idx {s : Slot V} {k j : ℕ} (hℓ : letterAt V k = .σ j) (hs : s.1 = (k, j))
    (hb : bit V k j = true) : (next hV s).1 = (k + 1, j + 1) := by
  have hj := σ_idx_pos hV hℓ
  rw [next_val, hs, nextPair_right V (by omega) hb (by rw [hℓ]; exact posR_σ_idx j)]

theorem next_σ_right_succ {s : Slot V} {k j : ℕ} (hℓ : letterAt V k = .σ j) (hs : s.1 = (k, j + 1))
    (hb : bit V k (j + 1) = true) : (next hV s).1 = (k + 1, j) := by
  rw [next_val, hs, nextPair_right V (by omega) hb (by rw [hℓ]; exact posR_σ_idx_succ j)]

theorem next_σ_left_idx {s : Slot V} {k j : ℕ} (hℓ : letterAt V k = .σ j) (hs : s.1 = (k + 1, j))
    (hb : bit V (k + 1) j = false) : (next hV s).1 = (k, j + 1) := by
  have hj := σ_idx_pos hV hℓ
  rw [next_val, hs, nextPair_left V (by omega) hb (by rw [Nat.add_sub_cancel, hℓ]; exact posL_σ_idx j)]
  simp

theorem next_σ_left_succ {s : Slot V} {k j : ℕ} (hℓ : letterAt V k = .σ j) (hs : s.1 = (k + 1, j + 1))
    (hb : bit V (k + 1) (j + 1) = false) : (next hV s).1 = (k, j) := by
  rw [next_val, hs, nextPair_left V (by omega) hb (by rw [Nat.add_sub_cancel, hℓ]; exact posL_σ_idx_succ j)]
  simp

/-! the left cusp -/

theorem l_bits {k j : ℕ} {d : Bool} (hk : k < V.length) (hℓ : letterAt V k = .l j d) :
    1 ≤ j ∧ bit V (k + 1) j = d ∧ bit V (k + 1) (j + 1) = !d := by
  obtain ⟨D⟩ := decomp hV k hk
  rw [hℓ] at D
  obtain ⟨h1, h2, -⟩ := D.bits_l
  refine ⟨D.hm, ?_, ?_⟩
  · rw [bit_eq]; exact h1
  · rw [bit_succ]; exact h2

theorem next_cusp_l {s : Slot V} {k j : ℕ} {d : Bool} (hℓ : letterAt V k = .l j d) (hs : s.1 = (k, 0)) :
    (next hV s).1 = (k + 1, if d then j else j + 1) := by
  rw [next_val, hs, nextPair_cusp_l V hℓ]

/-- the leftward arm of a left cusp enters its vertex -/
theorem next_arm_l {s : Slot V} {k j q : ℕ} {d : Bool} (hk : k < V.length) (hℓ : letterAt V k = .l j d)
    (hs : s.1 = (k + 1, q)) (hq : q = j ∨ q = j + 1) (hb : bit V (k + 1) q = false) :
    (next hV s).1 = (k, 0) := by
  have hj := (l_bits hV hk hℓ).1
  rw [next_val, hs, nextPair_left_none V (by omega) hb (by
    rw [Nat.add_sub_cancel, hℓ]
    rcases hq with h | h <;> rw [h]
    · exact posL_l_idx _ _
    · exact posL_l_idx_succ _ _)]
  simp

/-! the right cusp -/

theorem r_bits {k j : ℕ} (hk : k < V.length) (hℓ : letterAt V k = .r j) :
    1 ≤ j ∧ bit V k j ≠ bit V k (j + 1) := by
  obtain ⟨D⟩ := decomp hV k hk
  rw [hℓ] at D
  obtain ⟨h1, -⟩ := D.bits_r
  refine ⟨D.hm, ?_⟩
  rw [bit_eq, bit_succ]; exact h1

theorem next_cusp_r {s : Slot V} {k j : ℕ} (hℓ : letterAt V k = .r j) (hs : s.1 = (k, 0)) :
    (next hV s).1 = (k, if bit V k j then j + 1 else j) := by
  rw [next_val, hs, nextPair_cusp_r V hℓ]

/-- the rightward arm of a right cusp enters its vertex -/
theorem next_arm_r {s : Slot V} {k j p : ℕ} (hk : k < V.length) (hℓ : letterAt V k = .r j)
    (hs : s.1 = (k, p)) (hp : p = j ∨ p = j + 1) (hb : bit V k p = true) :
    (next hV s).1 = (k, 0) := by
  have hj := (r_bits hV hk hℓ).1
  rw [next_val, hs, nextPair_right_none V (by omega) hb (by
    rw [hℓ]
    rcases hp with h | h <;> rw [h]
    · exact posR_r_idx _
    · exact posR_r_idx_succ _)]

/-! cuts and letters of a block -/

omit hV in
theorem letterAt_block (X P Y : Word) {i : ℕ} (hi : i < P.length) :
    letterAt (X ++ P ++ Y) (X.length + i) = P.getD i (.l 0 false) := by
  unfold letterAt
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ hi]

omit hV in
theorem cut_start (X P Y : Word) {c₀ : Cuts} (hX : Word.run X [] = some c₀) : cut (X ++ P ++ Y) X.length = c₀ := by
  unfold cut
  rw [List.append_assoc, List.take_left' rfl, hX]; rfl

theorem cut_succ_of {k : ℕ} (hk : k < V.length) {ℓ : Letter} {c c' : Cuts} (hℓ : letterAt V k = ℓ)
    (hc : cut V k = c) (hstep : ℓ.step c = some c') : cut V (k + 1) = c' := by
  have := step_cut V hV hk
  rw [hℓ, hc, hstep] at this
  exact (Option.some.inj this).symm

/-- reaching an exterior piece: the recursion -/
theorem reach_of_next {E : Slot V → Prop} {u : Slot V} (h : ∃ n, E ((next hV)^[n] (next hV u))) :
    ∃ n, E ((next hV)^[n] u) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

theorem reach_self {E : Slot V → Prop} {u : Slot V} (h : E u) : ∃ n, E ((next hV)^[n] u) := ⟨0, h⟩

end Local

/-! #### D. Block passages: the generic bookkeeping -/

section Passages

variable {V : Word} (hV : V.Closed)
include hV

omit hV in
theorem block_col_true {s : Slot V} {k p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) (hb : bit V k p = true) :
    colOf s = k := by
  rw [colOf_val hs]; simp [hp, hb]

omit hV in
theorem block_col_false {s : Slot V} {k p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) (hb : bit V k p = false) :
    colOf s = k - 1 := by
  rw [colOf_val hs]; simp [hp, hb]

omit hV in
theorem block_col_vertex {s : Slot V} {k : ℕ} (hs : s.1 = (k, 0)) : colOf s = k := by
  rw [colOf_val hs]; simp

/-- one more step of a block passage (the current slot is inside the block) -/
theorem passage_step (Ext : ℕ → Prop) {b c : Slot V} (hb : ¬ Ext (colOf b))
    (h : ∃ n, (next hV)^[n] (next hV b) = c ∧ ∀ i < n, ¬ Ext (colOf ((next hV)^[i] (next hV b)))) :
    ∃ n, (next hV)^[n] b = c ∧ ∀ i < n, ¬ Ext (colOf ((next hV)^[i] b)) := by
  obtain ⟨n, hc, hmin⟩ := h
  refine ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hc, ?_⟩
  intro i hi
  cases i with
  | zero => simpa using hb
  | succ i => rw [Function.iterate_succ_apply]; exact hmin i (by omega)

theorem passage_end {Ext : ℕ → Prop} {b : Slot V} :
    ∃ n, (next hV)^[n] b = b ∧ ∀ i < n, ¬ Ext (colOf ((next hV)^[i] b)) :=
  ⟨0, rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

end Passages

/-! #### E. The zigzag deletion (ng:deletions, `l_m r_{m+1}` below / `l_{m+1} r_m` above) -/

section Zigzag

variable (X Y : Word) (m : ℕ) (d : Bool)

theorem zb_letters :
    letterAt (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y) X.length = .l m d ∧
    letterAt (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y) (X.length + 1) = .r (m + 1) := by
  constructor
  · have := letterAt_block X [Letter.l m d, Letter.r (m + 1)] Y (i := 0) (by simp)
    simpa using this
  · have := letterAt_block X [Letter.l m d, Letter.r (m + 1)] Y (i := 1) (by simp)
    simpa using this

theorem zb_length : (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y).length = X.length + 2 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem bool_eq_of_not_ne {d b : Bool} (h : (!d) ≠ b) : b = d := by cases d <;> cases b <;> simp_all

variable (hW : (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y).Closed)
include hW

/-- the bits of the middle cut at the zigzag: `d`, `!d` (the arms), `d` (the strand below) -/
theorem zb_bits :
    bit (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y) (X.length + 1) m = d ∧
    bit (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y) (X.length + 1) (m + 1) = !d ∧
    bit (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y) (X.length + 1) (m + 2) = d := by
  obtain ⟨hℓ₀, hℓ₁⟩ := zb_letters X Y m d
  have hk₀ : X.length < (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y).length := by rw [zb_length]; omega
  have hk₁ : X.length + 1 < (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y).length := by rw [zb_length]; omega
  obtain ⟨-, h1, h2⟩ := l_bits hW hk₀ hℓ₀
  obtain ⟨-, h3⟩ := r_bits hW hk₁ hℓ₁
  rw [h2] at h3
  exact ⟨h1, h2, bool_eq_of_not_ne h3⟩

local notation "Vz" => X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y
local notation "Pz" => [Letter.l m d, Letter.r (m + 1)]

omit hW in
theorem zb_extCol (k : ℕ) : ExtCol X Pz k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k := by
  unfold ExtCol; simp

omit hW in
theorem zb_shift : shiftIdx X Pz [] (X.length + 2) = X.length := by
  unfold shiftIdx; simp

/-! the successor table of the block `l_m r_{m+1}` (columns `|X|`, `|X|+1`) -/

theorem zb_T1 {s : Slot Vz} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vz X.length p = true)
    (hpm : p < m) : (next hW s).1 = (X.length + 1, p) ∧ bit Vz (X.length + 1) p = true :=
  next_right_lt hW hs hp hb (by rw [(zb_letters X Y m d).1]; exact hpm)

theorem zb_T2 {s : Slot Vz} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vz X.length p = true)
    (hpm : m ≤ p) : (next hW s).1 = (X.length + 1, p + 2) ∧ bit Vz (X.length + 1) (p + 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(zb_letters X Y m d).1]; simpa [idx, arity] using hpm)
  rwa [(zb_letters X Y m d).1] at this

theorem zb_T3 {s : Slot Vz} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vz (X.length + 1) p = true) (hpm : p < m + 1) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Vz (X.length + 2) p = true :=
  next_right_lt hW hs hp hb (by rw [(zb_letters X Y m d).2]; exact hpm)

theorem zb_T4 {s : Slot Vz} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vz (X.length + 1) p = true) (hpm : m + 3 ≤ p) :
    (next hW s).1 = (X.length + 2, p - 2) ∧ bit Vz (X.length + 2) (p - 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(zb_letters X Y m d).2]; simpa [idx, arity] using hpm)
  rw [(zb_letters X Y m d).2] at this
  simpa [coarity, arity] using this

theorem zb_T5 {s : Slot Vz} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p = m + 1 ∨ p = m + 2)
    (hb : bit Vz (X.length + 1) p = true) : (next hW s).1 = (X.length + 1, 0) :=
  next_arm_r hW (slot_col_lt hW hs) (zb_letters X Y m d).2 hs (by omega) hb

theorem zb_T6 {s : Slot Vz} (hs : s.1 = (X.length + 1, 0)) :
    (next hW s).1 = (X.length + 1, if d then m + 1 else m + 2) := by
  rw [next_cusp_r hW (zb_letters X Y m d).2 hs, (zb_bits X Y m d hW).2.1]
  cases d <;> rfl

theorem zb_T7 {s : Slot Vz} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vz (X.length + 1) q = false) (hqm : q < m) :
    (next hW s).1 = (X.length, q) ∧ bit Vz X.length q = false := by
  have := next_left_lt hW hs hq hb (by rw [Nat.add_sub_cancel, (zb_letters X Y m d).1]; exact hqm)
  rwa [Nat.add_sub_cancel] at this

theorem zb_T8 {s : Slot Vz} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q = m ∨ q = m + 1)
    (hb : bit Vz (X.length + 1) q = false) : (next hW s).1 = (X.length, 0) :=
  next_arm_l hW (by have := slot_col_lt hW hs; omega) (zb_letters X Y m d).1 hs hq hb

theorem zb_T9 {s : Slot Vz} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vz (X.length + 1) q = false) (hqm : m + 2 ≤ q) :
    (next hW s).1 = (X.length, q - 2) ∧ bit Vz X.length (q - 2) = false := by
  have := next_left_ge hW hs hq hb (by rw [Nat.add_sub_cancel, (zb_letters X Y m d).1]; simpa [idx, coarity] using hqm)
  rw [Nat.add_sub_cancel, (zb_letters X Y m d).1] at this
  simpa [arity, coarity] using this

theorem zb_T10 {s : Slot Vz} (hs : s.1 = (X.length, 0)) :
    (next hW s).1 = (X.length + 1, if d then m else m + 1) :=
  next_cusp_l hW (zb_letters X Y m d).1 hs

theorem zb_T11 {s : Slot Vz} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vz (X.length + 2) q = false) (hqm : q < m + 1) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Vz (X.length + 1) q = false := by
  have e : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_lt hW hs hq hb (by rw [e, (zb_letters X Y m d).2]; exact hqm)
  rwa [e] at this

theorem zb_T12 {s : Slot Vz} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vz (X.length + 2) q = false) (hqm : m + 1 ≤ q) :
    (next hW s).1 = (X.length + 1, q + 2) ∧ bit Vz (X.length + 1) (q + 2) = false := by
  have e : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_ge hW hs hq hb (by rw [e, (zb_letters X Y m d).2]; simpa [idx, coarity] using hqm)
  rw [e, (zb_letters X Y m d).2] at this
  simpa [arity, coarity] using this

/-- the traversal from the left-cusp vertex reaches the exterior -/
theorem zb_reach_v0 {u : Slot Vz} (hu : u.1 = (X.length, 0)) :
    ∃ n, ExtPiece X Pz Y ((next hW)^[n] u) := by
  obtain ⟨B1, B2, B3⟩ := zb_bits X Y m d hW
  have hm1 : 1 ≤ m := (l_bits hW (vertex_lt hu) (zb_letters X Y m d).1).1
  have h1 := zb_T10 X Y m d hW hu
  rcases Bool.eq_false_or_eq_true d with hd | hd
  · rw [ite_eq_left hd] at h1
    have hb1 : bit Vz (X.length + 1) m = true := by rw [B1, hd]
    obtain ⟨h2, hb2⟩ := zb_T3 X Y m d hW h1 (by omega) hb1 (by omega)
    refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
    show ExtCol X Pz (colOf _)
    rw [block_col_true h2 (by omega) hb2, zb_extCol]; omega
  · rw [ite_eq_right (by simp [hd])] at h1
    have hb1 : bit Vz (X.length + 1) (m + 1) = true := by rw [B2, hd]; rfl
    have h2 := zb_T5 X Y m d hW h1 (Or.inl rfl) hb1
    have h3 := zb_T6 X Y m d hW h2
    rw [ite_eq_right (by simp [hd])] at h3
    have hb3 : bit Vz (X.length + 1) (m + 2) = false := by rw [B3, hd]
    obtain ⟨h4, hb4⟩ := zb_T9 X Y m d hW h3 (by omega) hb3 le_rfl
    refine reach_of_next hW (reach_of_next hW (reach_of_next hW (reach_of_next hW (reach_self hW ?_))))
    show ExtCol X Pz (colOf _)
    have hk := (cutSlot_facts hW h4 (by omega)).2.2.1
    rw [block_col_false h4 (by omega) hb4, zb_extCol]; omega

/-- the traversal from the right-cusp vertex reaches the exterior -/
theorem zb_reach_v1 {u : Slot Vz} (hu : u.1 = (X.length + 1, 0)) :
    ∃ n, ExtPiece X Pz Y ((next hW)^[n] u) := by
  obtain ⟨B1, B2, B3⟩ := zb_bits X Y m d hW
  have hm1 : 1 ≤ m := (l_bits hW (by have := vertex_lt hu; omega) (zb_letters X Y m d).1).1
  have h1 := zb_T6 X Y m d hW hu
  rcases Bool.eq_false_or_eq_true d with hd | hd
  · rw [ite_eq_left hd] at h1
    have hb1 : bit Vz (X.length + 1) (m + 1) = false := by rw [B2, hd]; rfl
    have h2 := zb_T8 X Y m d hW h1 (Or.inr rfl) hb1
    exact reach_of_next hW (reach_of_next hW (zb_reach_v0 X Y m d hW h2))
  · rw [ite_eq_right (by simp [hd])] at h1
    have hb1 : bit Vz (X.length + 1) (m + 2) = false := by rw [B3, hd]
    obtain ⟨h2, hb2⟩ := zb_T9 X Y m d hW h1 (by omega) hb1 le_rfl
    refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
    show ExtCol X Pz (colOf _)
    have hk := (cutSlot_facts hW h2 (by omega)).2.2.1
    rw [block_col_false h2 (by omega) hb2, zb_extCol]; omega

/-- every component of the zigzag word meets the exterior -/
theorem zb_hexit : ∀ u : Slot Vz, ∃ n, ExtPiece X Pz Y ((next hW)^[n] u) := by
  intro u
  obtain ⟨B1, B2, B3⟩ := zb_bits X Y m d hW
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  by_cases hext : ExtCol X Pz (colOf u)
  · exact reach_self hW hext
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, zb_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · exact zb_reach_v0 X Y m d hW hu
    · exact zb_reach_v1 X Y m d hW hu
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hW hu hp
  have hm1 : 1 ≤ m := (l_bits hW (by rw [zb_length]; omega) (zb_letters X Y m d).1).1
  cases hb : bit Vz k p
  · rw [block_col_false hu hp hb, zb_extCol] at hext
    have : k = X.length + 1 ∨ k = X.length + 2 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := zb_T7 X Y m d hW hu hp hb hpm
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pz (colOf _)
        have := (cutSlot_facts hW h1 hp).2.2.1
        rw [block_col_false h1 hp hb1, zb_extCol]; omega
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have h1 := zb_T8 X Y m d hW hu (by omega) hb
        exact reach_of_next hW (zb_reach_v0 X Y m d hW h1)
      · obtain ⟨h1, hb1⟩ := zb_T9 X Y m d hW hu hp hb hpm2
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pz (colOf _)
        have := (cutSlot_facts hW h1 (by omega)).2.2.1
        rw [block_col_false h1 (by omega) hb1, zb_extCol]; omega
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · obtain ⟨h1, hb1⟩ := zb_T11 X Y m d hW hu hp hb hpm
        rcases lt_or_ge p m with hpm' | hpm'
        · obtain ⟨h2, hb2⟩ := zb_T7 X Y m d hW h1 hp hb1 hpm'
          refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
          show ExtCol X Pz (colOf _)
          have := (cutSlot_facts hW h2 hp).2.2.1
          rw [block_col_false h2 hp hb2, zb_extCol]; omega
        · have h2 := zb_T8 X Y m d hW h1 (by omega) hb1
          exact reach_of_next hW (reach_of_next hW (zb_reach_v0 X Y m d hW h2))
      · obtain ⟨h1, hb1⟩ := zb_T12 X Y m d hW hu hp hb hpm
        obtain ⟨h2, hb2⟩ := zb_T9 X Y m d hW h1 (by omega) hb1 (by omega)
        refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pz (colOf _)
        have := (cutSlot_facts hW h2 (by omega)).2.2.1
        rw [block_col_false h2 (by omega) hb2, zb_extCol]; omega
  · rw [block_col_true hu hp hb, zb_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := zb_T1 X Y m d hW hu hp hb hpm
        obtain ⟨h2, hb2⟩ := zb_T3 X Y m d hW h1 hp hb1 (by omega)
        refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pz (colOf _)
        rw [block_col_true h2 hp hb2, zb_extCol]; omega
      · obtain ⟨h1, hb1⟩ := zb_T2 X Y m d hW hu hp hb hpm
        rcases Nat.eq_or_lt_of_le hpm with rfl | hpm1
        · have h2 := zb_T5 X Y m d hW h1 (Or.inr rfl) hb1
          exact reach_of_next hW (reach_of_next hW (zb_reach_v1 X Y m d hW h2))
        · obtain ⟨h2, hb2⟩ := zb_T4 X Y m d hW h1 (by omega) hb1 (by omega)
          refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
          show ExtCol X Pz (colOf _)
          rw [block_col_true h2 (by omega) hb2, zb_extCol]; omega
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · obtain ⟨h1, hb1⟩ := zb_T3 X Y m d hW hu hp hb hpm
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pz (colOf _)
        rw [block_col_true h1 hp hb1, zb_extCol]; omega
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have h1 := zb_T5 X Y m d hW hu (by omega) hb
        exact reach_of_next hW (zb_reach_v1 X Y m d hW h1)
      · obtain ⟨h1, hb1⟩ := zb_T4 X Y m d hW hu hp hb hpm3
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pz (colOf _)
        rw [block_col_true h1 (by omega) hb1, zb_extCol]; omega

theorem zb_sameEffect : SameEffect X Pz [] := by
  have hm1 : 1 ≤ m := (l_bits hW (by rw [zb_length]; omega) (zb_letters X Y m d).1).1
  exact sameEffect_of_replace X Pz Y [] hW (fun c c' h => by obtain rfl := run_zigzag_below hm1 h; rfl)

/-- THE BLOCK PASSAGE of the zigzag `l_m r_{m+1}`: every entering strand exits at its own position. -/
theorem zb_passage (hW' : (X ++ [] ++ Y).Closed) : Passage X Pz Y [] hW hW' := by
  obtain ⟨hℓ₀, hℓ₁⟩ := zb_letters X Y m d
  obtain ⟨B1, B2, B3⟩ := zb_bits X Y m d hW
  have hm1 : 1 ≤ m := (l_bits hW (by rw [zb_length]; omega) hℓ₀).1
  have hP : Pz ≠ [] := by simp
  have hE := zb_sameEffect X Y m d hW
  constructor
  intro b hext hcol
  have side : ∀ {c : Slot Vz}, extPair X Pz [] b.1 = extPair X Pz [] c.1 →
      ∃ (m' : ℕ) (b' : Slot (X ++ [] ++ Y)), b'.1 = extPair X Pz [] b.1 ∧
        ((next hW')^[m'] b').1 = extPair X Pz [] c.1 ∧ ∀ i < m', ¬ ExtCol X [] (colOf ((next hW')^[i] b')) :=
    fun hbc => ⟨0, ⟨_, isSlot_ext X Pz Y [] hP hE b.2 hext⟩, rfl, hbc, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  have shiftL : ∀ p, extPair X Pz [] (X.length, p) = extPair X Pz [] (X.length + 2, p) := by
    intro p; simp only [extPair, shiftIdx_of_le X Pz [] le_rfl, zb_shift X m d]
  rcases (entry_iff X Pz Y hP hW b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
  · -- from the left at `(|X|, p)`
    rcases lt_or_ge p m with hpm | hpm
    · obtain ⟨h1, hb1⟩ := zb_T1 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := zb_T3 X Y m d hW h1 hp hb1 (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pz)
        (by rw [block_col_true hb hp hbit, zb_extCol]; omega)
        (passage_step hW (ExtCol X Pz) (by rw [block_col_true h1 hp hb1, zb_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · rw [block_col_true h2 hp hb2, zb_extCol]; omega
      · rw [hb, h2]; exact shiftL p
    rcases Nat.eq_or_lt_of_le hpm with hpe | hpm1
    · -- `p = m`: through the zigzag
      obtain ⟨h1, hb1⟩ := zb_T2 X Y m d hW hb hp hbit hpm
      rw [← hpe] at h1 hb1
      have hd : d = true := by rw [B3] at hb1; exact hb1
      have h2 := zb_T5 X Y m d hW h1 (Or.inr rfl) hb1
      have h3 := zb_T6 X Y m d hW h2
      rw [ite_eq_left hd] at h3
      have hb3 : bit Vz (X.length + 1) (m + 1) = false := by rw [B2, hd]; rfl
      have h4 := zb_T8 X Y m d hW h3 (Or.inr rfl) hb3
      have h5 := zb_T10 X Y m d hW h4
      rw [ite_eq_left hd] at h5
      have hb5 : bit Vz (X.length + 1) m = true := by rw [B1, hd]
      obtain ⟨h6, hb6⟩ := zb_T3 X Y m d hW h5 (by omega) hb5 (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pz)
        (by rw [block_col_true hb hp hbit, zb_extCol]; omega)
        (passage_step hW (ExtCol X Pz) (by rw [block_col_true h1 (by omega) hb1, zb_extCol]; omega)
        (passage_step hW (ExtCol X Pz) (by rw [block_col_vertex h2, zb_extCol]; omega)
        (passage_step hW (ExtCol X Pz) (by rw [block_col_false h3 (by omega) hb3, zb_extCol]; omega)
        (passage_step hW (ExtCol X Pz) (by rw [block_col_vertex h4, zb_extCol]; omega)
        (passage_step hW (ExtCol X Pz) (by rw [block_col_true h5 (by omega) hb5, zb_extCol]; omega) (passage_end hW))))))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · rw [block_col_true h6 (by omega) hb6, zb_extCol]; omega
      · rw [hb, h6, ← hpe]; exact shiftL m
    · obtain ⟨h1, hb1⟩ := zb_T2 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := zb_T4 X Y m d hW h1 (by omega) hb1 (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pz)
        (by rw [block_col_true hb hp hbit, zb_extCol]; omega)
        (passage_step hW (ExtCol X Pz) (by rw [block_col_true h1 (by omega) hb1, zb_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · rw [block_col_true h2 (by omega) hb2, zb_extCol]; omega
      · rw [hb, h2, show p + 2 - 2 = p by omega]; exact shiftL p
  · -- from the right at `(|X|+2, p)`
    replace hb : b.1 = (X.length + 2, p) := hb
    replace hbit : bit Vz (X.length + 2) p = false := hbit
    rcases lt_or_ge p (m + 1) with hpm | hpm
    · obtain ⟨h1, hb1⟩ := zb_T11 X Y m d hW hb hp hbit hpm
      rcases lt_or_ge p m with hpm' | hpm'
      · obtain ⟨h2, hb2⟩ := zb_T7 X Y m d hW h1 hp hb1 hpm'
        obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pz)
          (by rw [block_col_false hb hp hbit, zb_extCol]; omega)
          (passage_step hW (ExtCol X Pz) (by rw [block_col_false h1 hp hb1, zb_extCol]; omega) (passage_end hW))
        refine ⟨n, _, hc, ?_, hmin, side ?_⟩
        · have := (cutSlot_facts hW h2 hp).2.2.1
          rw [block_col_false h2 hp hb2, zb_extCol]; omega
        · rw [hb, h2]; exact (shiftL p).symm
      · -- `p = m`: through the zigzag, from the right
        have hpe : p = m := by omega
        rw [hpe] at h1 hb1
        have hd : d = false := by rw [B1] at hb1; exact hb1
        have h2 := zb_T8 X Y m d hW h1 (Or.inl rfl) hb1
        have h3 := zb_T10 X Y m d hW h2
        rw [ite_eq_right (by simp [hd])] at h3
        have hb3 : bit Vz (X.length + 1) (m + 1) = true := by rw [B2, hd]; rfl
        have h4 := zb_T5 X Y m d hW h3 (Or.inl rfl) hb3
        have h5 := zb_T6 X Y m d hW h4
        rw [ite_eq_right (by simp [hd])] at h5
        have hb5 : bit Vz (X.length + 1) (m + 2) = false := by rw [B3, hd]
        obtain ⟨h6, hb6⟩ := zb_T9 X Y m d hW h5 (by omega) hb5 le_rfl
        rw [show m + 2 - 2 = m by omega] at h6 hb6
        obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pz)
          (by rw [block_col_false hb hp hbit, zb_extCol]; omega)
          (passage_step hW (ExtCol X Pz) (by rw [block_col_false h1 (by omega) hb1, zb_extCol]; omega)
          (passage_step hW (ExtCol X Pz) (by rw [block_col_vertex h2, zb_extCol]; omega)
          (passage_step hW (ExtCol X Pz) (by rw [block_col_true h3 (by omega) hb3, zb_extCol]; omega)
          (passage_step hW (ExtCol X Pz) (by rw [block_col_vertex h4, zb_extCol]; omega)
          (passage_step hW (ExtCol X Pz) (by rw [block_col_false h5 (by omega) hb5, zb_extCol]; omega) (passage_end hW))))))
        refine ⟨n, _, hc, ?_, hmin, side ?_⟩
        · have := (cutSlot_facts hW h6 (by omega)).2.2.1
          rw [block_col_false h6 (by omega) hb6, zb_extCol]; omega
        · rw [hb, h6, hpe]; exact (shiftL m).symm
    · obtain ⟨h1, hb1⟩ := zb_T12 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := zb_T9 X Y m d hW h1 (by omega) hb1 (by omega)
      rw [show p + 2 - 2 = p by omega] at h2 hb2
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pz)
        (by rw [block_col_false hb hp hbit, zb_extCol]; omega)
        (passage_step hW (ExtCol X Pz) (by rw [block_col_false h1 (by omega) hb1, zb_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · have := (cutSlot_facts hW h2 hp).2.2.1
        rw [block_col_false h2 hp hb2, zb_extCol]; omega
      · rw [hb, h2]; exact (shiftL p).symm

/-- LEAF `zigzag_recordIso`, the `l_m r_{m+1}` case. -/
theorem zb_recordIso (W W' : OWord) (hWeq : W.letters = Vz) (hW'eq : W'.letters = X ++ Y)
    (hne' : W'.letters ≠ []) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := by
  have hW' : (X ++ [] ++ Y).Closed := by have := W'.closed; rw [hW'eq] at this; simpa using this
  refine realize_recordIso_of_ext X Pz Y [] (by simp) (zb_sameEffect X Y m d hW) hW hW' (by simp)
    (by rw [hW'eq] at hne'; simpa using hne') (zb_passage X Y m d hW hW') (zb_hexit X Y m d hW) ?_ ?_ ?_
    W W' hWeq (by simpa using hW'eq)
  · intro u; exact ⟨0, by show ExtCol X [] (colOf u); unfold ExtCol; simp; omega⟩
  · intro k hk1 hk2
    simp only [List.length_cons, List.length_nil] at hk2
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rw [(zb_letters X Y m d).1]; rfl
    · rw [(zb_letters X Y m d).2]; rfl
  · intro k hk1 hk2; simp at hk2; omega

end Zigzag

section ZigzagAbove

variable (X Y : Word) (m : ℕ) (d : Bool)

local notation "Va" => X ++ [Letter.l (m + 1) d, Letter.r m] ++ Y
local notation "Pa" => [Letter.l (m + 1) d, Letter.r m]

theorem za_letters : letterAt Va X.length = .l (m + 1) d ∧ letterAt Va (X.length + 1) = .r m := by
  constructor
  · have := letterAt_block X Pa Y (i := 0) (by simp)
    simpa using this
  · have := letterAt_block X Pa Y (i := 1) (by simp)
    simpa using this

theorem za_length : (X ++ [Letter.l (m + 1) d, Letter.r m] ++ Y).length = X.length + 2 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem za_extCol (k : ℕ) : ExtCol X Pa k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k := by
  unfold ExtCol; simp

theorem za_shift : shiftIdx X Pa [] (X.length + 2) = X.length := by
  unfold shiftIdx; simp

theorem bool_eq_not_of_ne {b d : Bool} (h : b ≠ d) : b = !d := by cases d <;> cases b <;> simp_all

variable (hW : (X ++ [Letter.l (m + 1) d, Letter.r m] ++ Y).Closed)
include hW

/-- the bits of the middle cut: `!d` (the strand above), `d`, `!d` (the arms) -/
theorem za_bits :
    bit Va (X.length + 1) m = !d ∧ bit Va (X.length + 1) (m + 1) = d ∧ bit Va (X.length + 1) (m + 2) = !d := by
  obtain ⟨hℓ₀, hℓ₁⟩ := za_letters X Y m d
  have hk₀ : X.length < (Va).length := by rw [za_length]; omega
  have hk₁ : X.length + 1 < (Va).length := by rw [za_length]; omega
  obtain ⟨-, h1, h2⟩ := l_bits hW hk₀ hℓ₀
  obtain ⟨-, h3⟩ := r_bits hW hk₁ hℓ₁
  rw [h1] at h3
  exact ⟨bool_eq_not_of_ne h3, h1, h2⟩

theorem za_m_pos : 1 ≤ m :=
  (r_bits hW (by rw [za_length]; omega) (za_letters X Y m d).2).1

theorem za_T1 {s : Slot Va} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Va X.length p = true)
    (hpm : p < m + 1) : (next hW s).1 = (X.length + 1, p) ∧ bit Va (X.length + 1) p = true :=
  next_right_lt hW hs hp hb (by rw [(za_letters X Y m d).1]; exact hpm)

theorem za_T2 {s : Slot Va} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Va X.length p = true)
    (hpm : m + 1 ≤ p) : (next hW s).1 = (X.length + 1, p + 2) ∧ bit Va (X.length + 1) (p + 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(za_letters X Y m d).1]; simpa [idx, arity] using hpm)
  rwa [(za_letters X Y m d).1] at this

theorem za_T3 {s : Slot Va} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Va (X.length + 1) p = true) (hpm : p < m) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Va (X.length + 2) p = true :=
  next_right_lt hW hs hp hb (by rw [(za_letters X Y m d).2]; exact hpm)

theorem za_T4 {s : Slot Va} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Va (X.length + 1) p = true) (hpm : m + 2 ≤ p) :
    (next hW s).1 = (X.length + 2, p - 2) ∧ bit Va (X.length + 2) (p - 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(za_letters X Y m d).2]; simpa [idx, arity] using hpm)
  rw [(za_letters X Y m d).2] at this
  simpa [coarity, arity] using this

theorem za_T5 {s : Slot Va} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p = m ∨ p = m + 1)
    (hb : bit Va (X.length + 1) p = true) : (next hW s).1 = (X.length + 1, 0) :=
  next_arm_r hW (slot_col_lt hW hs) (za_letters X Y m d).2 hs hp hb

theorem za_T6 {s : Slot Va} (hs : s.1 = (X.length + 1, 0)) :
    (next hW s).1 = (X.length + 1, if d then m else m + 1) := by
  rw [next_cusp_r hW (za_letters X Y m d).2 hs, (za_bits X Y m d hW).1]
  cases d <;> rfl

theorem za_T7 {s : Slot Va} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Va (X.length + 1) q = false) (hqm : q < m + 1) :
    (next hW s).1 = (X.length, q) ∧ bit Va X.length q = false := by
  have := next_left_lt hW hs hq hb (by rw [Nat.add_sub_cancel, (za_letters X Y m d).1]; exact hqm)
  rwa [Nat.add_sub_cancel] at this

theorem za_T8 {s : Slot Va} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q = m + 1 ∨ q = m + 2)
    (hb : bit Va (X.length + 1) q = false) : (next hW s).1 = (X.length, 0) :=
  next_arm_l hW (by have := slot_col_lt hW hs; omega) (za_letters X Y m d).1 hs hq hb

theorem za_T9 {s : Slot Va} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Va (X.length + 1) q = false) (hqm : m + 3 ≤ q) :
    (next hW s).1 = (X.length, q - 2) ∧ bit Va X.length (q - 2) = false := by
  have := next_left_ge hW hs hq hb (by rw [Nat.add_sub_cancel, (za_letters X Y m d).1]; simpa [idx, coarity] using hqm)
  rw [Nat.add_sub_cancel, (za_letters X Y m d).1] at this
  simpa [arity, coarity] using this

theorem za_T10 {s : Slot Va} (hs : s.1 = (X.length, 0)) :
    (next hW s).1 = (X.length + 1, if d then m + 1 else m + 2) :=
  next_cusp_l hW (za_letters X Y m d).1 hs

theorem za_T11 {s : Slot Va} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Va (X.length + 2) q = false) (hqm : q < m) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Va (X.length + 1) q = false := by
  have e : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_lt hW hs hq hb (by rw [e, (za_letters X Y m d).2]; exact hqm)
  rwa [e] at this

theorem za_T12 {s : Slot Va} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Va (X.length + 2) q = false) (hqm : m ≤ q) :
    (next hW s).1 = (X.length + 1, q + 2) ∧ bit Va (X.length + 1) (q + 2) = false := by
  have e : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_ge hW hs hq hb (by rw [e, (za_letters X Y m d).2]; simpa [idx, coarity] using hqm)
  rw [e, (za_letters X Y m d).2] at this
  simpa [arity, coarity] using this

theorem za_reach_v0 {u : Slot Va} (hu : u.1 = (X.length, 0)) :
    ∃ n, ExtPiece X Pa Y ((next hW)^[n] u) := by
  obtain ⟨B1, B2, B3⟩ := za_bits X Y m d hW
  have hm1 := za_m_pos X Y m d hW
  have h1 := za_T10 X Y m d hW hu
  rcases Bool.eq_false_or_eq_true d with hd | hd
  · rw [ite_eq_left hd] at h1
    have hb1 : bit Va (X.length + 1) (m + 1) = true := by rw [B2, hd]
    have h2 := za_T5 X Y m d hW h1 (Or.inr rfl) hb1
    have h3 := za_T6 X Y m d hW h2
    rw [ite_eq_left hd] at h3
    have hb3 : bit Va (X.length + 1) m = false := by rw [B1, hd]; rfl
    obtain ⟨h4, hb4⟩ := za_T7 X Y m d hW h3 (by omega) hb3 (by omega)
    refine reach_of_next hW (reach_of_next hW (reach_of_next hW (reach_of_next hW (reach_self hW ?_))))
    show ExtCol X Pa (colOf _)
    have hk := (cutSlot_facts hW h4 (by omega)).2.2.1
    rw [block_col_false h4 (by omega) hb4, za_extCol]; omega
  · rw [ite_eq_right (by simp [hd])] at h1
    have hb1 : bit Va (X.length + 1) (m + 2) = true := by rw [B3, hd]; rfl
    obtain ⟨h2, hb2⟩ := za_T4 X Y m d hW h1 (by omega) hb1 le_rfl
    refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
    show ExtCol X Pa (colOf _)
    rw [block_col_true h2 (by omega) hb2, za_extCol]; omega

theorem za_reach_v1 {u : Slot Va} (hu : u.1 = (X.length + 1, 0)) :
    ∃ n, ExtPiece X Pa Y ((next hW)^[n] u) := by
  obtain ⟨B1, B2, B3⟩ := za_bits X Y m d hW
  have hm1 := za_m_pos X Y m d hW
  have h1 := za_T6 X Y m d hW hu
  rcases Bool.eq_false_or_eq_true d with hd | hd
  · rw [ite_eq_left hd] at h1
    have hb1 : bit Va (X.length + 1) m = false := by rw [B1, hd]; rfl
    obtain ⟨h2, hb2⟩ := za_T7 X Y m d hW h1 (by omega) hb1 (by omega)
    refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
    show ExtCol X Pa (colOf _)
    have hk := (cutSlot_facts hW h2 (by omega)).2.2.1
    rw [block_col_false h2 (by omega) hb2, za_extCol]; omega
  · rw [ite_eq_right (by simp [hd])] at h1
    have hb1 : bit Va (X.length + 1) (m + 1) = false := by rw [B2, hd]
    have h2 := za_T8 X Y m d hW h1 (Or.inl rfl) hb1
    exact reach_of_next hW (reach_of_next hW (za_reach_v0 X Y m d hW h2))

theorem za_hexit : ∀ u : Slot Va, ∃ n, ExtPiece X Pa Y ((next hW)^[n] u) := by
  intro u
  obtain ⟨B1, B2, B3⟩ := za_bits X Y m d hW
  have hm1 := za_m_pos X Y m d hW
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  by_cases hext : ExtCol X Pa (colOf u)
  · exact reach_self hW hext
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, za_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · exact za_reach_v0 X Y m d hW hu
    · exact za_reach_v1 X Y m d hW hu
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hW hu hp
  cases hb : bit Va k p
  · rw [block_col_false hu hp hb, za_extCol] at hext
    have : k = X.length + 1 ∨ k = X.length + 2 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · obtain ⟨h1, hb1⟩ := za_T7 X Y m d hW hu hp hb hpm
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pa (colOf _)
        have := (cutSlot_facts hW h1 hp).2.2.1
        rw [block_col_false h1 hp hb1, za_extCol]; omega
      rcases lt_or_ge p (m + 3) with hpm2 | hpm2
      · have h1 := za_T8 X Y m d hW hu (by omega) hb
        exact reach_of_next hW (za_reach_v0 X Y m d hW h1)
      · obtain ⟨h1, hb1⟩ := za_T9 X Y m d hW hu hp hb hpm2
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pa (colOf _)
        have := (cutSlot_facts hW h1 (by omega)).2.2.1
        rw [block_col_false h1 (by omega) hb1, za_extCol]; omega
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := za_T11 X Y m d hW hu hp hb hpm
        obtain ⟨h2, hb2⟩ := za_T7 X Y m d hW h1 hp hb1 (by omega)
        refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pa (colOf _)
        have := (cutSlot_facts hW h2 hp).2.2.1
        rw [block_col_false h2 hp hb2, za_extCol]; omega
      · obtain ⟨h1, hb1⟩ := za_T12 X Y m d hW hu hp hb hpm
        rcases Nat.eq_or_lt_of_le hpm with hpe | hpm1
        · have h2 := za_T8 X Y m d hW h1 (by omega) hb1
          exact reach_of_next hW (reach_of_next hW (za_reach_v0 X Y m d hW h2))
        · obtain ⟨h2, hb2⟩ := za_T9 X Y m d hW h1 (by omega) hb1 (by omega)
          refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
          show ExtCol X Pa (colOf _)
          have := (cutSlot_facts hW h2 (by omega)).2.2.1
          rw [block_col_false h2 (by omega) hb2, za_extCol]; omega
  · rw [block_col_true hu hp hb, za_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · obtain ⟨h1, hb1⟩ := za_T1 X Y m d hW hu hp hb hpm
        rcases lt_or_ge p m with hpm' | hpm'
        · obtain ⟨h2, hb2⟩ := za_T3 X Y m d hW h1 hp hb1 hpm'
          refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
          show ExtCol X Pa (colOf _)
          rw [block_col_true h2 hp hb2, za_extCol]; omega
        · have h2 := za_T5 X Y m d hW h1 (by omega) hb1
          exact reach_of_next hW (reach_of_next hW (za_reach_v1 X Y m d hW h2))
      · obtain ⟨h1, hb1⟩ := za_T2 X Y m d hW hu hp hb hpm
        obtain ⟨h2, hb2⟩ := za_T4 X Y m d hW h1 (by omega) hb1 (by omega)
        refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pa (colOf _)
        rw [block_col_true h2 (by omega) hb2, za_extCol]; omega
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := za_T3 X Y m d hW hu hp hb hpm
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pa (colOf _)
        rw [block_col_true h1 hp hb1, za_extCol]; omega
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have h1 := za_T5 X Y m d hW hu (by omega) hb
        exact reach_of_next hW (za_reach_v1 X Y m d hW h1)
      · obtain ⟨h1, hb1⟩ := za_T4 X Y m d hW hu hp hb hpm2
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pa (colOf _)
        rw [block_col_true h1 (by omega) hb1, za_extCol]; omega

theorem za_sameEffect : SameEffect X Pa [] := by
  have hm1 := za_m_pos X Y m d hW
  exact sameEffect_of_replace X Pa Y [] hW (fun c c' h => by obtain rfl := run_zigzag_above hm1 h; rfl)

/-- THE BLOCK PASSAGE of the zigzag `l_{m+1} r_m`. -/
theorem za_passage (hW' : (X ++ [] ++ Y).Closed) : Passage X Pa Y [] hW hW' := by
  obtain ⟨hℓ₀, hℓ₁⟩ := za_letters X Y m d
  obtain ⟨B1, B2, B3⟩ := za_bits X Y m d hW
  have hm1 := za_m_pos X Y m d hW
  have hP : Pa ≠ [] := by simp
  have hE := za_sameEffect X Y m d hW
  constructor
  intro b hext hcol
  have side : ∀ {c : Slot Va}, extPair X Pa [] b.1 = extPair X Pa [] c.1 →
      ∃ (m' : ℕ) (b' : Slot (X ++ [] ++ Y)), b'.1 = extPair X Pa [] b.1 ∧
        ((next hW')^[m'] b').1 = extPair X Pa [] c.1 ∧ ∀ i < m', ¬ ExtCol X [] (colOf ((next hW')^[i] b')) :=
    fun hbc => ⟨0, ⟨_, isSlot_ext X Pa Y [] hP hE b.2 hext⟩, rfl, hbc, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  have shiftL : ∀ p, extPair X Pa [] (X.length, p) = extPair X Pa [] (X.length + 2, p) := by
    intro p; simp only [extPair, shiftIdx_of_le X Pa [] le_rfl, za_shift X m d]
  rcases (entry_iff X Pa Y hP hW b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
  · rcases lt_or_ge p (m + 1) with hpm | hpm
    · obtain ⟨h1, hb1⟩ := za_T1 X Y m d hW hb hp hbit hpm
      rcases lt_or_ge p m with hpm' | hpm'
      · obtain ⟨h2, hb2⟩ := za_T3 X Y m d hW h1 hp hb1 hpm'
        obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pa)
          (by rw [block_col_true hb hp hbit, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_true h1 hp hb1, za_extCol]; omega) (passage_end hW))
        refine ⟨n, _, hc, ?_, hmin, side ?_⟩
        · rw [block_col_true h2 hp hb2, za_extCol]; omega
        · rw [hb, h2]; exact shiftL p
      · -- `p = m`: through the zigzag
        have hpe : p = m := by omega
        rw [hpe] at h1 hb1
        have hd : d = false := by rw [B1] at hb1; cases d <;> simp_all
        have h2 := za_T5 X Y m d hW h1 (Or.inl rfl) hb1
        have h3 := za_T6 X Y m d hW h2
        rw [ite_eq_right (by simp [hd])] at h3
        have hb3 : bit Va (X.length + 1) (m + 1) = false := by rw [B2, hd]
        have h4 := za_T8 X Y m d hW h3 (Or.inl rfl) hb3
        have h5 := za_T10 X Y m d hW h4
        rw [ite_eq_right (by simp [hd])] at h5
        have hb5 : bit Va (X.length + 1) (m + 2) = true := by rw [B3, hd]; rfl
        obtain ⟨h6, hb6⟩ := za_T4 X Y m d hW h5 (by omega) hb5 le_rfl
        rw [show m + 2 - 2 = m by omega] at h6 hb6
        obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pa)
          (by rw [block_col_true hb hp hbit, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_true h1 (by omega) hb1, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_vertex h2, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_false h3 (by omega) hb3, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_vertex h4, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_true h5 (by omega) hb5, za_extCol]; omega)
            (passage_end hW))))))
        refine ⟨n, _, hc, ?_, hmin, side ?_⟩
        · rw [block_col_true h6 (by omega) hb6, za_extCol]; omega
        · rw [hb, h6, hpe]; exact shiftL m
    · obtain ⟨h1, hb1⟩ := za_T2 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := za_T4 X Y m d hW h1 (by omega) hb1 (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pa)
        (by rw [block_col_true hb hp hbit, za_extCol]; omega)
        (passage_step hW (ExtCol X Pa) (by rw [block_col_true h1 (by omega) hb1, za_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · rw [block_col_true h2 (by omega) hb2, za_extCol]; omega
      · rw [hb, h2, show p + 2 - 2 = p by omega]; exact shiftL p
  · replace hb : b.1 = (X.length + 2, p) := hb
    replace hbit : bit Va (X.length + 2) p = false := hbit
    rcases lt_or_ge p m with hpm | hpm
    · obtain ⟨h1, hb1⟩ := za_T11 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := za_T7 X Y m d hW h1 hp hb1 (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pa)
        (by rw [block_col_false hb hp hbit, za_extCol]; omega)
        (passage_step hW (ExtCol X Pa) (by rw [block_col_false h1 hp hb1, za_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · have := (cutSlot_facts hW h2 hp).2.2.1
        rw [block_col_false h2 hp hb2, za_extCol]; omega
      · rw [hb, h2]; exact (shiftL p).symm
    · obtain ⟨h1, hb1⟩ := za_T12 X Y m d hW hb hp hbit hpm
      rcases Nat.eq_or_lt_of_le hpm with hpe | hpm1
      · -- `p = m`: through the zigzag, from the right
        rw [← hpe] at h1 hb1
        have hd : d = true := by rw [B3] at hb1; cases d <;> simp_all
        have h2 := za_T8 X Y m d hW h1 (Or.inr rfl) hb1
        have h3 := za_T10 X Y m d hW h2
        rw [ite_eq_left hd] at h3
        have hb3 : bit Va (X.length + 1) (m + 1) = true := by rw [B2, hd]
        have h4 := za_T5 X Y m d hW h3 (Or.inr rfl) hb3
        have h5 := za_T6 X Y m d hW h4
        rw [ite_eq_left hd] at h5
        have hb5 : bit Va (X.length + 1) m = false := by rw [B1, hd]; rfl
        obtain ⟨h6, hb6⟩ := za_T7 X Y m d hW h5 (by omega) hb5 (by omega)
        obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pa)
          (by rw [block_col_false hb hp hbit, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_false h1 (by omega) hb1, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_vertex h2, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_true h3 (by omega) hb3, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_vertex h4, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_false h5 (by omega) hb5, za_extCol]; omega)
            (passage_end hW))))))
        refine ⟨n, _, hc, ?_, hmin, side ?_⟩
        · have := (cutSlot_facts hW h6 (by omega)).2.2.1
          rw [block_col_false h6 (by omega) hb6, za_extCol]; omega
        · rw [hb, h6, ← hpe]; exact (shiftL m).symm
      · obtain ⟨h2, hb2⟩ := za_T9 X Y m d hW h1 (by omega) hb1 (by omega)
        rw [show p + 2 - 2 = p by omega] at h2 hb2
        obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pa)
          (by rw [block_col_false hb hp hbit, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_false h1 (by omega) hb1, za_extCol]; omega) (passage_end hW))
        refine ⟨n, _, hc, ?_, hmin, side ?_⟩
        · have := (cutSlot_facts hW h2 hp).2.2.1
          rw [block_col_false h2 hp hb2, za_extCol]; omega
        · rw [hb, h2]; exact (shiftL p).symm

/-- LEAF `zigzag_recordIso`, the `l_{m+1} r_m` case. -/
theorem za_recordIso (W W' : OWord) (hWeq : W.letters = Va) (hW'eq : W'.letters = X ++ Y)
    (hne' : W'.letters ≠ []) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := by
  have hW' : (X ++ [] ++ Y).Closed := by have := W'.closed; rw [hW'eq] at this; simpa using this
  refine realize_recordIso_of_ext X Pa Y [] (by simp) (za_sameEffect X Y m d hW) hW hW' (by simp)
    (by rw [hW'eq] at hne'; simpa using hne') (za_passage X Y m d hW hW') (za_hexit X Y m d hW) ?_ ?_ ?_
    W W' hWeq (by simpa using hW'eq)
  · intro u; exact ⟨0, by show ExtCol X [] (colOf u); unfold ExtCol; simp; omega⟩
  · intro k hk1 hk2
    simp only [List.length_cons, List.length_nil] at hk2
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rw [(za_letters X Y m d).1]; rfl
    · rw [(za_letters X Y m d).2]; rfl
  · intro k hk1 hk2; simp at hk2; omega

end ZigzagAbove

/-! #### F. The circle deletion (ng:circle, `l_m r_m` a separated standard circle) -/

section Circle

variable (X Y : Word) (m : ℕ) (d : Bool)

local notation "Vc" => X ++ [Letter.l m d, Letter.r m] ++ Y
local notation "Pc" => [Letter.l m d, Letter.r m]

theorem ci_letters : letterAt Vc X.length = .l m d ∧ letterAt Vc (X.length + 1) = .r m := by
  constructor
  · have := letterAt_block X Pc Y (i := 0) (by simp)
    simpa using this
  · have := letterAt_block X Pc Y (i := 1) (by simp)
    simpa using this

theorem ci_length : (X ++ [Letter.l m d, Letter.r m] ++ Y).length = X.length + 2 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem ci_extCol (k : ℕ) : ExtCol X Pc k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k := by
  unfold ExtCol; simp

theorem ci_shift : shiftIdx X Pc [] (X.length + 2) = X.length := by
  unfold shiftIdx; simp

variable (hW : (X ++ [Letter.l m d, Letter.r m] ++ Y).Closed)
include hW

theorem ci_bits : bit Vc (X.length + 1) m = d ∧ bit Vc (X.length + 1) (m + 1) = !d :=
  (l_bits hW (by rw [ci_length]; omega) (ci_letters X Y m d).1).2

theorem ci_m_pos : 1 ≤ m := (l_bits hW (by rw [ci_length]; omega) (ci_letters X Y m d).1).1

theorem ci_T1 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vc X.length p = true)
    (hpm : p < m) : (next hW s).1 = (X.length + 1, p) ∧ bit Vc (X.length + 1) p = true :=
  next_right_lt hW hs hp hb (by rw [(ci_letters X Y m d).1]; exact hpm)

theorem ci_T2 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vc X.length p = true)
    (hpm : m ≤ p) : (next hW s).1 = (X.length + 1, p + 2) ∧ bit Vc (X.length + 1) (p + 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(ci_letters X Y m d).1]; simpa [idx, arity] using hpm)
  rwa [(ci_letters X Y m d).1] at this

theorem ci_T3 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vc (X.length + 1) p = true) (hpm : p < m) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Vc (X.length + 2) p = true :=
  next_right_lt hW hs hp hb (by rw [(ci_letters X Y m d).2]; exact hpm)

theorem ci_T4 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vc (X.length + 1) p = true) (hpm : m + 2 ≤ p) :
    (next hW s).1 = (X.length + 2, p - 2) ∧ bit Vc (X.length + 2) (p - 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(ci_letters X Y m d).2]; simpa [idx, arity] using hpm)
  rw [(ci_letters X Y m d).2] at this
  simpa [coarity, arity] using this

theorem ci_T5 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p = m ∨ p = m + 1)
    (hb : bit Vc (X.length + 1) p = true) : (next hW s).1 = (X.length + 1, 0) :=
  next_arm_r hW (slot_col_lt hW hs) (ci_letters X Y m d).2 hs hp hb

theorem ci_T6 {s : Slot Vc} (hs : s.1 = (X.length + 1, 0)) :
    (next hW s).1 = (X.length + 1, if d then m + 1 else m) := by
  rw [next_cusp_r hW (ci_letters X Y m d).2 hs, (ci_bits X Y m d hW).1]

theorem ci_T7 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 1) q = false) (hqm : q < m) :
    (next hW s).1 = (X.length, q) ∧ bit Vc X.length q = false := by
  have := next_left_lt hW hs hq hb (by rw [Nat.add_sub_cancel, (ci_letters X Y m d).1]; exact hqm)
  rwa [Nat.add_sub_cancel] at this

theorem ci_T8 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q = m ∨ q = m + 1)
    (hb : bit Vc (X.length + 1) q = false) : (next hW s).1 = (X.length, 0) :=
  next_arm_l hW (by have := slot_col_lt hW hs; omega) (ci_letters X Y m d).1 hs hq hb

theorem ci_T9 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 1) q = false) (hqm : m + 2 ≤ q) :
    (next hW s).1 = (X.length, q - 2) ∧ bit Vc X.length (q - 2) = false := by
  have := next_left_ge hW hs hq hb (by rw [Nat.add_sub_cancel, (ci_letters X Y m d).1]; simpa [idx, coarity] using hqm)
  rw [Nat.add_sub_cancel, (ci_letters X Y m d).1] at this
  simpa [arity, coarity] using this

theorem ci_T10 {s : Slot Vc} (hs : s.1 = (X.length, 0)) :
    (next hW s).1 = (X.length + 1, if d then m else m + 1) :=
  next_cusp_l hW (ci_letters X Y m d).1 hs

theorem ci_T11 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 2) q = false) (hqm : q < m) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Vc (X.length + 1) q = false := by
  have e : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_lt hW hs hq hb (by rw [e, (ci_letters X Y m d).2]; exact hqm)
  rwa [e] at this

theorem ci_T12 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 2) q = false) (hqm : m ≤ q) :
    (next hW s).1 = (X.length + 1, q + 2) ∧ bit Vc (X.length + 1) (q + 2) = false := by
  have e : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_ge hW hs hq hb (by rw [e, (ci_letters X Y m d).2]; simpa [idx, coarity] using hqm)
  rw [e, (ci_letters X Y m d).2] at this
  simpa [arity, coarity] using this

/-- the four slots of the separated circle -/
def InCirc (u : Slot Vc) : Prop :=
  u.1 = (X.length, 0) ∨ u.1 = (X.length + 1, if d then m else m + 1) ∨
  u.1 = (X.length + 1, 0) ∨ u.1 = (X.length + 1, if d then m + 1 else m)

omit hW in
theorem ci_bit_arm_true (B1 : bit Vc (X.length + 1) m = d) (B2 : bit Vc (X.length + 1) (m + 1) = !d) :
    bit Vc (X.length + 1) (if d then m else m + 1) = true := by
  cases d <;> simp_all

omit hW in
theorem ci_bit_arm_false (B1 : bit Vc (X.length + 1) m = d) (B2 : bit Vc (X.length + 1) (m + 1) = !d) :
    bit Vc (X.length + 1) (if d then m + 1 else m) = false := by
  cases d <;> simp_all

theorem inCirc_next {u : Slot Vc} (hu : InCirc X Y m d u) : InCirc X Y m d (next hW u) := by
  obtain ⟨B1, B2⟩ := ci_bits X Y m d hW
  have hm1 := ci_m_pos X Y m d hW
  rcases hu with hu | hu | hu | hu
  · exact Or.inr (Or.inl (ci_T10 X Y m d hW hu))
  · exact Or.inr (Or.inr (Or.inl (ci_T5 X Y m d hW hu (by split_ifs <;> simp) (ci_bit_arm_true X Y m d B1 B2))))
  · exact Or.inr (Or.inr (Or.inr (ci_T6 X Y m d hW hu)))
  · exact Or.inl (ci_T8 X Y m d hW hu (by split_ifs <;> simp) (ci_bit_arm_false X Y m d B1 B2))

theorem inCirc_iterate {u : Slot Vc} (hu : InCirc X Y m d u) (n : ℕ) : InCirc X Y m d ((next hW)^[n] u) := by
  induction n with
  | zero => exact hu
  | succ n ih => rw [Function.iterate_succ_apply']; exact inCirc_next X Y m d hW ih

theorem inCirc_not_ext {u : Slot Vc} (hu : InCirc X Y m d u) : ¬ ExtCol X Pc (colOf u) := by
  obtain ⟨B1, B2⟩ := ci_bits X Y m d hW
  have hm1 := ci_m_pos X Y m d hW
  rcases hu with hu | hu | hu | hu
  · rw [block_col_vertex hu, ci_extCol]; omega
  · rw [block_col_true hu (by split_ifs <;> omega) (ci_bit_arm_true X Y m d B1 B2), ci_extCol]; omega
  · rw [block_col_vertex hu, ci_extCol]; omega
  · rw [block_col_false hu (by split_ifs <;> omega) (ci_bit_arm_false X Y m d B1 B2), ci_extCol]; omega

/-- the left-cusp vertex of the circle -/
def circV : Slot Vc :=
  ⟨(X.length, 0), Or.inl ⟨rfl, by rw [ci_length]; omega, by rw [(ci_letters X Y m d).1]; rfl⟩⟩

omit hW in
theorem circV_val : (circV X Y m d).1 = (X.length, 0) := rfl

/-- the circle's slots all lie on the cycle of its vertex -/
theorem inCirc_sameCycle {u : Slot Vc} (hu : InCirc X Y m d u) :
    (nextPerm hW).SameCycle (circV X Y m d) u := by
  obtain ⟨B1, B2⟩ := ci_bits X Y m d hW
  have h1 := ci_T10 X Y m d hW (circV_val X Y m d)
  have h2 := ci_T5 X Y m d hW h1 (by split_ifs <;> simp) (ci_bit_arm_true X Y m d B1 B2)
  have h3 := ci_T6 X Y m d hW h2
  rcases hu with hu | hu | hu | hu
  · exact sameCycle_of_iterate hW (a := 0) (b := 0) (Subtype.ext (hu.symm.trans rfl))
  · exact sameCycle_of_iterate hW (a := 1) (b := 0) (Subtype.ext (h1.trans hu.symm))
  · exact sameCycle_of_iterate hW (a := 2) (b := 0) (Subtype.ext (h2.trans hu.symm))
  · exact sameCycle_of_iterate hW (a := 3) (b := 0) (Subtype.ext (h3.trans hu.symm))

/-- every slot lies on the circle or reaches the exterior -/
theorem ci_reach_or (u : Slot Vc) : InCirc X Y m d u ∨ ∃ n, ExtPiece X Pc Y ((next hW)^[n] u) := by
  obtain ⟨B1, B2⟩ := ci_bits X Y m d hW
  have hm1 := ci_m_pos X Y m d hW
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  by_cases hext : ExtCol X Pc (colOf u)
  · exact Or.inr (reach_self hW hext)
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, ci_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · exact Or.inl (Or.inl hu)
    · exact Or.inl (Or.inr (Or.inr (Or.inl hu)))
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hW hu hp
  cases hb : bit Vc k p
  · rw [block_col_false hu hp hb, ci_extCol] at hext
    have : k = X.length + 1 ∨ k = X.length + 2 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := ci_T7 X Y m d hW hu hp hb hpm
        refine Or.inr (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pc (colOf _)
        have := (cutSlot_facts hW h1 hp).2.2.1
        rw [block_col_false h1 hp hb1, ci_extCol]; omega
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · left; right; right; right
        rw [hu]
        rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
        · rw [← hpe] at hb; rw [B1] at hb; rw [hb, ← hpe]; rfl
        · have hpe' : p = m + 1 := by omega
          rw [hpe'] at hb; rw [B2] at hb
          have hd : d = true := by cases d <;> simp_all
          rw [hpe', hd]; rfl
      · obtain ⟨h1, hb1⟩ := ci_T9 X Y m d hW hu hp hb hpm2
        refine Or.inr (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pc (colOf _)
        have := (cutSlot_facts hW h1 (by omega)).2.2.1
        rw [block_col_false h1 (by omega) hb1, ci_extCol]; omega
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := ci_T11 X Y m d hW hu hp hb hpm
        obtain ⟨h2, hb2⟩ := ci_T7 X Y m d hW h1 hp hb1 hpm
        refine Or.inr (reach_of_next hW (reach_of_next hW (reach_self hW ?_)))
        show ExtCol X Pc (colOf _)
        have := (cutSlot_facts hW h2 hp).2.2.1
        rw [block_col_false h2 hp hb2, ci_extCol]; omega
      · obtain ⟨h1, hb1⟩ := ci_T12 X Y m d hW hu hp hb hpm
        obtain ⟨h2, hb2⟩ := ci_T9 X Y m d hW h1 (by omega) hb1 (by omega)
        refine Or.inr (reach_of_next hW (reach_of_next hW (reach_self hW ?_)))
        show ExtCol X Pc (colOf _)
        have := (cutSlot_facts hW h2 (by omega)).2.2.1
        rw [block_col_false h2 (by omega) hb2, ci_extCol]; omega
  · rw [block_col_true hu hp hb, ci_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := ci_T1 X Y m d hW hu hp hb hpm
        obtain ⟨h2, hb2⟩ := ci_T3 X Y m d hW h1 hp hb1 hpm
        refine Or.inr (reach_of_next hW (reach_of_next hW (reach_self hW ?_)))
        show ExtCol X Pc (colOf _)
        rw [block_col_true h2 hp hb2, ci_extCol]; omega
      · obtain ⟨h1, hb1⟩ := ci_T2 X Y m d hW hu hp hb hpm
        obtain ⟨h2, hb2⟩ := ci_T4 X Y m d hW h1 (by omega) hb1 (by omega)
        refine Or.inr (reach_of_next hW (reach_of_next hW (reach_self hW ?_)))
        show ExtCol X Pc (colOf _)
        rw [block_col_true h2 (by omega) hb2, ci_extCol]; omega
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := ci_T3 X Y m d hW hu hp hb hpm
        refine Or.inr (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pc (colOf _)
        rw [block_col_true h1 hp hb1, ci_extCol]; omega
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · left; right; left
        rw [hu]
        rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
        · rw [← hpe] at hb; rw [B1] at hb; rw [hb, ← hpe]; rfl
        · have hpe' : p = m + 1 := by omega
          rw [hpe'] at hb; rw [B2] at hb
          have hd : d = false := by cases d <;> simp_all
          rw [hpe', hd]; rfl
      · obtain ⟨h1, hb1⟩ := ci_T4 X Y m d hW hu hp hb hpm2
        refine Or.inr (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pc (colOf _)
        rw [block_col_true h1 (by omega) hb1, ci_extCol]; omega

/-- exactly the circle misses the exterior -/
theorem ci_hc₀ (u : Slot Vc) :
    (¬ ∃ n, ExtPiece X Pc Y ((next hW)^[n] u)) ↔ orbitOf hW u = orbitOf hW (circV X Y m d) := by
  constructor
  · intro hn
    rcases ci_reach_or X Y m d hW u with hu | hu
    · rw [orbitOf_eq_iff]
      exact (inCirc_sameCycle X Y m d hW hu).symm
    · exact absurd hu hn
  · intro ho
    rw [orbitOf_eq_iff] at ho
    obtain ⟨n, hn⟩ := exists_iterate_of_sameCycle hW ho.symm
    rintro ⟨j, hj⟩
    have hu : InCirc X Y m d u := by
      rw [← hn]; exact inCirc_iterate X Y m d hW (Or.inl rfl) n
    exact inCirc_not_ext X Y m d hW (inCirc_iterate X Y m d hW hu j) hj

theorem ci_sameEffect : SameEffect X Pc [] := by
  have hm1 := ci_m_pos X Y m d hW
  exact sameEffect_of_replace X Pc Y [] hW (fun c c' h => by obtain rfl := run_circle hm1 h; rfl)

/-- THE BLOCK PASSAGE of the circle block: every entering strand exits at its own position. -/
theorem ci_passage (hW' : (X ++ [] ++ Y).Closed) : Passage X Pc Y [] hW hW' := by
  have hm1 := ci_m_pos X Y m d hW
  have hP : Pc ≠ [] := by simp
  have hE := ci_sameEffect X Y m d hW
  constructor
  intro b hext hcol
  have side : ∀ {c : Slot Vc}, extPair X Pc [] b.1 = extPair X Pc [] c.1 →
      ∃ (m' : ℕ) (b' : Slot (X ++ [] ++ Y)), b'.1 = extPair X Pc [] b.1 ∧
        ((next hW')^[m'] b').1 = extPair X Pc [] c.1 ∧ ∀ i < m', ¬ ExtCol X [] (colOf ((next hW')^[i] b')) :=
    fun hbc => ⟨0, ⟨_, isSlot_ext X Pc Y [] hP hE b.2 hext⟩, rfl, hbc, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  have shiftL : ∀ p, extPair X Pc [] (X.length, p) = extPair X Pc [] (X.length + 2, p) := by
    intro p; simp only [extPair, shiftIdx_of_le X Pc [] le_rfl, ci_shift X m d]
  rcases (entry_iff X Pc Y hP hW b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
  · rcases lt_or_ge p m with hpm | hpm
    · obtain ⟨h1, hb1⟩ := ci_T1 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := ci_T3 X Y m d hW h1 hp hb1 hpm
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc)
        (by rw [block_col_true hb hp hbit, ci_extCol]; omega)
        (passage_step hW (ExtCol X Pc) (by rw [block_col_true h1 hp hb1, ci_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · rw [block_col_true h2 hp hb2, ci_extCol]; omega
      · rw [hb, h2]; exact shiftL p
    · obtain ⟨h1, hb1⟩ := ci_T2 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := ci_T4 X Y m d hW h1 (by omega) hb1 (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc)
        (by rw [block_col_true hb hp hbit, ci_extCol]; omega)
        (passage_step hW (ExtCol X Pc) (by rw [block_col_true h1 (by omega) hb1, ci_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · rw [block_col_true h2 (by omega) hb2, ci_extCol]; omega
      · rw [hb, h2, show p + 2 - 2 = p by omega]; exact shiftL p
  · replace hb : b.1 = (X.length + 2, p) := hb
    replace hbit : bit Vc (X.length + 2) p = false := hbit
    rcases lt_or_ge p m with hpm | hpm
    · obtain ⟨h1, hb1⟩ := ci_T11 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := ci_T7 X Y m d hW h1 hp hb1 hpm
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc)
        (by rw [block_col_false hb hp hbit, ci_extCol]; omega)
        (passage_step hW (ExtCol X Pc) (by rw [block_col_false h1 hp hb1, ci_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · have := (cutSlot_facts hW h2 hp).2.2.1
        rw [block_col_false h2 hp hb2, ci_extCol]; omega
      · rw [hb, h2]; exact (shiftL p).symm
    · obtain ⟨h1, hb1⟩ := ci_T12 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := ci_T9 X Y m d hW h1 (by omega) hb1 (by omega)
      rw [show p + 2 - 2 = p by omega] at h2 hb2
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc)
        (by rw [block_col_false hb hp hbit, ci_extCol]; omega)
        (passage_step hW (ExtCol X Pc) (by rw [block_col_false h1 (by omega) hb1, ci_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · have := (cutSlot_facts hW h2 hp).2.2.1
        rw [block_col_false h2 hp hb2, ci_extCol]; omega
      · rw [hb, h2]; exact (shiftL p).symm

/-- LEAF `circle_recordIso_addFree`. -/
theorem ci_recordIso (W W' : OWord) (hWeq : W.letters = Vc) (hW'eq : W'.letters = X ++ Y)
    (hne' : X ++ Y ≠ []) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record.addFree) := by
  have hW' : (X ++ [] ++ Y).Closed := by have := W'.closed; rw [hW'eq] at this; simpa using this
  refine realize_recordIso_addFree_of_ext X Pc Y [] (by simp) (ci_sameEffect X Y m d hW) hW hW' (by simp)
    (by simpa using hne') (ci_passage X Y m d hW hW') ?_ (orbitOf hW (circV X Y m d)) (ci_hc₀ X Y m d hW)
    ?_ ?_ W W' hWeq (by simpa using hW'eq)
  · intro u; exact ⟨0, by show ExtCol X [] (colOf u); unfold ExtCol; simp; omega⟩
  · intro k hk1 hk2
    simp only [List.length_cons, List.length_nil] at hk2
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rw [(ci_letters X Y m d).1]; rfl
    · rw [(ci_letters X Y m d).2]; rfl
  · intro k hk1 hk2; simp at hk2; omega

end Circle

/-! #### G. Blocks with interior `σ` slots: the extended passage hypothesis and the switch variant -/

/-- one more step of a passage for a slot predicate -/
theorem apassage_step {V : Word} (hV : V.Closed) (Q : Slot V → Prop) {b c : Slot V} (hb : ¬ Q b)
    (h : ∃ n, (next hV)^[n] (next hV b) = c ∧ ∀ i < n, ¬ Q ((next hV)^[i] (next hV b))) :
    ∃ n, (next hV)^[n] b = c ∧ ∀ i < n, ¬ Q ((next hV)^[i] b) := by
  obtain ⟨n, hc, hmin⟩ := h
  refine ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hc, ?_⟩
  intro i hi
  cases i with
  | zero => simpa using hb
  | succ i => rw [Function.iterate_succ_apply]; exact hmin i (by omega)

theorem apassage_end {V : Word} (hV : V.Closed) (Q : Slot V → Prop) {b : Slot V} :
    ∃ n, (next hV)^[n] b = b ∧ ∀ i < n, ¬ Q ((next hV)^[i] b) :=
  ⟨0, rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

/-- the positive-length version, for the interior clause -/
theorem apassage_pos {V : Word} (hV : V.Closed) (Q : Slot V → Prop) {u c : Slot V}
    (h : ∃ n, (next hV)^[n] (next hV u) = c ∧ ∀ i < n, ¬ Q ((next hV)^[i] (next hV u))) :
    ∃ (m : ℕ) (_ : 0 < m), (next hV)^[m] u = c ∧ ∀ i, 0 < i → i < m → ¬ Q ((next hV)^[i] u) := by
  obtain ⟨n, hc, hmin⟩ := h
  refine ⟨n + 1, Nat.succ_pos _, by rw [Function.iterate_succ_apply]; exact hc, ?_⟩
  intro i hi him
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [Function.iterate_succ_apply]; exact hmin i' (by omega)


section IntPassage

variable (X P Y P' : Word) (hP : P ≠ []) (hE : SameEffect X P P')
  (hW : (X ++ P ++ Y).Closed) (hW' : (X ++ P' ++ Y).Closed)

/-- the interior `σ` slots of the block -/
def IntSlot (u : Slot (X ++ P ++ Y)) : Prop := IsσSlot u ∧ ¬ ExtCol X P (colOf u)

instance : DecidablePred (IntSlot X P Y) := fun u => by unfold IntSlot; infer_instance

/-- the active superset: exterior pieces and interior `σ` slots -/
def ActE (u : Slot (X ++ P ++ Y)) : Prop := ExtPiece X P Y u ∨ IntSlot X P Y u

instance : DecidablePred (ActE X P Y) := fun u => by unfold ActE; infer_instance

theorem isσSlot_actE {u : Slot (X ++ P ++ Y)} (hu : IsσSlot u) : ActE X P Y u := by
  by_cases h : ExtCol X P (colOf u)
  · exact Or.inl h
  · exact Or.inr ⟨hu, h⟩

theorem not_actE_of {u : Slot (X ++ P ++ Y)} (h1 : ¬ ExtCol X P (colOf u)) (h2 : ¬ IsσSlot u) :
    ¬ ActE X P Y u := by
  rintro (h | h)
  · exact h1 h
  · exact h2 h.1

variable (φI : {u // IntSlot X P Y u} ≃ {u' // IntSlot X P' Y u'})
include hP hE hW

/-- the glued correspondence of the active supersets -/
noncomputable def φA : {u // ActE X P Y u} ≃ {u' // ActE X P' Y u'} :=
  glueEquiv (ExtPiece X P Y) (IntSlot X P Y) (ExtPiece X P' Y) (IntSlot X P' Y)
    (fun _ h h' => h'.2 h) (fun _ h h' => h'.2 h) (φE X P Y P' hP hE hW) φI

theorem φA_val_ext (u : {u // ActE X P Y u}) (h : ExtPiece X P Y u.1) :
    (φA X P Y P' hP hE hW φI u).1 = (φE X P Y P' hP hE hW ⟨u.1, h⟩).1 :=
  glueEquiv_val_left _ _ _ _ _ _ _ _ u h

theorem φA_val_int (u : {u // ActE X P Y u}) (h : ¬ ExtPiece X P Y u.1) :
    (φA X P Y P' hP hE hW φI u).1 = (φI ⟨u.1, u.2.resolve_left h⟩).1 :=
  glueEquiv_val_right _ _ _ _ _ _ _ _ u h

theorem φA_val_ext' (u : {u // ActE X P Y u}) (h : ExtPiece X P Y u.1) :
    (φA X P Y P' hP hE hW φI u).1.1 = extPair X P P' u.1.1 := by
  rw [φA_val_ext X P Y P' hP hE hW φI u h]; rfl

/-- THE EXTENDED BLOCK PASSAGE HYPOTHESIS: from every entry the traversal reaches an active slot
(exterior piece or interior `σ` slot), with the corresponding path in `W'`; from every interior `σ`
slot likewise. -/
structure IntPassage : Prop where
  entry : ∀ b : Slot (X ++ P ++ Y), IsExtSlot X P b.1 → ¬ ExtCol X P (colOf b) →
    ∃ (m : ℕ) (c : Slot (X ++ P ++ Y)) (hc : ActE X P Y c), (next hW)^[m] b = c ∧
      (∀ i < m, ¬ ActE X P Y ((next hW)^[i] b)) ∧
      ∃ (m' : ℕ) (b' : Slot (X ++ P' ++ Y)), b'.1 = extPair X P P' b.1 ∧
        (next hW')^[m'] b' = (φA X P Y P' hP hE hW φI ⟨c, hc⟩).1 ∧
        ∀ i < m', ¬ ActE X P' Y ((next hW')^[i] b')
  interior : ∀ (u : Slot (X ++ P ++ Y)) (hu : IntSlot X P Y u),
    ∃ (m : ℕ) (_ : 0 < m) (c : Slot (X ++ P ++ Y)) (hc : ActE X P Y c), (next hW)^[m] u = c ∧
      (∀ i, 0 < i → i < m → ¬ ActE X P Y ((next hW)^[i] u)) ∧
      ∃ (m' : ℕ), 0 < m' ∧ (next hW')^[m'] (φI ⟨u, hu⟩).1 = (φA X P Y P' hP hE hW φI ⟨c, hc⟩).1 ∧
        ∀ i, 0 < i → i < m' → ¬ ActE X P' Y ((next hW')^[i] (φI ⟨u, hu⟩).1)

/-- the extended passage makes the first returns to the active supersets conjugate -/
theorem conj_of_intPassage (hpass : IntPassage X P Y P' hP hE hW hW' φI) (u : {u // ActE X P Y u}) :
    firstReturn (nextPerm hW') (ActE X P' Y) (φA X P Y P' hP hE hW φI u) =
      φA X P Y P' hP hE hW φI (firstReturn (nextPerm hW) (ActE X P Y) u) := by
  revert u
  apply conj_of_paths_next
  intro u
  by_cases hext : ExtPiece X P Y u.1
  · obtain ⟨hnext_ext, hnext_eq⟩ :=
      next_ext X P Y P' hP hE hW hW' ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 hext⟩ hext
    have hφu : (φA X P Y P' hP hE hW φI u).1 = extSlot X P Y P' hP hE ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 hext⟩ :=
      φA_val_ext X P Y P' hP hE hW φI u hext
    by_cases hE1 : ExtCol X P (colOf (next hW u.1))
    · refine ⟨1, 1, one_pos, one_pos, Or.inl hE1, fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _),
        fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _), ?_⟩
      apply Subtype.ext
      rw [Function.iterate_one, hφu, hnext_eq]
      exact (φA_val_ext' X P Y P' hP hE hW φI ⟨_, Or.inl hE1⟩ hE1).symm
    · obtain ⟨m₀, c, hc, hmc, hmin, m₀', b', hb', hm', hmin'⟩ := hpass.entry (next hW u.1) hnext_ext hE1
      have hb'' : next hW' (φA X P Y P' hP hE hW φI u).1 = b' := Subtype.ext (by rw [hφu, hnext_eq, hb'])
      refine ⟨m₀ + 1, m₀' + 1, Nat.succ_pos _, Nat.succ_pos _, by rw [Function.iterate_succ_apply, hmc]; exact hc, ?_, ?_, ?_⟩
      · intro i hi him
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [Function.iterate_succ_apply]; exact hmin i' (by omega)
      · intro i hi him
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [Function.iterate_succ_apply, hb'']; exact hmin' i' (by omega)
      · rw [Function.iterate_succ_apply, hb'', hm']
        exact congrArg (fun x : {u // ActE X P Y u} => (φA X P Y P' hP hE hW φI x).1) (Subtype.ext hmc.symm)
  · have hu : IntSlot X P Y u.1 := u.2.resolve_left hext
    obtain ⟨m, hm, c, hc, hmc, hmin, m', hm', heq, hmin'⟩ := hpass.interior u.1 hu
    have hφu : (φA X P Y P' hP hE hW φI u).1 = (φI ⟨u.1, hu⟩).1 := φA_val_int X P Y P' hP hE hW φI u hext
    refine ⟨m, m', hm, hm', by rw [hmc]; exact hc, hmin, ?_, ?_⟩
    · intro i hi him; rw [hφu]; exact hmin' i hi him
    · rw [hφu, heq]
      exact congrArg (fun x : {u // ActE X P Y u} => (φA X P Y P' hP hE hW φI x).1) (Subtype.ext hmc.symm)

end IntPassage

section RecIsoSwitch

variable {W W' : Word} (hW : W.Closed) (hW' : W'.Closed)
  (E : Slot W → Prop) (E' : Slot W' → Prop) [DecidablePred E] [DecidablePred E']
  (φ : {u // E u} ≃ {u' // E' u'})

/-- THE RECORD ISOMORPHISM ONTO A SWITCHED RECORD: as `recordIsoOfConj`, but the over bits and signs
are reversed exactly on the slots `S` carried to the switched crossing `{x₀, σtwin x₀}`. -/
noncomputable def recordIsoOfConjSwitch
    (conj : ∀ u, firstReturn (nextPerm hW') E' (φ u) = φ (firstReturn (nextPerm hW) E u))
    (hexit : ∀ u : Slot W, ∃ n : ℕ, E ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot W', ∃ n : ℕ, E' ((next hW')^[n] u'))
    (hσE : ∀ u, IsσSlot u → E u) (hσE' : ∀ u', IsσSlot u' → E' u')
    (hσ : ∀ u : {u // E u}, IsσSlot (φ u).1 ↔ IsσSlot u.1)
    (htwin : ∀ (u : {u // E u}) (hu : IsσSlot u.1),
      (φ ⟨σtwin hW u.1, hσE _ (isσSlot_σtwin hW hu)⟩).1 = σtwin hW' (φ u).1)
    (x₀ : (slotRecord hW' IsσSlot (allActive hW')).M) (S : Slot W → Prop)
    (hS : ∀ u : {u // E u}, IsσSlot u.1 → (((φ u).1 = x₀.1 ∨ (φ u).1 = σtwin hW' x₀.1) ↔ S u.1))
    (hdescS : ∀ u : {u // E u}, IsσSlot u.1 → S u.1 → isDesc (φ u).1 = !isDesc u.1)
    (hdescN : ∀ u : {u // E u}, IsσSlot u.1 → ¬ S u.1 → isDesc (φ u).1 = isDesc u.1)
    (hsgnS : ∀ u : {u // E u}, IsσSlot u.1 → S u.1 → σsgn (φ u).1 = -σsgn u.1)
    (hsgnN : ∀ u : {u // E u}, IsσSlot u.1 → ¬ S u.1 → σsgn (φ u).1 = σsgn u.1) :
    RecordIso (slotRecord hW IsσSlot (allActive hW)) ((slotRecord hW' IsσSlot (allActive hW')).switch x₀) :=
  let hexitP : ∀ u : Slot W, ∃ n : ℕ, E (((nextPerm hW) ^ n) u) := fun u => by
    obtain ⟨n, hn⟩ := hexit u; exact ⟨n, by rw [nextPerm_pow_apply]; exact hn⟩
  let hexitP' : ∀ u' : Slot W', ∃ n : ℕ, E' (((nextPerm hW') ^ n) u') := fun u => by
    obtain ⟨n, hn⟩ := hexit' u; exact ⟨n, by rw [nextPerm_pow_apply]; exact hn⟩
  let oe : Orbit hW ≃ Orbit hW' := cycleEquiv (nextPerm hW) (nextPerm hW') E E' φ conj hexitP hexitP'
  let Φ : (slotRecord hW IsσSlot (allActive hW)).M ≃ (slotRecord hW' IsσSlot (allActive hW')).M :=
    { toFun := fun u => ⟨(φ ⟨u.1, hσE _ u.2⟩).1, (hσ _).2 u.2⟩
      invFun := fun u' => ⟨(φ.symm ⟨u'.1, hσE' _ u'.2⟩).1, by
        have h := (hσ (φ.symm ⟨u'.1, hσE' _ u'.2⟩)).1
        rw [Equiv.apply_symm_apply] at h
        exact h u'.2⟩
      left_inv := fun u => Subtype.ext (by
        show (φ.symm ⟨(φ ⟨u.1, hσE _ u.2⟩).1, _⟩).1 = u.1
        rw [show (⟨(φ ⟨u.1, hσE _ u.2⟩).1, _⟩ : {u' // E' u'}) = φ ⟨u.1, hσE _ u.2⟩ from rfl,
          Equiv.symm_apply_apply])
      right_inv := fun u' => Subtype.ext (by
        show (φ ⟨(φ.symm ⟨u'.1, hσE' _ u'.2⟩).1, _⟩).1 = u'.1
        rw [show (⟨(φ.symm ⟨u'.1, hσE' _ u'.2⟩).1, _⟩ : {u // E u}) = φ.symm ⟨u'.1, hσE' _ u'.2⟩ from rfl,
          Equiv.apply_symm_apply]) }
  have hmem : ∀ u : (slotRecord hW IsσSlot (allActive hW)).M,
      Φ u ∈ ({x₀, (slotRecord hW' IsσSlot (allActive hW')).pair x₀} :
        Finset (slotRecord hW' IsσSlot (allActive hW')).M) ↔ S u.1 := by
    intro u
    rw [Finset.mem_insert, Finset.mem_singleton, ← hS ⟨u.1, hσE _ u.2⟩ u.2]
    constructor
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr ((congrArg Subtype.val h).trans (slotRecord_pair_val hW' _ _ x₀))
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext (h.trans (slotRecord_pair_val hW' _ _ x₀).symm))
  { e := (Fintype.equivFin (Orbit hW)).symm.trans (oe.trans (Fintype.equivFin (Orbit hW')))
    Φ := Φ
    comp_eq := fun u => by
      show slotComp hW' (φ ⟨u.1, hσE _ u.2⟩).1 =
        ((Fintype.equivFin (Orbit hW)).symm.trans (oe.trans (Fintype.equivFin (Orbit hW')))) (slotComp hW u.1)
      rw [slotComp_eq_equivFin, slotComp_eq_equivFin]
      simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
      congr 1
      show orbitOf hW' _ = cycleEquiv (nextPerm hW) (nextPerm hW') E E' φ conj hexitP hexitP' (orbitOf hW u.1)
      exact (cycleEquiv_mk (nextPerm hW) (nextPerm hW') E E' φ conj hexitP hexitP' ⟨u.1, hσE _ u.2⟩).symm
    succ_eq := fun u => by
      apply Subtype.ext
      show (φ ⟨(firstReturn (nextPerm hW) IsσSlot u).1, _⟩).1 =
        (firstReturn (nextPerm hW') IsσSlot ⟨(φ ⟨u.1, _⟩).1, _⟩).1
      exact (firstReturn_conj_of_factor (nextPerm hW) (nextPerm hW') E E' φ conj IsσSlot IsσSlot hσE hσE' hσ u).symm
    pair_eq := fun u => by
      apply Subtype.ext
      show (φ ⟨σtwin hW u.1, _⟩).1 = σtwin hW' (φ ⟨u.1, _⟩).1
      exact htwin ⟨u.1, hσE _ u.2⟩ u.2
    bit_eq := fun u => by
      refine (Record.switch_isOver (slotRecord hW' IsσSlot (allActive hW')) x₀ (Φ u)).trans ?_
      by_cases hs : S u.1
      · rw [ite_eq_left ((hmem u).2 hs)]
        show (!isDesc (φ ⟨u.1, hσE _ u.2⟩).1) = isDesc u.1
        rw [hdescS ⟨u.1, hσE _ u.2⟩ u.2 hs, Bool.not_not]
      · rw [ite_eq_right (fun h => hs ((hmem u).1 h))]
        exact hdescN ⟨u.1, hσE _ u.2⟩ u.2 hs
    sgn_eq := fun u => by
      refine (Record.switch_sgn (slotRecord hW' IsσSlot (allActive hW')) x₀ (Φ u)).trans ?_
      by_cases hs : S u.1
      · rw [ite_eq_left ((hmem u).2 hs)]
        show -σsgn (φ ⟨u.1, hσE _ u.2⟩).1 = σsgn u.1
        rw [hsgnS ⟨u.1, hσE _ u.2⟩ u.2 hs, neg_neg]
      · rw [ite_eq_right (fun h => hs ((hmem u).1 h))]
        exact hsgnN ⟨u.1, hσE _ u.2⟩ u.2 hs }

end RecIsoSwitch

/-! generic pass lemmas with the letter named -/

section PassLetter

variable {V : Word} (hV : V.Closed)
include hV

theorem pass_r_lt {ℓ : Letter} {k : ℕ} (hℓ : letterAt V k = ℓ) {s : Slot V} {p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0)
    (hb : bit V k p = true) (hlt : p < ℓ.idx) : (next hV s).1 = (k + 1, p) ∧ bit V (k + 1) p = true :=
  next_right_lt hV hs hp hb (by rw [hℓ]; exact hlt)

theorem pass_r_ge {ℓ : Letter} {k : ℕ} (hℓ : letterAt V k = ℓ) {s : Slot V} {p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0)
    (hb : bit V k p = true) (hge : ℓ.idx + ℓ.arity ≤ p) :
    (next hV s).1 = (k + 1, p + ℓ.coarity - ℓ.arity) ∧ bit V (k + 1) (p + ℓ.coarity - ℓ.arity) = true := by
  have := next_right_ge hV hs hp hb (by rw [hℓ]; exact hge)
  rwa [hℓ] at this

theorem pass_l_lt {ℓ : Letter} {k : ℕ} (hℓ : letterAt V k = ℓ) {s : Slot V} {q : ℕ} (hs : s.1 = (k + 1, q)) (hq : q ≠ 0)
    (hb : bit V (k + 1) q = false) (hlt : q < ℓ.idx) : (next hV s).1 = (k, q) ∧ bit V k q = false := by
  have := next_left_lt hV hs hq hb (by rw [Nat.add_sub_cancel, hℓ]; exact hlt)
  rwa [Nat.add_sub_cancel] at this

theorem pass_l_ge {ℓ : Letter} {k : ℕ} (hℓ : letterAt V k = ℓ) {s : Slot V} {q : ℕ} (hs : s.1 = (k + 1, q)) (hq : q ≠ 0)
    (hb : bit V (k + 1) q = false) (hge : ℓ.idx + ℓ.coarity ≤ q) :
    (next hV s).1 = (k, q + ℓ.arity - ℓ.coarity) ∧ bit V k (q + ℓ.arity - ℓ.coarity) = false := by
  have := next_left_ge hV hs hq hb (by rw [Nat.add_sub_cancel, hℓ]; exact hge)
  rwa [Nat.add_sub_cancel, hℓ] at this

omit hV in
/-- a pass slot heading right is not a `σ` slot unless the letter is `σ j` and the position is `j` or `j+1` -/
theorem not_σ_right {s : Slot V} {k p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) (hb : bit V k p = true)
    (h : ∀ j, letterAt V k = .σ j → p ≠ j ∧ p ≠ j + 1) : ¬ IsσSlot s := by
  intro hσ
  have hcol : colOf s = k := block_col_true hs hp hb
  unfold IsσSlot at hσ
  rw [hcol] at hσ
  obtain ⟨hcr, hsh⟩ := hσ
  obtain ⟨j, hℓ⟩ : ∃ j, letterAt V k = .σ j := ⟨_, letterAt_σ_of_isCrossing hcr⟩
  obtain ⟨h1, h2⟩ := h j hℓ
  have hshape : shapeOf s = .pass p p := by
    unfold shapeOf
    rw [hs]
    simp only [hp, ↓reduceIte, hb, hℓ]
    unfold posR
    simp only [idx, arity, coarity]
    split_ifs with c1 c2
    · rfl
    · omega
    · rw [Nat.add_sub_cancel]
  rw [hℓ, hshape] at hsh
  simp only [idx, Shape.pass.injEq] at hsh
  omega

omit hV in
/-- a pass slot heading left is not a `σ` slot unless the previous letter is `σ j` and the position is `j` or `j+1` -/
theorem not_σ_left {s : Slot V} {k q : ℕ} (hs : s.1 = (k + 1, q)) (hq : q ≠ 0) (hb : bit V (k + 1) q = false)
    (h : ∀ j, letterAt V k = .σ j → q ≠ j ∧ q ≠ j + 1) : ¬ IsσSlot s := by
  intro hσ
  have hcol : colOf s = k := by rw [block_col_false hs hq hb, Nat.add_sub_cancel]
  unfold IsσSlot at hσ
  rw [hcol] at hσ
  obtain ⟨hcr, hsh⟩ := hσ
  obtain ⟨j, hℓ⟩ : ∃ j, letterAt V k = .σ j := ⟨_, letterAt_σ_of_isCrossing hcr⟩
  obtain ⟨h1, h2⟩ := h j hℓ
  have hshape : shapeOf s = .pass q q := by
    unfold shapeOf
    rw [hs]
    simp only [hq, ↓reduceIte, hb, Bool.false_eq_true, Nat.add_sub_cancel, hℓ]
    unfold posL
    simp only [idx, arity, coarity]
    split_ifs with c1 c2
    · rfl
    · omega
    · rw [Nat.add_sub_cancel]
  rw [hℓ, hshape] at hsh
  simp only [idx, Shape.pass.injEq] at hsh
  omega

omit hV in
/-- a cusp vertex is never a `σ` slot -/
theorem not_σ_vertex {s : Slot V} {k : ℕ} (hs : s.1 = (k, 0)) : ¬ IsσSlot s := by
  intro hσ
  have := vertex_not_crossing hs
  unfold IsσSlot at hσ
  rw [block_col_vertex hs] at hσ
  rw [hσ.1] at this
  exact Bool.noConfusion this

end PassLetter

/-! #### H. The cusp-skein interchange (ng:cusp-skein): `A = X l_{m+1} σ_m Y`, `A' = X l_m σ_{m+1} Y` -/

section Skein

variable (X Y : Word) (m : ℕ) (d a : Bool)

local notation "Vs" => X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y
local notation "Vsp" => X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y
local notation "Ps" => [Letter.l (m + 1) d, Letter.σ m]
local notation "Psp" => [Letter.l m d, Letter.σ (m + 1)]

theorem sk_letters : letterAt Vs X.length = .l (m + 1) d ∧ letterAt Vs (X.length + 1) = .σ m := by
  constructor
  · have := letterAt_block X Ps Y (i := 0) (by simp)
    simpa using this
  · have := letterAt_block X Ps Y (i := 1) (by simp)
    simpa using this

theorem sk'_letters : letterAt Vsp X.length = .l m d ∧ letterAt Vsp (X.length + 1) = .σ (m + 1) := by
  constructor
  · have := letterAt_block X Psp Y (i := 0) (by simp)
    simpa using this
  · have := letterAt_block X Psp Y (i := 1) (by simp)
    simpa using this

theorem sk_length : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).length = X.length + 2 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem sk'_length : (X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y).length = X.length + 2 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem sk_extCol (k : ℕ) : ExtCol X Ps k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k := by unfold ExtCol; simp
theorem sk'_extCol (k : ℕ) : ExtCol X Psp k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k := by unfold ExtCol; simp

/-- the index shift between the two principal words is the identity on exterior indices -/
theorem sk_shift {k : ℕ} (hk : k ≤ X.length ∨ X.length + 2 ≤ k) : shiftIdx X Psp Ps k = k := by
  unfold shiftIdx
  by_cases h : k ≤ X.length
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    have e1 : ([Letter.l m d, Letter.σ (m + 1)] : Word).length = 2 := rfl
    have e2 : ([Letter.l (m + 1) d, Letter.σ m] : Word).length = 2 := rfl
    rw [e1, e2]; omega

theorem sk_extPair {s : ℕ × ℕ} (hs : s.1 ≤ X.length ∨ X.length + 2 ≤ s.1) : extPair X Psp Ps s = s := by
  obtain ⟨k, p⟩ := s; simp only [extPair, sk_shift X m d hs]

theorem sk_Pne : ([Letter.l m d, Letter.σ (m + 1)] : Word) ≠ [] := List.cons_ne_nil _ _

variable {P L : Cuts} (hX : Word.run X [] = some (P ++ a :: L)) (hP : P.length = m - 1) (hm : 1 ≤ m)
variable (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed)
  (hA' : (X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y).Closed)

include hX hP in
/-- the through-strand bit at the cut before the factor -/
theorem sk_bit_a : bit Vs X.length m = a ∧ bit Vsp X.length m = a := by
  have h1 : cut Vs X.length = P ++ a :: L := cut_start X Ps Y hX
  have h2 : cut Vsp X.length = P ++ a :: L := cut_start X Psp Y hX
  have e : (P ++ a :: L).getD (m - 1) false = a := by
    rw [← hP, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]; rfl
  constructor
  · rw [bit_eq, h1, e]
  · rw [bit_eq, h2, e]

include hA in
theorem sk_bits (ha : bit Vs X.length m = a) :
    bit Vs (X.length + 1) m = a ∧ bit Vs (X.length + 1) (m + 1) = d ∧ bit Vs (X.length + 1) (m + 2) = !d ∧
    bit Vs (X.length + 2) m = d ∧ bit Vs (X.length + 2) (m + 1) = a ∧ bit Vs (X.length + 2) (m + 2) = !d := by
  obtain ⟨hℓ₀, hℓ₁⟩ := sk_letters X Y m d
  have hk₀ : X.length < (Vs).length := by rw [sk_length]; omega
  have hk₁ : X.length + 1 < (Vs).length := by rw [sk_length]; omega
  obtain ⟨-, h1, h2⟩ := l_bits hA hk₀ hℓ₀
  have hm1 : 1 ≤ m := σ_idx_pos hA hℓ₁
  have h0 : bit Vs (X.length + 1) m = a := by
    rw [bit_succ_of_lt hA hk₀ hm1 (by rw [hℓ₀]; exact Nat.lt_succ_self m), ha]
  obtain ⟨-, -, -, h3, h4⟩ := σ_facts hA hk₁ hℓ₁
  have h5 : bit Vs (X.length + 2) (m + 2) = bit Vs (X.length + 1) (m + 2) := by
    have := bit_succ_of_ge hA hk₁ (p := m + 2) (by rw [hℓ₁]; simp [idx, arity])
    rw [hℓ₁] at this; simpa [arity, coarity] using this
  exact ⟨h0, h1, h2, by rw [h4, h1], by rw [h3, h0], by rw [h5, h2]⟩

include hA' in
theorem sk'_bits (ha : bit Vsp X.length m = a) :
    bit Vsp (X.length + 1) m = d ∧ bit Vsp (X.length + 1) (m + 1) = !d ∧ bit Vsp (X.length + 1) (m + 2) = a ∧
    bit Vsp (X.length + 2) m = d ∧ bit Vsp (X.length + 2) (m + 1) = a ∧ bit Vsp (X.length + 2) (m + 2) = !d := by
  obtain ⟨hℓ₀, hℓ₁⟩ := sk'_letters X Y m d
  have hk₀ : X.length < (Vsp).length := by rw [sk'_length]; omega
  have hk₁ : X.length + 1 < (Vsp).length := by rw [sk'_length]; omega
  obtain ⟨hm1, h1, h2⟩ := l_bits hA' hk₀ hℓ₀
  have h0 : bit Vsp (X.length + 1) (m + 2) = a := by
    have := bit_succ_of_ge hA' hk₀ (p := m) (by rw [hℓ₀]; simp [idx, arity])
    rw [hℓ₀] at this; simp only [arity, coarity, Nat.sub_zero] at this
    rw [← ha, ← this]
  obtain ⟨-, -, -, h3, h4⟩ := σ_facts hA' hk₁ hℓ₁
  have h5 : bit Vsp (X.length + 2) m = bit Vsp (X.length + 1) m :=
    bit_succ_of_lt hA' hk₁ hm1 (by rw [hℓ₁]; exact Nat.lt_succ_self m)
  exact ⟨h1, h2, h0, by rw [h5, h1], by rw [h4, h0], by rw [h3, h2]⟩

theorem sk_m_pos (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed) : 1 ≤ m :=
  σ_idx_pos hA (sk_letters X Y m d).2

end Skein

section SkeinSwitch

variable (X Y : Word) (m : ℕ) (d a : Bool)

local notation "Vs" => X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y
local notation "Vsp" => X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y
local notation "Ps" => [Letter.l (m + 1) d, Letter.σ m]
local notation "Psp" => [Letter.l m d, Letter.σ (m + 1)]

variable (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed)
  (hA' : (X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y).Closed)

theorem sk_k₁ : X.length + 1 < (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).length := by rw [sk_length]; omega
theorem sk'_k₁ : X.length + 1 < (X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y).length := by rw [sk'_length]; omega

/-- the two site slots of `A` -/
noncomputable def siteA : Slot Vs := σSlotA hA (sk_k₁ X Y m d) (sk_letters X Y m d).2
noncomputable def siteB : Slot Vs := σSlotB hA (sk_k₁ X Y m d) (sk_letters X Y m d).2
/-- the two site slots of `A'` -/
noncomputable def siteA' : Slot Vsp := σSlotA hA' (sk'_k₁ X Y m d) (sk'_letters X Y m d).2
noncomputable def siteB' : Slot Vsp := σSlotB hA' (sk'_k₁ X Y m d) (sk'_letters X Y m d).2

include hA in
theorem siteA_val (ha : bit Vs X.length m = a) :
    (siteA X Y m d hA).1 = if a then (X.length + 1, m) else (X.length + 2, m + 1) := by
  have h := (sk_bits X Y m d a hA ha).1
  unfold siteA σSlotA
  rw [h]; cases a <;> rfl

include hA in
theorem siteB_val :
    (siteB X Y m d hA).1 = if d then (X.length + 1, m + 1) else (X.length + 2, m) := by
  have h := (l_bits hA (by rw [sk_length]; omega) (sk_letters X Y m d).1).2.1
  unfold siteB σSlotB
  rw [h]; cases d <;> rfl

include hA' in
theorem siteA'_val :
    (siteA' X Y m d hA').1 = if d then (X.length + 2, m + 2) else (X.length + 1, m + 1) := by
  have h := (l_bits hA' (by rw [sk'_length]; omega) (sk'_letters X Y m d).1).2.2
  unfold siteA' σSlotA
  rw [h]; cases d <;> rfl

include hA' in
theorem siteB'_val (ha : bit Vsp X.length m = a) :
    (siteB' X Y m d hA').1 = if a then (X.length + 1, m + 2) else (X.length + 2, m + 1) := by
  have h := (sk'_bits X Y m d a hA' ha).2.2.1
  unfold siteB' σSlotB
  rw [h]; cases a <;> rfl

omit hA hA' in
theorem σSlotA_congr {W : Word} (hW : W.Closed) {k k' j j' : ℕ} (hk : k < W.length) (hk' : k' < W.length)
    (hℓ : letterAt W k = .σ j) (hℓ' : letterAt W k' = .σ j') (e : k = k') : σSlotA hW hk hℓ = σSlotA hW hk' hℓ' := by
  subst e
  have : j = j' := by rw [hℓ] at hℓ'; exact Letter.σ.inj hℓ'
  subst this
  rfl

omit hA hA' in
theorem σSlotB_congr {W : Word} (hW : W.Closed) {k k' j j' : ℕ} (hk : k < W.length) (hk' : k' < W.length)
    (hℓ : letterAt W k = .σ j) (hℓ' : letterAt W k' = .σ j') (e : k = k') : σSlotB hW hk hℓ = σSlotB hW hk' hℓ' := by
  subst e
  have : j = j' := by rw [hℓ] at hℓ'; exact Letter.σ.inj hℓ'
  subst this
  rfl

include hA in
/-- the interior `σ` slots of `A` are the two site slots -/
theorem sk_int_iff (u : Slot Vs) : IntSlot X Ps Y u ↔ u = siteA X Y m d hA ∨ u = siteB X Y m d hA := by
  constructor
  · rintro ⟨hu, hext⟩
    rw [sk_extCol] at hext
    have hlt := colOf_lt hA u
    rw [sk_length] at hlt
    have hcol : colOf u = X.length + 1 := by
      rcases Nat.lt_or_ge (colOf u) (X.length + 1) with h | h
      · exfalso
        have e : colOf u = X.length := by omega
        have := hu.1
        rw [e, (sk_letters X Y m d).1] at this
        exact Bool.noConfusion this
      · omega
    rcases eq_σSlotA_or_σSlotB hA hu with h | h
    · left; rw [h]; exact σSlotA_congr hA _ _ _ _ hcol
    · right; rw [h]; exact σSlotB_congr hA _ _ _ _ hcol
  · rintro (rfl | rfl)
    · refine ⟨isσSlot_σSlotA hA _ _, ?_⟩
      unfold siteA; rw [(σSlotA_spec hA _ _).1, sk_extCol]; omega
    · refine ⟨isσSlot_σSlotB hA _ _, ?_⟩
      unfold siteB; rw [(σSlotB_spec hA _ _).1, sk_extCol]; omega

include hA' in
theorem sk'_int_iff (u : Slot Vsp) : IntSlot X Psp Y u ↔ u = siteA' X Y m d hA' ∨ u = siteB' X Y m d hA' := by
  constructor
  · rintro ⟨hu, hext⟩
    rw [sk'_extCol] at hext
    have hlt := colOf_lt hA' u
    rw [sk'_length] at hlt
    have hcol : colOf u = X.length + 1 := by
      rcases Nat.lt_or_ge (colOf u) (X.length + 1) with h | h
      · exfalso
        have e : colOf u = X.length := by omega
        have := hu.1
        rw [e, (sk'_letters X Y m d).1] at this
        exact Bool.noConfusion this
      · omega
    rcases eq_σSlotA_or_σSlotB hA' hu with h | h
    · left; rw [h]; exact σSlotA_congr hA' _ _ _ _ hcol
    · right; rw [h]; exact σSlotB_congr hA' _ _ _ _ hcol
  · rintro (rfl | rfl)
    · refine ⟨isσSlot_σSlotA hA' _ _, ?_⟩
      unfold siteA'; rw [(σSlotA_spec hA' _ _).1, sk'_extCol]; omega
    · refine ⟨isσSlot_σSlotB hA' _ _, ?_⟩
      unfold siteB'; rw [(σSlotB_spec hA' _ _).1, sk'_extCol]; omega

include hA in
theorem siteA_int : IntSlot X Ps Y (siteA X Y m d hA) := (sk_int_iff X Y m d hA _).2 (Or.inl rfl)
include hA in
theorem siteB_int : IntSlot X Ps Y (siteB X Y m d hA) := (sk_int_iff X Y m d hA _).2 (Or.inr rfl)
include hA' in
theorem siteA'_int : IntSlot X Psp Y (siteA' X Y m d hA') := (sk'_int_iff X Y m d hA' _).2 (Or.inl rfl)
include hA' in
theorem siteB'_int : IntSlot X Psp Y (siteB' X Y m d hA') := (sk'_int_iff X Y m d hA' _).2 (Or.inr rfl)

include hA in
theorem isDesc_siteA : isDesc (siteA X Y m d hA) = true := isDesc_σSlotA hA _ _
include hA in
theorem isDesc_siteB : isDesc (siteB X Y m d hA) = false := isDesc_σSlotB hA _ _
include hA' in
theorem isDesc_siteA' : isDesc (siteA' X Y m d hA') = true := isDesc_σSlotA hA' _ _
include hA' in
theorem isDesc_siteB' : isDesc (siteB' X Y m d hA') = false := isDesc_σSlotB hA' _ _

include hA in
theorem σtwin_siteA : σtwin hA (siteA X Y m d hA) = siteB X Y m d hA := σtwin_σSlotA hA _ _
include hA in
theorem σtwin_siteB : σtwin hA (siteB X Y m d hA) = siteA X Y m d hA := σtwin_σSlotB hA _ _
include hA' in
theorem σtwin_siteA' : σtwin hA' (siteA' X Y m d hA') = siteB' X Y m d hA' := σtwin_σSlotA hA' _ _
include hA' in
theorem σtwin_siteB' : σtwin hA' (siteB' X Y m d hA') = siteA' X Y m d hA' := σtwin_σSlotB hA' _ _

include hA hA' in
/-- THE INTERIOR SLOT CORRESPONDENCE of the cusp-skein switch: the through-strand slots and the arm slots
correspond (the over bit is reversed). -/
noncomputable def skφI : {u // IntSlot X Psp Y u} ≃ {u' // IntSlot X Ps Y u'} where
  toFun u := if isDesc u.1 then ⟨siteB X Y m d hA, siteB_int X Y m d hA⟩ else ⟨siteA X Y m d hA, siteA_int X Y m d hA⟩
  invFun u := if isDesc u.1 then ⟨siteB' X Y m d hA', siteB'_int X Y m d hA'⟩
    else ⟨siteA' X Y m d hA', siteA'_int X Y m d hA'⟩
  left_inv u := by
    rcases (sk'_int_iff X Y m d hA' u.1).1 u.2 with h | h
    · simp only [h, isDesc_siteA', ↓reduceIte, isDesc_siteB, Bool.false_eq_true]
      exact Subtype.ext h.symm
    · simp only [h, isDesc_siteB', Bool.false_eq_true, ↓reduceIte, isDesc_siteA]
      exact Subtype.ext h.symm
  right_inv u := by
    rcases (sk_int_iff X Y m d hA u.1).1 u.2 with h | h
    · simp only [h, isDesc_siteA, ↓reduceIte, isDesc_siteB', Bool.false_eq_true]
      exact Subtype.ext h.symm
    · simp only [h, isDesc_siteB, Bool.false_eq_true, ↓reduceIte, isDesc_siteA']
      exact Subtype.ext h.symm

include hA hA' in
theorem skφI_siteA' : (skφI X Y m d hA hA' ⟨_, siteA'_int X Y m d hA'⟩).1 = siteB X Y m d hA := by
  simp only [skφI, Equiv.coe_fn_mk, isDesc_siteA', ↓reduceIte]

include hA hA' in
theorem skφI_siteB' : (skφI X Y m d hA hA' ⟨_, siteB'_int X Y m d hA'⟩).1 = siteA X Y m d hA := by
  simp only [skφI, Equiv.coe_fn_mk, isDesc_siteB', Bool.false_eq_true, ↓reduceIte]

include hA hA' in
theorem skφI_val (u : {u // IntSlot X Psp Y u}) :
    (skφI X Y m d hA hA' u).1 = if isDesc u.1 then siteB X Y m d hA else siteA X Y m d hA := by
  simp only [skφI, Equiv.coe_fn_mk]
  split_ifs <;> rfl

include hA hA' in
theorem skφI_desc (u : {u // IntSlot X Psp Y u}) : isDesc (skφI X Y m d hA hA' u).1 = !isDesc u.1 := by
  rw [skφI_val]
  rcases (sk'_int_iff X Y m d hA' u.1).1 u.2 with h | h
  · rw [h, isDesc_siteA']; simp [isDesc_siteB]
  · rw [h, isDesc_siteB']; simp [isDesc_siteA]

include hA hA' in
theorem skφI_twin (u : {u // IntSlot X Psp Y u}) :
    (skφI X Y m d hA hA' ⟨σtwin hA' u.1, ⟨isσSlot_σtwin hA' u.2.1, by rw [colOf_σtwin hA' u.2.1]; exact u.2.2⟩⟩).1 =
      σtwin hA (skφI X Y m d hA hA' u).1 := by
  rw [skφI_val, skφI_val]
  rcases (sk'_int_iff X Y m d hA' u.1).1 u.2 with h | h
  · simp only [h, σtwin_siteA', isDesc_siteB', Bool.false_eq_true, ↓reduceIte, isDesc_siteA', σtwin_siteB]
  · simp only [h, σtwin_siteB', isDesc_siteA', ↓reduceIte, isDesc_siteB', Bool.false_eq_true, σtwin_siteA]

include hA hA' in
theorem skφI_sgn (ha : bit Vs X.length m = a) (ha' : bit Vsp X.length m = a) (u : {u // IntSlot X Psp Y u}) :
    σsgn (skφI X Y m d hA hA' u).1 = -σsgn u.1 := by
  obtain ⟨b1, b2, -, -, -, -⟩ := sk_bits X Y m d a hA ha
  obtain ⟨-, b2', b3', -, -, -⟩ := sk'_bits X Y m d a hA' ha'
  have hcol : colOf (skφI X Y m d hA hA' u).1 = X.length + 1 := by
    rw [skφI_val]; split_ifs
    · exact (σSlotB_spec hA _ _).1
    · exact (σSlotA_spec hA _ _).1
  have hcol' : colOf u.1 = X.length + 1 := by
    rcases (sk'_int_iff X Y m d hA' u.1).1 u.2 with h | h
    · rw [h]; exact (σSlotA_spec hA' _ _).1
    · rw [h]; exact (σSlotB_spec hA' _ _).1
  have b3'' : bit Vsp (X.length + 1) (m + 1 + 1) = a := b3'
  unfold σsgn σsgnCol
  rw [hcol, hcol', (sk_letters X Y m d).2, (sk'_letters X Y m d).2]
  simp only [idx, b1, b2, b2', b3'']
  cases a <;> cases d <;> decide

end SkeinSwitch

section SkeinPassage

variable (X Y : Word) (m : ℕ) (d a : Bool)

local notation "Vs" => X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y
local notation "Vsp" => X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y
local notation "Ps" => [Letter.l (m + 1) d, Letter.σ m]
local notation "Psp" => [Letter.l m d, Letter.σ (m + 1)]

variable {P L : Cuts} (hX : Word.run X [] = some (P ++ a :: L)) (hP : P.length = m - 1) (hm : 1 ≤ m)
variable (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed)
  (hA' : (X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y).Closed)
include hX hP hm

theorem sk_sameEffect : SameEffect X Psp Ps := by
  unfold SameEffect
  rw [Word.run_append, Word.run_append, hX, Option.bind_some, Option.bind_some, run_skein_A' hm hP, run_skein_A hm hP]

omit hX hP hm in
theorem sk_extPair_of_ext (c : Slot Vsp) (hc : IsExtSlot X Psp c.1) : extPair X Psp Ps c.1 = c.1 := by
  apply sk_extPair
  obtain ⟨⟨k, p⟩, hs⟩ := c
  unfold IsExtSlot at hc
  simp only at hc ⊢
  split_ifs at hc with hp
  · unfold ExtCol at hc; simp at hc; omega
  · unfold ExtCut at hc; simp at hc; omega

/-- the exterior bits of the two principal words agree (cuts `|X|` and `|X|+2`) -/
theorem sk_bits_ext (p : ℕ) : bit Vs X.length p = bit Vsp X.length p ∧ bit Vs (X.length + 2) p = bit Vsp (X.length + 2) p := by
  have hE := sk_sameEffect X m d a hX hP hm
  have h0 := bit_ext X Psp Y Ps (by simp) hE (k := X.length) (Or.inl le_rfl) p
  have h2 := bit_ext X Psp Y Ps (by simp) hE (k := X.length + 2) (Or.inr (by simp)) p
  rw [sk_shift X m d (Or.inl le_rfl)] at h0
  rw [sk_shift X m d (Or.inr le_rfl)] at h2
  exact ⟨h0.symm, h2.symm⟩

include hA hA'

omit hA in
/-- every slot of `A'` reaches the exterior -/
theorem sk'_hexit : ∀ u : Slot Vsp, ∃ n, ExtPiece X Psp Y ((next hA')^[n] u) := by
  obtain ⟨hℓ₀, hℓ₁⟩ := sk'_letters X Y m d
  have ha' := (sk_bit_a X Y m d a hX hP).2
  obtain ⟨c1, c2, c3, e1, e2, e3⟩ := sk'_bits X Y m d a hA' ha'
  have hm1 : 1 ≤ m := hm
  -- the vertex chain
  have hv : ∀ u : Slot Vsp, u.1 = (X.length, 0) → ∃ n, ExtPiece X Psp Y ((next hA')^[n] u) := by
    intro u hu
    have h1 := next_cusp_l hA' hℓ₀ hu
    rcases Bool.eq_false_or_eq_true d with hd | hd
    · rw [ite_eq_left hd] at h1
      have hb1 : bit Vsp (X.length + 1) m = true := by rw [c1, hd]
      obtain ⟨h2, hb2⟩ := pass_r_lt hA' hℓ₁ h1 (by omega) hb1 (by simp [idx])
      refine reach_of_next hA' (reach_of_next hA' (reach_self hA' ?_))
      show ExtCol X Psp (colOf _)
      rw [block_col_true h2 (by omega) hb2, sk'_extCol]; omega
    · rw [ite_eq_right (by simp [hd])] at h1
      have hb1 : bit Vsp (X.length + 1) (m + 1) = true := by rw [c2, hd]; rfl
      have h2 := next_σ_right_idx hA' hℓ₁ h1 hb1
      have hb2 : bit Vsp (X.length + 2) (m + 1 + 1) = true := by rw [e3, hd]; rfl
      refine reach_of_next hA' (reach_of_next hA' (reach_self hA' ?_))
      show ExtCol X Psp (colOf _)
      rw [block_col_true h2 (by omega) hb2, sk'_extCol]; omega
  intro u
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  by_cases hext : ExtCol X Psp (colOf u)
  · exact reach_self hA' hext
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, sk'_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · exact hv u hu
    · exfalso; have := vertex_not_crossing hu; rw [hℓ₁] at this; exact Bool.noConfusion this
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hA' hu hp
  cases hb : bit Vsp k p
  · rw [block_col_false hu hp hb, sk'_extCol] at hext
    have : k = X.length + 1 ∨ k = X.length + 2 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := pass_l_lt hA' hℓ₀ hu hp hb (by simpa [idx] using hpm)
        refine reach_of_next hA' (reach_self hA' ?_)
        show ExtCol X Psp (colOf _)
        have := (cutSlot_facts hA' h1 hp).2.2.1
        rw [block_col_false h1 hp hb1, sk'_extCol]; omega
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have h1 := next_arm_l hA' (by omega) hℓ₀ hu (by omega) hb
        exact reach_of_next hA' (hv _ h1)
      · obtain ⟨h1, hb1⟩ := pass_l_ge hA' hℓ₀ hu hp hb (by simpa [idx, coarity] using hpm2)
        simp only [arity, coarity] at h1 hb1
        refine reach_of_next hA' (reach_self hA' ?_)
        show ExtCol X Psp (colOf _)
        have := (cutSlot_facts hA' h1 (by omega)).2.2.1
        rw [block_col_false h1 (by omega) hb1, sk'_extCol]; omega
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · obtain ⟨h1, hb1⟩ := pass_l_lt hA' hℓ₁ hu hp hb (by simpa [idx] using hpm)
        rcases lt_or_ge p m with hpm' | hpm'
        · obtain ⟨h2, hb2⟩ := pass_l_lt hA' hℓ₀ h1 hp hb1 (by simpa [idx] using hpm')
          refine reach_of_next hA' (reach_of_next hA' (reach_self hA' ?_))
          show ExtCol X Psp (colOf _)
          have := (cutSlot_facts hA' h2 hp).2.2.1
          rw [block_col_false h2 hp hb2, sk'_extCol]; omega
        · have h2 := next_arm_l hA' (by omega) hℓ₀ h1 (by omega) hb1
          exact reach_of_next hA' (reach_of_next hA' (hv _ h2))
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
        · -- `p = m + 1`: the through-strand, heading left
          rw [← hpe] at hu hb
          have h1 := next_σ_left_idx hA' hℓ₁ hu hb
          have hb1 : bit Vsp (X.length + 1) (m + 1 + 1) = false := by rw [c3, ← e2, hb]
          obtain ⟨h2, hb2⟩ := pass_l_ge hA' hℓ₀ h1 (by omega) hb1 (by simp [idx, coarity])
          simp only [arity, coarity] at h2 hb2
          refine reach_of_next hA' (reach_of_next hA' (reach_self hA' ?_))
          show ExtCol X Psp (colOf _)
          have := (cutSlot_facts hA' h2 (by omega)).2.2.1
          rw [block_col_false h2 (by omega) hb2, sk'_extCol]; omega
        · have hpe' : p = m + 1 + 1 := by omega
          rw [hpe'] at hu hb
          have h1 := next_σ_left_succ hA' hℓ₁ hu hb
          have hb1 : bit Vsp (X.length + 1) (m + 1) = false := by rw [c2, ← e3, hb]
          have h2 := next_arm_l hA' (by omega) hℓ₀ h1 (Or.inr rfl) hb1
          exact reach_of_next hA' (reach_of_next hA' (hv _ h2))
      · obtain ⟨h1, hb1⟩ := pass_l_ge hA' hℓ₁ hu hp hb (by simpa [idx, coarity] using hpm3)
        simp only [arity, coarity, Nat.add_sub_cancel] at h1 hb1
        obtain ⟨h2, hb2⟩ := pass_l_ge hA' hℓ₀ h1 hp hb1 (by simp [idx, coarity]; omega)
        simp only [arity, coarity] at h2 hb2
        refine reach_of_next hA' (reach_of_next hA' (reach_self hA' ?_))
        show ExtCol X Psp (colOf _)
        have := (cutSlot_facts hA' h2 (by omega)).2.2.1
        rw [block_col_false h2 (by omega) hb2, sk'_extCol]; omega
  · rw [block_col_true hu hp hb, sk'_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := pass_r_lt hA' hℓ₀ hu hp hb (by simpa [idx] using hpm)
        obtain ⟨h2, hb2⟩ := pass_r_lt hA' hℓ₁ h1 hp hb1 (by simp [idx]; omega)
        refine reach_of_next hA' (reach_of_next hA' (reach_self hA' ?_))
        show ExtCol X Psp (colOf _)
        rw [block_col_true h2 hp hb2, sk'_extCol]; omega
      · obtain ⟨h1, hb1⟩ := pass_r_ge hA' hℓ₀ hu hp hb (by simpa [idx, arity] using hpm)
        simp only [arity, coarity, Nat.sub_zero] at h1 hb1
        rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
        · -- `p = m`: the through-strand enters the crossing
          rw [← hpe] at h1 hb1
          have h2 := next_σ_right_succ hA' hℓ₁ h1 hb1
          have hb2 : bit Vsp (X.length + 2) (m + 1) = true := by rw [e2, ← c3, hb1]
          refine reach_of_next hA' (reach_of_next hA' (reach_self hA' ?_))
          show ExtCol X Psp (colOf _)
          rw [block_col_true h2 (by omega) hb2, sk'_extCol]; omega
        · obtain ⟨h2, hb2⟩ := pass_r_ge hA' hℓ₁ h1 (by omega) hb1 (by simp [idx, arity]; omega)
          simp only [arity, coarity, Nat.add_sub_cancel] at h2 hb2
          refine reach_of_next hA' (reach_of_next hA' (reach_self hA' ?_))
          show ExtCol X Psp (colOf _)
          rw [block_col_true h2 (by omega) hb2, sk'_extCol]; omega
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · obtain ⟨h1, hb1⟩ := pass_r_lt hA' hℓ₁ hu hp hb (by simpa [idx] using hpm)
        refine reach_of_next hA' (reach_self hA' ?_)
        show ExtCol X Psp (colOf _)
        rw [block_col_true h1 hp hb1, sk'_extCol]; omega
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
        · rw [← hpe] at hu hb
          have h1 := next_σ_right_idx hA' hℓ₁ hu hb
          have hb1 : bit Vsp (X.length + 2) (m + 1 + 1) = true := by rw [e3, ← c2, hb]
          refine reach_of_next hA' (reach_self hA' ?_)
          show ExtCol X Psp (colOf _)
          rw [block_col_true h1 (by omega) hb1, sk'_extCol]; omega
        · have hpe' : p = m + 1 + 1 := by omega
          rw [hpe'] at hu hb
          have h1 := next_σ_right_succ hA' hℓ₁ hu hb
          have hb1 : bit Vsp (X.length + 2) (m + 1) = true := by rw [e2, ← c3, hb]
          refine reach_of_next hA' (reach_self hA' ?_)
          show ExtCol X Psp (colOf _)
          rw [block_col_true h1 (by omega) hb1, sk'_extCol]; omega
      · obtain ⟨h1, hb1⟩ := pass_r_ge hA' hℓ₁ hu hp hb (by simpa [idx, arity] using hpm3)
        simp only [arity, coarity, Nat.add_sub_cancel] at h1 hb1
        refine reach_of_next hA' (reach_self hA' ?_)
        show ExtCol X Psp (colOf _)
        rw [block_col_true h1 hp hb1, sk'_extCol]; omega

omit hA' in
/-- every slot of `A` reaches the exterior -/
theorem sk_hexit : ∀ u : Slot Vs, ∃ n, ExtPiece X Ps Y ((next hA)^[n] u) := by
  obtain ⟨hℓ₀, hℓ₁⟩ := sk_letters X Y m d
  have ha := (sk_bit_a X Y m d a hX hP).1
  obtain ⟨c1, c2, c3, e1, e2, e3⟩ := sk_bits X Y m d a hA ha
  have hm1 : 1 ≤ m := hm
  have hv : ∀ u : Slot Vs, u.1 = (X.length, 0) → ∃ n, ExtPiece X Ps Y ((next hA)^[n] u) := by
    intro u hu
    have h1 := next_cusp_l hA hℓ₀ hu
    rcases Bool.eq_false_or_eq_true d with hd | hd
    · rw [ite_eq_left hd] at h1
      have hb1 : bit Vs (X.length + 1) (m + 1) = true := by rw [c2, hd]
      have h2 := next_σ_right_succ hA hℓ₁ h1 hb1
      have hb2 : bit Vs (X.length + 2) m = true := by rw [e1, hd]
      refine reach_of_next hA (reach_of_next hA (reach_self hA ?_))
      show ExtCol X Ps (colOf _)
      rw [block_col_true h2 (by omega) hb2, sk_extCol]; omega
    · rw [ite_eq_right (by simp [hd])] at h1
      have hb1 : bit Vs (X.length + 1) (m + 1 + 1) = true := by rw [c3, hd]; rfl
      obtain ⟨h2, hb2⟩ := pass_r_ge hA hℓ₁ h1 (by omega) hb1 (by simp [idx, arity])
      simp only [arity, coarity, Nat.add_sub_cancel] at h2 hb2
      refine reach_of_next hA (reach_of_next hA (reach_self hA ?_))
      show ExtCol X Ps (colOf _)
      rw [block_col_true h2 (by omega) hb2, sk_extCol]; omega
  intro u
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  by_cases hext : ExtCol X Ps (colOf u)
  · exact reach_self hA hext
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, sk_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · exact hv u hu
    · exfalso; have := vertex_not_crossing hu; rw [hℓ₁] at this; exact Bool.noConfusion this
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hA hu hp
  cases hb : bit Vs k p
  · rw [block_col_false hu hp hb, sk_extCol] at hext
    have : k = X.length + 1 ∨ k = X.length + 2 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · obtain ⟨h1, hb1⟩ := pass_l_lt hA hℓ₀ hu hp hb (by simpa [idx] using hpm)
        refine reach_of_next hA (reach_self hA ?_)
        show ExtCol X Ps (colOf _)
        have := (cutSlot_facts hA h1 hp).2.2.1
        rw [block_col_false h1 hp hb1, sk_extCol]; omega
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have h1 := next_arm_l hA (by omega) hℓ₀ hu (by omega) hb
        exact reach_of_next hA (hv _ h1)
      · obtain ⟨h1, hb1⟩ := pass_l_ge hA hℓ₀ hu hp hb (by simpa [idx, coarity] using hpm3)
        simp only [arity, coarity] at h1 hb1
        refine reach_of_next hA (reach_self hA ?_)
        show ExtCol X Ps (colOf _)
        have := (cutSlot_facts hA h1 (by omega)).2.2.1
        rw [block_col_false h1 (by omega) hb1, sk_extCol]; omega
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := pass_l_lt hA hℓ₁ hu hp hb (by simpa [idx] using hpm)
        obtain ⟨h2, hb2⟩ := pass_l_lt hA hℓ₀ h1 hp hb1 (by simp [idx]; omega)
        refine reach_of_next hA (reach_of_next hA (reach_self hA ?_))
        show ExtCol X Ps (colOf _)
        have := (cutSlot_facts hA h2 hp).2.2.1
        rw [block_col_false h2 hp hb2, sk_extCol]; omega
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
        · -- `p = m`: the upper arm heading left
          rw [← hpe] at hu hb
          have h1 := next_σ_left_idx hA hℓ₁ hu hb
          have hb1 : bit Vs (X.length + 1) (m + 1) = false := by rw [c2, ← e1, hb]
          have h2 := next_arm_l hA (by omega) hℓ₀ h1 (Or.inl rfl) hb1
          exact reach_of_next hA (reach_of_next hA (hv _ h2))
        · have hpe' : p = m + 1 := by omega
          rw [hpe'] at hu hb
          have h1 := next_σ_left_succ hA hℓ₁ hu hb
          have hb1 : bit Vs (X.length + 1) m = false := by rw [c1, ← e2, hb]
          obtain ⟨h2, hb2⟩ := pass_l_lt hA hℓ₀ h1 (by omega) hb1 (by simp [idx])
          refine reach_of_next hA (reach_of_next hA (reach_self hA ?_))
          show ExtCol X Ps (colOf _)
          have := (cutSlot_facts hA h2 (by omega)).2.2.1
          rw [block_col_false h2 (by omega) hb2, sk_extCol]; omega
      · obtain ⟨h1, hb1⟩ := pass_l_ge hA hℓ₁ hu hp hb (by simpa [idx, coarity] using hpm2)
        simp only [arity, coarity, Nat.add_sub_cancel] at h1 hb1
        rcases lt_or_ge p (m + 3) with hpm3 | hpm3
        · have h2 := next_arm_l hA (by omega) hℓ₀ h1 (by omega) hb1
          exact reach_of_next hA (reach_of_next hA (hv _ h2))
        · obtain ⟨h2, hb2⟩ := pass_l_ge hA hℓ₀ h1 hp hb1 (by simpa [idx, coarity] using hpm3)
          simp only [arity, coarity] at h2 hb2
          refine reach_of_next hA (reach_of_next hA (reach_self hA ?_))
          show ExtCol X Ps (colOf _)
          have := (cutSlot_facts hA h2 (by omega)).2.2.1
          rw [block_col_false h2 (by omega) hb2, sk_extCol]; omega
  · rw [block_col_true hu hp hb, sk_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · obtain ⟨h1, hb1⟩ := pass_r_lt hA hℓ₀ hu hp hb (by simpa [idx] using hpm)
        rcases lt_or_ge p m with hpm' | hpm'
        · obtain ⟨h2, hb2⟩ := pass_r_lt hA hℓ₁ h1 hp hb1 (by simpa [idx] using hpm')
          refine reach_of_next hA (reach_of_next hA (reach_self hA ?_))
          show ExtCol X Ps (colOf _)
          rw [block_col_true h2 hp hb2, sk_extCol]; omega
        · have hpe : p = m := by omega
          rw [hpe] at h1 hb1
          have h2 := next_σ_right_idx hA hℓ₁ h1 hb1
          have hb2 : bit Vs (X.length + 2) (m + 1) = true := by rw [e2, ← c1, hb1]
          refine reach_of_next hA (reach_of_next hA (reach_self hA ?_))
          show ExtCol X Ps (colOf _)
          rw [block_col_true h2 (by omega) hb2, sk_extCol]; omega
      · obtain ⟨h1, hb1⟩ := pass_r_ge hA hℓ₀ hu hp hb (by simpa [idx, arity] using hpm)
        simp only [arity, coarity, Nat.sub_zero] at h1 hb1
        obtain ⟨h2, hb2⟩ := pass_r_ge hA hℓ₁ h1 (by omega) hb1 (by simp [idx, arity]; omega)
        simp only [arity, coarity, Nat.add_sub_cancel] at h2 hb2
        refine reach_of_next hA (reach_of_next hA (reach_self hA ?_))
        show ExtCol X Ps (colOf _)
        rw [block_col_true h2 (by omega) hb2, sk_extCol]; omega
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := pass_r_lt hA hℓ₁ hu hp hb (by simpa [idx] using hpm)
        refine reach_of_next hA (reach_self hA ?_)
        show ExtCol X Ps (colOf _)
        rw [block_col_true h1 hp hb1, sk_extCol]; omega
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
        · rw [← hpe] at hu hb
          have h1 := next_σ_right_idx hA hℓ₁ hu hb
          have hb1 : bit Vs (X.length + 2) (m + 1) = true := by rw [e2, ← c1, hb]
          refine reach_of_next hA (reach_self hA ?_)
          show ExtCol X Ps (colOf _)
          rw [block_col_true h1 (by omega) hb1, sk_extCol]; omega
        · have hpe' : p = m + 1 := by omega
          rw [hpe'] at hu hb
          have h1 := next_σ_right_succ hA hℓ₁ hu hb
          have hb1 : bit Vs (X.length + 2) m = true := by rw [e1, ← c2, hb]
          refine reach_of_next hA (reach_self hA ?_)
          show ExtCol X Ps (colOf _)
          rw [block_col_true h1 (by omega) hb1, sk_extCol]; omega
      · obtain ⟨h1, hb1⟩ := pass_r_ge hA hℓ₁ hu hp hb (by simpa [idx, arity] using hpm2)
        simp only [arity, coarity, Nat.add_sub_cancel] at h1 hb1
        refine reach_of_next hA (reach_self hA ?_)
        show ExtCol X Ps (colOf _)
        rw [block_col_true h1 hp hb1, sk_extCol]; omega

end SkeinPassage

section SkeinIntPassage

variable (X Y : Word) (m : ℕ) (d a : Bool)

local notation "Vs" => X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y
local notation "Vsp" => X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y
local notation "Ps" => [Letter.l (m + 1) d, Letter.σ m]
local notation "Psp" => [Letter.l m d, Letter.σ (m + 1)]

variable (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed)
  (hA' : (X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y).Closed)

/-! non-active block slots and exterior slots by coordinates -/

omit hA in
theorem sk'_notAct_r {s : Slot Vsp} {k p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) (hb : bit Vsp k p = true)
    (hk : k = X.length ∨ k = X.length + 1) (hσ : k = X.length + 1 → p ≠ m + 1 ∧ p ≠ m + 2) : ¬ ActE X Psp Y s := by
  refine not_actE_of X Psp Y (by rw [block_col_true hs hp hb, sk'_extCol]; omega) ?_
  refine not_σ_right hs hp hb (fun j hj => ?_)
  rcases hk with rfl | rfl
  · rw [(sk'_letters X Y m d).1] at hj; cases hj
  · rw [(sk'_letters X Y m d).2] at hj; injection hj with hj; subst hj; exact hσ rfl

omit hA in
theorem sk'_notAct_l {s : Slot Vsp} {k q : ℕ} (hs : s.1 = (k + 1, q)) (hq : q ≠ 0) (hb : bit Vsp (k + 1) q = false)
    (hk : k = X.length ∨ k = X.length + 1) (hσ : k = X.length + 1 → q ≠ m + 1 ∧ q ≠ m + 2) : ¬ ActE X Psp Y s := by
  refine not_actE_of X Psp Y (by rw [block_col_false hs hq hb, Nat.add_sub_cancel, sk'_extCol]; omega) ?_
  refine not_σ_left hs hq hb (fun j hj => ?_)
  rcases hk with rfl | rfl
  · rw [(sk'_letters X Y m d).1] at hj; cases hj
  · rw [(sk'_letters X Y m d).2] at hj; injection hj with hj; subst hj; exact hσ rfl

omit hA in
theorem sk'_notAct_v {s : Slot Vsp} {k : ℕ} (hs : s.1 = (k, 0)) (hk : k = X.length ∨ k = X.length + 1) :
    ¬ ActE X Psp Y s :=
  not_actE_of X Psp Y (by rw [block_col_vertex hs, sk'_extCol]; omega) (not_σ_vertex hs)

omit hA' in
theorem sk_notAct_r {s : Slot Vs} {k p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) (hb : bit Vs k p = true)
    (hk : k = X.length ∨ k = X.length + 1) (hσ : k = X.length + 1 → p ≠ m ∧ p ≠ m + 1) : ¬ ActE X Ps Y s := by
  refine not_actE_of X Ps Y (by rw [block_col_true hs hp hb, sk_extCol]; omega) ?_
  refine not_σ_right hs hp hb (fun j hj => ?_)
  rcases hk with rfl | rfl
  · rw [(sk_letters X Y m d).1] at hj; cases hj
  · rw [(sk_letters X Y m d).2] at hj; injection hj with hj; subst hj; exact hσ rfl

omit hA' in
theorem sk_notAct_l {s : Slot Vs} {k q : ℕ} (hs : s.1 = (k + 1, q)) (hq : q ≠ 0) (hb : bit Vs (k + 1) q = false)
    (hk : k = X.length ∨ k = X.length + 1) (hσ : k = X.length + 1 → q ≠ m ∧ q ≠ m + 1) : ¬ ActE X Ps Y s := by
  refine not_actE_of X Ps Y (by rw [block_col_false hs hq hb, Nat.add_sub_cancel, sk_extCol]; omega) ?_
  refine not_σ_left hs hq hb (fun j hj => ?_)
  rcases hk with rfl | rfl
  · rw [(sk_letters X Y m d).1] at hj; cases hj
  · rw [(sk_letters X Y m d).2] at hj; injection hj with hj; subst hj; exact hσ rfl

omit hA' in
theorem sk_notAct_v {s : Slot Vs} {k : ℕ} (hs : s.1 = (k, 0)) (hk : k = X.length ∨ k = X.length + 1) :
    ¬ ActE X Ps Y s :=
  not_actE_of X Ps Y (by rw [block_col_vertex hs, sk_extCol]; omega) (not_σ_vertex hs)

omit hA in
theorem sk'_ext_r {s : Slot Vsp} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p ≠ 0) (hb : bit Vsp (X.length + 2) p = true) :
    ExtCol X Psp (colOf s) := by rw [block_col_true hs hp hb, sk'_extCol]; omega

include hA' in
theorem sk'_ext_l {s : Slot Vsp} {q : ℕ} (hs : s.1 = (X.length, q)) (hq : q ≠ 0) (hb : bit Vsp X.length q = false) :
    ExtCol X Psp (colOf s) := by
  have := (cutSlot_facts hA' hs hq).2.2.1
  rw [block_col_false hs hq hb, sk'_extCol]; omega

omit hA' in
theorem sk_ext_r {s : Slot Vs} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p ≠ 0) (hb : bit Vs (X.length + 2) p = true) :
    ExtCol X Ps (colOf s) := by rw [block_col_true hs hp hb, sk_extCol]; omega

include hA in
theorem sk_ext_l {s : Slot Vs} {q : ℕ} (hs : s.1 = (X.length, q)) (hq : q ≠ 0) (hb : bit Vs X.length q = false) :
    ExtCol X Ps (colOf s) := by
  have := (cutSlot_facts hA hs hq).2.2.1
  rw [block_col_false hs hq hb, sk_extCol]; omega

variable {P L : Cuts} (hX : Word.run X [] = some (P ++ a :: L)) (hP : P.length = m - 1) (hm : 1 ≤ m)
include hX hP hm hA hA'

/-- THE EXTENDED BLOCK PASSAGE of the cusp-skein interchange, from `A'` to `A`. -/
theorem sk_intPassage :
    IntPassage X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' hA (skφI X Y m d hA hA') := by
  have hE := sk_sameEffect X m d a hX hP hm
  have hPne : Psp ≠ [] := sk_Pne m d
  obtain ⟨hℓ₀', hℓ₁'⟩ := sk'_letters X Y m d
  obtain ⟨hℓ₀, hℓ₁⟩ := sk_letters X Y m d
  have ha' := (sk_bit_a X Y m d a hX hP).2
  have ha := (sk_bit_a X Y m d a hX hP).1
  obtain ⟨c1', c2', c3', e1', e2', e3'⟩ := sk'_bits X Y m d a hA' ha'
  obtain ⟨c1, c2, c3, e1, e2, e3⟩ := sk_bits X Y m d a hA ha
  have hbx := sk_bits_ext X Y m d a hX hP hm
  -- the value of the glued correspondence
  have φext : ∀ (c : Slot Vsp) (hc : ExtCol X Psp (colOf c)),
      (φA X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' (skφI X Y m d hA hA') ⟨c, Or.inl hc⟩).1.1 = c.1 :=
    fun c hc => (φA_val_ext' X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' _ ⟨c, Or.inl hc⟩ hc).trans
      (sk_extPair_of_ext X Y m d c (isExtSlot_of_extCol X Psp Y Ps hPne hE c hc))
  have φintA : ∀ (hc : ActE X Psp Y (siteA' X Y m d hA')),
      (φA X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' (skφI X Y m d hA hA') ⟨_, hc⟩).1 =
        siteB X Y m d hA :=
    fun hc => (φA_val_int X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' _ ⟨_, hc⟩
      (siteA'_int X Y m d hA').2).trans (skφI_siteA' X Y m d hA hA')
  have φintB : ∀ (hc : ActE X Psp Y (siteB' X Y m d hA')),
      (φA X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' (skφI X Y m d hA hA') ⟨_, hc⟩).1 =
        siteA X Y m d hA :=
    fun hc => (φA_val_int X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' _ ⟨_, hc⟩
      (siteB'_int X Y m d hA').2).trans (skφI_siteB' X Y m d hA hA')
  have φcongr : ∀ (c c' : Slot Vsp) (hc : ActE X Psp Y c) (hc' : ActE X Psp Y c'), c = c' →
      (φA X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' (skφI X Y m d hA hA') ⟨c, hc⟩).1 =
      (φA X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' (skφI X Y m d hA hA') ⟨c', hc'⟩).1 := by
    rintro c c' hc hc' rfl; rfl
  have hsA' := siteA'_val X Y m d hA'
  have hsB' := siteB'_val X Y m d a hA' ha'
  have hsA := siteA_val X Y m d a hA ha
  have hsB := siteB_val X Y m d hA
  constructor
  · -- the entries
    intro b hext hcol
    let b' : Slot Vs := ⟨extPair X Psp Ps b.1, isSlot_ext X Psp Y Ps hPne hE b.2 hext⟩
    have hb'v : b'.1 = b.1 := sk_extPair_of_ext X Y m d b hext
    rcases (entry_iff X Psp Y hPne hA' b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
    · -- from the left at `(|X|, p)`
      have hb' : b'.1 = (X.length, p) := hb'v.trans hb
      have hbit' : bit Vs X.length p = true := by rw [(hbx p).1]; exact hbit
      have nb0 : ¬ ActE X Psp Y b := sk'_notAct_r X Y m d hb hp hbit (Or.inl rfl) (by omega)
      have nb0' : ¬ ActE X Ps Y b' := sk_notAct_r X Y m d hb' hp hbit' (Or.inl rfl) (by omega)
      rcases lt_or_ge p m with hpm | hpm
      · -- above the site
        obtain ⟨h1, hb1⟩ := pass_r_lt hA' hℓ₀' hb hp hbit (by simpa [idx] using hpm)
        obtain ⟨h2, hb2⟩ := pass_r_lt hA' hℓ₁' h1 hp hb1 (by simp [idx]; omega)
        obtain ⟨h1', hb1'⟩ := pass_r_lt hA hℓ₀ hb' hp hbit' (by simp [idx]; omega)
        obtain ⟨h2', hb2'⟩ := pass_r_lt hA hℓ₁ h1' hp hb1' (by simpa [idx] using hpm)
        have hcE := sk'_ext_r X Y m d h2 hp hb2
        obtain ⟨n, hc, hmin⟩ := apassage_step hA' (ActE X Psp Y) nb0
          (apassage_step hA' _ (sk'_notAct_r X Y m d h1 hp hb1 (Or.inr rfl) (by omega)) (apassage_end hA' _))
        obtain ⟨n', hc', hmin'⟩ := apassage_step hA (ActE X Ps Y) nb0'
          (apassage_step hA _ (sk_notAct_r X Y m d h1' hp hb1' (Or.inr rfl) (by omega)) (apassage_end hA _))
        refine ⟨n, _, Or.inl hcE, hc, hmin, n', b', rfl, ?_, hmin'⟩
        rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
      rcases Nat.eq_or_lt_of_le hpm with hpe | hpm1
      · -- `p = m`: the through-strand enters the crossing at once
        rw [← hpe] at hb hb' hbit hbit'
        have hat : a = true := ha'.symm.trans hbit
        obtain ⟨h1, hb1⟩ := pass_r_ge hA' hℓ₀' hb (by omega) hbit (by simp [idx, arity])
        simp only [arity, coarity, Nat.sub_zero] at h1 hb1
        have hcb : next hA' b = siteB' X Y m d hA' := Subtype.ext (by rw [h1, hsB', ite_eq_left hat])
        obtain ⟨h1', hb1'⟩ := pass_r_lt hA hℓ₀ hb' (by omega) hbit' (by simp [idx])
        have hcb' : next hA b' = siteA X Y m d hA := Subtype.ext (by rw [h1', hsA, ite_eq_left hat])
        obtain ⟨n, hc, hmin⟩ := apassage_step hA' (ActE X Psp Y) nb0 (apassage_end hA' _)
        obtain ⟨n', hc', hmin'⟩ := apassage_step hA (ActE X Ps Y) nb0' (apassage_end hA _)
        have hcA : ActE X Psp Y (next hA' b) := by rw [hcb]; exact Or.inr (siteB'_int X Y m d hA')
        refine ⟨n, _, hcA, hc, hmin, n', b', rfl, ?_, hmin'⟩
        rw [hc', hcb']
        exact ((φcongr _ _ hcA (Or.inr (siteB'_int X Y m d hA')) hcb).trans (φintB _)).symm
      · -- below the site
        obtain ⟨h1, hb1⟩ := pass_r_ge hA' hℓ₀' hb hp hbit (by simp [idx, arity]; omega)
        simp only [arity, coarity, Nat.sub_zero] at h1 hb1
        obtain ⟨h2, hb2⟩ := pass_r_ge hA' hℓ₁' h1 (by omega) hb1 (by simp [idx, arity]; omega)
        simp only [arity, coarity, Nat.add_sub_cancel] at h2 hb2
        obtain ⟨h1', hb1'⟩ := pass_r_ge hA hℓ₀ hb' hp hbit' (by simp [idx, arity]; omega)
        simp only [arity, coarity, Nat.sub_zero] at h1' hb1'
        obtain ⟨h2', hb2'⟩ := pass_r_ge hA hℓ₁ h1' (by omega) hb1' (by simp [idx, arity]; omega)
        simp only [arity, coarity, Nat.add_sub_cancel] at h2' hb2'
        have hcE := sk'_ext_r X Y m d h2 (by omega) hb2
        obtain ⟨n, hc, hmin⟩ := apassage_step hA' (ActE X Psp Y) nb0
          (apassage_step hA' _ (sk'_notAct_r X Y m d h1 (by omega) hb1 (Or.inr rfl) (by omega)) (apassage_end hA' _))
        obtain ⟨n', hc', hmin'⟩ := apassage_step hA (ActE X Ps Y) nb0'
          (apassage_step hA _ (sk_notAct_r X Y m d h1' (by omega) hb1' (Or.inr rfl) (by omega)) (apassage_end hA _))
        refine ⟨n, _, Or.inl hcE, hc, hmin, n', b', rfl, ?_, hmin'⟩
        rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
    · -- from the right at `(|X|+2, p)`
      replace hb : b.1 = (X.length + 2, p) := hb
      replace hbit : bit Vsp (X.length + 2) p = false := hbit
      have hb' : b'.1 = (X.length + 2, p) := hb'v.trans hb
      have hbit' : bit Vs (X.length + 2) p = false := by rw [(hbx p).2]; exact hbit
      rcases lt_or_ge p m with hpm | hpm
      · -- above the site
        obtain ⟨h1, hb1⟩ := pass_l_lt hA' hℓ₁' hb hp hbit (by simp [idx]; omega)
        obtain ⟨h2, hb2⟩ := pass_l_lt hA' hℓ₀' h1 hp hb1 (by simpa [idx] using hpm)
        obtain ⟨h1', hb1'⟩ := pass_l_lt hA hℓ₁ hb' hp hbit' (by simpa [idx] using hpm)
        obtain ⟨h2', hb2'⟩ := pass_l_lt hA hℓ₀ h1' hp hb1' (by simp [idx]; omega)
        have hcE := sk'_ext_l X Y m d hA' h2 hp hb2
        obtain ⟨n, hc, hmin⟩ := apassage_step hA' (ActE X Psp Y)
          (sk'_notAct_l X Y m d hb hp hbit (Or.inr rfl) (by omega))
          (apassage_step hA' _ (sk'_notAct_l X Y m d h1 hp hb1 (Or.inl rfl) (by omega)) (apassage_end hA' _))
        obtain ⟨n', hc', hmin'⟩ := apassage_step hA (ActE X Ps Y)
          (sk_notAct_l X Y m d hb' hp hbit' (Or.inr rfl) (by omega))
          (apassage_step hA _ (sk_notAct_l X Y m d h1' hp hb1' (Or.inl rfl) (by omega)) (apassage_end hA _))
        refine ⟨n, _, Or.inl hcE, hc, hmin, n', b', rfl, ?_, hmin'⟩
        rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · -- the three site positions
        have hp3 : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
        rcases hp3 with hpe | hpe | hpe
        · -- `p = m`: the upper arm heading left; in `A` this is the arm slot at once
          rw [hpe] at hb hb' hbit hbit'
          have hdf : d = false := e1'.symm.trans hbit
          obtain ⟨h1, hb1⟩ := pass_l_lt hA' hℓ₁' hb (by omega) hbit (by simp [idx])
          have h2 := next_arm_l hA' (by rw [sk'_length]; omega) hℓ₀' h1 (Or.inl rfl) hb1
          have h3 := next_cusp_l hA' hℓ₀' h2
          rw [ite_eq_right (by simp [hdf])] at h3
          have hb3 : bit Vsp (X.length + 1) (m + 1) = true := by rw [c2', hdf]; rfl
          have hcb : next hA' (next hA' (next hA' b)) = siteA' X Y m d hA' :=
            Subtype.ext (by rw [h3, hsA', ite_eq_right (by simp [hdf])])
          have hcb' : b' = siteB X Y m d hA := Subtype.ext (by rw [hb', hsB, ite_eq_right (by simp [hdf])])
          obtain ⟨n, hc, hmin⟩ := apassage_step hA' (ActE X Psp Y)
            (sk'_notAct_l X Y m d hb (by omega) hbit (Or.inr rfl) (by omega))
            (apassage_step hA' _ (sk'_notAct_l X Y m d h1 (by omega) hb1 (Or.inl rfl) (by omega))
            (apassage_step hA' _ (sk'_notAct_v X Y m d h2 (Or.inl rfl)) (apassage_end hA' _)))
          have hcA : ActE X Psp Y (next hA' (next hA' (next hA' b))) := by
            rw [hcb]; exact Or.inr (siteA'_int X Y m d hA')
          refine ⟨n, _, hcA, hc, hmin, 0, b', rfl, ?_, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
          rw [Function.iterate_zero, id, hcb']
          exact ((φcongr _ _ hcA (Or.inr (siteA'_int X Y m d hA')) hcb).trans (φintA _)).symm
        · -- `p = m + 1`: the through-strand heading left is the site slot in both words
          rw [hpe] at hb hb' hbit hbit'
          have haf : a = false := e2'.symm.trans hbit
          have hcb : b = siteB' X Y m d hA' := Subtype.ext (by rw [hb, hsB', ite_eq_right (by simp [haf])])
          have hcb' : b' = siteA X Y m d hA := Subtype.ext (by rw [hb', hsA, ite_eq_right (by simp [haf])])
          have hcA : ActE X Psp Y b := by rw [hcb]; exact Or.inr (siteB'_int X Y m d hA')
          refine ⟨0, b, hcA, rfl, fun _ hi => absurd hi (Nat.not_lt_zero _), 0, b', rfl, ?_,
            fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
          rw [Function.iterate_zero, id, hcb']
          exact ((φcongr _ _ hcA (Or.inr (siteB'_int X Y m d hA')) hcb).trans (φintB _)).symm
        · -- `p = m + 2`: the lower arm heading left is the site slot of `A'`; in `A` it reaches the arm slot
          rw [hpe] at hb hb' hbit hbit'
          have hdt : d = true := by
            have := e3'.symm.trans hbit
            cases d <;> simp_all
          have hcb : b = siteA' X Y m d hA' := Subtype.ext (by rw [hb, hsA', ite_eq_left hdt])
          have hcA : ActE X Psp Y b := by rw [hcb]; exact Or.inr (siteA'_int X Y m d hA')
          obtain ⟨h1', hb1'⟩ := pass_l_ge hA hℓ₁ hb' (by omega) hbit' (by simp [idx, coarity])
          simp only [arity, coarity, Nat.add_sub_cancel] at h1' hb1'
          have h2' := next_arm_l hA (by rw [sk_length]; omega) hℓ₀ h1' (Or.inr rfl) hb1'
          have h3' := next_cusp_l hA hℓ₀ h2'
          rw [ite_eq_left hdt] at h3'
          have hcb' : next hA (next hA (next hA b')) = siteB X Y m d hA :=
            Subtype.ext (by rw [h3', hsB, ite_eq_left hdt])
          obtain ⟨n', hc', hmin'⟩ := apassage_step hA (ActE X Ps Y)
            (sk_notAct_l X Y m d hb' (by omega) hbit' (Or.inr rfl) (by omega))
            (apassage_step hA _ (sk_notAct_l X Y m d h1' (by omega) hb1' (Or.inl rfl) (by omega))
            (apassage_step hA _ (sk_notAct_v X Y m d h2' (Or.inl rfl)) (apassage_end hA _)))
          refine ⟨0, b, hcA, rfl, fun _ hi => absurd hi (Nat.not_lt_zero _), n', b', rfl, ?_, hmin'⟩
          rw [hc', hcb']
          exact ((φcongr _ _ hcA (Or.inr (siteA'_int X Y m d hA')) hcb).trans (φintA _)).symm
      · -- below the site
        obtain ⟨h1, hb1⟩ := pass_l_ge hA' hℓ₁' hb hp hbit (by simp [idx, coarity]; omega)
        simp only [arity, coarity, Nat.add_sub_cancel] at h1 hb1
        obtain ⟨h2, hb2⟩ := pass_l_ge hA' hℓ₀' h1 hp hb1 (by simp [idx, coarity]; omega)
        simp only [arity, coarity] at h2 hb2
        obtain ⟨h1', hb1'⟩ := pass_l_ge hA hℓ₁ hb' hp hbit' (by simp [idx, coarity]; omega)
        simp only [arity, coarity, Nat.add_sub_cancel] at h1' hb1'
        obtain ⟨h2', hb2'⟩ := pass_l_ge hA hℓ₀ h1' hp hb1' (by simp [idx, coarity]; omega)
        simp only [arity, coarity] at h2' hb2'
        have hcE := sk'_ext_l X Y m d hA' h2 (by omega) hb2
        obtain ⟨n, hc, hmin⟩ := apassage_step hA' (ActE X Psp Y)
          (sk'_notAct_l X Y m d hb hp hbit (Or.inr rfl) (by omega))
          (apassage_step hA' _ (sk'_notAct_l X Y m d h1 hp hb1 (Or.inl rfl) (by omega)) (apassage_end hA' _))
        obtain ⟨n', hc', hmin'⟩ := apassage_step hA (ActE X Ps Y)
          (sk_notAct_l X Y m d hb' hp hbit' (Or.inr rfl) (by omega))
          (apassage_step hA _ (sk_notAct_l X Y m d h1' hp hb1' (Or.inl rfl) (by omega)) (apassage_end hA _))
        refine ⟨n, _, Or.inl hcE, hc, hmin, n', b', rfl, ?_, hmin'⟩
        rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
  · -- the interior slots
    intro u hu
    rcases (sk'_int_iff X Y m d hA' u).1 hu with rfl | rfl
    · -- the arm slot of `A'` ↦ the arm slot of `A`
      have hφ : (skφI X Y m d hA hA' ⟨_, hu⟩).1 = siteB X Y m d hA := skφI_siteA' X Y m d hA hA'
      rcases Bool.eq_false_or_eq_true d with hdt | hdf
      · -- `d = true`: `(|X|+2, m+2)` leftward, through the cusp, out at `(|X|+2, m)`
        have hu1 : (siteA' X Y m d hA').1 = (X.length + 2, m + 1 + 1) := by rw [hsA', ite_eq_left hdt]
        have hb1 : bit Vsp (X.length + 2) (m + 1 + 1) = false := by rw [e3', hdt]; rfl
        have h1 := next_σ_left_succ hA' hℓ₁' hu1 hb1
        have hb2 : bit Vsp (X.length + 1) (m + 1) = false := by rw [c2', hdt]; rfl
        have h2 := next_arm_l hA' (by rw [sk'_length]; omega) hℓ₀' h1 (Or.inr rfl) hb2
        have h3 := next_cusp_l hA' hℓ₀' h2
        rw [ite_eq_left hdt] at h3
        have hb3 : bit Vsp (X.length + 1) m = true := by rw [c1', hdt]
        obtain ⟨h4, hb4⟩ := pass_r_lt hA' hℓ₁' h3 (by omega) hb3 (by simp [idx])
        have hcE := sk'_ext_r X Y m d h4 (by omega) hb4
        obtain ⟨n, hn, hc, hmin⟩ := apassage_pos hA' (ActE X Psp Y)
          (apassage_step hA' _ (sk'_notAct_l X Y m d h1 (by omega) hb2 (Or.inl rfl) (by omega))
          (apassage_step hA' _ (sk'_notAct_v X Y m d h2 (Or.inl rfl))
          (apassage_step hA' _ (sk'_notAct_r X Y m d h3 (by omega) hb3 (Or.inr rfl) (by omega)) (apassage_end hA' _))))
        have hu1' : (siteB X Y m d hA).1 = (X.length + 1, m + 1) := by rw [hsB, ite_eq_left hdt]
        have hb1' : bit Vs (X.length + 1) (m + 1) = true := by rw [c2, hdt]
        have h1' := next_σ_right_succ hA hℓ₁ hu1' hb1'
        refine ⟨n, hn, _, Or.inl hcE, hc, hmin, 1, one_pos, ?_,
          fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _)⟩
        rw [Function.iterate_one, hφ]; apply Subtype.ext; rw [φext _ hcE, h4, h1']
      · -- `d = false`: `(|X|+1, m+1)` rightward through the crossing, out at `(|X|+2, m+2)`
        have hu1 : (siteA' X Y m d hA').1 = (X.length + 1, m + 1) := by rw [hsA', ite_eq_right (by simp [hdf])]
        have hb1 : bit Vsp (X.length + 1) (m + 1) = true := by rw [c2', hdf]; rfl
        have h1 := next_σ_right_idx hA' hℓ₁' hu1 hb1
        have hb1e : bit Vsp (X.length + 2) (m + 1 + 1) = true := by rw [e3', hdf]; rfl
        have hcE := sk'_ext_r X Y m d h1 (by omega) hb1e
        obtain ⟨n, hn, hc, hmin⟩ := apassage_pos hA' (ActE X Psp Y) (apassage_end hA' _)
        have hu1' : (siteB X Y m d hA).1 = (X.length + 2, m) := by rw [hsB, ite_eq_right (by simp [hdf])]
        have hb1' : bit Vs (X.length + 2) m = false := by rw [e1, hdf]
        have h1' := next_σ_left_idx hA hℓ₁ hu1' hb1'
        have hb2' : bit Vs (X.length + 1) (m + 1) = false := by rw [c2, hdf]
        have h2' := next_arm_l hA (by rw [sk_length]; omega) hℓ₀ h1' (Or.inl rfl) hb2'
        have h3' := next_cusp_l hA hℓ₀ h2'
        rw [ite_eq_right (by simp [hdf])] at h3'
        have hb3' : bit Vs (X.length + 1) (m + 1 + 1) = true := by rw [c3, hdf]; rfl
        obtain ⟨h4', hb4'⟩ := pass_r_ge hA hℓ₁ h3' (by omega) hb3' (by simp [idx, arity])
        simp only [arity, coarity, Nat.add_sub_cancel] at h4' hb4'
        obtain ⟨n', hn', hc', hmin'⟩ := apassage_pos hA (ActE X Ps Y)
          (apassage_step hA _ (sk_notAct_l X Y m d h1' (by omega) hb2' (Or.inl rfl) (by omega))
          (apassage_step hA _ (sk_notAct_v X Y m d h2' (Or.inl rfl))
          (apassage_step hA _ (sk_notAct_r X Y m d h3' (by omega) hb3' (Or.inr rfl) (by omega)) (apassage_end hA _))))
        refine ⟨n, hn, _, Or.inl hcE, hc, hmin, n', hn', ?_, ?_⟩
        · rw [hφ, hc']; apply Subtype.ext; rw [φext _ hcE, h1, h4']
        · rw [hφ]; exact hmin'
    · -- the through-strand slot of `A'` ↦ the through-strand slot of `A`
      have hφ : (skφI X Y m d hA hA' ⟨_, hu⟩).1 = siteA X Y m d hA := skφI_siteB' X Y m d hA hA'
      rcases Bool.eq_false_or_eq_true a with hat | haf
      · -- `a = true`: `(|X|+1, m+2)` rightward through the crossing, out at `(|X|+2, m+1)`
        have hu1 : (siteB' X Y m d hA').1 = (X.length + 1, m + 1 + 1) := by rw [hsB', ite_eq_left hat]
        have hb1 : bit Vsp (X.length + 1) (m + 1 + 1) = true := by rw [c3', hat]
        have h1 := next_σ_right_succ hA' hℓ₁' hu1 hb1
        have hb1e : bit Vsp (X.length + 2) (m + 1) = true := by rw [e2', hat]
        have hcE := sk'_ext_r X Y m d h1 (by omega) hb1e
        obtain ⟨n, hn, hc, hmin⟩ := apassage_pos hA' (ActE X Psp Y) (apassage_end hA' _)
        have hu1' : (siteA X Y m d hA).1 = (X.length + 1, m) := by rw [hsA, ite_eq_left hat]
        have hb1' : bit Vs (X.length + 1) m = true := by rw [c1, hat]
        have h1' := next_σ_right_idx hA hℓ₁ hu1' hb1'
        refine ⟨n, hn, _, Or.inl hcE, hc, hmin, 1, one_pos, ?_,
          fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _)⟩
        rw [Function.iterate_one, hφ]; apply Subtype.ext; rw [φext _ hcE, h1, h1']
      · -- `a = false`: `(|X|+2, m+1)` leftward through the crossing, out at `(|X|, m)`
        have hu1 : (siteB' X Y m d hA').1 = (X.length + 2, m + 1) := by rw [hsB', ite_eq_right (by simp [haf])]
        have hb1 : bit Vsp (X.length + 2) (m + 1) = false := by rw [e2', haf]
        have h1 := next_σ_left_idx hA' hℓ₁' hu1 hb1
        have hb2 : bit Vsp (X.length + 1) (m + 1 + 1) = false := by rw [c3', haf]
        obtain ⟨h2, hb2e⟩ := pass_l_ge hA' hℓ₀' h1 (by omega) hb2 (by simp [idx, coarity])
        simp only [arity, coarity] at h2 hb2e
        have hcE := sk'_ext_l X Y m d hA' h2 (by omega) hb2e
        obtain ⟨n, hn, hc, hmin⟩ := apassage_pos hA' (ActE X Psp Y)
          (apassage_step hA' _ (sk'_notAct_l X Y m d h1 (by omega) hb2 (Or.inl rfl) (by omega)) (apassage_end hA' _))
        have hu1' : (siteA X Y m d hA).1 = (X.length + 2, m + 1) := by rw [hsA, ite_eq_right (by simp [haf])]
        have hb1' : bit Vs (X.length + 2) (m + 1) = false := by rw [e2, haf]
        have h1' := next_σ_left_succ hA hℓ₁ hu1' hb1'
        have hb2b : bit Vs (X.length + 1) m = false := by rw [c1, haf]
        obtain ⟨h2', hb2c⟩ := pass_l_lt hA hℓ₀ h1' (by omega) hb2b (by simp [idx])
        obtain ⟨n', hn', hc', hmin'⟩ := apassage_pos hA (ActE X Ps Y)
          (apassage_step hA _ (sk_notAct_l X Y m d h1' (by omega) hb2b (Or.inl rfl) (by omega)) (apassage_end hA _))
        refine ⟨n, hn, _, Or.inl hcE, hc, hmin, n', hn', ?_, ?_⟩
        · rw [hφ, hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
          simp only [Prod.mk.injEq, true_and]; omega
        · rw [hφ]; exact hmin'

end SkeinIntPassage

section SkeinSwitchIso

variable (X Y : Word) (m : ℕ) (d a : Bool)

local notation "Vs" => X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y
local notation "Vsp" => X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y
local notation "Ps" => [Letter.l (m + 1) d, Letter.σ m]
local notation "Psp" => [Letter.l m d, Letter.σ (m + 1)]

variable (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed)
  (hA' : (X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y).Closed)
variable {P L : Cuts} (hX : Word.run X [] = some (P ++ a :: L)) (hP : P.length = m - 1) (hm : 1 ≤ m)

/-- the site slot of `A` as an occurrence of its abstract record -/
noncomputable def siteX : (slotRecord hA IsσSlot (allActive hA)).M := ⟨siteA X Y m d hA, isσSlot_σSlotA hA _ _⟩

theorem siteX_val : (siteX X Y m d hA).1 = siteA X Y m d hA := rfl

include hX hP hm hA' in
/-- THE SWITCH HALF of the cusp-skein site: the `σ`-slot record of `A'` is the `σ`-slot record of `A`
switched at the site. -/
theorem sk_switchIso :
    Nonempty (RecordIso (slotRecord hA' IsσSlot (allActive hA'))
      ((slotRecord hA IsσSlot (allActive hA)).switch (siteX X Y m d hA))) := by
  have hE := sk_sameEffect X m d a hX hP hm
  have hPne : Psp ≠ [] := sk_Pne m d
  have ha' := (sk_bit_a X Y m d a hX hP).2
  have ha := (sk_bit_a X Y m d a hX hP).1
  refine ⟨recordIsoOfConjSwitch hA' hA (ActE X Psp Y) (ActE X Ps Y)
    (φA X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' (skφI X Y m d hA hA'))
    (conj_of_intPassage X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' hA _
      (sk_intPassage X Y m d a hA hA' hX hP hm))
    (fun u => by obtain ⟨n, hn⟩ := sk'_hexit X Y m d a hX hP hm hA' u; exact ⟨n, Or.inl hn⟩)
    (fun u => by obtain ⟨n, hn⟩ := sk_hexit X Y m d a hX hP hm hA u; exact ⟨n, Or.inl hn⟩)
    (fun _ hu => isσSlot_actE X Psp Y hu) (fun _ hu => isσSlot_actE X Ps Y hu) ?_ ?_ (siteX X Y m d hA)
    (IntSlot X Psp Y) ?_ ?_ ?_ ?_ ?_⟩
  · -- `σ` slots correspond
    intro u
    by_cases hext : ExtPiece X Psp Y u.1
    · rw [φA_val_ext X Psp Y Ps _ _ hA' _ u hext]
      exact isσSlot_φE_iff X Psp Y Ps _ _ hA' ⟨u.1, hext⟩
    · rw [φA_val_int X Psp Y Ps _ _ hA' _ u hext]
      exact iff_of_true (skφI X Y m d hA hA' ⟨u.1, u.2.resolve_left hext⟩).2.1 (u.2.resolve_left hext).1
  · -- twins correspond
    intro u hu
    by_cases hext : ExtPiece X Psp Y u.1
    · have hext2 : ExtPiece X Psp Y (σtwin hA' u.1) := extPiece_σtwin X Psp Y hA' hu hext
      rw [φA_val_ext X Psp Y Ps _ _ hA' _ _ hext2, φA_val_ext X Psp Y Ps _ _ hA' _ u hext]
      exact φE_σtwin X Psp Y Ps _ _ hA' hA ⟨u.1, hext⟩ hu
    · have hint : IntSlot X Psp Y u.1 := u.2.resolve_left hext
      have hext2 : ¬ ExtPiece X Psp Y (σtwin hA' u.1) := by
        show ¬ ExtCol X Psp (colOf _); rw [colOf_σtwin hA' hu]; exact hint.2
      rw [φA_val_int X Psp Y Ps _ _ hA' _ _ hext2, φA_val_int X Psp Y Ps _ _ hA' _ u hext]
      exact skφI_twin X Y m d hA hA' ⟨u.1, hint⟩
  · -- the site
    intro u hu
    constructor
    · intro h
      by_contra hint
      have hext : ExtPiece X Psp Y u.1 := u.2.resolve_right hint
      have hE2 := (φE X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' ⟨u.1, hext⟩).2
      rw [← φA_val_ext X Psp Y Ps _ _ hA' (skφI X Y m d hA hA') u hext] at hE2
      rcases h with h | h
      · rw [h, siteX_val] at hE2; exact (siteA_int X Y m d hA).2 hE2
      · rw [h, siteX_val, σtwin_siteA] at hE2; exact (siteB_int X Y m d hA).2 hE2
    · intro hint
      rw [φA_val_int X Psp Y Ps _ _ hA' _ u (fun h => hint.2 h), skφI_val, siteX_val, σtwin_siteA]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  · intro u hu hint
    rw [φA_val_int X Psp Y Ps _ _ hA' _ u (fun h => hint.2 h)]
    exact skφI_desc X Y m d hA hA' ⟨u.1, hint⟩
  · intro u hu hint
    have hext : ExtPiece X Psp Y u.1 := u.2.resolve_right hint
    rw [φA_val_ext X Psp Y Ps _ _ hA' _ u hext]
    exact isDesc_φE X Psp Y Ps _ _ hA' ⟨u.1, hext⟩
  · intro u hu hint
    rw [φA_val_int X Psp Y Ps _ _ hA' _ u (fun h => hint.2 h)]
    exact skφI_sgn X Y m d a hA hA' ha ha' ⟨u.1, hint⟩
  · intro u hu hint
    have hext : ExtPiece X Psp Y u.1 := u.2.resolve_right hint
    rw [φA_val_ext X Psp Y Ps _ _ hA' _ u hext]
    exact σsgn_φE X Psp Y Ps _ _ hA' ⟨u.1, hext⟩

include hX hP in
/-- the sign of the site -/
theorem siteX_sgn :
    (((slotRecord hA IsσSlot (allActive hA)).sgn (siteX X Y m d hA) : SignType) : ℤ) = if a = d then 1 else -1 := by
  have ha := (sk_bit_a X Y m d a hX hP).1
  obtain ⟨c1, c2, -, -, -, -⟩ := sk_bits X Y m d a hA ha
  show ((σsgn (siteA X Y m d hA) : SignType) : ℤ) = _
  unfold σsgn
  rw [show colOf (siteA X Y m d hA) = X.length + 1 from (σSlotA_spec hA _ _).1, coe_σsgnCol,
    (sk_letters X Y m d).2]
  simp only [idx, c1, c2]

end SkeinSwitchIso

/-! #### I. The smoothing half: `Record.smooth` of a slot record as a first return of a reconnected slot
permutation, and its transport along record isomorphisms -/

section SmoothGeneric

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- the swap on a subtype has the swapped value -/
theorem swap_subtype_val {S : α → Prop} (a b v : {x // S x}) :
    (Equiv.swap a b v).1 = Equiv.swap a.1 b.1 v.1 := by
  by_cases hva : v = a
  · subst hva; simp
  · by_cases hvb : v = b
    · subst hvb; simp
    · rw [Equiv.swap_apply_of_ne_of_ne hva hvb,
        Equiv.swap_apply_of_ne_of_ne (fun h => hva (Subtype.ext h)) (fun h => hvb (Subtype.ext h))]

/-- the first return of `f ∘ swap` to `S` (with `a, b ∈ S`) is the first return of `f` composed with the swap -/
theorem firstReturn_mul_swap (f : Perm α) (S : α → Prop) [DecidablePred S] (a b : α) (ha : S a) (hb : S b)
    (v : {x // S x}) :
    firstReturn (f * Equiv.swap a b) S v = firstReturn f S (Equiv.swap ⟨a, ha⟩ ⟨b, hb⟩ v) := by
  set w := Equiv.swap (⟨a, ha⟩ : {x // S x}) ⟨b, hb⟩ v with hw
  have hwv : w.1 = Equiv.swap a b v.1 := swap_subtype_val ⟨a, ha⟩ ⟨b, hb⟩ v
  set r := returnTime f S w.1 w.2 with hr
  have hrpos : 0 < r := returnTime_pos f S w.1 w.2
  have hpow : ∀ i, 1 ≤ i → i ≤ r → ((f * Equiv.swap a b) ^ i) v.1 = (f ^ i) w.1 := by
    intro i hi1 hir
    induction i with
    | zero => omega
    | succ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp only [zero_add, pow_one, Perm.mul_apply, hwv]
      · rw [pow_succ', Perm.mul_apply, ih hi (by omega), Perm.mul_apply, pow_succ', Perm.mul_apply]
        congr 1
        have hnot : ¬ S ((f ^ i) w.1) := returnTime_min f S w.1 w.2 hi (by omega)
        exact Equiv.swap_apply_of_ne_of_ne (fun h => hnot (h ▸ ha)) (fun h => hnot (h ▸ hb))
  apply Subtype.ext
  rw [firstReturn_eq_of_path (f * Equiv.swap a b) S v hrpos]
  · rw [hpow r hrpos le_rfl, firstReturn_apply]
  · rw [hpow r hrpos le_rfl]; exact returnTime_spec f S w.1 w.2
  · intro i hi hir
    rw [hpow i hi hir.le]
    exact returnTime_min f S w.1 w.2 hi hir

omit [DecidableEq α] in
/-- first returns to pointwise-equivalent predicates (instances given explicitly) have equal values -/
theorem firstReturn_val_congr (f : Perm α) (p q : α → Prop) (ip : DecidablePred p) (iq : DecidablePred q)
    (hpq : ∀ a, p a ↔ q a) (a : {x // p x}) :
    (@firstReturn α _ f p ip a).1 = (@firstReturn α _ f q iq ⟨a.1, (hpq _).1 a.2⟩).1 := by
  have hr : @returnTime α _ f q iq a.1 ((hpq _).1 a.2) = @returnTime α _ f p ip a.1 a.2 := by
    rw [@returnTime_eq_iff α _ f q iq]
    refine ⟨⟨@returnTime_pos α _ f p ip a.1 a.2, (hpq _).1 (@returnTime_spec α _ f p ip a.1 a.2)⟩, ?_⟩
    intro j hj ⟨hj0, hq⟩
    exact @returnTime_min α _ f p ip a.1 a.2 j hj0 hj ((hpq _).2 hq)
  rw [@firstReturn_apply α _ f p ip a, @firstReturn_apply α _ f q iq _, hr]

end SmoothGeneric

section SmoothCongr

/-- `Record.smooth` is functorial in named record isomorphisms. -/
noncomputable def smoothCongr {ρ ρ' : Record} (ι : RecordIso ρ ρ') (x : ρ.M) :
    RecordIso (ρ.smooth x) (ρ'.smooth (ι.Φ x)) :=
  let hrec : ∀ v, ι.Φ (ρ.reconnect x v) = ρ'.reconnect (ι.Φ x) (ι.Φ v) := fun v => by
    unfold Record.reconnect
    rw [Perm.mul_apply, Perm.mul_apply, ι.succ_eq]
    congr 1
    by_cases hv : v = x
    · subst hv; rw [Equiv.swap_apply_left, Equiv.swap_apply_left]; exact ι.pair_eq _
    · by_cases hv' : v = ρ.pair x
      · subst hv'; rw [Equiv.swap_apply_right, ι.pair_eq, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hv hv', Equiv.swap_apply_of_ne_of_ne (fun h => hv (ι.Φ.injective h))
          (fun h => hv' (ι.Φ.injective (by rw [h, ι.pair_eq])))]
  let hkeep : ∀ v, ρ.SmoothKeep x v ↔ ρ'.SmoothKeep (ι.Φ x) (ι.Φ v) := fun v => by
    unfold Record.SmoothKeep
    rw [not_iff_not, ι.mem_pair_iff]
  { e := Equiv.sumCongr
      (Quotient.congr ι.Φ (fun v w => (sameCycle_iff_of_conj (ρ.reconnect x) (ρ'.reconnect (ι.Φ x)) hrec v w).symm))
      { toFun := fun c => ⟨ι.e c.1, fun v h => c.2 (ι.Φ.symm v) (by
            rw [← ι.e.injective.eq_iff, ← ι.comp_eq, Equiv.apply_symm_apply, h])⟩
        invFun := fun c => ⟨ι.e.symm c.1, fun v h => c.2 (ι.Φ v) (by rw [ι.comp_eq, h, Equiv.apply_symm_apply])⟩
        left_inv := fun c => Subtype.ext (Equiv.symm_apply_apply _ _)
        right_inv := fun c => Subtype.ext (Equiv.apply_symm_apply _ _) }
    Φ := Equiv.subtypeEquiv ι.Φ hkeep
    comp_eq := fun v => by
      show Sum.inl (Quotient.mk _ (ι.Φ v.1)) = Sum.inl (Quotient.congr ι.Φ _ (Quotient.mk _ v.1))
      rfl
    succ_eq := fun v => by
      apply Subtype.ext
      show ι.Φ (firstReturn (ρ.reconnect x) (ρ.SmoothKeep x) v).1 =
        (firstReturn (ρ'.reconnect (ι.Φ x)) (ρ'.SmoothKeep (ι.Φ x)) ⟨ι.Φ v.1, (hkeep v.1).1 v.2⟩).1
      exact (firstReturn_conj (ρ.reconnect x) (ρ'.reconnect (ι.Φ x)) (ρ.SmoothKeep x) (ρ'.SmoothKeep (ι.Φ x))
        ι.Φ hrec (fun v => (hkeep v).symm) v).symm
    pair_eq := fun v => by
      apply Subtype.ext
      show ι.Φ (ρ.pair v.1) = ρ'.pair (ι.Φ v.1)
      exact ι.pair_eq v.1
    bit_eq := fun v => ι.bit_eq v.1
    sgn_eq := fun v => ι.sgn_eq v.1 }

end SmoothCongr

section SmoothIso

variable {W W' : Word} (hW : W.Closed) (hW' : W'.Closed)
  (E : Slot W → Prop) (E' : Slot W' → Prop) [DecidablePred E] [DecidablePred E']
  (φ : {u // E u} ≃ {u' // E' u'}) (x₀ : (slotRecord hW IsσSlot (allActive hW)).M)

/-- the reconnected slot permutation: the traversal with the two site slots exchanged -/
noncomputable def gPerm : Perm (Slot W) := nextPerm hW * Equiv.swap x₀.1 (σtwin hW x₀.1)

omit hW' E E' φ in
theorem gPerm_apply_of_ne {u : Slot W} (h1 : u ≠ x₀.1) (h2 : u ≠ σtwin hW x₀.1) :
    gPerm hW x₀ u = next hW u := by
  unfold gPerm
  rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, nextPerm_apply]

omit hW' E E' φ in
theorem gPerm_apply_of_not_σ {u : Slot W} (h : ¬ IsσSlot u) : gPerm hW x₀ u = next hW u :=
  gPerm_apply_of_ne hW x₀ (fun e => h (e ▸ x₀.2)) (fun e => h (e ▸ isσSlot_σtwin hW x₀.2))

omit hW' E E' φ in
theorem gPerm_pow_of_not_σ {u : Slot W} (h : ∀ n, ¬ IsσSlot ((next hW)^[n] u)) (n : ℕ) :
    ((gPerm hW x₀) ^ n) u = (next hW)^[n] u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, Function.iterate_succ_apply']
    exact gPerm_apply_of_not_σ hW x₀ (h n)

omit hW' E E' φ in
/-- the record-level reconnection is the first return of the reconnected slot permutation -/
theorem reconnect_eq :
    (slotRecord hW IsσSlot (allActive hW)).reconnect x₀ =
      (firstReturn (gPerm hW x₀) IsσSlot : Perm (slotRecord hW IsσSlot (allActive hW)).M) := by
  refine Equiv.ext fun v => ?_
  have hpair : (slotRecord hW IsσSlot (allActive hW)).pair x₀ = ⟨σtwin hW x₀.1, isσSlot_σtwin hW x₀.2⟩ :=
    Subtype.ext (slotRecord_pair_val hW _ _ x₀)
  have h := firstReturn_mul_swap (nextPerm hW) IsσSlot x₀.1 (σtwin hW x₀.1) x₀.2 (isσSlot_σtwin hW x₀.2) v
  refine Eq.trans ?_ h.symm
  show (slotRecord hW IsσSlot (allActive hW)).succ
    (Equiv.swap x₀ ((slotRecord hW IsσSlot (allActive hW)).pair x₀) v) = _
  rw [hpair]
  rfl

omit hW' E E' φ in
theorem smoothKeep_iff' (v : (slotRecord hW IsσSlot (allActive hW)).M) :
    (slotRecord hW IsσSlot (allActive hW)).SmoothKeep x₀ v ↔ v.1 ≠ x₀.1 ∧ v.1 ≠ σtwin hW x₀.1 := by
  rw [Record.smoothKeep_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (Subtype.ext h), fun h => h2 (Subtype.ext (h.trans (slotRecord_pair_val hW _ _ x₀).symm))⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (congrArg Subtype.val h),
      fun h => h2 ((congrArg Subtype.val h).trans (slotRecord_pair_val hW _ _ x₀))⟩

/-- the kept σ slots -/
noncomputable def KeptSlot (u : Slot W) : Prop := IsσSlot u ∧ u ≠ x₀.1 ∧ u ≠ σtwin hW x₀.1

noncomputable instance : DecidablePred (KeptSlot hW x₀) := fun u => by unfold KeptSlot; infer_instance


omit hW' E E' φ in
/-- the smoothed successor is the first return of the reconnected slot permutation to the kept slots -/
theorem smooth_succ_val_eq (v : ((slotRecord hW IsσSlot (allActive hW)).smooth x₀).M) :
    (((slotRecord hW IsσSlot (allActive hW)).smooth x₀).succ v).1.1 =
      (firstReturn (gPerm hW x₀) (KeptSlot hW x₀) ⟨v.1.1, v.1.2, ((smoothKeep_iff' hW x₀ v.1).1 v.2)⟩).1 := by
  have e1 : (((slotRecord hW IsσSlot (allActive hW)).smooth x₀).succ v).1 =
      (firstReturn ((slotRecord hW IsσSlot (allActive hW)).reconnect x₀)
        ((slotRecord hW IsσSlot (allActive hW)).SmoothKeep x₀) v).1 := rfl
  rw [reconnect_eq hW x₀] at e1
  have e2 := @firstReturn_val_congr _ _ (firstReturn (gPerm hW x₀) IsσSlot)
    ((slotRecord hW IsσSlot (allActive hW)).SmoothKeep x₀) (fun b => KeptSlot hW x₀ b.1)
    (Record.instDecidablePredMSmoothKeep _ x₀) inferInstance
    (fun b => by rw [smoothKeep_iff' hW x₀ b]; exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩) v
  rw [firstReturn_factor (gPerm hW x₀) IsσSlot (KeptSlot hW x₀) (fun _ h => h.1)]
  exact congrArg Subtype.val (e1.trans e2)

variable (hint : ∀ u, IsσSlot u → u ≠ x₀.1 → u ≠ σtwin hW x₀.1 → E u)
  (hnot₁ : ¬ E x₀.1) (hnot₂ : ¬ E (σtwin hW x₀.1))
  (hσE' : ∀ u', IsσSlot u' → E' u')
  (conj : ∀ u, firstReturn (nextPerm hW') E' (φ u) = φ (firstReturn (gPerm hW x₀) E u))
  (hexit : ∀ u : Slot W, ∃ n : ℕ, E (((gPerm hW x₀) ^ n) u))
  (hexit' : ∀ u' : Slot W', ∃ n : ℕ, E' (((nextPerm hW') ^ n) u'))
  (hσ : ∀ u : {u // E u}, IsσSlot (φ u).1 ↔ IsσSlot u.1)
  (hEtwin : ∀ u, E u → IsσSlot u → E (σtwin hW u))
  (htwin : ∀ (u : {u // E u}) (hu : IsσSlot u.1), (φ ⟨σtwin hW u.1, hEtwin _ u.2 hu⟩).1 = σtwin hW' (φ u).1)
  (hdesc : ∀ u : {u // E u}, IsσSlot u.1 → isDesc (φ u).1 = isDesc u.1)
  (hsgn : ∀ u : {u // E u}, IsσSlot u.1 → σsgn (φ u).1 = σsgn u.1)

include hnot₁ hnot₂ in
omit hW' E' φ [DecidablePred E] in
theorem kept_of_E {u : Slot W} (hu : E u) (hσu : IsσSlot u) : KeptSlot hW x₀ u :=
  ⟨hσu, fun h => hnot₁ (h ▸ hu), fun h => hnot₂ (h ▸ hu)⟩

include hint in
omit hW' E' φ [DecidablePred E] in
theorem E_of_kept {u : Slot W} (hu : KeptSlot hW x₀ u) : E u := hint u hu.1 hu.2.1 hu.2.2

/-- the components of the smoothing are the cycles of the reconnected slot permutation -/
noncomputable def smoothCompsEquiv :
    ((slotRecord hW IsσSlot (allActive hW)).smooth x₀).comps ≃ Quotient (Perm.SameCycle.setoid (gPerm hW x₀)) := by
  let ρ := slotRecord hW IsσSlot (allActive hW)
  let g := gPerm hW x₀
  -- the σ-cycles
  let toG : Quotient (Perm.SameCycle.setoid (ρ.reconnect x₀)) → Quotient (Perm.SameCycle.setoid g) :=
    Quotient.lift (fun v : ρ.M => Quotient.mk _ v.1) (fun v w h => Quotient.sound (by
      have h' : (ρ.reconnect x₀).SameCycle v w := h
      rw [reconnect_eq hW x₀] at h'
      exact (firstReturn_sameCycle_iff g IsσSlot v w).1 h'))
  -- the crossing-free cycles
  have hfree : ∀ (i : Fin (numComp hW)), (∀ v : ρ.M, ρ.comp v ≠ i) → ∀ n, ¬ IsσSlot ((next hW)^[n] (rep hW i)) := by
    intro i hi n hσn
    apply hi ⟨_, hσn⟩
    show slotComp hW ((next hW)^[n] (rep hW i)) = i
    rw [slotComp_eq_equivFin]
    have : orbitOf hW ((next hW)^[n] (rep hW i)) = orbitOf hW (rep hW i) := by
      rw [orbitOf_eq_iff]
      exact sameCycle_of_iterate hW (a := 0) (b := n) rfl
    rw [this, orbitOf_rep, Equiv.apply_symm_apply]
  have hfreeCycle : ∀ (i : Fin (numComp hW)) (hi : ∀ v : ρ.M, ρ.comp v ≠ i) (w : Slot W),
      g.SameCycle (rep hW i) w ↔ (nextPerm hW).SameCycle (rep hW i) w := by
    intro i hi w
    constructor
    · intro h
      obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
      rw [gPerm_pow_of_not_σ hW x₀ (hfree i hi) n] at hn
      exact sameCycle_of_iterate hW (a := n) (b := 0) hn
    · intro h
      obtain ⟨n, hn⟩ := exists_iterate_of_sameCycle hW h
      exact ⟨n, by rw [zpow_natCast, gPerm_pow_of_not_σ hW x₀ (hfree i hi) n]; exact hn⟩
  let freeG : ρ.FreeComp → Quotient (Perm.SameCycle.setoid g) := fun c => Quotient.mk _ (rep hW c.1)
  refine Equiv.ofBijective (Sum.elim toG freeG) ⟨?_, ?_⟩
  · -- injective
    rintro (q | c) (q' | c') h
    · induction q using Quotient.inductionOn with
      | h v =>
        induction q' using Quotient.inductionOn with
        | h w =>
          have h' : g.SameCycle v.1 w.1 := Quotient.exact h
          rw [← firstReturn_sameCycle_iff g IsσSlot v w, ← reconnect_eq hW x₀] at h'
          exact congrArg Sum.inl (Quotient.sound h')
    · exfalso
      induction q using Quotient.inductionOn with
      | h v =>
        have h' : g.SameCycle v.1 (rep hW c'.1) := Quotient.exact h
        obtain ⟨n, hn⟩ := exists_iterate_of_sameCycle hW ((hfreeCycle c'.1 c'.2 v.1).1 h'.symm)
        exact hfree c'.1 c'.2 n (hn ▸ v.2)
    · exfalso
      induction q' using Quotient.inductionOn with
      | h v =>
        have h' : g.SameCycle (rep hW c.1) v.1 := Quotient.exact h
        obtain ⟨n, hn⟩ := exists_iterate_of_sameCycle hW ((hfreeCycle c.1 c.2 v.1).1 h')
        exact hfree c.1 c.2 n (hn ▸ v.2)
    · have h' : g.SameCycle (rep hW c.1) (rep hW c'.1) := Quotient.exact h
      exact congrArg Sum.inr (Subtype.ext (rep_injective_orbit hW ((hfreeCycle c.1 c.2 _).1 h')))
  · -- surjective
    intro q
    induction q using Quotient.inductionOn with
    | h u =>
      by_cases h : ∃ n, IsσSlot ((g ^ n) u)
      · obtain ⟨n, hn⟩ := h
        refine ⟨Sum.inl (Quotient.mk _ ⟨(g ^ n) u, hn⟩), ?_⟩
        show Quotient.mk _ ((g ^ n) u) = Quotient.mk _ u
        exact Quotient.sound (sameCycle_pow g n u).symm
      · replace h : ∀ n, ¬ IsσSlot ((g ^ n) u) := fun n hn => h ⟨n, hn⟩
        have hpow : ∀ n, (g ^ n) u = (next hW)^[n] u := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih =>
            rw [pow_succ', Perm.mul_apply, Function.iterate_succ_apply', ← ih]
            exact gPerm_apply_of_not_σ hW x₀ (h n)
        have hnoσ : ∀ n, ¬ IsσSlot ((next hW)^[n] u) := fun n => by rw [← hpow n]; exact h n
        have hfreeu : ∀ v : ρ.M, ρ.comp v ≠ slotComp hW u := by
          intro v hv
          have : (nextPerm hW).SameCycle u v.1 := ((slotComp_eq_iff hW _ _).1 hv).symm
          obtain ⟨n, hn⟩ := exists_iterate_of_sameCycle hW this
          exact hnoσ n (hn ▸ v.2)
        refine ⟨Sum.inr ⟨slotComp hW u, hfreeu⟩, ?_⟩
        show Quotient.mk _ (rep hW (slotComp hW u)) = Quotient.mk _ u
        apply Quotient.sound
        apply (hfreeCycle (slotComp hW u) hfreeu u).2
        rw [← orbitOf_eq_iff, orbitOf_rep, slotComp_eq_equivFin, Equiv.symm_apply_apply]

theorem smoothCompsEquiv_inl (v : (slotRecord hW IsσSlot (allActive hW)).M) :
    smoothCompsEquiv hW x₀ (Sum.inl (Quotient.mk _ v)) = Quotient.mk _ v.1 := rfl

include hint hnot₁ hnot₂ hσE' conj hexit hexit' hσ hEtwin htwin hdesc hsgn in
/-- THE RECORD ISOMORPHISM OF THE SMOOTHING: the σ-slot record of `W` smoothed at the site `x₀` is the σ-slot
record of `W'`, given conjugate first returns of the reconnected slot permutation of `W` and the traversal
of `W'` on the active supersets `E`, `E'` (all σ slots of `W` other than the site, all σ slots of `W'`). -/
noncomputable def smoothRecordIso :
    RecordIso ((slotRecord hW IsσSlot (allActive hW)).smooth x₀) (slotRecord hW' IsσSlot (allActive hW')) :=
  let ρ := slotRecord hW IsσSlot (allActive hW)
  let g := gPerm hW x₀
  let oe : Quotient (Perm.SameCycle.setoid g) ≃ Orbit hW' := cycleEquiv g (nextPerm hW') E E' φ conj hexit hexit'
  let keptE : ∀ v : (ρ.smooth x₀).M, E v.1.1 := fun v =>
    E_of_kept hW E x₀ hint ⟨v.1.2, (smoothKeep_iff' hW x₀ v.1).1 v.2⟩
  let Φ : (ρ.smooth x₀).M ≃ (slotRecord hW' IsσSlot (allActive hW')).M :=
    { toFun := fun v => ⟨(φ ⟨v.1.1, keptE v⟩).1, (hσ _).2 v.1.2⟩
      invFun := fun u' =>
        let a := φ.symm ⟨u'.1, hσE' _ u'.2⟩
        have hσa : IsσSlot a.1 := by
          have h := (hσ a).1
          rw [Equiv.apply_symm_apply] at h
          exact h u'.2
        ⟨⟨a.1, hσa⟩, (smoothKeep_iff' hW x₀ ⟨a.1, hσa⟩).2 (kept_of_E hW E x₀ hnot₁ hnot₂ a.2 hσa).2⟩
      left_inv := fun v => Subtype.ext (Subtype.ext (by
        show (φ.symm ⟨(φ ⟨v.1.1, keptE v⟩).1, _⟩).1 = v.1.1
        rw [show (⟨(φ ⟨v.1.1, keptE v⟩).1, _⟩ : {u' // E' u'}) = φ ⟨v.1.1, keptE v⟩ from rfl,
          Equiv.symm_apply_apply]))
      right_inv := fun u' => Subtype.ext (by
        show (φ ⟨(φ.symm ⟨u'.1, hσE' _ u'.2⟩).1, _⟩).1 = u'.1
        rw [show (⟨(φ.symm ⟨u'.1, hσE' _ u'.2⟩).1, _⟩ : {u // E u}) = φ.symm ⟨u'.1, hσE' _ u'.2⟩ from rfl,
          Equiv.apply_symm_apply]) }
  { e := (smoothCompsEquiv hW x₀).trans (oe.trans (Fintype.equivFin (Orbit hW')))
    Φ := Φ
    comp_eq := fun v => by
      have h1 : (slotRecord hW' IsσSlot (allActive hW')).comp (Φ v) =
          Fintype.equivFin (Orbit hW') (orbitOf hW' (φ ⟨v.1.1, keptE v⟩).1) := slotComp_eq_equivFin hW' _
      have h2 : ((smoothCompsEquiv hW x₀).trans (oe.trans (Fintype.equivFin (Orbit hW')))) ((ρ.smooth x₀).comp v) =
          Fintype.equivFin (Orbit hW') (oe (Quotient.mk _ v.1.1)) := rfl
      have key : orbitOf hW' (φ ⟨v.1.1, keptE v⟩).1 = oe (Quotient.mk _ v.1.1) :=
        (cycleEquiv_mk g (nextPerm hW') E E' φ conj hexit hexit' ⟨v.1.1, keptE v⟩).symm
      exact h1.trans ((congrArg (Fintype.equivFin (Orbit hW')) key).trans h2.symm)
    succ_eq := fun v => by
      apply Subtype.ext
      show (φ ⟨((ρ.smooth x₀).succ v).1.1, _⟩).1 = (firstReturn (nextPerm hW') IsσSlot ⟨(φ ⟨v.1.1, _⟩).1, _⟩).1
      have h1 := firstReturn_conj_of_factor g (nextPerm hW') E E' φ conj (KeptSlot hW x₀) IsσSlot
        (fun _ h => E_of_kept hW E x₀ hint h) hσE' (fun a => ⟨fun h => kept_of_E hW E x₀ hnot₁ hnot₂ a.2 ((hσ a).1 h),
          fun h => (hσ a).2 h.1⟩) ⟨v.1.1, v.1.2, (smoothKeep_iff' hW x₀ v.1).1 v.2⟩
      exact (congrArg (fun x : {u // E u} => (φ x).1) (Subtype.ext (smooth_succ_val_eq hW x₀ v))).trans h1.symm
    pair_eq := fun v => by
      apply Subtype.ext
      show (φ ⟨σtwin hW v.1.1, _⟩).1 = σtwin hW' (φ ⟨v.1.1, keptE v⟩).1
      exact htwin ⟨v.1.1, keptE v⟩ v.1.2
    bit_eq := fun v => hdesc ⟨v.1.1, keptE v⟩ v.1.2
    sgn_eq := fun v => hsgn ⟨v.1.1, keptE v⟩ v.1.2 }

end SmoothIso

section PassageF

variable (X P Y P' : Word) (hP : P ≠ []) (hE : SameEffect X P P')
  (hW : (X ++ P ++ Y).Closed) (hW' : (X ++ P' ++ Y).Closed) (f : Perm (Slot (X ++ P ++ Y)))

/-- the block passage hypothesis for a slot permutation `f` agreeing with the traversal on the exterior -/
structure PassageF : Prop where
  pass : ∀ b : Slot (X ++ P ++ Y), IsExtSlot X P b.1 → ¬ ExtCol X P (colOf b) →
    ∃ (m : ℕ) (c : Slot (X ++ P ++ Y)), (f ^ m) b = c ∧ ExtCol X P (colOf c) ∧
      (∀ i < m, ¬ ExtCol X P (colOf ((f ^ i) b))) ∧
      ∃ (m' : ℕ) (b' : Slot (X ++ P' ++ Y)), b'.1 = extPair X P P' b.1 ∧
        ((next hW')^[m'] b').1 = extPair X P P' c.1 ∧
        ∀ i < m', ¬ ExtCol X P' (colOf ((next hW')^[i] b'))

include hP hE in
/-- the passage makes the first returns to the exterior pieces conjugate (`U2.conj_of_passage` for `f`) -/
theorem conj_of_passageF (hf : ∀ u, ExtPiece X P Y u → f u = next hW u) (hpass : PassageF X P Y P' hW' f)
    (u : {u // ExtPiece X P Y u}) :
    firstReturn (nextPerm hW') (ExtPiece X P' Y) (φE X P Y P' hP hE hW u) =
      φE X P Y P' hP hE hW (firstReturn f (ExtPiece X P Y) u) := by
  revert u
  apply conj_of_paths
  intro u
  obtain ⟨hnext_ext, hnext_eq⟩ :=
    next_ext X P Y P' hP hE hW hW' ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩ u.2
  have hfu : f u.1 = next hW u.1 := hf u.1 u.2
  have hφu : (φE X P Y P' hP hE hW u).1 = extSlot X P Y P' hP hE ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩ := rfl
  by_cases hE1 : ExtPiece X P Y (next hW u.1)
  · refine ⟨1, 1, one_pos, one_pos, by rw [pow_one, hfu]; exact hE1,
      fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _),
      fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _), ?_⟩
    apply Subtype.ext
    rw [pow_one, nextPerm_apply, hφu, hnext_eq, φE_val]
    exact congrArg (fun x => extPair X P P' x.1) hfu.symm
  · obtain ⟨m, c, hmc, hc, hint, m', b', hb', hm', hint'⟩ := hpass.pass (next hW u.1) hnext_ext hE1
    have hb'' : next hW' (φE X P Y P' hP hE hW u).1 = b' := Subtype.ext (by rw [hφu, hnext_eq, hb'])
    have hfpow : ∀ i, (f ^ (i + 1)) u.1 = (f ^ i) (next hW u.1) := fun i => by
      rw [pow_succ, Perm.mul_apply, hfu]
    refine ⟨m + 1, m' + 1, Nat.succ_pos _, Nat.succ_pos _, by rw [hfpow, hmc]; exact hc, ?_, ?_, ?_⟩
    · intro i hi him
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [hfpow]; exact hint i' (by omega)
    · intro i hi him
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [pow_succ, Perm.mul_apply, nextPerm_apply, hb'', nextPerm_pow_apply]; exact hint' i' (by omega)
    · apply Subtype.ext
      rw [pow_succ, Perm.mul_apply, nextPerm_apply, hb'', nextPerm_pow_apply, hm', φE_val]
      exact congrArg (fun x => extPair X P P' x.1) (hmc.symm.trans (hfpow m).symm)

end PassageF

/-! #### J. The cusp-skein smoothing: the reconnected traversal of `A` against the compatible smoothing `C` -/

section CuspColumn

variable (X Y : Word) (j : ℕ) (d : Bool)

local notation "Vc1" => X ++ [Letter.l j d] ++ Y
local notation "Pc1" => [Letter.l j d]

theorem c1_letter : letterAt Vc1 X.length = .l j d := by
  have := letterAt_block X Pc1 Y (i := 0) (by simp)
  simpa using this

theorem c1_length : (X ++ [Letter.l j d] ++ Y).length = X.length + 1 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem c1_extCol (k : ℕ) : ExtCol X Pc1 k ↔ k + 1 ≤ X.length ∨ X.length + 1 ≤ k := by unfold ExtCol; simp

theorem c1_Pne : ([Letter.l j d] : Word) ≠ [] := List.cons_ne_nil _ _

variable (hC : (X ++ [Letter.l j d] ++ Y).Closed)
include hC

theorem c1_j_pos : 1 ≤ j := (l_bits hC (by rw [c1_length]; omega) (c1_letter X Y j d)).1

/-- every `σ` slot of a single-cusp block word is exterior -/
theorem c1_σ_ext {u : Slot Vc1} (hu : IsσSlot u) : ExtPiece X Pc1 Y u := by
  by_contra h
  have hcol : colOf u = X.length := by
    have := colOf_lt hC u
    have h' : ¬ ExtCol X Pc1 (colOf u) := h
    rw [c1_extCol] at h'
    rw [c1_length] at this
    omega
  have := hu.1
  rw [hcol, c1_letter] at this
  exact Bool.noConfusion this

/-- every slot of a single-cusp block word reaches the exterior -/
theorem c1_hexit : ∀ u : Slot Vc1, ∃ n, ExtPiece X Pc1 Y ((next hC)^[n] u) := by
  have hℓ := c1_letter X Y j d
  have hj := c1_j_pos X Y j d hC
  have hk₀ : X.length < (Vc1).length := by rw [c1_length]; omega
  obtain ⟨-, b1, b2⟩ := l_bits hC hk₀ hℓ
  have hv : ∀ u : Slot Vc1, u.1 = (X.length, 0) → ∃ n, ExtPiece X Pc1 Y ((next hC)^[n] u) := by
    intro u hu
    have h1 := next_cusp_l hC hℓ hu
    refine reach_of_next hC (reach_self hC ?_)
    show ExtCol X Pc1 (colOf _)
    rcases Bool.eq_false_or_eq_true d with hd | hd
    · rw [ite_eq_left hd] at h1
      rw [block_col_true h1 (by omega) (by rw [b1, hd]), c1_extCol]; omega
    · rw [ite_eq_right (by simp [hd])] at h1
      rw [block_col_true h1 (by omega) (by rw [b2, hd]; rfl), c1_extCol]; omega
  intro u
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  by_cases hext : ExtCol X Pc1 (colOf u)
  · exact reach_self hC hext
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, c1_extCol] at hext
    have : k = X.length := by omega
    subst this
    exact hv u hu
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hC hu hp
  cases hb : bit Vc1 k p
  · rw [block_col_false hu hp hb, c1_extCol] at hext
    have : k = X.length + 1 := by omega
    subst this
    rcases lt_or_ge p j with hpj | hpj
    · obtain ⟨h1, hb1⟩ := pass_l_lt hC hℓ hu hp hb (by simpa [idx] using hpj)
      refine reach_of_next hC (reach_self hC ?_)
      show ExtCol X Pc1 (colOf _)
      have := (cutSlot_facts hC h1 hp).2.2.1
      rw [block_col_false h1 hp hb1, c1_extCol]; omega
    rcases lt_or_ge p (j + 2) with hpj2 | hpj2
    · have h1 := next_arm_l hC hk₀ hℓ hu (by omega) hb
      exact reach_of_next hC (hv _ h1)
    · obtain ⟨h1, hb1⟩ := pass_l_ge hC hℓ hu hp hb (by simpa [idx, coarity] using hpj2)
      simp only [arity, coarity] at h1 hb1
      refine reach_of_next hC (reach_self hC ?_)
      show ExtCol X Pc1 (colOf _)
      have := (cutSlot_facts hC h1 (by omega)).2.2.1
      rw [block_col_false h1 (by omega) hb1, c1_extCol]; omega
  · rw [block_col_true hu hp hb, c1_extCol] at hext
    have : k = X.length := by omega
    subst this
    rcases lt_or_ge p j with hpj | hpj
    · obtain ⟨h1, hb1⟩ := pass_r_lt hC hℓ hu hp hb (by simpa [idx] using hpj)
      refine reach_of_next hC (reach_self hC ?_)
      show ExtCol X Pc1 (colOf _)
      rw [block_col_true h1 hp hb1, c1_extCol]; omega
    · obtain ⟨h1, hb1⟩ := pass_r_ge hC hℓ hu hp hb (by simpa [idx, arity] using hpj)
      simp only [arity, coarity, Nat.sub_zero] at h1 hb1
      refine reach_of_next hC (reach_self hC ?_)
      show ExtCol X Pc1 (colOf _)
      rw [block_col_true h1 (by omega) hb1, c1_extCol]; omega

end CuspColumn

section GPassage

variable {V : Word} (f : Perm (Slot V))

/-- one more step of a block passage for a slot permutation -/
theorem gpassage_step (Ext : ℕ → Prop) {b c : Slot V} (hb : ¬ Ext (colOf b))
    (h : ∃ n, (f ^ n) (f b) = c ∧ ∀ i < n, ¬ Ext (colOf ((f ^ i) (f b)))) :
    ∃ n, (f ^ n) b = c ∧ ∀ i < n, ¬ Ext (colOf ((f ^ i) b)) := by
  obtain ⟨n, hc, hmin⟩ := h
  refine ⟨n + 1, by rw [pow_succ, Perm.mul_apply]; exact hc, ?_⟩
  intro i hi
  cases i with
  | zero => simpa using hb
  | succ i => rw [pow_succ, Perm.mul_apply]; exact hmin i (by omega)

theorem gpassage_end (Ext : ℕ → Prop) {b : Slot V} :
    ∃ n, (f ^ n) b = b ∧ ∀ i < n, ¬ Ext (colOf ((f ^ i) b)) :=
  ⟨0, rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

end GPassage

section SkeinG

variable (X Y : Word) (m : ℕ) (d a : Bool)

local notation "Vs" => X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y
local notation "Ps" => [Letter.l (m + 1) d, Letter.σ m]

variable (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed)

/-- the reconnected traversal of `A` at its site -/
noncomputable abbrev skG : Perm (Slot Vs) := gPerm hA (siteX X Y m d hA)

theorem skG_siteA : skG X Y m d hA (siteA X Y m d hA) = next hA (siteB X Y m d hA) := by
  unfold skG gPerm
  rw [Perm.mul_apply, siteX_val, Equiv.swap_apply_left, nextPerm_apply, σtwin_siteA]

theorem skG_siteB : skG X Y m d hA (siteB X Y m d hA) = next hA (siteA X Y m d hA) := by
  unfold skG gPerm
  rw [Perm.mul_apply, siteX_val, σtwin_siteA, Equiv.swap_apply_right, nextPerm_apply]

theorem skG_of_not_σ {u : Slot Vs} (h : ¬ IsσSlot u) : skG X Y m d hA u = next hA u :=
  gPerm_apply_of_not_σ hA _ h

theorem skG_of_ext {u : Slot Vs} (h : ExtPiece X Ps Y u) : skG X Y m d hA u = next hA u := by
  refine gPerm_apply_of_ne hA _ (fun e => ?_) (fun e => ?_)
  · rw [siteX_val] at e; exact (siteA_int X Y m d hA).2 (e ▸ h)
  · rw [siteX_val, σtwin_siteA] at e; exact (siteB_int X Y m d hA).2 (e ▸ h)

theorem sk_Pne2 : ([Letter.l (m + 1) d, Letter.σ m] : Word) ≠ [] := List.cons_ne_nil _ _

end SkeinG

section SkeinSmoothPassage

variable (X Y : Word) (m : ℕ) (d a : Bool) (j : ℕ)

local notation "Vs" => X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y
local notation "Ps" => [Letter.l (m + 1) d, Letter.σ m]
local notation "Vc" => X ++ [Letter.l j d] ++ Y
local notation "Pc" => [Letter.l j d]

variable {P L : Cuts} (hX : Word.run X [] = some (P ++ a :: L)) (hP : P.length = m - 1) (hm : 1 ≤ m)
variable (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed) (hC : (X ++ [Letter.l j d] ++ Y).Closed)
variable (hj : (a = !d ∧ j = m) ∨ (a = d ∧ j = m + 1))

include hX hP hm hj in
theorem skc_sameEffect : SameEffect X Ps Pc := by
  unfold SameEffect
  rw [Word.run_append, Word.run_append, hX, Option.bind_some, Option.bind_some, run_skein_A hm hP]
  rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [run_skein_Ctop hm hP]
  · rw [run_skein_Cbottom hm hP]

theorem skc_shift0 : shiftIdx X Ps Pc X.length = X.length := shiftIdx_of_le X Ps Pc le_rfl

theorem skc_shift2 : shiftIdx X Ps Pc (X.length + 2) = X.length + 1 := by
  unfold shiftIdx
  rw [ite_eq_right (by omega)]
  have e1 : ([Letter.l (m + 1) d, Letter.σ m] : Word).length = 2 := rfl
  have e2 : ([Letter.l j d] : Word).length = 1 := rfl
  rw [e1, e2]; omega

theorem skc_extPair0 (p : ℕ) : extPair X Ps Pc (X.length, p) = (X.length, p) := by
  simp only [extPair, skc_shift0]

theorem skc_extPair2 (p : ℕ) : extPair X Ps Pc (X.length + 2, p) = (X.length + 1, p) := by
  simp only [extPair, skc_shift2]

include hX hP hm hj in
/-- the bits of the cut after the smoothing's cusp are those after `A`'s block -/
theorem skc_bits (p : ℕ) : bit Vc (X.length + 1) p = bit Vs (X.length + 2) p := by
  have hE := skc_sameEffect X m d a j hX hP hm hj
  have := bit_ext X Ps Y Pc (sk_Pne2 m d) hE (k := X.length + 2) (Or.inr (by simp)) p
  rw [skc_shift2] at this
  exact this.symm

include hX hP hm hj in
theorem skc_bits0 (p : ℕ) : bit Vc X.length p = bit Vs X.length p := by
  have hE := skc_sameEffect X m d a j hX hP hm hj
  have := bit_ext X Ps Y Pc (sk_Pne2 m d) hE (k := X.length) (Or.inl le_rfl) p
  rw [skc_shift0] at this
  exact this.symm

include hX hP hm hj hA hC in
/-- THE BLOCK PASSAGE OF THE RECONNECTED TRAVERSAL of `A` against the compatible smoothing `C`. -/
theorem skc_passageF : PassageF X Ps Y Pc hC (skG X Y m d hA) := by
  have hE := skc_sameEffect X m d a j hX hP hm hj
  have hPne := sk_Pne2 m d
  obtain ⟨hℓ₀, hℓ₁⟩ := sk_letters X Y m d
  have hℓC := c1_letter X Y j d
  have ha := (sk_bit_a X Y m d a hX hP).1
  obtain ⟨c1, c2, c3, e1, e2, e3⟩ := sk_bits X Y m d a hA ha
  have cb1 : bit Vc (X.length + 1) m = d := by rw [skc_bits X Y m d a j hX hP hm hj, e1]
  have cb2 : bit Vc (X.length + 1) (m + 1) = a := by rw [skc_bits X Y m d a j hX hP hm hj, e2]
  have cb3 : bit Vc (X.length + 1) (m + 2) = !d := by rw [skc_bits X Y m d a j hX hP hm hj, e3]
  have hbx := skc_bits0 X Y m d a j hX hP hm hj
  have hsA := siteA_val X Y m d a hA ha
  have hsB := siteB_val X Y m d hA
  have hjm : j = m ∨ j = m + 1 := by rcases hj with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hk₀C : X.length < (Vc).length := by rw [c1_length]; omega
  have hk₀ : X.length < (Vs).length := by rw [sk_length]; omega
  constructor
  intro b hext hcol
  let b' : Slot Vc := ⟨extPair X Ps Pc b.1, isSlot_ext X Ps Y Pc hPne hE b.2 hext⟩
  have hb'v : b'.1 = extPair X Ps Pc b.1 := rfl
  rcases (entry_iff X Ps Y hPne hA b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
  · -- from the left at `(|X|, p)`
    have hb' : b'.1 = (X.length, p) := by rw [hb'v, hb, skc_extPair0]
    have hbit' : bit Vc X.length p = true := by rw [hbx]; exact hbit
    have nσb : ¬ IsσSlot b := not_σ_right hb hp hbit (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
    have g0 : (skG X Y m d hA b).1 = (next hA b).1 := by rw [skG_of_not_σ X Y m d hA nσb]
    have nb0 : ¬ ExtCol X Ps (colOf b) := by rw [block_col_true hb hp hbit, sk_extCol]; omega
    have nb0' : ¬ ExtCol X Pc (colOf b') := by rw [block_col_true hb' hp hbit', c1_extCol]; omega
    rcases lt_or_ge p m with hpm | hpm
    · -- above the site
      obtain ⟨h1, hb1⟩ := pass_r_lt hA hℓ₀ hb hp hbit (by simp [idx]; omega)
      rw [← g0] at h1
      have nσ1 : ¬ IsσSlot (skG X Y m d hA b) := not_σ_right h1 hp hb1 (fun _ hj' => by
        rw [hℓ₁] at hj'; injection hj' with hj'; omega)
      obtain ⟨h2, hb2⟩ := pass_r_lt hA hℓ₁ h1 hp hb1 (by simpa [idx] using hpm)
      rw [← skG_of_not_σ X Y m d hA nσ1] at h2
      obtain ⟨h1', hb1'⟩ := pass_r_lt hC hℓC hb' hp hbit' (by simp [idx]; omega)
      obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps) nb0
        (gpassage_step _ _ (by rw [block_col_true h1 hp hb1, sk_extCol]; omega) (gpassage_end _ _))
      obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0' (passage_end hC)
      refine ⟨n, _, hc, by rw [block_col_true h2 hp hb2, sk_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h2, skc_extPair2]
    rcases Nat.eq_or_lt_of_le hpm with hpe | hpm1
    · -- `p = m`: the through-strand enters the site
      rw [← hpe] at hb hb' hbit hbit'
      have hat : a = true := ha.symm.trans hbit
      have hp0 : m ≠ 0 := by omega
      obtain ⟨h1, hb1⟩ := pass_r_lt hA hℓ₀ hb hp0 hbit (by simp [idx])
      rw [← g0] at h1
      have hs1 : skG X Y m d hA b = siteA X Y m d hA := Subtype.ext (by rw [h1, hsA, ite_eq_left hat])
      rcases Bool.eq_false_or_eq_true d with hdt | hdf
      · -- `d = true`: `C = X l_{m+1} Y`, the arm exits at `(|X|+2, m)`
        have hjb : j = m + 1 := by
          rcases hj with ⟨h, -⟩ | ⟨-, h⟩
          · rw [hat, hdt] at h; cases h
          · exact h
        have hsB' : (siteB X Y m d hA).1 = (X.length + 1, m + 1) := by rw [hsB, ite_eq_left hdt]
        have hb2 : bit Vs (X.length + 1) (m + 1) = true := by rw [c2, hdt]
        have h2 := next_σ_right_succ hA hℓ₁ hsB' hb2
        have g2 : (skG X Y m d hA (skG X Y m d hA b)).1 = (X.length + 2, m) := by rw [hs1, skG_siteA, h2]
        have hb2e : bit Vs (X.length + 2) m = true := by rw [e1, hdt]
        obtain ⟨h1', hb1'⟩ := pass_r_lt hC hℓC hb' hp0 hbit' (by simp [idx]; omega)
        obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps) nb0
          (gpassage_step _ _ (by rw [block_col_true h1 hp0 hb1, sk_extCol]; omega) (gpassage_end _ _))
        obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0' (passage_end hC)
        refine ⟨n, _, hc, by rw [block_col_true g2 hp0 hb2e, sk_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
        rw [hc', h1', g2, skc_extPair2]
      · -- `d = false`: `C = X l_m Y`, the reconnected strand runs through the cusp, exits at `(|X|+2, m+2)`
        have hjt : j = m := by
          rcases hj with ⟨-, h⟩ | ⟨h, -⟩
          · exact h
          · rw [hat, hdf] at h; cases h
        have hsB' : (siteB X Y m d hA).1 = (X.length + 2, m) := by rw [hsB, ite_eq_right (by simp [hdf])]
        have hb2 : bit Vs (X.length + 2) m = false := by rw [e1, hdf]
        have h2 := next_σ_left_idx hA hℓ₁ hsB' hb2
        have g2 : (skG X Y m d hA (skG X Y m d hA b)).1 = (X.length + 1, m + 1) := by rw [hs1, skG_siteA, h2]
        have hb3 : bit Vs (X.length + 1) (m + 1) = false := by rw [c2, hdf]
        have nσ2 : ¬ IsσSlot (skG X Y m d hA (skG X Y m d hA b)) :=
          not_σ_left g2 (by omega) hb3 (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
        have h3 := next_arm_l hA hk₀ hℓ₀ g2 (Or.inl rfl) hb3
        rw [← skG_of_not_σ X Y m d hA nσ2] at h3
        have nσ3 : ¬ IsσSlot (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA b))) := not_σ_vertex h3
        have h4 := next_cusp_l hA hℓ₀ h3
        rw [ite_eq_right (by simp [hdf]), ← skG_of_not_σ X Y m d hA nσ3] at h4
        have hb4 : bit Vs (X.length + 1) (m + 1 + 1) = true := by rw [c3, hdf]; rfl
        have nσ4 : ¬ IsσSlot (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA b)))) :=
          not_σ_right h4 (by omega) hb4 (fun _ hj' => by rw [hℓ₁] at hj'; injection hj' with hj'; omega)
        obtain ⟨h5, hb5⟩ := pass_r_ge hA hℓ₁ h4 (by omega) hb4 (by simp [idx, arity])
        simp only [arity, coarity, Nat.add_sub_cancel] at h5 hb5
        rw [← skG_of_not_σ X Y m d hA nσ4] at h5
        obtain ⟨h1', hb1'⟩ := pass_r_ge hC hℓC hb' hp0 hbit' (by simp [idx, arity]; omega)
        simp only [arity, coarity, Nat.sub_zero] at h1' hb1'
        obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps) nb0
          (gpassage_step _ _ (by rw [block_col_true h1 hp0 hb1, sk_extCol]; omega)
          (gpassage_step _ _ (by rw [block_col_false g2 (by omega) hb3, sk_extCol]; omega)
          (gpassage_step _ _ (by rw [block_col_vertex h3, sk_extCol]; omega)
          (gpassage_step _ _ (by rw [block_col_true h4 (by omega) hb4, sk_extCol]; omega) (gpassage_end _ _)))))
        obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0' (passage_end hC)
        refine ⟨n, _, hc, by rw [block_col_true h5 (by omega) hb5, sk_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
        rw [hc', h1', h5, skc_extPair2]
    · -- below the site
      obtain ⟨h1, hb1⟩ := pass_r_ge hA hℓ₀ hb hp hbit (by simp [idx, arity]; omega)
      simp only [arity, coarity, Nat.sub_zero] at h1 hb1
      rw [← g0] at h1
      have nσ1 : ¬ IsσSlot (skG X Y m d hA b) := not_σ_right h1 (by omega) hb1 (fun _ hj' => by
        rw [hℓ₁] at hj'; injection hj' with hj'; omega)
      obtain ⟨h2, hb2⟩ := pass_r_ge hA hℓ₁ h1 (by omega) hb1 (by simp [idx, arity]; omega)
      simp only [arity, coarity, Nat.add_sub_cancel] at h2 hb2
      rw [← skG_of_not_σ X Y m d hA nσ1] at h2
      obtain ⟨h1', hb1'⟩ := pass_r_ge hC hℓC hb' hp hbit' (by simp [idx, arity]; omega)
      simp only [arity, coarity, Nat.sub_zero] at h1' hb1'
      obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps) nb0
        (gpassage_step _ _ (by rw [block_col_true h1 (by omega) hb1, sk_extCol]; omega) (gpassage_end _ _))
      obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0' (passage_end hC)
      refine ⟨n, _, hc, by rw [block_col_true h2 (by omega) hb2, sk_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h2, skc_extPair2]
  · -- from the right at `(|X|+2, p)`
    replace hb : b.1 = (X.length + 2, p) := hb
    replace hbit : bit Vs (X.length + 2) p = false := hbit
    have hb' : b'.1 = (X.length + 1, p) := by rw [hb'v, hb, skc_extPair2]
    have hbit' : bit Vc (X.length + 1) p = false := by rw [skc_bits X Y m d a j hX hP hm hj]; exact hbit
    have nb0' : ¬ ExtCol X Pc (colOf b') := by rw [block_col_false hb' hp hbit', c1_extCol]; omega
    rcases lt_or_ge p m with hpm | hpm
    · -- above the site
      have nσb : ¬ IsσSlot b := not_σ_left hb hp hbit (fun _ hj' => by rw [hℓ₁] at hj'; injection hj' with hj'; omega)
      obtain ⟨h1, hb1⟩ := pass_l_lt hA hℓ₁ hb hp hbit (by simpa [idx] using hpm)
      rw [← skG_of_not_σ X Y m d hA nσb] at h1
      have nσ1 : ¬ IsσSlot (skG X Y m d hA b) := not_σ_left h1 hp hb1 (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
      obtain ⟨h2, hb2⟩ := pass_l_lt hA hℓ₀ h1 hp hb1 (by simp [idx]; omega)
      rw [← skG_of_not_σ X Y m d hA nσ1] at h2
      obtain ⟨h1', hb1'⟩ := pass_l_lt hC hℓC hb' hp hbit' (by simp [idx]; omega)
      obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps)
        (by rw [block_col_false hb hp hbit, sk_extCol]; omega)
        (gpassage_step _ _ (by rw [block_col_false h1 hp hb1, sk_extCol]; omega) (gpassage_end _ _))
      obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0' (passage_end hC)
      refine ⟨n, _, hc, ?_, hmin, n', b', rfl, ?_, hmin'⟩
      · have := (cutSlot_facts hA h2 hp).2.2.1
        rw [block_col_false h2 hp hb2, sk_extCol]; omega
      · rw [hc', h1', h2, skc_extPair0]
    rcases lt_or_ge p (m + 3) with hpm3 | hpm3
    · have hp3 : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
      rcases hp3 with hpe | hpe | hpe
      · -- `p = m`: the upper arm heading left is the arm slot; the reconnection follows the through-strand
        rw [hpe] at hb hb' hbit hbit'
        have hdf : d = false := e1.symm.trans hbit
        have hs0 : b = siteB X Y m d hA := Subtype.ext (by rw [hb, hsB, ite_eq_right (by simp [hdf])])
        rcases Bool.eq_false_or_eq_true a with hat | haf
        · -- `a = true`, `C = X l_m Y`: out at `(|X|+2, m+1)`
          have hjt : j = m := by
            rcases hj with ⟨-, h⟩ | ⟨h, -⟩
            · exact h
            · rw [hat, hdf] at h; cases h
          have hsA' : (siteA X Y m d hA).1 = (X.length + 1, m) := by rw [hsA, ite_eq_left hat]
          have hb1 : bit Vs (X.length + 1) m = true := by rw [c1, hat]
          have h1 := next_σ_right_idx hA hℓ₁ hsA' hb1
          have g1 : (skG X Y m d hA b).1 = (X.length + 2, m + 1) := by rw [hs0, skG_siteB, h1]
          have hb1e : bit Vs (X.length + 2) (m + 1) = true := by rw [e2, hat]
          -- `C`: through the cusp
          have h1' := next_arm_l hC hk₀C hℓC hb' (by omega) hbit'
          have h2' := next_cusp_l hC hℓC h1'
          rw [ite_eq_right (by simp [hdf])] at h2'
          have hb2' : bit Vc (X.length + 1) (j + 1) = true := by
            have h := cb2; rw [← hjt] at h; rw [h, hat]
          obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps)
            (by rw [block_col_false hb (by omega) hbit, sk_extCol]; omega) (gpassage_end _ _)
          obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0'
            (passage_step hC _ (by rw [block_col_vertex h1', c1_extCol]; omega) (passage_end hC))
          refine ⟨n, _, hc, by rw [block_col_true g1 (by omega) hb1e, sk_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
          rw [hc', h2', g1, skc_extPair2, hjt]
        · -- `a = false`, `C = X l_{m+1} Y`: out at `(|X|, m)`
          have hjb : j = m + 1 := by
            rcases hj with ⟨h, -⟩ | ⟨-, h⟩
            · rw [haf, hdf] at h; cases h
            · exact h
          have hsA' : (siteA X Y m d hA).1 = (X.length + 2, m + 1) := by rw [hsA, ite_eq_right (by simp [haf])]
          have hb1 : bit Vs (X.length + 2) (m + 1) = false := by rw [e2, haf]
          have h1 := next_σ_left_succ hA hℓ₁ hsA' hb1
          have g1 : (skG X Y m d hA b).1 = (X.length + 1, m) := by rw [hs0, skG_siteB, h1]
          have hb1e : bit Vs (X.length + 1) m = false := by rw [c1, haf]
          have nσ1 : ¬ IsσSlot (skG X Y m d hA b) := not_σ_left g1 (by omega) hb1e (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
          obtain ⟨h2, hb2⟩ := pass_l_lt hA hℓ₀ g1 (by omega) hb1e (by simp [idx])
          rw [← skG_of_not_σ X Y m d hA nσ1] at h2
          obtain ⟨h1', hb1'⟩ := pass_l_lt hC hℓC hb' (by omega) hbit' (by simp [idx]; omega)
          obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps)
            (by rw [block_col_false hb (by omega) hbit, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [block_col_false g1 (by omega) hb1e, sk_extCol]; omega) (gpassage_end _ _))
          obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0' (passage_end hC)
          refine ⟨n, _, hc, ?_, hmin, n', b', rfl, ?_, hmin'⟩
          · have := (cutSlot_facts hA h2 (by omega)).2.2.1
            rw [block_col_false h2 (by omega) hb2, sk_extCol]; omega
          · rw [hc', h1', h2, skc_extPair0]
      · -- `p = m + 1`: the through-strand heading left is the site slot
        rw [hpe] at hb hb' hbit hbit'
        have haf : a = false := e2.symm.trans hbit
        have hs0 : b = siteA X Y m d hA := Subtype.ext (by rw [hb, hsA, ite_eq_right (by simp [haf])])
        rcases Bool.eq_false_or_eq_true d with hdt | hdf
        · -- `d = true`, `C = X l_m Y`: out at `(|X|+2, m)`
          have hjt : j = m := by
            rcases hj with ⟨-, h⟩ | ⟨h, -⟩
            · exact h
            · rw [haf, hdt] at h; cases h
          have hsB' : (siteB X Y m d hA).1 = (X.length + 1, m + 1) := by rw [hsB, ite_eq_left hdt]
          have hb1 : bit Vs (X.length + 1) (m + 1) = true := by rw [c2, hdt]
          have h1 := next_σ_right_succ hA hℓ₁ hsB' hb1
          have g1 : (skG X Y m d hA b).1 = (X.length + 2, m) := by rw [hs0, skG_siteA, h1]
          have hb1e : bit Vs (X.length + 2) m = true := by rw [e1, hdt]
          have h1' := next_arm_l hC hk₀C hℓC hb' (by omega) hbit'
          have h2' := next_cusp_l hC hℓC h1'
          rw [ite_eq_left hdt] at h2'
          have hb2' : bit Vc (X.length + 1) j = true := by
            have h := cb1; rw [← hjt] at h; rw [h, hdt]
          obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps)
            (by rw [block_col_false hb (by omega) hbit, sk_extCol]; omega) (gpassage_end _ _)
          obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0'
            (passage_step hC _ (by rw [block_col_vertex h1', c1_extCol]; omega) (passage_end hC))
          refine ⟨n, _, hc, by rw [block_col_true g1 (by omega) hb1e, sk_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
          rw [hc', h2', g1, skc_extPair2, hjt]
        · -- `d = false`, `C = X l_{m+1} Y`: through the cusp, out at `(|X|+2, m+2)`
          have hjb : j = m + 1 := by
            rcases hj with ⟨h, -⟩ | ⟨-, h⟩
            · rw [haf, hdf] at h; cases h
            · exact h
          have hsB' : (siteB X Y m d hA).1 = (X.length + 2, m) := by rw [hsB, ite_eq_right (by simp [hdf])]
          have hb1 : bit Vs (X.length + 2) m = false := by rw [e1, hdf]
          have h1 := next_σ_left_idx hA hℓ₁ hsB' hb1
          have g1 : (skG X Y m d hA b).1 = (X.length + 1, m + 1) := by rw [hs0, skG_siteA, h1]
          have hb1e : bit Vs (X.length + 1) (m + 1) = false := by rw [c2, hdf]
          have nσ1 : ¬ IsσSlot (skG X Y m d hA b) := not_σ_left g1 (by omega) hb1e (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
          have h2 := next_arm_l hA hk₀ hℓ₀ g1 (Or.inl rfl) hb1e
          rw [← skG_of_not_σ X Y m d hA nσ1] at h2
          have nσ2 : ¬ IsσSlot (skG X Y m d hA (skG X Y m d hA b)) := not_σ_vertex h2
          have h3 := next_cusp_l hA hℓ₀ h2
          rw [ite_eq_right (by simp [hdf]), ← skG_of_not_σ X Y m d hA nσ2] at h3
          have hb3 : bit Vs (X.length + 1) (m + 1 + 1) = true := by rw [c3, hdf]; rfl
          have nσ3 : ¬ IsσSlot (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA b))) :=
            not_σ_right h3 (by omega) hb3 (fun _ hj' => by rw [hℓ₁] at hj'; injection hj' with hj'; omega)
          obtain ⟨h4, hb4⟩ := pass_r_ge hA hℓ₁ h3 (by omega) hb3 (by simp [idx, arity])
          simp only [arity, coarity, Nat.add_sub_cancel] at h4 hb4
          rw [← skG_of_not_σ X Y m d hA nσ3] at h4
          have h1' := next_arm_l hC hk₀C hℓC hb' (by omega) hbit'
          have h2' := next_cusp_l hC hℓC h1'
          rw [ite_eq_right (by simp [hdf])] at h2'
          have hb2' : bit Vc (X.length + 1) (j + 1) = true := by
            have h := cb3; rw [show m + 2 = j + 1 by omega] at h; rw [h, hdf]; rfl
          obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps)
            (by rw [block_col_false hb (by omega) hbit, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [block_col_false g1 (by omega) hb1e, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [block_col_vertex h2, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [block_col_true h3 (by omega) hb3, sk_extCol]; omega) (gpassage_end _ _))))
          obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0'
            (passage_step hC _ (by rw [block_col_vertex h1', c1_extCol]; omega) (passage_end hC))
          refine ⟨n, _, hc, by rw [block_col_true h4 (by omega) hb4, sk_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
          rw [hc', h2', h4, skc_extPair2, hjb]
      · -- `p = m + 2`: the lower arm heading left, through the cusp to the arm slot, then the reconnection
        rw [hpe] at hb hb' hbit hbit'
        have hdt : d = true := by have := e3.symm.trans hbit; cases d <;> simp_all
        have nσb : ¬ IsσSlot b := not_σ_left hb (by omega) hbit (fun _ hj' => by rw [hℓ₁] at hj'; injection hj' with hj'; omega)
        obtain ⟨h1, hb1⟩ := pass_l_ge hA hℓ₁ hb (by omega) hbit (by simp [idx, coarity])
        simp only [arity, coarity, Nat.add_sub_cancel] at h1 hb1
        rw [← skG_of_not_σ X Y m d hA nσb] at h1
        have nσ1 : ¬ IsσSlot (skG X Y m d hA b) := not_σ_left h1 (by omega) hb1 (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
        have h2 := next_arm_l hA hk₀ hℓ₀ h1 (Or.inr rfl) hb1
        rw [← skG_of_not_σ X Y m d hA nσ1] at h2
        have nσ2 : ¬ IsσSlot (skG X Y m d hA (skG X Y m d hA b)) := not_σ_vertex h2
        have h3 := next_cusp_l hA hℓ₀ h2
        rw [ite_eq_left hdt, ← skG_of_not_σ X Y m d hA nσ2] at h3
        have hs3 : skG X Y m d hA (skG X Y m d hA (skG X Y m d hA b)) = siteB X Y m d hA :=
          Subtype.ext (by rw [h3, hsB, ite_eq_left hdt])
        rcases Bool.eq_false_or_eq_true a with hat | haf
        · -- `a = true`, `C = X l_{m+1} Y`: through the cusp to the arm at `(|X|+1, j)`, out at `(|X|+2, m+1)`
          have hjb : j = m + 1 := by
            rcases hj with ⟨h, -⟩ | ⟨-, h⟩
            · rw [hat, hdt] at h; cases h
            · exact h
          have hsA' : (siteA X Y m d hA).1 = (X.length + 1, m) := by rw [hsA, ite_eq_left hat]
          have hb4 : bit Vs (X.length + 1) m = true := by rw [c1, hat]
          have h4 := next_σ_right_idx hA hℓ₁ hsA' hb4
          have g4 : (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA b)))).1 = (X.length + 2, m + 1) := by
            rw [hs3, skG_siteB, h4]
          have hb4e : bit Vs (X.length + 2) (m + 1) = true := by rw [e2, hat]
          have h1' := next_arm_l hC hk₀C hℓC hb' (by omega) hbit'
          have h2' := next_cusp_l hC hℓC h1'
          rw [ite_eq_left hdt] at h2'
          have hb2' : bit Vc (X.length + 1) j = true := by
            have h := cb2; rw [← hjb] at h; rw [h, hat]
          obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps)
            (by rw [block_col_false hb (by omega) hbit, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [block_col_false h1 (by omega) hb1, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [block_col_vertex h2, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [hs3]; exact (siteB_int X Y m d hA).2) (gpassage_end _ _))))
          obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0'
            (passage_step hC _ (by rw [block_col_vertex h1', c1_extCol]; omega) (passage_end hC))
          refine ⟨n, _, hc, by rw [block_col_true g4 (by omega) hb4e, sk_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
          rw [hc', h2', g4, skc_extPair2, hjb]
        · -- `a = false`, `C = X l_m Y`: out at `(|X|, m)`
          have hjt : j = m := by
            rcases hj with ⟨-, h⟩ | ⟨h, -⟩
            · exact h
            · rw [haf, hdt] at h; cases h
          have hsA' : (siteA X Y m d hA).1 = (X.length + 2, m + 1) := by rw [hsA, ite_eq_right (by simp [haf])]
          have hb4 : bit Vs (X.length + 2) (m + 1) = false := by rw [e2, haf]
          have h4 := next_σ_left_succ hA hℓ₁ hsA' hb4
          have g4 : (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA b)))).1 = (X.length + 1, m) := by
            rw [hs3, skG_siteB, h4]
          have hb4e : bit Vs (X.length + 1) m = false := by rw [c1, haf]
          have nσ4 : ¬ IsσSlot (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA b)))) :=
            not_σ_left g4 (by omega) hb4e (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
          obtain ⟨h5, hb5⟩ := pass_l_lt hA hℓ₀ g4 (by omega) hb4e (by simp [idx])
          rw [← skG_of_not_σ X Y m d hA nσ4] at h5
          -- `C`: the arm strand passes below the cusp straight to `(|X|, m)`
          obtain ⟨h1c, hb1c⟩ := pass_l_ge hC hℓC hb' (by omega) hbit' (by simp [idx, coarity]; omega)
          simp only [arity, coarity] at h1c hb1c
          obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps)
            (by rw [block_col_false hb (by omega) hbit, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [block_col_false h1 (by omega) hb1, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [block_col_vertex h2, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [hs3]; exact (siteB_int X Y m d hA).2)
            (gpassage_step _ _ (by rw [block_col_false g4 (by omega) hb4e, sk_extCol]; omega) (gpassage_end _ _)))))
          obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0' (passage_end hC)
          refine ⟨n, _, hc, ?_, hmin, n', b', rfl, ?_, hmin'⟩
          · have := (cutSlot_facts hA h5 (by omega)).2.2.1
            rw [block_col_false h5 (by omega) hb5, sk_extCol]; omega
          · rw [hc', h1c, h5, skc_extPair0]
            simp only [Prod.mk.injEq, true_and]; omega
    · -- below the site
      have nσb : ¬ IsσSlot b := not_σ_left hb hp hbit (fun _ hj' => by rw [hℓ₁] at hj'; injection hj' with hj'; omega)
      obtain ⟨h1, hb1⟩ := pass_l_ge hA hℓ₁ hb hp hbit (by simp [idx, coarity]; omega)
      simp only [arity, coarity, Nat.add_sub_cancel] at h1 hb1
      rw [← skG_of_not_σ X Y m d hA nσb] at h1
      have nσ1 : ¬ IsσSlot (skG X Y m d hA b) := not_σ_left h1 hp hb1 (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
      obtain ⟨h2, hb2⟩ := pass_l_ge hA hℓ₀ h1 hp hb1 (by simp [idx, coarity]; omega)
      simp only [arity, coarity] at h2 hb2
      rw [← skG_of_not_σ X Y m d hA nσ1] at h2
      obtain ⟨h1', hb1'⟩ := pass_l_ge hC hℓC hb' hp hbit' (by simp [idx, coarity]; omega)
      simp only [arity, coarity] at h1' hb1'
      obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps)
        (by rw [block_col_false hb hp hbit, sk_extCol]; omega)
        (gpassage_step _ _ (by rw [block_col_false h1 hp hb1, sk_extCol]; omega) (gpassage_end _ _))
      obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0' (passage_end hC)
      refine ⟨n, _, hc, ?_, hmin, n', b', rfl, ?_, hmin'⟩
      · have := (cutSlot_facts hA h2 (by omega)).2.2.1
        rw [block_col_false h2 (by omega) hb2, sk_extCol]; omega
      · rw [hc', h1', h2, skc_extPair0]

end SkeinSmoothPassage

section SkeinSmoothIso

variable (X Y : Word) (m : ℕ) (d a : Bool) (j : ℕ)

local notation "Vs" => X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y
local notation "Ps" => [Letter.l (m + 1) d, Letter.σ m]
local notation "Vc" => X ++ [Letter.l j d] ++ Y
local notation "Pc" => [Letter.l j d]

variable {P L : Cuts} (hX : Word.run X [] = some (P ++ a :: L)) (hP : P.length = m - 1) (hm : 1 ≤ m)
variable (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed) (hC : (X ++ [Letter.l j d] ++ Y).Closed)
variable (hj : (a = !d ∧ j = m) ∨ (a = d ∧ j = m + 1))

theorem greach_step {V : Word} {f : Perm (Slot V)} {E : Slot V → Prop} {u : Slot V} (h : ∃ n, E ((f ^ n) (f u))) :
    ∃ n, E ((f ^ n) u) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [pow_succ, Perm.mul_apply]; exact hn⟩

theorem greach_self {V : Word} {f : Perm (Slot V)} {E : Slot V → Prop} {u : Slot V} (h : E u) : ∃ n, E ((f ^ n) u) :=
  ⟨0, h⟩

include hX hP hm hA hC hj in
/-- every slot of `A` reaches the exterior under the reconnected traversal -/
theorem sk_ghexit : ∀ u : Slot Vs, ∃ n, ExtPiece X Ps Y (((skG X Y m d hA) ^ n) u) := by
  have hpass := skc_passageF X Y m d a j hX hP hm hA hC hj
  obtain ⟨hℓ₀, hℓ₁⟩ := sk_letters X Y m d
  have ha := (sk_bit_a X Y m d a hX hP).1
  obtain ⟨c1, c2, c3, e1, e2, e3⟩ := sk_bits X Y m d a hA ha
  have hsA := siteA_val X Y m d a hA ha
  have hsB := siteB_val X Y m d hA
  have hk₀ : X.length < (Vs).length := by rw [sk_length]; omega
  have hPne := sk_Pne2 m d
  -- from the successor of the through-strand slot
  have R2 : ∀ u : Slot Vs, u = next hA (siteA X Y m d hA) → ∃ n, ExtPiece X Ps Y (((skG X Y m d hA) ^ n) u) := by
    intro u hu
    rcases Bool.eq_false_or_eq_true a with hat | haf
    · have hs : (siteA X Y m d hA).1 = (X.length + 1, m) := by rw [hsA, ite_eq_left hat]
      have h1 := next_σ_right_idx hA hℓ₁ hs (by rw [c1, hat])
      rw [← hu] at h1
      refine greach_self ?_
      show ExtCol X Ps (colOf _)
      rw [block_col_true h1 (by omega) (by rw [e2, hat]), sk_extCol]; omega
    · have hs : (siteA X Y m d hA).1 = (X.length + 2, m + 1) := by rw [hsA, ite_eq_right (by simp [haf])]
      have h1 := next_σ_left_succ hA hℓ₁ hs (by rw [e2, haf])
      rw [← hu] at h1
      have hb1 : bit Vs (X.length + 1) m = false := by rw [c1, haf]
      have nσ1 : ¬ IsσSlot u := not_σ_left h1 (by omega) hb1 (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
      obtain ⟨h2, hb2⟩ := pass_l_lt hA hℓ₀ h1 (by omega) hb1 (by simp [idx])
      rw [← skG_of_not_σ X Y m d hA nσ1] at h2
      refine greach_step (greach_self ?_)
      show ExtCol X Ps (colOf _)
      have := (cutSlot_facts hA h2 (by omega)).2.2.1
      rw [block_col_false h2 (by omega) hb2, sk_extCol]; omega
  have RsiteB : ∃ n, ExtPiece X Ps Y (((skG X Y m d hA) ^ n) (siteB X Y m d hA)) :=
    greach_step (R2 _ (skG_siteB X Y m d hA))
  -- from the left-cusp vertex
  have Rv : ∀ u : Slot Vs, u.1 = (X.length, 0) → ∃ n, ExtPiece X Ps Y (((skG X Y m d hA) ^ n) u) := by
    intro u hu
    have h1 := next_cusp_l hA hℓ₀ hu
    rw [← skG_of_not_σ X Y m d hA (not_σ_vertex hu)] at h1
    rcases Bool.eq_false_or_eq_true d with hdt | hdf
    · rw [ite_eq_left hdt] at h1
      have hs : skG X Y m d hA u = siteB X Y m d hA := Subtype.ext (by rw [h1, hsB, ite_eq_left hdt])
      exact greach_step (by rw [hs]; exact RsiteB)
    · rw [ite_eq_right (by simp [hdf])] at h1
      have hb1 : bit Vs (X.length + 1) (m + 1 + 1) = true := by rw [c3, hdf]; rfl
      have nσ1 : ¬ IsσSlot (skG X Y m d hA u) :=
        not_σ_right h1 (by omega) hb1 (fun _ hj' => by rw [hℓ₁] at hj'; injection hj' with hj'; omega)
      obtain ⟨h2, hb2⟩ := pass_r_ge hA hℓ₁ h1 (by omega) hb1 (by simp [idx, arity])
      simp only [arity, coarity, Nat.add_sub_cancel] at h2 hb2
      rw [← skG_of_not_σ X Y m d hA nσ1] at h2
      refine greach_step (greach_step (greach_self ?_))
      show ExtCol X Ps (colOf _)
      rw [block_col_true h2 (by omega) hb2, sk_extCol]; omega
  -- from the successor of the arm slot
  have R1 : ∀ u : Slot Vs, u = next hA (siteB X Y m d hA) → ∃ n, ExtPiece X Ps Y (((skG X Y m d hA) ^ n) u) := by
    intro u hu
    rcases Bool.eq_false_or_eq_true d with hdt | hdf
    · have hs : (siteB X Y m d hA).1 = (X.length + 1, m + 1) := by rw [hsB, ite_eq_left hdt]
      have h1 := next_σ_right_succ hA hℓ₁ hs (by rw [c2, hdt])
      rw [← hu] at h1
      refine greach_self ?_
      show ExtCol X Ps (colOf _)
      rw [block_col_true h1 (by omega) (by rw [e1, hdt]), sk_extCol]; omega
    · have hs : (siteB X Y m d hA).1 = (X.length + 2, m) := by rw [hsB, ite_eq_right (by simp [hdf])]
      have h1 := next_σ_left_idx hA hℓ₁ hs (by rw [e1, hdf])
      rw [← hu] at h1
      have hb1 : bit Vs (X.length + 1) (m + 1) = false := by rw [c2, hdf]
      have nσ1 : ¬ IsσSlot u := not_σ_left h1 (by omega) hb1 (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
      have h2 := next_arm_l hA hk₀ hℓ₀ h1 (Or.inl rfl) hb1
      rw [← skG_of_not_σ X Y m d hA nσ1] at h2
      exact greach_step (Rv _ h2)
  have RsiteA : ∃ n, ExtPiece X Ps Y (((skG X Y m d hA) ^ n) (siteA X Y m d hA)) :=
    greach_step (R1 _ (skG_siteA X Y m d hA))
  intro u
  by_cases hext : ExtCol X Ps (colOf u)
  · exact greach_self hext
  -- the entries
  by_cases hentry : IsExtSlot X Ps u.1
  · obtain ⟨n, c, hmc, hc, -, -⟩ := hpass.pass u hentry hext
    exact ⟨n, by rw [hmc]; exact hc⟩
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, sk_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · exact Rv u hu
    · exfalso; have := vertex_not_crossing hu; rw [hℓ₁] at this; exact Bool.noConfusion this
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hA hu hp
  cases hb : bit Vs k p
  · rw [block_col_false hu hp hb, sk_extCol] at hext
    have : k = X.length + 1 ∨ k = X.length + 2 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · have nσ : ¬ IsσSlot u := not_σ_left hu hp hb (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
        obtain ⟨h1, hb1⟩ := pass_l_lt hA hℓ₀ hu hp hb (by simpa [idx] using hpm)
        rw [← skG_of_not_σ X Y m d hA nσ] at h1
        refine greach_step (greach_self ?_)
        show ExtCol X Ps (colOf _)
        have := (cutSlot_facts hA h1 hp).2.2.1
        rw [block_col_false h1 hp hb1, sk_extCol]; omega
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have nσ : ¬ IsσSlot u := not_σ_left hu hp hb (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
        have h1 := next_arm_l hA hk₀ hℓ₀ hu (by omega) hb
        rw [← skG_of_not_σ X Y m d hA nσ] at h1
        exact greach_step (Rv _ h1)
      · have nσ : ¬ IsσSlot u := not_σ_left hu hp hb (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
        obtain ⟨h1, hb1⟩ := pass_l_ge hA hℓ₀ hu hp hb (by simpa [idx, coarity] using hpm3)
        simp only [arity, coarity] at h1 hb1
        rw [← skG_of_not_σ X Y m d hA nσ] at h1
        refine greach_step (greach_self ?_)
        show ExtCol X Ps (colOf _)
        have := (cutSlot_facts hA h1 (by omega)).2.2.1
        rw [block_col_false h1 (by omega) hb1, sk_extCol]; omega
    · -- a right entry
      exfalso; apply hentry
      unfold IsExtSlot; rw [hu]; simp only
      rw [ite_eq_right hp]; right; simp
  · rw [block_col_true hu hp hb, sk_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · -- a left entry
      exfalso; apply hentry
      unfold IsExtSlot; rw [hu]; simp only
      rw [ite_eq_right hp]; left; exact le_rfl
    · rcases lt_or_ge p m with hpm | hpm
      · have nσ : ¬ IsσSlot u := not_σ_right hu hp hb (fun _ hj' => by rw [hℓ₁] at hj'; injection hj' with hj'; omega)
        obtain ⟨h1, hb1⟩ := pass_r_lt hA hℓ₁ hu hp hb (by simpa [idx] using hpm)
        rw [← skG_of_not_σ X Y m d hA nσ] at h1
        refine greach_step (greach_self ?_)
        show ExtCol X Ps (colOf _)
        rw [block_col_true h1 hp hb1, sk_extCol]; omega
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
        · -- the through-strand slot
          have hat : a = true := by rw [← hpe] at hb; exact c1.symm.trans hb
          have hs : u = siteA X Y m d hA := Subtype.ext (by rw [hu, hsA, ite_eq_left hat, hpe])
          rw [hs]; exact RsiteA
        · have hpe' : p = m + 1 := by omega
          have hdt : d = true := by rw [hpe'] at hb; exact c2.symm.trans hb
          have hs : u = siteB X Y m d hA := Subtype.ext (by rw [hu, hsB, ite_eq_left hdt, hpe'])
          rw [hs]; exact RsiteB
      · have nσ : ¬ IsσSlot u := not_σ_right hu hp hb (fun _ hj' => by rw [hℓ₁] at hj'; injection hj' with hj'; omega)
        obtain ⟨h1, hb1⟩ := pass_r_ge hA hℓ₁ hu hp hb (by simpa [idx, arity] using hpm2)
        simp only [arity, coarity, Nat.add_sub_cancel] at h1 hb1
        rw [← skG_of_not_σ X Y m d hA nσ] at h1
        refine greach_step (greach_self ?_)
        show ExtCol X Ps (colOf _)
        rw [block_col_true h1 hp hb1, sk_extCol]; omega

include hX hP hm hj in
/-- THE SMOOTHING HALF of the cusp-skein site: the σ-slot record of `A` smoothed at the site is the σ-slot
record of the compatible smoothing `C`. -/
theorem sk_smoothIso :
    Nonempty (RecordIso ((slotRecord hA IsσSlot (allActive hA)).smooth (siteX X Y m d hA))
      (slotRecord hC IsσSlot (allActive hC))) := by
  have hE := skc_sameEffect X m d a j hX hP hm hj
  have hPne := sk_Pne2 m d
  refine ⟨smoothRecordIso hA hC (ExtPiece X Ps Y) (ExtPiece X Pc Y) (φE X Ps Y Pc hPne hE hA) (siteX X Y m d hA)
    ?_ ?_ ?_ (fun _ hu => c1_σ_ext X Y j d hC hu)
    (conj_of_passageF X Ps Y Pc hPne hE hA hC (skG X Y m d hA) (fun _ hu => skG_of_ext X Y m d hA hu)
      (skc_passageF X Y m d a j hX hP hm hA hC hj))
    (sk_ghexit X Y m d a j hX hP hm hA hC hj) ?_
    (isσSlot_φE_iff X Ps Y Pc hPne hE hA) (fun _ hE' hσ => extPiece_σtwin X Ps Y hA hσ hE')
    (fun u hu => φE_σtwin X Ps Y Pc hPne hE hA hC u hu) (fun u _ => isDesc_φE X Ps Y Pc hPne hE hA u)
    (fun u _ => σsgn_φE X Ps Y Pc hPne hE hA u)⟩
  · intro u hu h1 h2
    by_contra hext
    have hint : IntSlot X Ps Y u := ⟨hu, hext⟩
    rcases (sk_int_iff X Y m d hA u).1 hint with h | h
    · exact h1 (by rw [h, siteX_val])
    · exact h2 (by rw [h, siteX_val, σtwin_siteA])
  · rw [siteX_val]; exact (siteA_int X Y m d hA).2
  · rw [siteX_val, σtwin_siteA]; exact (siteB_int X Y m d hA).2
  · intro u
    obtain ⟨n, hn⟩ := c1_hexit X Y j d hC u
    exact ⟨n, by rw [nextPerm_pow_apply]; exact hn⟩

include hP hm in
/-- the writhe of the site's factor is the sign of the site -/
theorem sk_writhe_factor : Word.writheFrom [Letter.l (m + 1) d, Letter.σ m] (P ++ a :: L) = if a = d then 1 else -1 := by
  have s1 : (Letter.l (m + 1) d).step (P ++ a :: L) = some (P ++ a :: d :: (!d) :: L) := by
    rw [show P ++ a :: L = (P ++ [a]) ++ L by simp,
      step_of_prefix (ℓ := .l (m + 1) d) (by idxomega) (by idxomega) (act_l _ _ _)]
    simp
  have s2 : (Letter.σ m).step (P ++ a :: d :: (!d) :: L) = some (P ++ d :: a :: (!d) :: L) :=
    step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  have d1 : (P ++ a :: d :: (!d) :: L).drop (m - 1) = a :: d :: (!d) :: L := List.drop_left' hP
  rw [u1_writheFrom_cons s1, u1_writheFrom_cons s2, u1_writheFrom_nil, u1_signBit_σ_drop d1, u1_signBit_l]
  simp

end SkeinSmoothIso

/-! #### K. The disjoint-gadget commutation (ng:commutation): `X a b Y ↦ X b a' Y` with `b` above `a` -/

section Comm

variable (X Y : Word) (a b : Letter)

local notation "Wc" => X ++ [a, b] ++ Y
local notation "Pc2" => [a, b]
local notation "Wc'" => X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y
local notation "Pc2'" => [b, a.reindex (a.idx + b.coarity - b.arity)]

theorem arity_reindex (ℓ : Letter) (n : ℕ) : (ℓ.reindex n).arity = ℓ.arity := by cases ℓ <;> rfl
theorem coarity_reindex (ℓ : Letter) (n : ℕ) : (ℓ.reindex n).coarity = ℓ.coarity := by cases ℓ <;> rfl

theorem cm_letters : letterAt Wc X.length = a ∧ letterAt Wc (X.length + 1) = b := by
  constructor
  · have := letterAt_block X Pc2 Y (i := 0) (by simp)
    simpa using this
  · have := letterAt_block X Pc2 Y (i := 1) (by simp)
    simpa using this

theorem cm_letters' : letterAt Wc' X.length = b ∧ letterAt Wc' (X.length + 1) = a.reindex (a.idx + b.coarity - b.arity) := by
  constructor
  · have := letterAt_block X Pc2' Y (i := 0) (by simp)
    simpa using this
  · have := letterAt_block X Pc2' Y (i := 1) (by simp)
    simpa using this

theorem cm_length : (X ++ [a, b] ++ Y).length = X.length + 2 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem cm_length' : (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).length = X.length + 2 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem cm_extCol (k : ℕ) : ExtCol X Pc2 k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k := by unfold ExtCol; simp
theorem cm_extCol' (k : ℕ) : ExtCol X Pc2' k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k := by unfold ExtCol; simp

theorem cm_shift {k : ℕ} (hk : k ≤ X.length ∨ X.length + 2 ≤ k) : shiftIdx X Pc2 Pc2' k = k := by
  unfold shiftIdx
  by_cases h : k ≤ X.length
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    have e1 : ([a, b] : Word).length = 2 := rfl
    have e2 : ([b, a.reindex (a.idx + b.coarity - b.arity)] : Word).length = 2 := rfl
    rw [e1, e2]; omega

theorem cm_extPair {s : ℕ × ℕ} (hs : s.1 ≤ X.length ∨ X.length + 2 ≤ s.1) : extPair X Pc2 Pc2' s = s := by
  obtain ⟨k, p⟩ := s; simp only [extPair, cm_shift X a b hs]

theorem cm_Pne : ([a, b] : Word) ≠ [] := List.cons_ne_nil _ _

theorem cm_extPair_of_ext (c : Slot Wc) (hc : IsExtSlot X Pc2 c.1) : extPair X Pc2 Pc2' c.1 = c.1 := by
  apply cm_extPair
  obtain ⟨⟨k, p⟩, hs⟩ := c
  unfold IsExtSlot at hc
  simp only at hc ⊢
  split_ifs at hc with hp
  · unfold ExtCol at hc; simp at hc; omega
  · unfold ExtCut at hc; simp at hc; omega

variable (hab : b.idx + b.arity ≤ a.idx)
variable (hW : (X ++ [a, b] ++ Y).Closed) (hW' : (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).Closed)

include hab hW in
theorem cm_sameEffect : SameEffect X Pc2 Pc2' :=
  sameEffect_of_replace X Pc2 Y Pc2' hW (fun _ _ h => run_comm_above hab h)

include hab hW in
theorem cm_bits_ext (p : ℕ) :
    bit Wc X.length p = bit Wc' X.length p ∧ bit Wc (X.length + 2) p = bit Wc' (X.length + 2) p := by
  have hE := cm_sameEffect X Y a b hab hW
  have h0 := bit_ext X Pc2 Y Pc2' (cm_Pne a b) hE (k := X.length) (Or.inl le_rfl) p
  have h2 := bit_ext X Pc2 Y Pc2' (cm_Pne a b) hE (k := X.length + 2) (Or.inr (by simp)) p
  rw [cm_shift X a b (Or.inl le_rfl)] at h0
  rw [cm_shift X a b (Or.inr le_rfl)] at h2
  exact ⟨h0, h2⟩

include hW' in
theorem cm_b_pos : 1 ≤ b.idx := by
  have := letter_idx_pos hW' (k := X.length) (by rw [cm_length']; omega)
  rwa [(cm_letters' X Y a b).1] at this

include hW in
theorem cm_a_pos : 1 ≤ a.idx := by
  have := letter_idx_pos hW (k := X.length) (by rw [cm_length]; omega)
  rwa [(cm_letters X Y a b).1] at this

include hW in
/-- the interior `σ` slots of `W` are the `σ` slots of the two block columns -/
theorem cm_int_iff (u : Slot Wc) :
    IntSlot X Pc2 Y u ↔ IsσSlot u ∧ (colOf u = X.length ∨ colOf u = X.length + 1) := by
  have hlt := colOf_lt hW u
  rw [cm_length] at hlt
  constructor
  · rintro ⟨hu, hext⟩
    rw [cm_extCol] at hext
    exact ⟨hu, by omega⟩
  · rintro ⟨hu, hc⟩
    exact ⟨hu, by rw [cm_extCol]; omega⟩

include hW' in
theorem cm_int_iff' (u : Slot Wc') :
    IntSlot X Pc2' Y u ↔ IsσSlot u ∧ (colOf u = X.length ∨ colOf u = X.length + 1) := by
  have hlt := colOf_lt hW' u
  rw [cm_length'] at hlt
  constructor
  · rintro ⟨hu, hext⟩
    rw [cm_extCol'] at hext
    exact ⟨hu, by omega⟩
  · rintro ⟨hu, hc⟩
    exact ⟨hu, by rw [cm_extCol']; omega⟩

theorem cm_k₀ : X.length < (X ++ [a, b] ++ Y).length := by rw [cm_length]; omega
theorem cm_k₁ : X.length + 1 < (X ++ [a, b] ++ Y).length := by rw [cm_length]; omega
theorem cm_k₀' : X.length < (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).length := by rw [cm_length']; omega
theorem cm_k₁' : X.length + 1 < (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).length := by rw [cm_length']; omega

/-- the crossing-ness of the letters corresponds across the exchange -/
theorem cm_cross_k₀ {u : Slot Wc} (hu : IsσSlot u) (hc : colOf u = X.length) :
    (letterAt Wc' (X.length + 1)).isCrossing = true := by
  have := hu.1
  rw [hc, (cm_letters X Y a b).1] at this
  rw [(cm_letters' X Y a b).2, isCrossing_reindex]; exact this

theorem cm_cross_k₁ {u : Slot Wc} (hu : IsσSlot u) (hc : colOf u = X.length + 1) :
    (letterAt Wc' X.length).isCrossing = true := by
  have := hu.1
  rw [hc, (cm_letters X Y a b).2] at this
  rw [(cm_letters' X Y a b).1]; exact this

theorem cm_cross_k₀' {u : Slot Wc'} (hu : IsσSlot u) (hc : colOf u = X.length) :
    (letterAt Wc (X.length + 1)).isCrossing = true := by
  have := hu.1
  rw [hc, (cm_letters' X Y a b).1] at this
  rw [(cm_letters X Y a b).2]; exact this

theorem cm_cross_k₁' {u : Slot Wc'} (hu : IsσSlot u) (hc : colOf u = X.length + 1) :
    (letterAt Wc X.length).isCrossing = true := by
  have := hu.1
  rw [hc, (cm_letters' X Y a b).2, isCrossing_reindex] at this
  rw [(cm_letters X Y a b).1]; exact this

include hW hW' in
/-- the forward interior correspondence of the commutation -/
noncomputable def cmφI_to (u : {u // IntSlot X Pc2 Y u}) : {u' // IntSlot X Pc2' Y u'} :=
  if hc : colOf u.1 = X.length then
    if isDesc u.1 then
      ⟨σSlotA hW' (cm_k₁' X Y a b) (letterAt_σ_of_isCrossing (cm_cross_k₀ X Y a b u.2.1 hc)),
        (cm_int_iff' X Y a b hW' _).2 ⟨isσSlot_σSlotA hW' _ _, Or.inr (σSlotA_spec hW' _ _).1⟩⟩
    else
      ⟨σSlotB hW' (cm_k₁' X Y a b) (letterAt_σ_of_isCrossing (cm_cross_k₀ X Y a b u.2.1 hc)),
        (cm_int_iff' X Y a b hW' _).2 ⟨isσSlot_σSlotB hW' _ _, Or.inr (σSlotB_spec hW' _ _).1⟩⟩
  else
    have hc1 : colOf u.1 = X.length + 1 := ((cm_int_iff X Y a b hW u.1).1 u.2).2.resolve_left hc
    if isDesc u.1 then
      ⟨σSlotA hW' (cm_k₀' X Y a b) (letterAt_σ_of_isCrossing (cm_cross_k₁ X Y a b u.2.1 hc1)),
        (cm_int_iff' X Y a b hW' _).2 ⟨isσSlot_σSlotA hW' _ _, Or.inl (σSlotA_spec hW' _ _).1⟩⟩
    else
      ⟨σSlotB hW' (cm_k₀' X Y a b) (letterAt_σ_of_isCrossing (cm_cross_k₁ X Y a b u.2.1 hc1)),
        (cm_int_iff' X Y a b hW' _).2 ⟨isσSlot_σSlotB hW' _ _, Or.inl (σSlotB_spec hW' _ _).1⟩⟩

include hW hW' in
/-- the inverse interior correspondence of the commutation -/
noncomputable def cmφI_inv (u : {u' // IntSlot X Pc2' Y u'}) : {u // IntSlot X Pc2 Y u} :=
  if hc : colOf u.1 = X.length then
    if isDesc u.1 then
      ⟨σSlotA hW (cm_k₁ X Y a b) (letterAt_σ_of_isCrossing (cm_cross_k₀' X Y a b u.2.1 hc)),
        (cm_int_iff X Y a b hW _).2 ⟨isσSlot_σSlotA hW _ _, Or.inr (σSlotA_spec hW _ _).1⟩⟩
    else
      ⟨σSlotB hW (cm_k₁ X Y a b) (letterAt_σ_of_isCrossing (cm_cross_k₀' X Y a b u.2.1 hc)),
        (cm_int_iff X Y a b hW _).2 ⟨isσSlot_σSlotB hW _ _, Or.inr (σSlotB_spec hW _ _).1⟩⟩
  else
    have hc1 : colOf u.1 = X.length + 1 := ((cm_int_iff' X Y a b hW' u.1).1 u.2).2.resolve_left hc
    if isDesc u.1 then
      ⟨σSlotA hW (cm_k₀ X Y a b) (letterAt_σ_of_isCrossing (cm_cross_k₁' X Y a b u.2.1 hc1)),
        (cm_int_iff X Y a b hW _).2 ⟨isσSlot_σSlotA hW _ _, Or.inl (σSlotA_spec hW _ _).1⟩⟩
    else
      ⟨σSlotB hW (cm_k₀ X Y a b) (letterAt_σ_of_isCrossing (cm_cross_k₁' X Y a b u.2.1 hc1)),
        (cm_int_iff X Y a b hW _).2 ⟨isσSlot_σSlotB hW _ _, Or.inl (σSlotB_spec hW _ _).1⟩⟩

include hW hW' in
theorem cmφI_to_val₀ (u : {u // IntSlot X Pc2 Y u}) (hc : colOf u.1 = X.length)
    (hcr : (letterAt Wc' (X.length + 1)).isCrossing = true) :
    (cmφI_to X Y a b hW hW' u).1 =
      if isDesc u.1 then σSlotA hW' (cm_k₁' X Y a b) (letterAt_σ_of_isCrossing hcr)
      else σSlotB hW' (cm_k₁' X Y a b) (letterAt_σ_of_isCrossing hcr) := by
  unfold cmφI_to
  rw [dite_eq_left hc]
  split_ifs <;> rfl

include hW hW' in
theorem cmφI_to_val₁ (u : {u // IntSlot X Pc2 Y u}) (hc : colOf u.1 = X.length + 1)
    (hcr : (letterAt Wc' X.length).isCrossing = true) :
    (cmφI_to X Y a b hW hW' u).1 =
      if isDesc u.1 then σSlotA hW' (cm_k₀' X Y a b) (letterAt_σ_of_isCrossing hcr)
      else σSlotB hW' (cm_k₀' X Y a b) (letterAt_σ_of_isCrossing hcr) := by
  unfold cmφI_to
  rw [dite_eq_right (by omega)]
  split_ifs <;> rfl

include hW hW' in
theorem cmφI_inv_val₀ (u : {u' // IntSlot X Pc2' Y u'}) (hc : colOf u.1 = X.length)
    (hcr : (letterAt Wc (X.length + 1)).isCrossing = true) :
    (cmφI_inv X Y a b hW hW' u).1 =
      if isDesc u.1 then σSlotA hW (cm_k₁ X Y a b) (letterAt_σ_of_isCrossing hcr)
      else σSlotB hW (cm_k₁ X Y a b) (letterAt_σ_of_isCrossing hcr) := by
  unfold cmφI_inv
  rw [dite_eq_left hc]
  split_ifs <;> rfl

include hW hW' in
theorem cmφI_inv_val₁ (u : {u' // IntSlot X Pc2' Y u'}) (hc : colOf u.1 = X.length + 1)
    (hcr : (letterAt Wc X.length).isCrossing = true) :
    (cmφI_inv X Y a b hW hW' u).1 =
      if isDesc u.1 then σSlotA hW (cm_k₀ X Y a b) (letterAt_σ_of_isCrossing hcr)
      else σSlotB hW (cm_k₀ X Y a b) (letterAt_σ_of_isCrossing hcr) := by
  unfold cmφI_inv
  rw [dite_eq_right (by omega)]
  split_ifs <;> rfl

include hW hW' in
/-- column and over bit of the forward correspondence -/
theorem cmφI_to_spec (u : {u // IntSlot X Pc2 Y u}) :
    isDesc (cmφI_to X Y a b hW hW' u).1 = isDesc u.1 ∧
    (colOf u.1 = X.length → colOf (cmφI_to X Y a b hW hW' u).1 = X.length + 1) ∧
    (colOf u.1 = X.length + 1 → colOf (cmφI_to X Y a b hW hW' u).1 = X.length) := by
  obtain ⟨hσ, hc⟩ := (cm_int_iff X Y a b hW u.1).1 u.2
  rcases hc with hc | hc
  · rw [cmφI_to_val₀ X Y a b hW hW' u hc (cm_cross_k₀ X Y a b hσ hc)]
    refine ⟨?_, fun _ => ?_, fun h => absurd (hc.symm.trans h) (by omega)⟩
    · split_ifs with hd
      · rw [isDesc_σSlotA, hd]
      · rw [isDesc_σSlotB, eq_comm, Bool.eq_false_iff]; exact hd
    · split_ifs
      · exact (σSlotA_spec hW' _ _).1
      · exact (σSlotB_spec hW' _ _).1
  · rw [cmφI_to_val₁ X Y a b hW hW' u hc (cm_cross_k₁ X Y a b hσ hc)]
    refine ⟨?_, fun h => absurd (hc.symm.trans h) (by omega), fun _ => ?_⟩
    · split_ifs with hd
      · rw [isDesc_σSlotA, hd]
      · rw [isDesc_σSlotB, eq_comm, Bool.eq_false_iff]; exact hd
    · split_ifs
      · exact (σSlotA_spec hW' _ _).1
      · exact (σSlotB_spec hW' _ _).1

include hW hW' in
theorem cmφI_inv_spec (u : {u' // IntSlot X Pc2' Y u'}) :
    isDesc (cmφI_inv X Y a b hW hW' u).1 = isDesc u.1 ∧
    (colOf u.1 = X.length → colOf (cmφI_inv X Y a b hW hW' u).1 = X.length + 1) ∧
    (colOf u.1 = X.length + 1 → colOf (cmφI_inv X Y a b hW hW' u).1 = X.length) := by
  obtain ⟨hσ, hc⟩ := (cm_int_iff' X Y a b hW' u.1).1 u.2
  rcases hc with hc | hc
  · rw [cmφI_inv_val₀ X Y a b hW hW' u hc (cm_cross_k₀' X Y a b hσ hc)]
    refine ⟨?_, fun _ => ?_, fun h => absurd (hc.symm.trans h) (by omega)⟩
    · split_ifs with hd
      · rw [isDesc_σSlotA, hd]
      · rw [isDesc_σSlotB, eq_comm, Bool.eq_false_iff]; exact hd
    · split_ifs
      · exact (σSlotA_spec hW _ _).1
      · exact (σSlotB_spec hW _ _).1
  · rw [cmφI_inv_val₁ X Y a b hW hW' u hc (cm_cross_k₁' X Y a b hσ hc)]
    refine ⟨?_, fun h => absurd (hc.symm.trans h) (by omega), fun _ => ?_⟩
    · split_ifs with hd
      · rw [isDesc_σSlotA, hd]
      · rw [isDesc_σSlotB, eq_comm, Bool.eq_false_iff]; exact hd
    · split_ifs
      · exact (σSlotA_spec hW _ _).1
      · exact (σSlotB_spec hW _ _).1

include hW hW' in
/-- THE INTERIOR SLOT CORRESPONDENCE of the commutation: the `σ` slots of `a` (column `|X|` of `W`, column
`|X|+1` of `W'`) and of `b` (column `|X|+1` of `W`, column `|X|` of `W'`), over bit preserved. -/
noncomputable def cmφI : {u // IntSlot X Pc2 Y u} ≃ {u' // IntSlot X Pc2' Y u'} where
  toFun := cmφI_to X Y a b hW hW'
  invFun := cmφI_inv X Y a b hW hW'
  left_inv u := by
    apply Subtype.ext
    obtain ⟨hσ, hc⟩ := (cm_int_iff X Y a b hW u.1).1 u.2
    obtain ⟨hd, hc0, hc1⟩ := cmφI_to_spec X Y a b hW hW' u
    obtain ⟨hd', hc0', hc1'⟩ := cmφI_inv_spec X Y a b hW hW' (cmφI_to X Y a b hW hW' u)
    refine σslot_ext hW (cmφI_inv X Y a b hW hW' _).2.1 hσ ?_ (hd'.trans hd)
    rcases hc with hc | hc
    · rw [hc1' (hc0 hc), hc]
    · rw [hc0' (hc1 hc), hc]
  right_inv u := by
    apply Subtype.ext
    obtain ⟨hσ, hc⟩ := (cm_int_iff' X Y a b hW' u.1).1 u.2
    obtain ⟨hd, hc0, hc1⟩ := cmφI_inv_spec X Y a b hW hW' u
    obtain ⟨hd', hc0', hc1'⟩ := cmφI_to_spec X Y a b hW hW' (cmφI_inv X Y a b hW hW' u)
    refine σslot_ext hW' (cmφI_to X Y a b hW hW' _).2.1 hσ ?_ (hd'.trans hd)
    rcases hc with hc | hc
    · rw [hc1' (hc0 hc), hc]
    · rw [hc0' (hc1 hc), hc]

include hW hW' in
theorem cmφI_val (u : {u // IntSlot X Pc2 Y u}) : (cmφI X Y a b hW hW' u).1 = (cmφI_to X Y a b hW hW' u).1 := rfl

end Comm

section WindowSteps

variable {V : Word} (hV : V.Closed)
include hV

omit hV in
/-- a position above a letter is never one of a crossing's positions -/
theorem notσ_of_lt {ℓ : Letter} {k p : ℕ} (hℓ : letterAt V k = ℓ) (hp : p < ℓ.idx) :
    ∀ j, letterAt V k = .σ j → p ≠ j ∧ p ≠ j + 1 := by
  intro j hj
  rw [hℓ] at hj
  subst hj
  simp only [idx] at hp
  omega

omit hV in
theorem notσ_of_ge {ℓ : Letter} {k p : ℕ} (hℓ : letterAt V k = ℓ) (hp : ℓ.idx + ℓ.arity ≤ p) :
    ∀ j, letterAt V k = .σ j → p ≠ j ∧ p ≠ j + 1 := by
  intro j hj
  rw [hℓ] at hj
  subst hj
  simp only [idx, arity] at hp
  omega

/-- the right cusp: the rightward arm enters the vertex, which sends the traversal out along the other arm -/
theorem r_window {k j p : ℕ} (hℓ : letterAt V k = .r j) {s : Slot V} (hs : s.1 = (k, p)) (hp : p = j ∨ p = j + 1)
    (hb : bit V k p = true) :
    (next hV s).1 = (k, 0) ∧ (next hV (next hV s)).1 = (k, if bit V k j then j + 1 else j) ∧
      bit V k (if bit V k j then j + 1 else j) = false := by
  have hk := slot_col_lt hV hs
  have h1 := next_arm_r hV hk hℓ hs hp hb
  refine ⟨h1, next_cusp_r hV hℓ h1, ?_⟩
  obtain ⟨-, hne⟩ := r_bits hV hk hℓ
  cases hbj : bit V k j
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact hbj
  · simp only [↓reduceIte]
    rw [hbj] at hne
    cases h : bit V k (j + 1)
    · rfl
    · exact absurd rfl (h ▸ hne)

/-- the left cusp: the leftward arm enters the vertex, which sends the traversal out along the other arm -/
theorem l_window {k j q : ℕ} {d : Bool} (hℓ : letterAt V k = .l j d) (hk : k < V.length) {s : Slot V}
    (hs : s.1 = (k + 1, q)) (hq : q = j ∨ q = j + 1) (hb : bit V (k + 1) q = false) :
    (next hV s).1 = (k, 0) ∧ (next hV (next hV s)).1 = (k + 1, if d then j else j + 1) ∧
      bit V (k + 1) (if d then j else j + 1) = true := by
  have h1 := next_arm_l hV hk hℓ hs hq hb
  refine ⟨h1, next_cusp_l hV hℓ h1, ?_⟩
  obtain ⟨-, hb1, hb2⟩ := l_bits hV hk hℓ
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hb2]; rfl
  · simp only [↓reduceIte]; exact hb1

/-- the crossing, rightward: the slot is a `σ` slot with the recorded over bit -/
theorem σ_window_right {k j p : ℕ} (hℓ : letterAt V k = .σ j) {s : Slot V} (hs : s.1 = (k, p)) (hp : p = j ∨ p = j + 1)
    (hb : bit V k p = true) :
    (next hV s).1 = (k + 1, if p = j then j + 1 else j) ∧ bit V (k + 1) (if p = j then j + 1 else j) = true ∧
      IsσSlot s ∧ isDesc s = decide (p = j) ∧ colOf s = k := by
  have hk := slot_col_lt hV hs
  obtain ⟨hj1, -, -, b1, b2⟩ := σ_facts hV hk hℓ
  have hp0 : p ≠ 0 := by omega
  have hcol : colOf s = k := block_col_true hs hp0 hb
  rcases hp with hpj | hpj
  · rw [ite_eq_left hpj]
    have hs' : s.1 = (k, j) := hpj ▸ hs
    have hb' : bit V k j = true := hpj ▸ hb
    have hsh : shapeOf s = .pass j (j + 1) := by
      unfold shapeOf; rw [hs']; simp only [show j ≠ 0 by omega, ↓reduceIte, hb', hℓ, posR_σ_idx]
    refine ⟨next_σ_right_idx hV hℓ hs' hb', by rw [b1, hb'], ⟨by rw [hcol, hℓ]; rfl, ?_⟩, ?_, hcol⟩
    · rw [hcol, hℓ, hsh]; simp [idx]
    · unfold isDesc; rw [hsh]; simp [hpj]
  · have hne : p ≠ j := by omega
    rw [ite_eq_right hne]
    have hs' : s.1 = (k, j + 1) := hpj ▸ hs
    have hb' : bit V k (j + 1) = true := hpj ▸ hb
    have hsh : shapeOf s = .pass (j + 1) j := by
      unfold shapeOf; rw [hs']; simp only [show j + 1 ≠ 0 by omega, ↓reduceIte, hb', hℓ, posR_σ_idx_succ]
    refine ⟨next_σ_right_succ hV hℓ hs' hb', by rw [b2, hb'], ⟨by rw [hcol, hℓ]; rfl, ?_⟩, ?_, hcol⟩
    · rw [hcol, hℓ, hsh]; simp [idx]
    · unfold isDesc; rw [hsh]; simp [hne]

/-- the crossing, leftward -/
theorem σ_window_left {k j q : ℕ} (hℓ : letterAt V k = .σ j) {s : Slot V} (hs : s.1 = (k + 1, q)) (hq : q = j ∨ q = j + 1)
    (hb : bit V (k + 1) q = false) :
    (next hV s).1 = (k, if q = j then j + 1 else j) ∧ bit V k (if q = j then j + 1 else j) = false ∧
      IsσSlot s ∧ isDesc s = decide (q = j + 1) ∧ colOf s = k := by
  have hk := lt_length_of_letterAt_σ hℓ
  obtain ⟨hj1, -, -, b1, b2⟩ := σ_facts hV hk hℓ
  have hq0 : q ≠ 0 := by omega
  have hcol : colOf s = k := by rw [block_col_false hs hq0 hb, Nat.add_sub_cancel]
  rcases hq with hqj | hqj
  · rw [ite_eq_left hqj]
    have hs' : s.1 = (k + 1, j) := hqj ▸ hs
    have hb' : bit V (k + 1) j = false := hqj ▸ hb
    have hsh : shapeOf s = .pass (j + 1) j := by
      unfold shapeOf; rw [hs']
      simp only [show j ≠ 0 by omega, ↓reduceIte, hb', Bool.false_eq_true, Nat.add_sub_cancel, hℓ, posL_σ_idx]
    have hne : ¬ (q = j + 1) := by omega
    refine ⟨next_σ_left_idx hV hℓ hs' hb', by rw [← b2, hb'], ⟨by rw [hcol, hℓ]; rfl, ?_⟩, ?_, hcol⟩
    · rw [hcol, hℓ, hsh]; simp [idx]
    · unfold isDesc; rw [hsh]; simp [hne]
  · have hne : q ≠ j := by omega
    rw [ite_eq_right hne]
    have hs' : s.1 = (k + 1, j + 1) := hqj ▸ hs
    have hb' : bit V (k + 1) (j + 1) = false := hqj ▸ hb
    have hsh : shapeOf s = .pass j (j + 1) := by
      unfold shapeOf; rw [hs']
      simp only [show j + 1 ≠ 0 by omega, ↓reduceIte, hb', Bool.false_eq_true, Nat.add_sub_cancel, hℓ, posL_σ_idx_succ]
    refine ⟨next_σ_left_succ hV hℓ hs' hb', by rw [← b1, hb'], ⟨by rw [hcol, hℓ]; rfl, ?_⟩, ?_, hcol⟩
    · rw [hcol, hℓ, hsh]; simp [idx]
    · unfold isDesc; rw [hsh]; simp [hqj]

end WindowSteps

section Hexit2

variable {V : Word} (hV : V.Closed)
include hV

/-- a vertex sends the traversal out along an arm of its cusp -/
theorem exit_vertex {ℓ : Letter} {k : ℕ} (hℓ : letterAt V k = ℓ) {s : Slot V} (hs : s.1 = (k, 0)) :
    ∃ p', p' ≠ 0 ∧ ((next hV s).1 = (k + 1, p') ∧ bit V (k + 1) p' = true ∨
      (next hV s).1 = (k, p') ∧ bit V k p' = false) := by
  have hk := vertex_lt hs
  have hnc := vertex_not_crossing hs
  rw [hℓ] at hnc
  cases ℓ with
  | σ j => exact Bool.noConfusion hnc
  | l j d =>
    obtain ⟨hj, hb1, hb2⟩ := l_bits hV hk hℓ
    refine ⟨_, ?_, Or.inl ⟨next_cusp_l hV hℓ hs, ?_⟩⟩
    · split <;> omega
    · cases d
      · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hb2]; rfl
      · simp only [↓reduceIte]; exact hb1
  | r j =>
    obtain ⟨hj, hne⟩ := r_bits hV hk hℓ
    refine ⟨_, ?_, Or.inr ⟨next_cusp_r hV hℓ hs, ?_⟩⟩
    · split <;> omega
    · cases hbj : bit V k j
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact hbj
      · simp only [↓reduceIte]
        rw [hbj] at hne
        cases h : bit V k (j + 1)
        · rfl
        · exact absurd rfl (h ▸ hne)

/-- a rightward slot at a cut is a `σ` slot or leaves its letter's column within two steps -/
theorem exit_right {ℓ : Letter} {k p : ℕ} (hℓ : letterAt V k = ℓ) {s : Slot V} (hs : s.1 = (k, p)) (hp : p ≠ 0)
    (hb : bit V k p = true) :
    IsσSlot s ∨ ∃ n p', p' ≠ 0 ∧ (((next hV)^[n] s).1 = (k + 1, p') ∧ bit V (k + 1) p' = true ∨
      ((next hV)^[n] s).1 = (k, p') ∧ bit V k p' = false ∧ ℓ.idx ≤ p' ∧ p' < ℓ.idx + ℓ.arity) := by
  have hk := slot_col_lt hV hs
  have hi := letter_idx_pos hV hk
  rw [hℓ] at hi
  rcases lt_or_ge p ℓ.idx with hlt | hge
  · obtain ⟨h1, hb1⟩ := pass_r_lt hV hℓ hs hp hb hlt
    exact Or.inr ⟨1, p, hp, Or.inl ⟨h1, hb1⟩⟩
  rcases lt_or_ge p (ℓ.idx + ℓ.arity) with hlt2 | hge2
  · cases ℓ with
    | σ j =>
      simp only [idx, arity] at hge hlt2
      exact Or.inl (σ_window_right hV hℓ hs (by omega) hb).2.2.1
    | l j d => simp only [arity] at hlt2; omega
    | r j =>
      simp only [idx, arity] at hge hlt2
      obtain ⟨-, h2, hb2⟩ := r_window hV hℓ hs (by omega) hb
      have := (r_bits hV hk hℓ).1
      refine Or.inr ⟨2, _, by split <;> omega, Or.inr ⟨?_, hb2, by simp only [idx]; split <;> omega,
        by simp only [idx, arity]; split <;> omega⟩⟩
      show (next hV (next hV s)).1 = _
      exact h2
  · obtain ⟨h1, hb1⟩ := pass_r_ge hV hℓ hs hp hb hge2
    exact Or.inr ⟨1, _, by omega, Or.inl ⟨h1, hb1⟩⟩

/-- a leftward slot at a cut is a `σ` slot or leaves its letter's column within two steps -/
theorem exit_left {ℓ : Letter} {k q : ℕ} (hℓ : letterAt V k = ℓ) {s : Slot V} (hs : s.1 = (k + 1, q)) (hq : q ≠ 0)
    (hb : bit V (k + 1) q = false) :
    IsσSlot s ∨ ∃ n p', p' ≠ 0 ∧
      (((next hV)^[n] s).1 = (k + 1, p') ∧ bit V (k + 1) p' = true ∧ ℓ.idx ≤ p' ∧ p' < ℓ.idx + ℓ.coarity ∨
      ((next hV)^[n] s).1 = (k, p') ∧ bit V k p' = false) := by
  have hk : k < V.length := by have := slot_col_lt hV hs; omega
  have hi := letter_idx_pos hV hk
  rw [hℓ] at hi
  rcases lt_or_ge q ℓ.idx with hlt | hge
  · obtain ⟨h1, hb1⟩ := pass_l_lt hV hℓ hs hq hb hlt
    exact Or.inr ⟨1, q, hq, Or.inr ⟨h1, hb1⟩⟩
  rcases lt_or_ge q (ℓ.idx + ℓ.coarity) with hlt2 | hge2
  · cases ℓ with
    | σ j =>
      simp only [idx, coarity] at hge hlt2
      exact Or.inl (σ_window_left hV hℓ hs (by omega) hb).2.2.1
    | r j => simp only [coarity] at hlt2; omega
    | l j d =>
      simp only [idx, coarity] at hge hlt2
      obtain ⟨-, h2, hb2⟩ := l_window hV hℓ hk hs (by omega) hb
      have := (l_bits hV hk hℓ).1
      refine Or.inr ⟨2, _, by split <;> omega, Or.inl ⟨?_, hb2, by simp only [idx]; split <;> omega,
        by simp only [idx, coarity]; split <;> omega⟩⟩
      show (next hV (next hV s)).1 = _
      exact h2
  · obtain ⟨h1, hb1⟩ := pass_l_ge hV hℓ hs hq hb hge2
    exact Or.inr ⟨1, _, by omega, Or.inr ⟨h1, hb1⟩⟩

end Hexit2

section CommExit

variable {V : Word} (hV : V.Closed)

/-- the target of the two-letter exits: a slot in column `k-1` or `k+2` -/
def CExit (k : ℕ) (s : Slot V) : Prop :=
  (∃ p', p' ≠ 0 ∧ s.1 = (k + 1 + 1, p') ∧ bit V (k + 1 + 1) p' = true) ∨
  (∃ p', p' ≠ 0 ∧ s.1 = (k, p') ∧ bit V k p' = false)

/-- the traversal from `s` reaches a `σ` slot or leaves the two columns `k`, `k+1` -/
def CDone (k : ℕ) (s : Slot V) : Prop := ∃ n, IsσSlot ((next hV)^[n] s) ∨ CExit k ((next hV)^[n] s)

theorem cdone_of_iter {k : ℕ} {s : Slot V} (n : ℕ) (h : CDone hV k ((next hV)^[n] s)) : CDone hV k s := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m + n, by rw [Function.iterate_add_apply]; exact hm⟩

variable {k : ℕ} {ℓa ℓb : Letter} (hℓa : letterAt V k = ℓa) (hℓb : letterAt V (k + 1) = ℓb)
  (hab : ℓb.idx + ℓb.arity ≤ ℓa.idx ∨ ℓa.idx + ℓa.coarity ≤ ℓb.idx)
include hV hℓa hℓb hab

/-- rightward at the middle cut -/
theorem cexit_D {s : Slot V} {p : ℕ} (hs : s.1 = (k + 1, p)) (hp : p ≠ 0) (hb : bit V (k + 1) p = true) :
    CDone hV k s := by
  have hk1 := slot_col_lt hV hs
  have hi := letter_idx_pos hV (by omega : k < V.length)
  rw [hℓa] at hi
  rcases exit_right hV hℓb hs hp hb with hσ | ⟨n, p', hp', ⟨h1, hb1⟩ | ⟨h1, hb1, hw1, hw2⟩⟩
  · exact ⟨0, Or.inl hσ⟩
  · exact ⟨n, Or.inr (Or.inl ⟨p', hp', h1, hb1⟩)⟩
  · rcases hab with hab | hab
    · obtain ⟨h2, hb2⟩ := pass_l_lt hV hℓa h1 hp' hb1 (by omega)
      exact ⟨n + 1, Or.inr (Or.inr ⟨p', hp', by rw [Function.iterate_succ_apply']; exact h2, hb2⟩)⟩
    · obtain ⟨h2, hb2⟩ := pass_l_ge hV hℓa h1 hp' hb1 (by omega)
      exact ⟨n + 1, Or.inr (Or.inr ⟨_, by omega, by rw [Function.iterate_succ_apply']; exact h2, hb2⟩)⟩

/-- leftward at the middle cut -/
theorem cexit_B {s : Slot V} {q : ℕ} (hs : s.1 = (k + 1, q)) (hq : q ≠ 0) (hb : bit V (k + 1) q = false) :
    CDone hV k s := by
  have hk1 := slot_col_lt hV hs
  have hi := letter_idx_pos hV hk1
  rw [hℓb] at hi
  rcases exit_left hV hℓa hs hq hb with hσ | ⟨n, p', hp', ⟨h1, hb1, hw1, hw2⟩ | ⟨h1, hb1⟩⟩
  · exact ⟨0, Or.inl hσ⟩
  · rcases hab with hab | hab
    · obtain ⟨h2, hb2⟩ := pass_r_ge hV hℓb h1 hp' hb1 (by omega)
      exact ⟨n + 1, Or.inr (Or.inl ⟨_, by omega, by rw [Function.iterate_succ_apply']; exact h2, hb2⟩)⟩
    · obtain ⟨h2, hb2⟩ := pass_r_lt hV hℓb h1 hp' hb1 (by omega)
      exact ⟨n + 1, Or.inr (Or.inl ⟨p', hp', by rw [Function.iterate_succ_apply']; exact h2, hb2⟩)⟩
  · exact ⟨n, Or.inr (Or.inr ⟨p', hp', h1, hb1⟩)⟩

/-- rightward at the first cut -/
theorem cexit_A {s : Slot V} {p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) (hb : bit V k p = true) :
    CDone hV k s := by
  rcases exit_right hV hℓa hs hp hb with hσ | ⟨n, p', hp', ⟨h1, hb1⟩ | ⟨h1, hb1, -, -⟩⟩
  · exact ⟨0, Or.inl hσ⟩
  · exact cdone_of_iter hV n (cexit_D hV hℓa hℓb hab h1 hp' hb1)
  · exact ⟨n, Or.inr (Or.inr ⟨p', hp', h1, hb1⟩)⟩

/-- the first vertex -/
theorem cexit_C {s : Slot V} (hs : s.1 = (k, 0)) : CDone hV k s := by
  obtain ⟨p', hp', ⟨h1, hb1⟩ | ⟨h1, hb1⟩⟩ := exit_vertex hV hℓa hs
  · exact cdone_of_iter hV 1 (cexit_D hV hℓa hℓb hab (by rw [Function.iterate_one]; exact h1) hp' hb1)
  · exact ⟨1, Or.inr (Or.inr ⟨p', hp', by rw [Function.iterate_one]; exact h1, hb1⟩)⟩

/-- leftward at the last cut -/
theorem cexit_E {s : Slot V} {q : ℕ} (hs : s.1 = (k + 1 + 1, q)) (hq : q ≠ 0) (hb : bit V (k + 1 + 1) q = false) :
    CDone hV k s := by
  rcases exit_left hV hℓb hs hq hb with hσ | ⟨n, p', hp', ⟨h1, hb1, -, -⟩ | ⟨h1, hb1⟩⟩
  · exact ⟨0, Or.inl hσ⟩
  · exact ⟨n, Or.inr (Or.inl ⟨p', hp', h1, hb1⟩)⟩
  · exact cdone_of_iter hV n (cexit_B hV hℓa hℓb hab h1 hp' hb1)

/-- the second vertex -/
theorem cexit_F {s : Slot V} (hs : s.1 = (k + 1, 0)) : CDone hV k s := by
  obtain ⟨p', hp', ⟨h1, hb1⟩ | ⟨h1, hb1⟩⟩ := exit_vertex hV hℓb hs
  · exact ⟨1, Or.inr (Or.inl ⟨p', hp', by rw [Function.iterate_one]; exact h1, hb1⟩)⟩
  · exact cdone_of_iter hV 1 (cexit_B hV hℓa hℓb hab (by rw [Function.iterate_one]; exact h1) hp' hb1)

end CommExit

section HexitBlock

variable {X P Y : Word} (hV : (X ++ P ++ Y).Closed)
include hV

/-- every slot of a word with a two-letter block of non-interacting letters reaches an active slot -/
theorem hexit_of_comm (hext : ∀ k, ExtCol X P k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k) {ℓa ℓb : Letter}
    (hℓa : letterAt (X ++ P ++ Y) X.length = ℓa) (hℓb : letterAt (X ++ P ++ Y) (X.length + 1) = ℓb)
    (hab : ℓb.idx + ℓb.arity ≤ ℓa.idx ∨ ℓa.idx + ℓa.coarity ≤ ℓb.idx) (u : Slot (X ++ P ++ Y)) :
    ∃ n, ActE X P Y ((next hV)^[n] u) := by
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  by_cases he : ExtCol X P (colOf u)
  · exact ⟨0, Or.inl he⟩
  have hcol : colOf u = X.length ∨ colOf u = X.length + 1 := by
    have := he
    rw [hext] at this
    omega
  suffices h : CDone hV X.length u by
    obtain ⟨n, hσ | ⟨p', hp', h1, hb1⟩ | ⟨p', hp', h1, hb1⟩⟩ := h
    · exact ⟨n, isσSlot_actE X P Y hσ⟩
    · refine ⟨n, Or.inl ?_⟩
      show ExtCol X P (colOf _)
      rw [block_col_true h1 hp' hb1, hext]; omega
    · refine ⟨n, Or.inl ?_⟩
      show ExtCol X P (colOf _)
      have := (cutSlot_facts hV h1 hp').2.2.1
      rw [block_col_false h1 hp' hb1, hext]; omega
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu] at hcol
    rcases hcol with rfl | rfl
    · exact cexit_C hV hℓa hℓb hab hu
    · exact cexit_F hV hℓa hℓb hab hu
  have hp : p ≠ 0 := by omega
  cases hb : bit (X ++ P ++ Y) k p
  · rw [block_col_false hu hp hb] at hcol
    have hk0 := (cutSlot_facts hV hu hp).2.2.1
    rcases hcol with h | h
    · have hk : k = X.length + 1 := by omega
      subst hk
      exact cexit_B hV hℓa hℓb hab hu hp hb
    · have hk : k = X.length + 1 + 1 := by omega
      subst hk
      exact cexit_E hV hℓa hℓb hab hu hp hb
  · rw [block_col_true hu hp hb] at hcol
    rcases hcol with rfl | rfl
    · exact cexit_A hV hℓa hℓb hab hu hp hb
    · exact cexit_D hV hℓa hℓb hab hu hp hb

end HexitBlock

section CommPassage

variable (X Y : Word) (a b : Letter)

local notation "Wc" => X ++ [a, b] ++ Y
local notation "Pc2" => [a, b]
local notation "Wc'" => X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y
local notation "Pc2'" => [b, a.reindex (a.idx + b.coarity - b.arity)]

variable (hab : b.idx + b.arity ≤ a.idx)
variable (hW : (X ++ [a, b] ++ Y).Closed) (hW' : (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).Closed)

omit hW in
theorem notσ_of_ge' {V : Word} {ℓ : Letter} {k p : ℕ} (hℓ : letterAt V k = ℓ) (hp : ℓ.idx + ℓ.coarity ≤ p) :
    ∀ j, letterAt V k = .σ j → p ≠ j ∧ p ≠ j + 1 := by
  intro j hj
  rw [hℓ] at hj
  subst hj
  simp only [idx, coarity] at hp
  omega

/-- the coordinates of the two `σ` slots of a crossing column -/
theorem σSlotA_val {W : Word} (hW : W.Closed) {k j : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ j) :
    (σSlotA hW hk hℓ).1 = if bit W k j then (k, j) else (k + 1, j + 1) := by
  unfold σSlotA; split_ifs <;> rfl

theorem σSlotB_val {W : Word} (hW : W.Closed) {k j : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ j) :
    (σSlotB hW hk hℓ).1 = if bit W k (j + 1) then (k, j + 1) else (k + 1, j) := by
  unfold σSlotB; split_ifs <;> rfl

include hW hW' in
/-- twins correspond -/
theorem cmφI_twin (u : {u // IntSlot X Pc2 Y u}) :
    (cmφI X Y a b hW hW' ⟨σtwin hW u.1, ⟨isσSlot_σtwin hW u.2.1, by rw [colOf_σtwin hW u.2.1]; exact u.2.2⟩⟩).1 =
      σtwin hW' (cmφI X Y a b hW hW' u).1 := by
  rw [cmφI_val, cmφI_val]
  obtain ⟨hσ, hc⟩ := (cm_int_iff X Y a b hW u.1).1 u.2
  obtain ⟨hd, hc0, hc1⟩ := cmφI_to_spec X Y a b hW hW' u
  obtain ⟨hd', hc0', hc1'⟩ := cmφI_to_spec X Y a b hW hW' ⟨σtwin hW u.1, _⟩
  have hσ1 : IsσSlot (cmφI_to X Y a b hW hW' u).1 := (cmφI_to X Y a b hW hW' u).2.1
  refine σslot_ext hW' (cmφI_to X Y a b hW hW' _).2.1 (isσSlot_σtwin hW' hσ1) ?_ ?_
  · rcases hc with hc | hc
    · exact (hc0' (by show colOf (σtwin hW u.1) = _; rw [colOf_σtwin hW hσ]; exact hc)).trans
        ((hc0 hc).symm.trans (colOf_σtwin hW' hσ1).symm)
    · exact (hc1' (by show colOf (σtwin hW u.1) = _; rw [colOf_σtwin hW hσ]; exact hc)).trans
        ((hc1 hc).symm.trans (colOf_σtwin hW' hσ1).symm)
  · refine hd'.trans ?_
    show isDesc (σtwin hW u.1) = isDesc (σtwin hW' (cmφI_to X Y a b hW hW' u).1)
    rw [isDesc_σtwin hW hσ, isDesc_σtwin hW' hσ1, hd]

theorem arity_of_crossing {ℓ : Letter} (h : ℓ.isCrossing = true) : ℓ.arity = 2 := by
  cases ℓ with
  | l _ _ => cases h
  | r _ => cases h
  | σ _ => rfl

theorem coarity_of_crossing {ℓ : Letter} (h : ℓ.isCrossing = true) : ℓ.coarity = 2 := by
  cases ℓ with
  | l _ _ => cases h
  | r _ => cases h
  | σ _ => rfl

theorem eq_σ_of_crossing {ℓ : Letter} (h : ℓ.isCrossing = true) : ℓ = .σ ℓ.idx := by
  cases ℓ with
  | l _ _ => cases h
  | r _ => cases h
  | σ _ => rfl

include hab hW hW' in
/-- signs correspond -/
theorem cmφI_sgn (u : {u // IntSlot X Pc2 Y u}) : σsgn (cmφI X Y a b hW hW' u).1 = σsgn u.1 := by
  rw [cmφI_val]
  obtain ⟨hσ, hc⟩ := (cm_int_iff X Y a b hW u.1).1 u.2
  obtain ⟨-, hc0, hc1⟩ := cmφI_to_spec X Y a b hW hW' u
  obtain ⟨hℓa, hℓb⟩ := cm_letters X Y a b
  obtain ⟨hℓb', hℓa'⟩ := cm_letters' X Y a b
  have hk₀ := cm_k₀ X Y a b
  have hk₀' := cm_k₀' X Y a b
  have hb1 := cm_b_pos X Y a b hW'
  have tE := cm_bits_ext X Y a b hab hW
  unfold σsgn σsgnCol
  rcases hc with hc | hc
  · rw [hc0 hc, hc, hℓa', hℓa, idx_reindex]
    have t1 : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity) = bit Wc' X.length a.idx := by
      have := bit_succ_of_ge hW' hk₀' (p := a.idx) (by rw [hℓb']; exact hab)
      rwa [hℓb'] at this
    have t2 : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity + 1) = bit Wc' X.length (a.idx + 1) := by
      have := bit_succ_of_ge hW' hk₀' (p := a.idx + 1) (by rw [hℓb']; omega)
      rw [hℓb'] at this
      rw [show a.idx + b.coarity - b.arity + 1 = a.idx + 1 + b.coarity - b.arity by omega]
      exact this
    rw [t1, t2, ← (tE a.idx).1, ← (tE (a.idx + 1)).1]
  · rw [hc1 hc, hc, hℓb', hℓb]
    have hcr : b.isCrossing = true := by have := hσ.1; rwa [hc, hℓb] at this
    have hb2 : b.arity = 2 := arity_of_crossing hcr
    have t1 : bit Wc (X.length + 1) b.idx = bit Wc X.length b.idx :=
      bit_succ_of_lt hW hk₀ (p := b.idx) hb1 (by rw [hℓa]; omega)
    have t2 : bit Wc (X.length + 1) (b.idx + 1) = bit Wc X.length (b.idx + 1) :=
      bit_succ_of_lt hW hk₀ (p := b.idx + 1) (by omega) (by rw [hℓa]; omega)
    rw [t1, t2, (tE b.idx).1, (tE (b.idx + 1)).1]

end CommPassage

section CommEntries

variable (X Y : Word) (a b : Letter)

local notation "Wc" => X ++ [a, b] ++ Y
local notation "Pc2" => [a, b]
local notation "Wc'" => X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y
local notation "Pc2'" => [b, a.reindex (a.idx + b.coarity - b.arity)]

variable (hab : b.idx + b.arity ≤ a.idx)
variable (hW : (X ++ [a, b] ++ Y).Closed) (hW' : (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).Closed)

local notation "φc" => φA X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) hW (cmφI X Y a b hW hW')

include hab hW hW' in
theorem cm_φext (c : Slot Wc) (hc : ExtCol X Pc2 (colOf c)) : (φc ⟨c, Or.inl hc⟩).1.1 = c.1 :=
  (φA_val_ext' X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) hW _ ⟨c, Or.inl hc⟩ hc).trans
    (cm_extPair_of_ext X Y a b c (isExtSlot_of_extCol X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) c hc))

include hab hW hW' in
theorem cm_φint (c : Slot Wc) (hc : ActE X Pc2 Y c) (hint : IntSlot X Pc2 Y c) :
    (φc ⟨c, hc⟩).1 = (cmφI_to X Y a b hW hW' ⟨c, hint⟩).1 :=
  φA_val_int X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) hW _ ⟨c, hc⟩ hint.2

/-- the kinds with a nonempty read window / write window -/
theorem kind_of_arity {ℓ : Letter} (h : ℓ.arity ≠ 0) : (∃ j, ℓ = .r j) ∨ (∃ j, ℓ = .σ j) := by
  cases ℓ with
  | l _ _ => exact absurd rfl h
  | r j => exact Or.inl ⟨j, rfl⟩
  | σ j => exact Or.inr ⟨j, rfl⟩

theorem kind_of_coarity {ℓ : Letter} (h : ℓ.coarity ≠ 0) : (∃ j d, ℓ = .l j d) ∨ (∃ j, ℓ = .σ j) := by
  cases ℓ with
  | l j d => exact Or.inl ⟨j, d, rfl⟩
  | r _ => exact absurd rfl h
  | σ j => exact Or.inr ⟨j, rfl⟩

include hab hW hW' in
/-- the entries of the commutation block from the left -/
theorem cm_left (e : Slot Wc) (hext : IsExtSlot X Pc2 e.1) {p : ℕ} (he : e.1 = (X.length, p)) (hp : p ≠ 0)
    (hbit : bit Wc X.length p = true) :
    ∃ (m : ℕ) (c : Slot Wc) (hc : ActE X Pc2 Y c), (next hW)^[m] e = c ∧
      (∀ i < m, ¬ ActE X Pc2 Y ((next hW)^[i] e)) ∧
      ∃ (m' : ℕ) (b' : Slot Wc'), b'.1 = extPair X Pc2 Pc2' e.1 ∧
        (next hW')^[m'] b' = (φc ⟨c, hc⟩).1 ∧ ∀ i < m', ¬ ActE X Pc2' Y ((next hW')^[i] b') := by
  have hE := cm_sameEffect X Y a b hab hW
  have hPne := cm_Pne a b
  obtain ⟨hℓa, hℓb⟩ := cm_letters X Y a b
  obtain ⟨hℓb', hℓa'⟩ := cm_letters' X Y a b
  have hk₀ := cm_k₀ X Y a b
  have hk₁ := cm_k₁ X Y a b
  have hk₀' := cm_k₀' X Y a b
  have hk₁' := cm_k₁' X Y a b
  have ha1 := cm_a_pos X Y a b hW
  have hb1 := cm_b_pos X Y a b hW'
  have tE := cm_bits_ext X Y a b hab hW
  have hidx' : (a.reindex (a.idx + b.coarity - b.arity)).idx = a.idx + b.coarity - b.arity := idx_reindex a _
  have har' := arity_reindex a (a.idx + b.coarity - b.arity)
  have hco' := coarity_reindex a (a.idx + b.coarity - b.arity)
  let e' : Slot Wc' := ⟨extPair X Pc2 Pc2' e.1, isSlot_ext X Pc2 Y Pc2' hPne hE e.2 hext⟩
  have he' : e'.1 = (X.length, p) := by
    show extPair X Pc2 Pc2' e.1 = _
    rw [he, cm_extPair X a b (Or.inl le_rfl)]
  have hbit' : bit Wc' X.length p = true := by rw [← (tE p).1]; exact hbit
  have φext := cm_φext X Y a b hab hW hW'
  have φint := cm_φint X Y a b hab hW hW'
  rcases lt_or_ge p b.idx with R1 | hpb
  · -- above both gadgets
    obtain ⟨h1, hb1e⟩ := pass_r_lt hW hℓa he hp hbit (by omega)
    obtain ⟨h2, hb2e⟩ := pass_r_lt hW hℓb h1 hp hb1e R1
    obtain ⟨h1', hb1'⟩ := pass_r_lt hW' hℓb' he' hp hbit' R1
    obtain ⟨h2', hb2'⟩ := pass_r_lt hW' hℓa' h1' hp hb1' (by rw [hidx']; omega)
    have hcE : ExtCol X Pc2 (colOf (next hW (next hW e))) := by rw [block_col_true h2 hp hb2e, cm_extCol]; omega
    obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y)
      (not_actE_of X Pc2 Y (by rw [block_col_true he hp hbit, cm_extCol]; omega) (not_σ_right he hp hbit (notσ_of_lt hℓa (by omega))))
      (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_true h1 hp hb1e, cm_extCol]; omega)
        (not_σ_right h1 hp hb1e (notσ_of_lt hℓb R1))) (apassage_end hW _))
    obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y)
      (not_actE_of X Pc2' Y (by rw [block_col_true he' hp hbit', cm_extCol']; omega) (not_σ_right he' hp hbit' (notσ_of_lt hℓb' R1)))
      (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_true h1' hp hb1', cm_extCol']; omega)
        (not_σ_right h1' hp hb1' (notσ_of_lt hℓa' (by rw [hidx']; omega)))) (apassage_end hW' _))
    refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
    rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
  rcases lt_or_ge p (b.idx + b.arity) with R2 | hpb2
  · -- the read window of `b`
    obtain ⟨h1, hb1e⟩ := pass_r_lt hW hℓa he hp hbit (by omega)
    have nE0 : ¬ ActE X Pc2 Y e :=
      not_actE_of X Pc2 Y (by rw [block_col_true he hp hbit, cm_extCol]; omega) (not_σ_right he hp hbit (notσ_of_lt hℓa (by omega)))
    rcases kind_of_arity (ℓ := b) (by omega) with ⟨j, hbj⟩ | ⟨j, hbj⟩
    · -- `b = r j`
      have hℓb2 : letterAt Wc (X.length + 1) = .r j := hℓb.trans hbj
      have hℓb'2 : letterAt Wc' X.length = .r j := hℓb'.trans hbj
      have hbidx : b.idx = j := by rw [hbj]; rfl
      have hbar : b.arity = 2 := by rw [hbj]; rfl
      obtain ⟨g1, g2, gb⟩ := r_window hW hℓb2 h1 (by omega) hb1e
      have hq0 : (if bit Wc (X.length + 1) j then j + 1 else j) ≠ 0 := by split_ifs <;> omega
      obtain ⟨h4, hb4⟩ := pass_l_lt hW hℓa (k := X.length) g2 hq0 gb (by split_ifs <;> omega)
      obtain ⟨g1', g2', gb'⟩ := r_window hW' hℓb'2 he' (by omega) hbit'
      have hqq : (if bit Wc (X.length + 1) j then j + 1 else j) = (if bit Wc' X.length j then j + 1 else j) := by
        rw [bit_succ_of_lt hW hk₀ (p := j) (by omega) (by rw [hℓa]; omega), (tE j).1]
      have hcE : ExtCol X Pc2 (colOf (next hW (next hW (next hW (next hW e))))) := by
        have := (cutSlot_facts hW h4 hq0).2.2.1
        rw [block_col_false h4 hq0 hb4, cm_extCol]; omega
      obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y) nE0
        (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_true h1 hp hb1e, cm_extCol]; omega)
          (not_σ_right h1 hp hb1e (fun _ hj' => by rw [hℓb2] at hj'; cases hj')))
        (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_vertex g1, cm_extCol]; omega) (not_σ_vertex g1))
        (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_false g2 hq0 gb, Nat.add_sub_cancel, cm_extCol]; omega)
          (not_σ_left g2 hq0 gb (notσ_of_lt hℓa (by split_ifs <;> omega)))) (apassage_end hW _))))
      obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y)
        (not_actE_of X Pc2' Y (by rw [block_col_true he' hp hbit', cm_extCol']; omega)
          (not_σ_right he' hp hbit' (fun _ hj' => by rw [hℓb'2] at hj'; cases hj')))
        (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_vertex g1', cm_extCol']; omega) (not_σ_vertex g1'))
          (apassage_end hW' _))
      refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
      rw [hc']; apply Subtype.ext; rw [φext _ hcE, h4, g2', hqq]
    · -- `b = σ j`: the entry reaches the crossing slot; in `W'` the entry is the crossing slot
      have hℓb2 : letterAt Wc (X.length + 1) = .σ j := hℓb.trans hbj
      have hℓb'2 : letterAt Wc' X.length = .σ j := hℓb'.trans hbj
      have hbidx : b.idx = j := by rw [hbj]; rfl
      have hbar : b.arity = 2 := by rw [hbj]; rfl
      obtain ⟨-, -, hσ1, hd1, hcol1⟩ := σ_window_right hW hℓb2 h1 (by omega) hb1e
      have hint1 : IntSlot X Pc2 Y (next hW e) := ⟨hσ1, by rw [hcol1, cm_extCol]; omega⟩
      obtain ⟨-, -, hσ', hd', hcol'⟩ := σ_window_right hW' hℓb'2 he' (by omega) hbit'
      obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y) nE0 (apassage_end hW _)
      refine ⟨n, _, Or.inr hint1, hc, hmin, 0, e', rfl, ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
      rw [Function.iterate_zero, id]
      refine Eq.trans ?_ (φint _ _ hint1).symm
      obtain ⟨hdφ, -, hcφ⟩ := cmφI_to_spec X Y a b hW hW' ⟨next hW e, hint1⟩
      exact σslot_ext hW' hσ' (cmφI_to X Y a b hW hW' _).2.1 (hcol'.trans (hcφ hcol1).symm)
        (hd'.trans (hd1.symm.trans hdφ.symm))
  rcases lt_or_ge p a.idx with R3 | hpa
  · -- between the gadgets
    obtain ⟨h1, hb1e⟩ := pass_r_lt hW hℓa he hp hbit R3
    obtain ⟨h2, hb2e⟩ := pass_r_ge hW hℓb h1 hp hb1e hpb2
    obtain ⟨h1', hb1'⟩ := pass_r_ge hW' hℓb' he' hp hbit' hpb2
    obtain ⟨h2', hb2'⟩ := pass_r_lt hW' hℓa' h1' (by omega) hb1' (by rw [hidx']; omega)
    have hcE : ExtCol X Pc2 (colOf (next hW (next hW e))) := by
      rw [block_col_true h2 (by omega) hb2e, cm_extCol]; omega
    obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y)
      (not_actE_of X Pc2 Y (by rw [block_col_true he hp hbit, cm_extCol]; omega) (not_σ_right he hp hbit (notσ_of_lt hℓa R3)))
      (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_true h1 hp hb1e, cm_extCol]; omega)
        (not_σ_right h1 hp hb1e (notσ_of_ge hℓb hpb2))) (apassage_end hW _))
    obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y)
      (not_actE_of X Pc2' Y (by rw [block_col_true he' hp hbit', cm_extCol']; omega) (not_σ_right he' hp hbit' (notσ_of_ge hℓb' hpb2)))
      (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_true h1' (by omega) hb1', cm_extCol']; omega)
        (not_σ_right h1' (by omega) hb1' (notσ_of_lt hℓa' (by rw [hidx']; omega)))) (apassage_end hW' _))
    refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
    rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
  rcases lt_or_ge p (a.idx + a.arity) with R4 | R5
  · -- the read window of `a`
    obtain ⟨h1', hb1'⟩ := pass_r_ge hW' hℓb' he' hp hbit' (by omega)
    have nE0' : ¬ ActE X Pc2' Y e' :=
      not_actE_of X Pc2' Y (by rw [block_col_true he' hp hbit', cm_extCol']; omega) (not_σ_right he' hp hbit' (notσ_of_ge hℓb' (by omega)))
    rcases kind_of_arity (ℓ := a) (by omega) with ⟨i, hai⟩ | ⟨i, hai⟩
    · -- `a = r i`
      have hℓa2 : letterAt Wc X.length = .r i := hℓa.trans hai
      have hℓa'2 : letterAt Wc' (X.length + 1) = .r (a.idx + b.coarity - b.arity) := hℓa'.trans (by rw [hai]; rfl)
      have haidx : a.idx = i := by rw [hai]; rfl
      have haar : a.arity = 2 := by rw [hai]; rfl
      obtain ⟨g1, g2, gb⟩ := r_window hW hℓa2 he (by omega) hbit
      have hq0 : (if bit Wc X.length i then i + 1 else i) ≠ 0 := by split_ifs <;> omega
      have hcE : ExtCol X Pc2 (colOf (next hW (next hW e))) := by
        have := (cutSlot_facts hW g2 hq0).2.2.1
        rw [block_col_false g2 hq0 gb, cm_extCol]; omega
      obtain ⟨g1', g2', gb'⟩ := r_window hW' hℓa'2 h1' (by omega) hb1'
      have hq0' : (if bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity) then a.idx + b.coarity - b.arity + 1
          else a.idx + b.coarity - b.arity) ≠ 0 := by split_ifs <;> omega
      obtain ⟨h4', hb4'⟩ := pass_l_ge hW' hℓb' (k := X.length) g2' hq0' gb' (by split_ifs <;> omega)
      have t1 : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity) = bit Wc X.length i := by
        have := bit_succ_of_ge hW' hk₀' (p := a.idx) (by rw [hℓb']; exact hab)
        rw [hℓb'] at this
        rw [this, ← (tE a.idx).1, haidx]
      obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y)
        (not_actE_of X Pc2 Y (by rw [block_col_true he hp hbit, cm_extCol]; omega)
          (not_σ_right he hp hbit (fun _ hj' => by rw [hℓa2] at hj'; cases hj')))
        (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_vertex g1, cm_extCol]; omega) (not_σ_vertex g1))
          (apassage_end hW _))
      obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y) nE0'
        (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_true h1' (by omega) hb1', cm_extCol']; omega)
          (not_σ_right h1' (by omega) hb1' (fun _ hj' => by rw [hℓa'2] at hj'; cases hj')))
        (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_vertex g1', cm_extCol']; omega) (not_σ_vertex g1'))
        (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_false g2' hq0' gb', Nat.add_sub_cancel, cm_extCol']; omega)
          (not_σ_left g2' hq0' gb' (notσ_of_ge' hℓb' (by split_ifs <;> omega)))) (apassage_end hW' _))))
      refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
      rw [hc']; apply Subtype.ext; rw [φext _ hcE, g2, h4', t1]
      simp only [Prod.mk.injEq, true_and]
      split_ifs <;> omega
    · -- `a = σ i`: the entry is the crossing slot; in `W'` it reaches the crossing slot in one step
      have hℓa2 : letterAt Wc X.length = .σ i := hℓa.trans hai
      have hℓa'2 : letterAt Wc' (X.length + 1) = .σ (a.idx + b.coarity - b.arity) := hℓa'.trans (by rw [hai]; rfl)
      have haidx : a.idx = i := by rw [hai]; rfl
      have haar : a.arity = 2 := by rw [hai]; rfl
      obtain ⟨-, -, hσe, hde, hcole⟩ := σ_window_right hW hℓa2 he (by omega) hbit
      have hinte : IntSlot X Pc2 Y e := ⟨hσe, by rw [hcole, cm_extCol]; omega⟩
      obtain ⟨-, -, hσ1', hd1', hcol1'⟩ := σ_window_right hW' hℓa'2 h1' (by omega) hb1'
      obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y) nE0' (apassage_end hW' _)
      refine ⟨0, e, Or.inr hinte, rfl, fun _ h => absurd h (Nat.not_lt_zero _), n', e', rfl, ?_, hmin'⟩
      rw [hc']
      refine Eq.trans ?_ (φint _ _ hinte).symm
      obtain ⟨hdφ, hcφ, -⟩ := cmφI_to_spec X Y a b hW hW' ⟨e, hinte⟩
      refine σslot_ext hW' hσ1' (cmφI_to X Y a b hW hW' _).2.1 (hcol1'.trans (hcφ hcole).symm) ?_
      rw [hd1', hdφ, hde]
      exact decide_eq_decide.2 (by omega)
  · -- below both gadgets
    obtain ⟨h1, hb1e⟩ := pass_r_ge hW hℓa he hp hbit R5
    obtain ⟨h2, hb2e⟩ := pass_r_ge hW hℓb h1 (by omega) hb1e (by omega)
    obtain ⟨h1', hb1'⟩ := pass_r_ge hW' hℓb' he' hp hbit' (by omega)
    obtain ⟨h2', hb2'⟩ := pass_r_ge hW' hℓa' h1' (by omega) hb1' (by rw [hidx', har']; omega)
    rw [hco', har'] at h2' hb2'
    have hcE : ExtCol X Pc2 (colOf (next hW (next hW e))) := by
      rw [block_col_true h2 (by omega) hb2e, cm_extCol]; omega
    obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y)
      (not_actE_of X Pc2 Y (by rw [block_col_true he hp hbit, cm_extCol]; omega) (not_σ_right he hp hbit (notσ_of_ge hℓa R5)))
      (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_true h1 (by omega) hb1e, cm_extCol]; omega)
        (not_σ_right h1 (by omega) hb1e (notσ_of_ge hℓb (by omega)))) (apassage_end hW _))
    obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y)
      (not_actE_of X Pc2' Y (by rw [block_col_true he' hp hbit', cm_extCol']; omega) (not_σ_right he' hp hbit' (notσ_of_ge hℓb' (by omega))))
      (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_true h1' (by omega) hb1', cm_extCol']; omega)
        (not_σ_right h1' (by omega) hb1' (notσ_of_ge hℓa' (by rw [hidx', har']; omega)))) (apassage_end hW' _))
    refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
    rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
    simp only [Prod.mk.injEq, true_and]; omega

end CommEntries

section CommEntriesRight

variable (X Y : Word) (a b : Letter)

local notation "Wc" => X ++ [a, b] ++ Y
local notation "Pc2" => [a, b]
local notation "Wc'" => X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y
local notation "Pc2'" => [b, a.reindex (a.idx + b.coarity - b.arity)]

variable (hab : b.idx + b.arity ≤ a.idx)
variable (hW : (X ++ [a, b] ++ Y).Closed) (hW' : (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).Closed)

local notation "φc" => φA X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) hW (cmφI X Y a b hW hW')

include hab hW hW' in
/-- the entries of the commutation block from the right -/
theorem cm_right (e : Slot Wc) (hext : IsExtSlot X Pc2 e.1) {q : ℕ} (he : e.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hbit : bit Wc (X.length + 2) q = false) :
    ∃ (m : ℕ) (c : Slot Wc) (hc : ActE X Pc2 Y c), (next hW)^[m] e = c ∧
      (∀ i < m, ¬ ActE X Pc2 Y ((next hW)^[i] e)) ∧
      ∃ (m' : ℕ) (b' : Slot Wc'), b'.1 = extPair X Pc2 Pc2' e.1 ∧
        (next hW')^[m'] b' = (φc ⟨c, hc⟩).1 ∧ ∀ i < m', ¬ ActE X Pc2' Y ((next hW')^[i] b') := by
  have hE := cm_sameEffect X Y a b hab hW
  have hPne := cm_Pne a b
  obtain ⟨hℓa, hℓb⟩ := cm_letters X Y a b
  obtain ⟨hℓb', hℓa'⟩ := cm_letters' X Y a b
  have hk₀ := cm_k₀ X Y a b
  have hk₁ := cm_k₁ X Y a b
  have hk₀' := cm_k₀' X Y a b
  have hk₁' := cm_k₁' X Y a b
  have ha1 := cm_a_pos X Y a b hW
  have hb1 := cm_b_pos X Y a b hW'
  have tE := cm_bits_ext X Y a b hab hW
  have hidx' : (a.reindex (a.idx + b.coarity - b.arity)).idx = a.idx + b.coarity - b.arity := idx_reindex a _
  have har' := arity_reindex a (a.idx + b.coarity - b.arity)
  have hco' := coarity_reindex a (a.idx + b.coarity - b.arity)
  let e' : Slot Wc' := ⟨extPair X Pc2 Pc2' e.1, isSlot_ext X Pc2 Y Pc2' hPne hE e.2 hext⟩
  have he' : e'.1 = (X.length + 2, q) := by
    show extPair X Pc2 Pc2' e.1 = _
    rw [he, cm_extPair X a b (Or.inr le_rfl)]
  have he2 : e.1 = (X.length + 1 + 1, q) := he
  have he2' : e'.1 = (X.length + 1 + 1, q) := he'
  have hbit' : bit Wc' (X.length + 2) q = false := by rw [← (tE q).2]; exact hbit
  have φext := cm_φext X Y a b hab hW hW'
  have φint := cm_φint X Y a b hab hW hW'
  rcases lt_or_ge q b.idx with R1 | hqb
  · -- above both gadgets
    obtain ⟨h1, hb1e⟩ := pass_l_lt hW hℓb he2 hq hbit R1
    obtain ⟨h2, hb2e⟩ := pass_l_lt hW hℓa h1 hq hb1e (by omega)
    obtain ⟨h1', hb1'⟩ := pass_l_lt hW' hℓa' he2' hq hbit' (by rw [hidx']; omega)
    obtain ⟨h2', hb2'⟩ := pass_l_lt hW' hℓb' h1' hq hb1' R1
    have hcE : ExtCol X Pc2 (colOf (next hW (next hW e))) := by
      have := (cutSlot_facts hW h2 hq).2.2.1
      rw [block_col_false h2 hq hb2e, cm_extCol]; omega
    obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y)
      (not_actE_of X Pc2 Y (by rw [block_col_false he2 hq hbit, Nat.add_sub_cancel, cm_extCol]; omega)
        (not_σ_left he2 hq hbit (notσ_of_lt hℓb R1)))
      (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_false h1 hq hb1e, Nat.add_sub_cancel, cm_extCol]; omega)
        (not_σ_left h1 hq hb1e (notσ_of_lt hℓa (by omega)))) (apassage_end hW _))
    obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y)
      (not_actE_of X Pc2' Y (by rw [block_col_false he2' hq hbit', Nat.add_sub_cancel, cm_extCol']; omega)
        (not_σ_left he2' hq hbit' (notσ_of_lt hℓa' (by rw [hidx']; omega))))
      (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_false h1' hq hb1', Nat.add_sub_cancel, cm_extCol']; omega)
        (not_σ_left h1' hq hb1' (notσ_of_lt hℓb' R1))) (apassage_end hW' _))
    refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
    rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
  rcases lt_or_ge q (b.idx + b.coarity) with R2 | hqb2
  · -- the write window of `b`
    have hqn : q < a.idx + b.coarity - b.arity := by omega
    obtain ⟨h1', hb1'⟩ := pass_l_lt hW' hℓa' he2' hq hbit' (by rw [hidx']; exact hqn)
    have nE0' : ¬ ActE X Pc2' Y e' :=
      not_actE_of X Pc2' Y (by rw [block_col_false he2' hq hbit', Nat.add_sub_cancel, cm_extCol']; omega)
        (not_σ_left he2' hq hbit' (notσ_of_lt hℓa' (by rw [hidx']; exact hqn)))
    rcases kind_of_coarity (ℓ := b) (by omega) with ⟨j, d, hbj⟩ | ⟨j, hbj⟩
    · -- `b = l j d`
      have hℓb2 : letterAt Wc (X.length + 1) = .l j d := hℓb.trans hbj
      have hℓb'2 : letterAt Wc' X.length = .l j d := hℓb'.trans hbj
      have hbidx : b.idx = j := by rw [hbj]; rfl
      have hbco : b.coarity = 2 := by rw [hbj]; rfl
      obtain ⟨g1, g2, gb⟩ := l_window hW hℓb2 hk₁ he2 (by omega) hbit
      have hcE : ExtCol X Pc2 (colOf (next hW (next hW e))) := by
        rw [block_col_true g2 (by split_ifs <;> omega) gb, cm_extCol]; omega
      obtain ⟨g1', g2', gb'⟩ := l_window hW' hℓb'2 hk₀' h1' (by omega) hb1'
      obtain ⟨h4', hb4'⟩ := pass_r_lt hW' hℓa' g2' (by split_ifs <;> omega) gb' (by rw [hidx']; split_ifs <;> omega)
      obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y)
        (not_actE_of X Pc2 Y (by rw [block_col_false he2 hq hbit, Nat.add_sub_cancel, cm_extCol]; omega)
          (not_σ_left he2 hq hbit (fun _ hj' => by rw [hℓb2] at hj'; cases hj')))
        (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_vertex g1, cm_extCol]; omega) (not_σ_vertex g1))
          (apassage_end hW _))
      obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y) nE0'
        (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_false h1' hq hb1', Nat.add_sub_cancel, cm_extCol']; omega)
          (not_σ_left h1' hq hb1' (fun _ hj' => by rw [hℓb'2] at hj'; cases hj')))
        (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_vertex g1', cm_extCol']; omega) (not_σ_vertex g1'))
        (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_true g2' (by split_ifs <;> omega) gb', cm_extCol']; omega)
          (not_σ_right g2' (by split_ifs <;> omega) gb' (notσ_of_lt hℓa' (by rw [hidx']; split_ifs <;> omega))))
          (apassage_end hW' _))))
      refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
      rw [hc']; apply Subtype.ext; rw [φext _ hcE, g2, h4']
    · -- `b = σ j`: the entry is the crossing slot; in `W'` it reaches the crossing slot in one step
      have hℓb2 : letterAt Wc (X.length + 1) = .σ j := hℓb.trans hbj
      have hℓb'2 : letterAt Wc' X.length = .σ j := hℓb'.trans hbj
      have hbidx : b.idx = j := by rw [hbj]; rfl
      have hbco : b.coarity = 2 := by rw [hbj]; rfl
      obtain ⟨-, -, hσe, hde, hcole⟩ := σ_window_left hW hℓb2 he2 (by omega) hbit
      have hinte : IntSlot X Pc2 Y e := ⟨hσe, by rw [hcole, cm_extCol]; omega⟩
      obtain ⟨-, -, hσ1', hd1', hcol1'⟩ := σ_window_left hW' hℓb'2 h1' (by omega) hb1'
      obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y) nE0' (apassage_end hW' _)
      refine ⟨0, e, Or.inr hinte, rfl, fun _ h => absurd h (Nat.not_lt_zero _), n', e', rfl, ?_, hmin'⟩
      rw [hc']
      refine Eq.trans ?_ (φint _ _ hinte).symm
      obtain ⟨hdφ, -, hcφ⟩ := cmφI_to_spec X Y a b hW hW' ⟨e, hinte⟩
      exact σslot_ext hW' hσ1' (cmφI_to X Y a b hW hW' _).2.1 (hcol1'.trans (hcφ hcole).symm)
        (hd1'.trans (hde.symm.trans hdφ.symm))
  rcases lt_or_ge q (a.idx + b.coarity - b.arity) with R3 | hqn
  · -- between the gadgets
    obtain ⟨h1, hb1e⟩ := pass_l_ge hW hℓb he2 hq hbit hqb2
    obtain ⟨h2, hb2e⟩ := pass_l_lt hW hℓa h1 (by omega) hb1e (by omega)
    obtain ⟨h1', hb1'⟩ := pass_l_lt hW' hℓa' he2' hq hbit' (by rw [hidx']; exact R3)
    obtain ⟨h2', hb2'⟩ := pass_l_ge hW' hℓb' h1' hq hb1' hqb2
    have hcE : ExtCol X Pc2 (colOf (next hW (next hW e))) := by
      have := (cutSlot_facts hW h2 (by omega)).2.2.1
      rw [block_col_false h2 (by omega) hb2e, cm_extCol]; omega
    obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y)
      (not_actE_of X Pc2 Y (by rw [block_col_false he2 hq hbit, Nat.add_sub_cancel, cm_extCol]; omega)
        (not_σ_left he2 hq hbit (notσ_of_ge' hℓb hqb2)))
      (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_false h1 (by omega) hb1e, Nat.add_sub_cancel, cm_extCol]; omega)
        (not_σ_left h1 (by omega) hb1e (notσ_of_lt hℓa (by omega)))) (apassage_end hW _))
    obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y)
      (not_actE_of X Pc2' Y (by rw [block_col_false he2' hq hbit', Nat.add_sub_cancel, cm_extCol']; omega)
        (not_σ_left he2' hq hbit' (notσ_of_lt hℓa' (by rw [hidx']; exact R3))))
      (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_false h1' hq hb1', Nat.add_sub_cancel, cm_extCol']; omega)
        (not_σ_left h1' hq hb1' (notσ_of_ge' hℓb' hqb2))) (apassage_end hW' _))
    refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
    rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
  rcases lt_or_ge q (a.idx + b.coarity - b.arity + a.coarity) with R4 | R5
  · -- the write window of `a`
    obtain ⟨h1, hb1e⟩ := pass_l_ge hW hℓb he2 hq hbit (by omega)
    have nE0 : ¬ ActE X Pc2 Y e :=
      not_actE_of X Pc2 Y (by rw [block_col_false he2 hq hbit, Nat.add_sub_cancel, cm_extCol]; omega)
        (not_σ_left he2 hq hbit (notσ_of_ge' hℓb (by omega)))
    rcases kind_of_coarity (ℓ := a) (by omega) with ⟨i, d, hai⟩ | ⟨i, hai⟩
    · -- `a = l i d`
      have hℓa2 : letterAt Wc X.length = .l i d := hℓa.trans hai
      have hℓa'2 : letterAt Wc' (X.length + 1) = .l (a.idx + b.coarity - b.arity) d := hℓa'.trans (by rw [hai]; rfl)
      have haidx : a.idx = i := by rw [hai]; rfl
      have haco : a.coarity = 2 := by rw [hai]; rfl
      obtain ⟨g1, g2, gb⟩ := l_window hW hℓa2 hk₀ h1 (by omega) hb1e
      obtain ⟨h4, hb4⟩ := pass_r_ge hW hℓb g2 (by split_ifs <;> omega) gb (by split_ifs <;> omega)
      have hcE : ExtCol X Pc2 (colOf (next hW (next hW (next hW (next hW e))))) := by
        rw [block_col_true h4 (by split_ifs <;> omega) hb4, cm_extCol]; omega
      obtain ⟨g1', g2', gb'⟩ := l_window hW' hℓa'2 hk₁' he2' (by omega) hbit'
      obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y) nE0
        (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_false h1 (by omega) hb1e, Nat.add_sub_cancel, cm_extCol]; omega)
          (not_σ_left h1 (by omega) hb1e (fun _ hj' => by rw [hℓa2] at hj'; cases hj')))
        (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_vertex g1, cm_extCol]; omega) (not_σ_vertex g1))
        (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_true g2 (by split_ifs <;> omega) gb, cm_extCol]; omega)
          (not_σ_right g2 (by split_ifs <;> omega) gb (notσ_of_ge hℓb (by split_ifs <;> omega)))) (apassage_end hW _))))
      obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y)
        (not_actE_of X Pc2' Y (by rw [block_col_false he2' hq hbit', Nat.add_sub_cancel, cm_extCol']; omega)
          (not_σ_left he2' hq hbit' (fun _ hj' => by rw [hℓa'2] at hj'; cases hj')))
        (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_vertex g1', cm_extCol']; omega) (not_σ_vertex g1'))
          (apassage_end hW' _))
      refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
      rw [hc']; apply Subtype.ext; rw [φext _ hcE, h4, g2']
      simp only [Prod.mk.injEq, true_and]
      cases d <;> simp <;> omega
    · -- `a = σ i`: reaches the crossing slot in one step; in `W'` the entry is the crossing slot
      have hℓa2 : letterAt Wc X.length = .σ i := hℓa.trans hai
      have hℓa'2 : letterAt Wc' (X.length + 1) = .σ (a.idx + b.coarity - b.arity) := hℓa'.trans (by rw [hai]; rfl)
      have haidx : a.idx = i := by rw [hai]; rfl
      have haco : a.coarity = 2 := by rw [hai]; rfl
      have haar : a.arity = 2 := by rw [hai]; rfl
      obtain ⟨-, -, hσ1, hd1, hcol1⟩ := σ_window_left hW hℓa2 h1 (by omega) hb1e
      have hint1 : IntSlot X Pc2 Y (next hW e) := ⟨hσ1, by rw [hcol1, cm_extCol]; omega⟩
      obtain ⟨-, -, hσ', hd', hcol'⟩ := σ_window_left hW' hℓa'2 he2' (by omega) hbit'
      obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y) nE0 (apassage_end hW _)
      refine ⟨n, _, Or.inr hint1, hc, hmin, 0, e', rfl, ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
      rw [Function.iterate_zero, id]
      refine Eq.trans ?_ (φint _ _ hint1).symm
      obtain ⟨hdφ, hcφ, -⟩ := cmφI_to_spec X Y a b hW hW' ⟨next hW e, hint1⟩
      refine σslot_ext hW' hσ' (cmφI_to X Y a b hW hW' _).2.1 (hcol'.trans (hcφ hcol1).symm) ?_
      rw [hd', hdφ, hd1]
      exact decide_eq_decide.2 (by omega)
  · -- below both gadgets
    obtain ⟨h1, hb1e⟩ := pass_l_ge hW hℓb he2 hq hbit (by omega)
    obtain ⟨h2, hb2e⟩ := pass_l_ge hW hℓa h1 (by omega) hb1e (by omega)
    obtain ⟨h1', hb1'⟩ := pass_l_ge hW' hℓa' he2' hq hbit' (by rw [hidx', hco']; exact R5)
    rw [har', hco'] at h1' hb1'
    obtain ⟨h2', hb2'⟩ := pass_l_ge hW' hℓb' h1' (by omega) hb1' (by omega)
    have hcE : ExtCol X Pc2 (colOf (next hW (next hW e))) := by
      have := (cutSlot_facts hW h2 (by omega)).2.2.1
      rw [block_col_false h2 (by omega) hb2e, cm_extCol]; omega
    obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y)
      (not_actE_of X Pc2 Y (by rw [block_col_false he2 hq hbit, Nat.add_sub_cancel, cm_extCol]; omega)
        (not_σ_left he2 hq hbit (notσ_of_ge' hℓb (by omega))))
      (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_false h1 (by omega) hb1e, Nat.add_sub_cancel, cm_extCol]; omega)
        (not_σ_left h1 (by omega) hb1e (notσ_of_ge' hℓa (by omega)))) (apassage_end hW _))
    obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y)
      (not_actE_of X Pc2' Y (by rw [block_col_false he2' hq hbit', Nat.add_sub_cancel, cm_extCol']; omega)
        (not_σ_left he2' hq hbit' (notσ_of_ge' hℓa' (by rw [hidx', hco']; exact R5))))
      (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_false h1' (by omega) hb1', Nat.add_sub_cancel, cm_extCol']; omega)
        (not_σ_left h1' (by omega) hb1' (notσ_of_ge' hℓb' (by omega)))) (apassage_end hW' _))
    refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
    rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
    simp only [Prod.mk.injEq, true_and]; omega

end CommEntriesRight

section CommInterior

variable (X Y : Word) (a b : Letter)

local notation "Wc" => X ++ [a, b] ++ Y
local notation "Pc2" => [a, b]
local notation "Wc'" => X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y
local notation "Pc2'" => [b, a.reindex (a.idx + b.coarity - b.arity)]

variable (hab : b.idx + b.arity ≤ a.idx)
variable (hW : (X ++ [a, b] ++ Y).Closed) (hW' : (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).Closed)

local notation "φc" => φA X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) hW (cmφI X Y a b hW hW')

include hab hW hW' in
/-- the interior `σ` slots of the commutation block -/
theorem cm_interior (u : Slot Wc) (hu : IntSlot X Pc2 Y u) :
    ∃ (m : ℕ) (_ : 0 < m) (c : Slot Wc) (hc : ActE X Pc2 Y c), (next hW)^[m] u = c ∧
      (∀ i, 0 < i → i < m → ¬ ActE X Pc2 Y ((next hW)^[i] u)) ∧
      ∃ (m' : ℕ), 0 < m' ∧ (next hW')^[m'] (cmφI X Y a b hW hW' ⟨u, hu⟩).1 = (φc ⟨c, hc⟩).1 ∧
        ∀ i, 0 < i → i < m' → ¬ ActE X Pc2' Y ((next hW')^[i] (cmφI X Y a b hW hW' ⟨u, hu⟩).1) := by
  have hE := cm_sameEffect X Y a b hab hW
  obtain ⟨hℓa, hℓb⟩ := cm_letters X Y a b
  obtain ⟨hℓb', hℓa'⟩ := cm_letters' X Y a b
  have hk₀ := cm_k₀ X Y a b
  have hk₁ := cm_k₁ X Y a b
  have hk₀' := cm_k₀' X Y a b
  have hk₁' := cm_k₁' X Y a b
  have ha1 := cm_a_pos X Y a b hW
  have hb1 := cm_b_pos X Y a b hW'
  have tE := cm_bits_ext X Y a b hab hW
  have hidx' : (a.reindex (a.idx + b.coarity - b.arity)).idx = a.idx + b.coarity - b.arity := idx_reindex a _
  have har' := arity_reindex a (a.idx + b.coarity - b.arity)
  have hco' := coarity_reindex a (a.idx + b.coarity - b.arity)
  have φext := cm_φext X Y a b hab hW hW'
  obtain ⟨hσ, hc⟩ := (cm_int_iff X Y a b hW u).1 hu
  rw [cmφI_val]
  obtain ⟨hdφ, hcφ0, hcφ1⟩ := cmφI_to_spec X Y a b hW hW' ⟨u, hu⟩
  rcases hc with hc | hc
  · -- a crossing letter `a`
    have hcr : a.isCrossing = true := by have := hσ.1; rwa [hc, hℓa] at this
    have hai : a = .σ a.idx := eq_σ_of_crossing hcr
    have hℓa2 : letterAt Wc X.length = .σ a.idx := hℓa.trans hai
    have hℓa'2 : letterAt Wc' (X.length + 1) = .σ (a.idx + b.coarity - b.arity) := hℓa'.trans (by rw [hai]; rfl)
    have haar : a.arity = 2 := arity_of_crossing hcr
    have haco : a.coarity = 2 := coarity_of_crossing hcr
    obtain ⟨-, -, -, b1, b2⟩ := σ_facts hW hk₀ hℓa2
    obtain ⟨-, -, -, b1', b2'⟩ := σ_facts hW' hk₁' hℓa'2
    have t1 : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity) = bit Wc X.length a.idx := by
      have := bit_succ_of_ge hW' hk₀' (p := a.idx) (by rw [hℓb']; exact hab)
      rw [hℓb'] at this; rw [this, (tE a.idx).1]
    have t2 : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity + 1) = bit Wc X.length (a.idx + 1) := by
      have := bit_succ_of_ge hW' hk₀' (p := a.idx + 1) (by rw [hℓb']; omega)
      rw [hℓb'] at this
      rw [show a.idx + b.coarity - b.arity + 1 = a.idx + 1 + b.coarity - b.arity by omega, this, (tE (a.idx + 1)).1]
    have hcol1 : colOf (cmφI_to X Y a b hW hW' ⟨u, hu⟩).1 = X.length + 1 := hcφ0 hc
    have hcr' : (letterAt Wc' (X.length + 1)).isCrossing = true := by rw [hℓa', isCrossing_reindex]; exact hcr
    rw [cmφI_to_val₀ X Y a b hW hW' ⟨u, hu⟩ hc hcr']
    rcases eq_σSlotA_or_σSlotB hW hσ with huA | huB
    · -- the descending slot of `a`
      have hu1 : u.1 = if bit Wc X.length a.idx then (X.length, a.idx) else (X.length + 1, a.idx + 1) := by
        rw [huA, σSlotA_congr hW _ hk₀ _ hℓa2 hc, σSlotA_val]
      have hdu : isDesc u = true := by rw [huA]; exact isDesc_σSlotA hW _ _
      simp only [hdu, ↓reduceIte]
      rw [σSlotA_congr hW' hk₁' hk₁' (letterAt_σ_of_isCrossing hcr') hℓa'2 rfl]
      cases hba : bit Wc X.length a.idx
      · -- the leftward crossing strand: `(|X|+1, a.idx+1)` heading left
        rw [hba] at hu1; simp only [Bool.false_eq_true, ↓reduceIte] at hu1
        have hb1u : bit Wc (X.length + 1) (a.idx + 1) = false := by rw [b1, hba]
        have h1 := next_σ_left_succ hW hℓa2 hu1 hb1u
        have hcE : ExtCol X Pc2 (colOf (next hW u)) := by
          have := (cutSlot_facts hW h1 (by omega)).2.2.1
          rw [block_col_false h1 (by omega) (by rw [← b1, hb1u]), cm_extCol]; omega
        -- `W'`: `(|X|+2, n+1)` heading left, through the crossing, then below `b`
        have hs' : (σSlotA hW' hk₁' hℓa'2).1 = (X.length + 1 + 1, a.idx + b.coarity - b.arity + 1) := by
          rw [σSlotA_val, t1, hba]; rfl
        have hb1' : bit Wc' (X.length + 1 + 1) (a.idx + b.coarity - b.arity + 1) = false := by rw [b1', t1, hba]
        have h1' := next_σ_left_succ hW' hℓa'2 hs' hb1'
        have hb2' : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity) = false := by rw [t1, hba]
        obtain ⟨h2', hb2e⟩ := pass_l_ge hW' hℓb' (k := X.length) h1' (by omega) hb2' (by omega)
        refine ⟨1, one_pos, _, Or.inl hcE, rfl, fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _),
          2, by omega, ?_, ?_⟩
        · apply Subtype.ext
          rw [φext _ hcE, h1]
          show (next hW' (next hW' (σSlotA hW' hk₁' hℓa'2))).1 = _
          rw [h2']; simp only [Prod.mk.injEq, true_and]; omega
        · intro i hi him
          have : i = 1 := by omega
          subst this
          show ¬ ActE X Pc2' Y (next hW' (σSlotA hW' hk₁' hℓa'2))
          exact not_actE_of X Pc2' Y (by rw [block_col_false h1' (by omega) hb2', Nat.add_sub_cancel, cm_extCol']; omega)
            (not_σ_left h1' (by omega) hb2' (notσ_of_ge' hℓb' (by omega)))
      · -- the rightward crossing strand: `(|X|, a.idx)` heading right
        rw [hba] at hu1; simp only [↓reduceIte] at hu1
        have h1 := next_σ_right_idx hW hℓa2 hu1 hba
        have hb1u : bit Wc (X.length + 1) (a.idx + 1) = true := by rw [b1, hba]
        obtain ⟨h2, hb2e⟩ := pass_r_ge hW hℓb h1 (by omega) hb1u (by omega)
        have hcE : ExtCol X Pc2 (colOf (next hW (next hW u))) := by
          rw [block_col_true h2 (by omega) hb2e, cm_extCol]; omega
        have hs' : (σSlotA hW' hk₁' hℓa'2).1 = (X.length + 1, a.idx + b.coarity - b.arity) := by
          rw [σSlotA_val, t1, hba]; rfl
        have hb1' : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity) = true := by rw [t1, hba]
        have h1' := next_σ_right_idx hW' hℓa'2 hs' hb1'
        refine ⟨2, by omega, _, Or.inl hcE, rfl, ?_, 1, one_pos, ?_,
          fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _)⟩
        · intro i hi him
          have : i = 1 := by omega
          subst this
          show ¬ ActE X Pc2 Y (next hW u)
          exact not_actE_of X Pc2 Y (by rw [block_col_true h1 (by omega) hb1u, cm_extCol]; omega)
            (not_σ_right h1 (by omega) hb1u (notσ_of_ge hℓb (by omega)))
        · apply Subtype.ext
          rw [φext _ hcE, h2]
          show (next hW' (σSlotA hW' hk₁' hℓa'2)).1 = _
          rw [h1']; simp only [Prod.mk.injEq, true_and]; omega
    · -- the ascending slot of `a`
      have hu1 : u.1 = if bit Wc X.length (a.idx + 1) then (X.length, a.idx + 1) else (X.length + 1, a.idx) := by
        rw [huB, σSlotB_congr hW _ hk₀ _ hℓa2 hc, σSlotB_val]
      have hdu : isDesc u = false := by rw [huB]; exact isDesc_σSlotB hW _ _
      simp only [hdu, Bool.false_eq_true, ↓reduceIte]
      rw [σSlotB_congr hW' hk₁' hk₁' (letterAt_σ_of_isCrossing hcr') hℓa'2 rfl]
      cases hba : bit Wc X.length (a.idx + 1)
      · -- `(|X|+1, a.idx)` heading left
        rw [hba] at hu1; simp only [Bool.false_eq_true, ↓reduceIte] at hu1
        have hb1u : bit Wc (X.length + 1) a.idx = false := by rw [b2, hba]
        have h1 := next_σ_left_idx hW hℓa2 hu1 hb1u
        have hcE : ExtCol X Pc2 (colOf (next hW u)) := by
          have := (cutSlot_facts hW h1 (by omega)).2.2.1
          rw [block_col_false h1 (by omega) (by rw [← b2, hb1u]), cm_extCol]; omega
        have hs' : (σSlotB hW' hk₁' hℓa'2).1 = (X.length + 1 + 1, a.idx + b.coarity - b.arity) := by
          rw [σSlotB_val, t2, hba]; rfl
        have hb1' : bit Wc' (X.length + 1 + 1) (a.idx + b.coarity - b.arity) = false := by rw [b2', t2, hba]
        have h1' := next_σ_left_idx hW' hℓa'2 hs' hb1'
        have hb2' : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity + 1) = false := by rw [t2, hba]
        obtain ⟨h2', hb2e⟩ := pass_l_ge hW' hℓb' (k := X.length) h1' (by omega) hb2' (by omega)
        refine ⟨1, one_pos, _, Or.inl hcE, rfl, fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _),
          2, by omega, ?_, ?_⟩
        · apply Subtype.ext
          rw [φext _ hcE, h1]
          show (next hW' (next hW' (σSlotB hW' hk₁' hℓa'2))).1 = _
          rw [h2']; simp only [Prod.mk.injEq, true_and]; omega
        · intro i hi him
          have : i = 1 := by omega
          subst this
          show ¬ ActE X Pc2' Y (next hW' (σSlotB hW' hk₁' hℓa'2))
          exact not_actE_of X Pc2' Y (by rw [block_col_false h1' (by omega) hb2', Nat.add_sub_cancel, cm_extCol']; omega)
            (not_σ_left h1' (by omega) hb2' (notσ_of_ge' hℓb' (by omega)))
      · -- `(|X|, a.idx+1)` heading right
        rw [hba] at hu1; simp only [↓reduceIte] at hu1
        have h1 := next_σ_right_succ hW hℓa2 hu1 hba
        have hb1u : bit Wc (X.length + 1) a.idx = true := by rw [b2, hba]
        obtain ⟨h2, hb2e⟩ := pass_r_ge hW hℓb h1 (by omega) hb1u (by omega)
        have hcE : ExtCol X Pc2 (colOf (next hW (next hW u))) := by
          rw [block_col_true h2 (by omega) hb2e, cm_extCol]; omega
        have hs' : (σSlotB hW' hk₁' hℓa'2).1 = (X.length + 1, a.idx + b.coarity - b.arity + 1) := by
          rw [σSlotB_val, t2, hba]; rfl
        have hb1' : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity + 1) = true := by rw [t2, hba]
        have h1' := next_σ_right_succ hW' hℓa'2 hs' hb1'
        refine ⟨2, by omega, _, Or.inl hcE, rfl, ?_, 1, one_pos, ?_,
          fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _)⟩
        · intro i hi him
          have : i = 1 := by omega
          subst this
          show ¬ ActE X Pc2 Y (next hW u)
          exact not_actE_of X Pc2 Y (by rw [block_col_true h1 (by omega) hb1u, cm_extCol]; omega)
            (not_σ_right h1 (by omega) hb1u (notσ_of_ge hℓb (by omega)))
        · apply Subtype.ext
          rw [φext _ hcE, h2]
          show (next hW' (σSlotB hW' hk₁' hℓa'2)).1 = _
          rw [h1']
  · -- a crossing letter `b`
    have hcr : b.isCrossing = true := by have := hσ.1; rwa [hc, hℓb] at this
    have hbj : b = .σ b.idx := eq_σ_of_crossing hcr
    have hℓb2 : letterAt Wc (X.length + 1) = .σ b.idx := hℓb.trans hbj
    have hℓb'2 : letterAt Wc' X.length = .σ b.idx := hℓb'.trans hbj
    have hbar : b.arity = 2 := arity_of_crossing hcr
    have hbco : b.coarity = 2 := coarity_of_crossing hcr
    obtain ⟨-, -, -, b1, b2⟩ := σ_facts hW hk₁ hℓb2
    obtain ⟨-, -, -, b1', b2'⟩ := σ_facts hW' hk₀' hℓb'2
    have t1 : bit Wc' X.length b.idx = bit Wc (X.length + 1) b.idx := by
      rw [← (tE b.idx).1, bit_succ_of_lt hW hk₀ (p := b.idx) hb1 (by rw [hℓa]; omega)]
    have t2 : bit Wc' X.length (b.idx + 1) = bit Wc (X.length + 1) (b.idx + 1) := by
      rw [← (tE (b.idx + 1)).1, bit_succ_of_lt hW hk₀ (p := b.idx + 1) (by omega) (by rw [hℓa]; omega)]
    have hcr' : (letterAt Wc' X.length).isCrossing = true := by rw [hℓb']; exact hcr
    rw [cmφI_to_val₁ X Y a b hW hW' ⟨u, hu⟩ hc hcr']
    rcases eq_σSlotA_or_σSlotB hW hσ with huA | huB
    · have hu1 : u.1 = if bit Wc (X.length + 1) b.idx then (X.length + 1, b.idx) else (X.length + 1 + 1, b.idx + 1) := by
        rw [huA, σSlotA_congr hW _ hk₁ _ hℓb2 hc, σSlotA_val]
      have hdu : isDesc u = true := by rw [huA]; exact isDesc_σSlotA hW _ _
      simp only [hdu, ↓reduceIte]
      rw [σSlotA_congr hW' hk₀' hk₀' (letterAt_σ_of_isCrossing hcr') hℓb'2 rfl]
      cases hbb : bit Wc (X.length + 1) b.idx
      · -- `(|X|+2, b.idx+1)` heading left
        rw [hbb] at hu1; simp only [Bool.false_eq_true, ↓reduceIte] at hu1
        have hb1u : bit Wc (X.length + 1 + 1) (b.idx + 1) = false := by rw [b1, hbb]
        have h1 := next_σ_left_succ hW hℓb2 hu1 hb1u
        obtain ⟨h2, hb2e⟩ := pass_l_lt hW hℓa (k := X.length) h1 (by omega) hbb (by omega)
        have hcE : ExtCol X Pc2 (colOf (next hW (next hW u))) := by
          have := (cutSlot_facts hW h2 (by omega)).2.2.1
          rw [block_col_false h2 (by omega) hb2e, cm_extCol]; omega
        have hs' : (σSlotA hW' hk₀' hℓb'2).1 = (X.length + 1, b.idx + 1) := by
          rw [σSlotA_val, t1, hbb]; rfl
        have hb1' : bit Wc' (X.length + 1) (b.idx + 1) = false := by rw [b1', t1, hbb]
        have h1' := next_σ_left_succ hW' hℓb'2 hs' hb1'
        have hcE' : ExtCol X Pc2' (colOf (next hW' (σSlotA hW' hk₀' hℓb'2))) := by
          have := (cutSlot_facts hW' h1' (by omega)).2.2.1
          rw [block_col_false h1' (by omega) (by rw [← b1', hb1']), cm_extCol']; omega
        refine ⟨2, by omega, _, Or.inl hcE, rfl, ?_, 1, one_pos, ?_,
          fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _)⟩
        · intro i hi him
          have : i = 1 := by omega
          subst this
          show ¬ ActE X Pc2 Y (next hW u)
          exact not_actE_of X Pc2 Y (by rw [block_col_false h1 (by omega) hbb, Nat.add_sub_cancel, cm_extCol]; omega)
            (not_σ_left h1 (by omega) hbb (notσ_of_lt hℓa (by omega)))
        · apply Subtype.ext
          rw [φext _ hcE, h2]
          show (next hW' (σSlotA hW' hk₀' hℓb'2)).1 = _
          rw [h1']
      · -- `(|X|+1, b.idx)` heading right
        rw [hbb] at hu1; simp only [↓reduceIte] at hu1
        have h1 := next_σ_right_idx hW hℓb2 hu1 hbb
        have hcE : ExtCol X Pc2 (colOf (next hW u)) := by
          rw [block_col_true h1 (by omega) (by rw [b1, hbb]), cm_extCol]; omega
        have hs' : (σSlotA hW' hk₀' hℓb'2).1 = (X.length, b.idx) := by rw [σSlotA_val, t1, hbb]; rfl
        have hb1' : bit Wc' X.length b.idx = true := by rw [t1, hbb]
        have h1' := next_σ_right_idx hW' hℓb'2 hs' hb1'
        have hb2' : bit Wc' (X.length + 1) (b.idx + 1) = true := by rw [b1', t1, hbb]
        obtain ⟨h2', hb2e⟩ := pass_r_lt hW' hℓa' h1' (by omega) hb2' (by rw [hidx']; omega)
        refine ⟨1, one_pos, _, Or.inl hcE, rfl, fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _),
          2, by omega, ?_, ?_⟩
        · apply Subtype.ext
          rw [φext _ hcE, h1]
          show (next hW' (next hW' (σSlotA hW' hk₀' hℓb'2))).1 = _
          rw [h2']
        · intro i hi him
          have : i = 1 := by omega
          subst this
          show ¬ ActE X Pc2' Y (next hW' (σSlotA hW' hk₀' hℓb'2))
          exact not_actE_of X Pc2' Y (by rw [block_col_true h1' (by omega) hb2', cm_extCol']; omega)
            (not_σ_right h1' (by omega) hb2' (notσ_of_lt hℓa' (by rw [hidx']; omega)))
    · have hu1 : u.1 = if bit Wc (X.length + 1) (b.idx + 1) then (X.length + 1, b.idx + 1) else (X.length + 1 + 1, b.idx) := by
        rw [huB, σSlotB_congr hW _ hk₁ _ hℓb2 hc, σSlotB_val]
      have hdu : isDesc u = false := by rw [huB]; exact isDesc_σSlotB hW _ _
      simp only [hdu, Bool.false_eq_true, ↓reduceIte]
      rw [σSlotB_congr hW' hk₀' hk₀' (letterAt_σ_of_isCrossing hcr') hℓb'2 rfl]
      cases hbb : bit Wc (X.length + 1) (b.idx + 1)
      · -- `(|X|+2, b.idx)` heading left
        rw [hbb] at hu1; simp only [Bool.false_eq_true, ↓reduceIte] at hu1
        have hb1u : bit Wc (X.length + 1 + 1) b.idx = false := by rw [b2, hbb]
        have h1 := next_σ_left_idx hW hℓb2 hu1 hb1u
        obtain ⟨h2, hb2e⟩ := pass_l_lt hW hℓa (k := X.length) h1 (by omega) hbb (by omega)
        have hcE : ExtCol X Pc2 (colOf (next hW (next hW u))) := by
          have := (cutSlot_facts hW h2 (by omega)).2.2.1
          rw [block_col_false h2 (by omega) hb2e, cm_extCol]; omega
        have hs' : (σSlotB hW' hk₀' hℓb'2).1 = (X.length + 1, b.idx) := by
          rw [σSlotB_val, t2, hbb]; rfl
        have hb1' : bit Wc' (X.length + 1) b.idx = false := by rw [b2', t2, hbb]
        have h1' := next_σ_left_idx hW' hℓb'2 hs' hb1'
        have hcE' : ExtCol X Pc2' (colOf (next hW' (σSlotB hW' hk₀' hℓb'2))) := by
          have := (cutSlot_facts hW' h1' (by omega)).2.2.1
          rw [block_col_false h1' (by omega) (by rw [← b2', hb1']), cm_extCol']; omega
        refine ⟨2, by omega, _, Or.inl hcE, rfl, ?_, 1, one_pos, ?_,
          fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _)⟩
        · intro i hi him
          have : i = 1 := by omega
          subst this
          show ¬ ActE X Pc2 Y (next hW u)
          exact not_actE_of X Pc2 Y (by rw [block_col_false h1 (by omega) hbb, Nat.add_sub_cancel, cm_extCol]; omega)
            (not_σ_left h1 (by omega) hbb (notσ_of_lt hℓa (by omega)))
        · apply Subtype.ext
          rw [φext _ hcE, h2]
          show (next hW' (σSlotB hW' hk₀' hℓb'2)).1 = _
          rw [h1']
      · -- `(|X|+1, b.idx+1)` heading right
        rw [hbb] at hu1; simp only [↓reduceIte] at hu1
        have h1 := next_σ_right_succ hW hℓb2 hu1 hbb
        have hcE : ExtCol X Pc2 (colOf (next hW u)) := by
          rw [block_col_true h1 (by omega) (by rw [b2, hbb]), cm_extCol]; omega
        have hs' : (σSlotB hW' hk₀' hℓb'2).1 = (X.length, b.idx + 1) := by rw [σSlotB_val, t2, hbb]; rfl
        have hb1' : bit Wc' X.length (b.idx + 1) = true := by rw [t2, hbb]
        have h1' := next_σ_right_succ hW' hℓb'2 hs' hb1'
        have hb2' : bit Wc' (X.length + 1) b.idx = true := by rw [b2', t2, hbb]
        obtain ⟨h2', hb2e⟩ := pass_r_lt hW' hℓa' h1' (by omega) hb2' (by rw [hidx']; omega)
        refine ⟨1, one_pos, _, Or.inl hcE, rfl, fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _),
          2, by omega, ?_, ?_⟩
        · apply Subtype.ext
          rw [φext _ hcE, h1]
          show (next hW' (next hW' (σSlotB hW' hk₀' hℓb'2))).1 = _
          rw [h2']
        · intro i hi him
          have : i = 1 := by omega
          subst this
          show ¬ ActE X Pc2' Y (next hW' (σSlotB hW' hk₀' hℓb'2))
          exact not_actE_of X Pc2' Y (by rw [block_col_true h1' (by omega) hb2', cm_extCol']; omega)
            (not_σ_right h1' (by omega) hb2' (notσ_of_lt hℓa' (by rw [hidx']; omega)))

include hab hW hW' in
/-- THE EXTENDED BLOCK PASSAGE of the commutation. -/
theorem cm_intPassage :
    IntPassage X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) hW hW' (cmφI X Y a b hW hW') := by
  constructor
  · intro e hext hcol
    rcases (entry_iff X Pc2 Y (cm_Pne a b) hW e).1 ⟨hext, hcol⟩ with ⟨p, he, hp, hbit⟩ | ⟨p, he, hp, hbit⟩
    · exact cm_left X Y a b hab hW hW' e hext he hp hbit
    · exact cm_right X Y a b hab hW hW' e hext he hp hbit
  · exact cm_interior X Y a b hab hW hW'

end CommInterior

section CommAssembly

variable (X Y : Word) (a b : Letter)

local notation "Wc" => X ++ [a, b] ++ Y
local notation "Pc2" => [a, b]
local notation "Wc'" => X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y
local notation "Pc2'" => [b, a.reindex (a.idx + b.coarity - b.arity)]

variable (hab : b.idx + b.arity ≤ a.idx)
variable (hW : (X ++ [a, b] ++ Y).Closed) (hW' : (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).Closed)

local notation "φc" => φA X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) hW (cmφI X Y a b hW hW')

include hab hW hW' in
/-- THE COMMUTATION RECORD ISOMORPHISM on the slot records: the active supersets are the exterior pieces
together with the interior `σ` slots of the two letters, matched by `cmφI`. -/
theorem cm_slotIso :
    Nonempty (RecordIso (slotRecord hW IsσSlot (allActive hW)) (slotRecord hW' IsσSlot (allActive hW'))) := by
  obtain ⟨hℓa, hℓb⟩ := cm_letters X Y a b
  obtain ⟨hℓb', hℓa'⟩ := cm_letters' X Y a b
  refine ⟨recordIsoOfConj hW hW' (ActE X Pc2 Y) (ActE X Pc2' Y) φc
    (conj_of_intPassage X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) hW hW' _
      (cm_intPassage X Y a b hab hW hW'))
    (hexit_of_comm hW (cm_extCol X a b) hℓa hℓb (Or.inl hab))
    (hexit_of_comm hW' (cm_extCol' X a b) hℓb' hℓa' (Or.inr (by rw [idx_reindex]; omega)))
    (fun _ hu => isσSlot_actE X Pc2 Y hu) (fun _ hu => isσSlot_actE X Pc2' Y hu) ?_ ?_ ?_ ?_⟩
  · -- `σ` slots correspond
    intro u
    by_cases hext : ExtPiece X Pc2 Y u.1
    · rw [φA_val_ext X Pc2 Y Pc2' _ _ hW _ u hext]
      exact isσSlot_φE_iff X Pc2 Y Pc2' _ _ hW ⟨u.1, hext⟩
    · rw [φA_val_int X Pc2 Y Pc2' _ _ hW _ u hext]
      exact iff_of_true (cmφI X Y a b hW hW' ⟨u.1, u.2.resolve_left hext⟩).2.1 (u.2.resolve_left hext).1
  · -- twins correspond
    intro u hu
    by_cases hext : ExtPiece X Pc2 Y u.1
    · have hext2 : ExtPiece X Pc2 Y (σtwin hW u.1) := extPiece_σtwin X Pc2 Y hW hu hext
      rw [φA_val_ext X Pc2 Y Pc2' _ _ hW _ _ hext2, φA_val_ext X Pc2 Y Pc2' _ _ hW _ u hext]
      exact φE_σtwin X Pc2 Y Pc2' _ _ hW hW' ⟨u.1, hext⟩ hu
    · have hint : IntSlot X Pc2 Y u.1 := u.2.resolve_left hext
      have hext2 : ¬ ExtPiece X Pc2 Y (σtwin hW u.1) := by
        show ¬ ExtCol X Pc2 (colOf _); rw [colOf_σtwin hW hu]; exact hint.2
      rw [φA_val_int X Pc2 Y Pc2' _ _ hW _ _ hext2, φA_val_int X Pc2 Y Pc2' _ _ hW _ u hext]
      exact cmφI_twin X Y a b hW hW' ⟨u.1, hint⟩
  · -- over bits
    intro u hu
    by_cases hext : ExtPiece X Pc2 Y u.1
    · rw [φA_val_ext X Pc2 Y Pc2' _ _ hW _ u hext]
      exact isDesc_φE X Pc2 Y Pc2' _ _ hW ⟨u.1, hext⟩
    · rw [φA_val_int X Pc2 Y Pc2' _ _ hW _ u hext, cmφI_val]
      exact (cmφI_to_spec X Y a b hW hW' _).1
  · -- signs
    intro u hu
    by_cases hext : ExtPiece X Pc2 Y u.1
    · rw [φA_val_ext X Pc2 Y Pc2' _ _ hW _ u hext]
      exact σsgn_φE X Pc2 Y Pc2' _ _ hW ⟨u.1, hext⟩
    · rw [φA_val_int X Pc2 Y Pc2' _ _ hW _ u hext]
      exact cmφI_sgn X Y a b hab hW hW' ⟨u.1, u.2.resolve_left hext⟩

include hab in
/-- the commutation (above case) on the named records of the realizations -/
theorem cm_recordIso_above (W W' : OWord) (hWeq : W.letters = Wc) (hW'eq : W'.letters = Wc') :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := by
  have hne : W.letters ≠ [] := by rw [hWeq]; simp
  have hne' : W'.letters ≠ [] := by rw [hW'eq]; simp
  obtain ⟨L, hL⟩ := W
  obtain ⟨L', hL'⟩ := W'
  simp only at hWeq hW'eq hne hne'
  subst hWeq hW'eq
  obtain ⟨κ⟩ := cm_slotIso X Y a b hab hL hL'
  exact ⟨(realizeRecordIso ⟨_, hL⟩ hne).trans (κ.trans (realizeRecordIso ⟨_, hL'⟩ hne').symm)⟩

end CommAssembly

end U3


/-! ### L-rec (unit U3, on the record core U2) — named-record isomorphisms (rp:record-polynomial
`presentations`, lp:split-circle in record form `P_addFree`, the accepted smoothing gate
`exists_smoothing_record_visit`).  Record of a realization: visits = the two slots of each `σ` letter,
successor = the next `σ` slot along the slot cycle `next` (`toSlot_succ`, `crossingParam_eq_half`), twin = the
other slot of the column, over = the descending strand (`overStrand_crossingOf`), sign = `sign_crossingOf`;
exterior slots of two words correspond by the index shift (`shiftIdx`, `next_ext`). -/

/-- LEAF (ng:commutation, sm-3:1929-1933 "After cusp rounding this is a positive page isotopy; equivalently,
the full named records are the same"). -/
theorem comm_recordIso {W W' : OWord} (h : IsComm W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := by
  -- one direction of the exchange gives the isomorphism; `IsComm` is symmetric
  suffices key : ∀ {W W' : OWord}, IsCommStep W.letters W'.letters →
      Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) by
    rcases h with h | h
    · exact key h
    · obtain ⟨κ⟩ := key h
      exact ⟨κ.symm⟩
  intro W W' h
  obtain ⟨X, Y, a, b, hWeq, hpat⟩ := h
  rcases hpat with ⟨hab, hW'eq⟩ | ⟨hab, hW'eq⟩
  · exact U3.cm_recordIso_above X Y a b hab W W' hWeq hW'eq
  · -- the below case is the above case for the exchanged pair, read backwards
    have hb : a.idx + a.arity ≤ (b.reindex (b.idx + a.arity - a.coarity)).idx := by
      rw [Letter.idx_reindex]; omega
    obtain ⟨κ⟩ := U3.cm_recordIso_above X Y (b.reindex (b.idx + a.arity - a.coarity)) a hb W' W hW'eq (by
      rw [hWeq, Letter.idx_reindex, Letter.reindex_reindex,
        show b.idx + a.arity - a.coarity + a.coarity - a.arity = b.idx by omega, Letter.reindex_self])
    exact ⟨κ.symm⟩

/-- LEAF (ng:deletions, sm-3:2017-2019: after rounding the zigzag "is a simple ordinary arc, positively page
isotopic relative to its endpoints to the straightened arc" — no crossing is touched; every strand passes
through the block, the exterior visits and their cyclic orders are unchanged). -/
theorem zigzag_recordIso {W W' : OWord} (h : IsZigzagDeletion W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := by
  obtain ⟨X, Y, m, d, hm, hpat, hW'eq⟩ := h
  have hne' : W'.letters ≠ [] := IsZigzagDeletion.ne_nil ⟨X, Y, m, d, hm, hpat, hW'eq⟩ W.closed
  rcases hpat with hWeq | hWeq
  · exact U3.zb_recordIso X Y m d (hWeq ▸ W.closed) W W' hWeq hW'eq hne'
  · exact U3.za_recordIso X Y m d (hWeq ▸ W.closed) W W' hWeq hW'eq hne'

/-- LEAF (ng:circle, sm-3:2054-2059 "A standard circle separated by the word procedure has no mixed crossings
... Lemma lp:split-circle permits this nesting"): the record of the word with the circle is the record of the
remainder with one free (crossing-free) component added. -/
theorem circle_recordIso_addFree {W W' : OWord} (h : IsCircleDeletion W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record.addFree) := by
  obtain ⟨X, Y, m, d, hm, hWeq, hW'eq, hne'⟩ := h
  exact U3.ci_recordIso X Y m d (hWeq ▸ W.closed) W W' hWeq hW'eq hne'

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
theorem skein_site {A A' C : OWord} (h : IsCuspSkeinStep A.letters A'.letters C.letters) : SkeinSite A A' C := by
  obtain ⟨X, Y, m, d, a, P, L, hm, hX, hP, hAe, hA'e, hCe⟩ := h
  obtain ⟨LA, hLA⟩ := A
  obtain ⟨LA', hLA'⟩ := A'
  obtain ⟨LC, hLC⟩ := C
  simp only at hAe hA'e hCe
  subst hAe hA'e
  have hne : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y) ≠ [] := by simp
  have hne' : (X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y) ≠ [] := by simp
  let ι := U2.realizeRecordIso ⟨_, hLA⟩ hne
  let ι' := U2.realizeRecordIso ⟨_, hLA'⟩ hne'
  let x₀ := U3.siteX X Y m d hLA
  let v := ι.Φ.symm x₀
  have hx : ι.Φ v = x₀ := Equiv.apply_symm_apply _ _
  refine ⟨v.1, ?_, ?_, ?_⟩
  · -- the switch half
    obtain ⟨κ⟩ := U3.sk_switchIso X Y m d a hLA hLA' hX hP hm
    have κ' := ι.switch v
    rw [hx] at κ'
    obtain ⟨jj⟩ := (realize ⟨_, hLA⟩).diagram.switch_record v.1 v rfl
    exact ⟨ι'.trans (κ.trans (κ'.symm.trans jj.symm))⟩
  · -- the smoothing half
    obtain ⟨D₀, hsm, ⟨θ⟩⟩ := exists_smoothing_record_visit (realize ⟨_, hLA⟩).diagram v.1 v rfl
    refine ⟨D₀, hsm, ?_⟩
    have sc := U3.smoothCongr ι v
    rw [hx] at sc
    rcases hCe with ⟨had, hCe⟩ | ⟨had, hCe⟩
    · subst hCe
      have hneC : (X ++ [Letter.l m d] ++ Y) ≠ [] := by simp
      obtain ⟨μ⟩ := U3.sk_smoothIso X Y m d a m hX hP hm hLA hLC (Or.inl ⟨had, rfl⟩)
      exact ⟨θ.trans (sc.trans (μ.trans (U2.realizeRecordIso ⟨_, hLC⟩ hneC).symm))⟩
    · subst hCe
      have hneC : (X ++ [Letter.l (m + 1) d] ++ Y) ≠ [] := by simp
      obtain ⟨μ⟩ := U3.sk_smoothIso X Y m d a (m + 1) hX hP hm hLA hLC (Or.inr ⟨had, rfl⟩)
      exact ⟨θ.trans (sc.trans (μ.trans (U2.realizeRecordIso ⟨_, hLC⟩ hneC).symm))⟩
  · -- the sign of the site is the writhe difference
    have h1 : (((realize ⟨_, hLA⟩).diagram.sign v.1 : SignType) : ℤ) = if a = d then 1 else -1 := by
      have := ι.sgn_eq v
      rw [hx] at this
      show (((realize ⟨_, hLA⟩).diagram.record.sgn v : SignType) : ℤ) = _
      rw [← this]
      exact U3.siteX_sgn X Y m d a hLA hX hP
    rw [h1, realize_writhe _ hne]
    unfold OWord.writheSyn
    simp only
    rw [u1_writheFrom_append₃ X _ Y hX (run_skein_A hm hP), U3.sk_writhe_factor m d a hP hm]
    rcases hCe with ⟨had, hCe⟩ | ⟨had, hCe⟩
    · subst hCe
      have hneC : (X ++ [Letter.l m d] ++ Y) ≠ [] := by simp
      rw [realize_writhe _ hneC]
      unfold OWord.writheSyn
      simp only
      subst had
      rw [u1_writheFrom_append₃ X _ Y hX (run_skein_Ctop hm hP), u1_writheFrom_cons
        (Letter.step_of_prefix (ℓ := .l m d) (by idxomega) (by idxomega) (Letter.act_l _ _ _)), u1_writheFrom_nil, u1_signBit_l]
      simp
    · subst hCe
      have hneC : (X ++ [Letter.l (m + 1) d] ++ Y) ≠ [] := by simp
      rw [realize_writhe _ hneC]
      unfold OWord.writheSyn
      simp only
      subst had
      have s : (Letter.l (m + 1) a).step (P ++ a :: L) = some (P ++ a :: a :: (!a) :: L) := by
        rw [show P ++ a :: L = (P ++ [a]) ++ L by simp,
          Letter.step_of_prefix (ℓ := .l (m + 1) a) (by idxomega) (by idxomega) (Letter.act_l _ _ _)]
        simp
      rw [u1_writheFrom_append₃ X _ Y hX (run_skein_Cbottom hm hP), u1_writheFrom_cons s, u1_writheFrom_nil,
        u1_signBit_l]
      simp

/-- LEAF (ng:cusp-skein "the unique compatible smoothing", FR-12): the interchange determines `C` — the two
principal words differ first at the cusp letter, which fixes `X`, `m`, `d`, `Y`; the through-strand bit is
read from `run X []`; the reverse-direction case is contradictory (`l (m+1) = l m'`, `l m = l (m'+1)`). -/
theorem skein_unique {A A' C C' : Word} (h : IsCuspSkein A A' C) (h' : IsCuspSkein A A' C') : C = C' := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact U3.skeinStep_unique h h'
  · exact (U3.skeinStep_not_both h h').elim
  · exact (U3.skeinStep_not_both h' h).elim
  · exact U3.skeinStep_unique h h'

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

/-- LEAF (ng:commutation, sm-3:1934-1936 "A deformation without a singular event preserves the records, D and
w: signs, cusp directions and cyclic attachments cannot change"): `D`.  Along a jointly smooth family inside
the class, the cusp set `{x' = 0}` is a covering of `[0,1]` (`x'' ≠ 0` at every zero, vertical tangencies
excluded), on which the discriminant `x''·det(γ'', γ''')` is continuous and nonzero. -/
theorem deform_downCount (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) :
    F.downCount = F'.downCount := sorry

/-- LEAF: the same for `w` (the transverse double points form a covering of `[0,1]`, no accumulation at a
semicubical cusp, `crossSign` continuous and nonzero). -/
theorem deform_writhe (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) :
    F.writhe = F'.writhe := sorry

/-- LEAF: the same for the records of the roundings, hence (sm-3:1936-1937 "Lemma rp:record-polynomial gives
scalar equality") the polynomial: the `Marking` of `F` transports along the family to a `Marking` of `F'`. -/
theorem deform_P (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) (S S' : Diagram)
    (hS : F.IsRounding S) (hS' : F'.IsRounding S') : P S = P S' := sorry

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
