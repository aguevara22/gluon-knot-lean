import DirectGLSSW.ExtendedReturnLocalCaps
import Mathlib.Data.Finset.Max

set_option autoImplicit false

namespace DirectGLSSW.ExtendedReturnArcGeometry
open DirectGLSSW ExtendedReturnLocalCaps

abbrev Point := PlanarPoint ℝ

/-- Explicit radius for a quadratic with nonzero constant term. -/
noncomputable def quadraticRadius (d₀ d₁ d₂ : ℝ) : ℝ :=
  min 1 (|d₀| / (2 * (1 + |d₁| + |d₂|)))

theorem quadraticRadius_pos (d₀ d₁ d₂ : ℝ) (h₀ : d₀ ≠ 0) :
    0  <  quadraticRadius d₀ d₁ d₂ := by
  apply lt_min (by norm_num)
  exact div_pos (abs_pos.mpr h₀) (by positivity)

theorem quadratic_ne_zero (d₀ d₁ d₂ ε : ℝ) (h₀ : d₀ ≠ 0)
    (hε : 0 ≤ ε) (hbound : ε  <  quadraticRadius d₀ d₁ d₂) :
    d₀ + ε * d₁ + ε ^ 2 * d₂ ≠ 0 := by
  have hsmall : ε  <  1 := lt_of_lt_of_le hbound (min_le_left _ _)
  have hfrac : ε  <  |d₀| / (2 * (1 + |d₁| + |d₂|)) :=
    lt_of_lt_of_le hbound (min_le_right _ _)
  have hden : 0  <  2 * (1 + |d₁| + |d₂|) := by positivity
  have hmul := (lt_div_iff₀ hden).mp hfrac
  have hsq : ε ^ 2 ≤ ε := by nlinarith
  have hsqmul := mul_le_mul_of_nonneg_right hsq (abs_nonneg d₂)
  have hpert : |ε * d₁ + ε ^ 2 * d₂|  <  |d₀| := by
    calc
      |ε * d₁ + ε ^ 2 * d₂| ≤ |ε * d₁| + |ε ^ 2 * d₂| := abs_add _ _
      _ = ε * |d₁| + ε ^ 2 * |d₂| := by rw [abs_mul, abs_mul, abs_of_nonneg hε, abs_of_nonneg (sq_nonneg ε)]
      _  <  |d₀| := by nlinarith [abs_nonneg d₁, abs_nonneg d₂, abs_pos.mpr h₀]
  intro hz
  have heq : ε * d₁ + ε ^ 2 * d₂ = -d₀ := by linarith
  rw [heq, abs_neg] at hpert
  exact (lt_irrefl _) hpert

/-- A concrete finite minimum, including one so it is defined for an empty family. -/
noncomputable def finiteRadius {ι : Type*} [Fintype ι] (r : ι → ℝ) : ℝ := by
  classical
  exact (insert 1 (Finset.univ.image r)).min' (Finset.insert_nonempty _ _)

theorem finiteRadius_pos {ι : Type*} [Fintype ι] (r : ι → ℝ)
    (hr : ∀ i, 0  <  r i) : 0  <  finiteRadius r := by
  classical
  unfold finiteRadius
  apply (Finset.lt_min'_iff _ _).mpr
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · norm_num
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hr i

theorem finiteRadius_le {ι : Type*} [Fintype ι] (r : ι → ℝ) (i : ι) :
    finiteRadius r ≤ r i := by
  classical
  unfold finiteRadius
  exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

noncomputable def affineWord {n : ℕ} (A B : Fin n → Point) (ε : ℝ) : Fin n → Point :=
  fun i => A i + ε • B i

noncomputable def detConstant {n : ℕ} (A : Fin n → Point) (a b c : Fin n) : ℝ :=
  planarDet (A b - A c) (A a - A c)
noncomputable def detLinear {n : ℕ} (A B : Fin n → Point) (a b c : Fin n) : ℝ :=
  planarDet (B b - B c) (A a - A c) + planarDet (A b - A c) (B a - B c)
noncomputable def detQuadratic {n : ℕ} (B : Fin n → Point) (a b c : Fin n) : ℝ :=
  planarDet (B b - B c) (B a - B c)

theorem affineWord_det {n : ℕ} (A B : Fin n → Point) (a b c : Fin n) (ε : ℝ) :
    planarDet (affineWord A B ε b - affineWord A B ε c)
        (affineWord A B ε a - affineWord A B ε c) =
      detConstant A a b c + ε * detLinear A B a b c + ε ^ 2 * detQuadratic B a b c := by
  simp [affineWord, detConstant, detLinear, detQuadratic, planarDet]
  ring

noncomputable def wordG1Radius {n : ℕ} (A B : Fin n → Point) : ℝ := by
  classical
  exact finiteRadius (fun t : Fin n × Fin n × Fin n =>
    if t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2 then
      quadraticRadius (detConstant A t.1 t.2.1 t.2.2)
        (detLinear A B t.1 t.2.1 t.2.2) (detQuadratic B t.1 t.2.1 t.2.2)
    else 1)

theorem wordG1Radius_pos {n : ℕ} (A B : Fin n → Point)
    (hA : cyclicNoncollinear A) : 0  <  wordG1Radius A B := by
  classical
  apply finiteRadius_pos
  intro t
  split_ifs with h
  · apply quadraticRadius_pos
    exact hA t.1 t.2.1 t.2.2 h.1 h.2.1 h.2.2
  · norm_num

theorem affineWord_G1 {n : ℕ} (A B : Fin n → Point)
    (hA : cyclicNoncollinear A) (ε : ℝ) (hε : 0 ≤ ε) (hbound : ε  <  wordG1Radius A B) :
    cyclicNoncollinear (affineWord A B ε) := by
  classical
  intro a b c hab hbc hac
  rw [affineWord_det]
  apply quadratic_ne_zero _ _ _ _ (hA a b c hab hbc hac) hε
  have hle := finiteRadius_le (fun t : Fin n × Fin n × Fin n =>
    if t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2 then
      quadraticRadius (detConstant A t.1 t.2.1 t.2.2)
        (detLinear A B t.1 t.2.1 t.2.2) (detQuadratic B t.1 t.2.1 t.2.2)
    else 1) (a,b,c)
  simpa [hab, hbc, hac, detConstant] using lt_of_lt_of_le hbound hle

/-- Explicit clearance from a fixed carrier for the whole added endpoint piece. -/
noncomputable def carrierRadius (C D ζ w : Point) : ℝ :=
  |planarDet (D-C) (ζ-C)| / (2 * (1 + |planarDet (D-C) w|))

theorem carrierRadius_pos (C D ζ w : Point) (h : planarDet (D-C) (ζ-C) ≠ 0) :
    0  <  carrierRadius C D ζ w := div_pos (abs_pos.mpr h) (by positivity)

theorem added_piece_avoids_carrier (C D ζ w : Point)
    (h : planarDet (D-C) (ζ-C) ≠ 0) (ε t : ℝ)
    (ht : 0 ≤ t) (htε : t ≤ ε) (hε : ε  <  carrierRadius C D ζ w) :
    planarDet (D-C) (ζ + t • w - C) ≠ 0 := by
  have hden : 0  <  2 * (1 + |planarDet (D-C) w|) := by positivity
  have hmul := (lt_div_iff₀ hden).mp hε
  have htprod := mul_le_mul_of_nonneg_right htε (abs_nonneg (planarDet (D-C) w))
  have hlt : |t * planarDet (D-C) w|  <  |planarDet (D-C) (ζ-C)| := by
    rw [abs_mul, abs_of_nonneg ht]
    nlinarith [abs_pos.mpr h, abs_nonneg (planarDet (D-C) w)]
  have heq : planarDet (D-C) (ζ + t • w - C) =
      planarDet (D-C) (ζ-C) + t * planarDet (D-C) w := by
    simp [planarDet]
    ring
  rw [heq]
  intro hz
  have hneg : t * planarDet (D-C) w = -planarDet (D-C) (ζ-C) := by linarith
  rw [hneg, abs_neg] at hlt
  exact (lt_irrefl _) hlt

/-- Extend the endpoint A away from its first neighbour B. -/
noncomputable def extendBack (A B : Point) (ε : ℝ) : Point := A + ε • (A-B)

theorem extended_first_decomposition (A B X : Point) (ε : ℝ) (hε : 0 ≤ ε)
    (hX : OnOpenSegment (extendBack A B ε) B X) :
    OnOpenSegment A B X ∨ ∃ t : ℝ, 0 ≤ t ∧ t ≤ ε ∧ X = A + t • (A-B) := by
  obtain ⟨s, hs0, hs1, rfl⟩ := hX
  let r := (1+ε)*s-ε
  have hid : affinePoint (extendBack A B ε) B s = affinePoint A B r := by
    ext <;> simp [affinePoint, extendBack, r] <;> ring
  have hr1 : r  <  1 := by dsimp [r]; nlinarith [mul_pos (by linarith : 0  <  1+ε) (sub_pos.mpr hs1)]
  by_cases hr0 : 0  <  r
  · exact Or.inl ⟨r, hr0, hr1, hid⟩
  · right
    refine ⟨-r, by linarith, ?_, ?_⟩
    · dsimp [r]; nlinarith [mul_nonneg (by linarith : 0 ≤ 1+ε) (le_of_lt hs0)]
    · rw [hid]
      ext <;> simp [affinePoint] <;> ring

theorem extended_first_carrier (A B X : Point) (ε : ℝ)
    (hX : OnOpenSegment (extendBack A B ε) B X) : planarDet (B-A) (X-A) = 0 := by
  obtain ⟨s, _, _, rfl⟩ := hX
  simp [affinePoint, extendBack, planarDet]
  ring

theorem extended_first_intersection_pullback (A B C D X : Point)
    (hbase : planarDet (D-C) (A-C) ≠ 0) (ε : ℝ) (hε : 0 ≤ ε)
    (hbound : ε  <  carrierRadius C D A (A-B))
    (hX : OnOpenSegment (extendBack A B ε) B X)
    (hcarrier : planarDet (D-C) (X-C) = 0) : OnOpenSegment A B X := by
  rcases extended_first_decomposition A B X ε hε hX with h | ⟨t, ht, htε, rfl⟩
  · exact h
  · exact False.elim ((added_piece_avoids_carrier C D A (A-B) hbase ε t ht htε hbound) hcarrier)

theorem extended_last_intersection_pullback (A B C D X : Point)
    (hbase : planarDet (D-C) (B-C) ≠ 0) (ε : ℝ) (hε : 0 ≤ ε)
    (hbound : ε  <  carrierRadius C D B (B-A))
    (hX : OnOpenSegment A (extendBack B A ε) X)
    (hcarrier : planarDet (D-C) (X-C) = 0) : OnOpenSegment A B X := by
  exact onOpenSegment_symm (extended_first_intersection_pullback B A C D X hbase ε hε hbound
    (onOpenSegment_symm hX) hcarrier)

abbrev zeroIndex {n : ℕ} (hn : 3 ≤ n) : Fin n := ⟨0, by omega⟩
abbrev firstIndex {n : ℕ} (hn : 3 ≤ n) : Fin n := ⟨1, by omega⟩
abbrev lastIndex {n : ℕ} (hn : 3 ≤ n) : Fin n := ⟨n-1, by omega⟩
abbrev penultimateIndex {n : ℕ} (hn : 3 ≤ n) : Fin n := ⟨n-2, by omega⟩

/-- Only the two endpoints of the opened return word move. -/
noncomputable def endpointVelocity {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point) (i : Fin n) : Point :=
  if i.val = 0 then P (zeroIndex hn) - P (firstIndex hn)
  else if i.val+1 = n then P (lastIndex hn) - P (penultimateIndex hn) else 0

noncomputable def extendedWord {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point) (ε : ℝ) : Fin n → Point :=
  affineWord P (endpointVelocity hn P) ε

theorem extendedWord_first {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point) (ε : ℝ) :
    extendedWord hn P ε (zeroIndex hn) = extendBack (P (zeroIndex hn)) (P (firstIndex hn)) ε := by
  simp [extendedWord, affineWord, endpointVelocity, extendBack]

theorem extendedWord_last {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point) (ε : ℝ) :
    extendedWord hn P ε (lastIndex hn) = extendBack (P (lastIndex hn)) (P (penultimateIndex hn)) ε := by
  have hn0 : n-1 ≠ 0 := by omega
  have hn1 : n-1+1 = n := by omega
  simp [extendedWord, affineWord, endpointVelocity, extendBack, hn0, hn1]

theorem extendedWord_interior {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point) (ε : ℝ)
    (i : Fin n) (hi : 0  <  i.val) (hi' : i.val+1  <  n) : extendedWord hn P ε i = P i := by
  simp [extendedWord, affineWord, endpointVelocity, ne_of_gt hi, ne_of_lt hi']

theorem return_successor_eq {n : ℕ} (e : Fin n) (he : e.val+1  <  n) :
    cyclicSuccessor e = ⟨e.val+1, he⟩ := by
  apply Fin.ext
  simp [cyclicSuccessor, cyclicVertexIndex, Nat.mod_eq_of_lt he]

/-- Every extended return edge stays on its original carrier. The omitted closing
edge is intentionally outside the assertion. -/
theorem extended_return_carrier {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (ε : ℝ) (e : Fin n) (he : e.val+1  <  n) (X : Point)
    (hX : edgeInterior (extendedWord hn P ε) e X) :
    planarDet (cyclicTangent P e) (X-P e) = 0 := by
  have hs := return_successor_eq e he
  by_cases hfirst : e.val = 0
  · have heq : e = (zeroIndex hn) := Fin.ext hfirst
    subst e
    have hs' : cyclicSuccessor ((zeroIndex hn) : Fin n) = (firstIndex hn) := by
      simpa using hs
    change OnOpenSegment _ _ X at hX
    rw [hs', extendedWord_first, extendedWord_interior hn P ε _ (by norm_num) (by change 1+1 < n; omega)] at hX
    simpa [cyclicTangent, hs'] using extended_first_carrier _ _ X ε hX
  · by_cases hlast : e.val+2 = n
    · have heq : e = (penultimateIndex hn) := by apply Fin.ext; simp only [penultimateIndex, Fin.val_mk]; omega
      subst e
      have hs' : cyclicSuccessor ((penultimateIndex hn) : Fin n) = (lastIndex hn) := by
        apply Fin.ext
        rw [hs]
        simp only [zeroIndex, firstIndex, lastIndex, penultimateIndex, Fin.val_mk]
        omega
      change OnOpenSegment _ _ X at hX
      rw [hs', extendedWord_last, extendedWord_interior hn P ε _ (by omega) (by omega)] at hX
      have h := extended_first_carrier _ _ X ε (onOpenSegment_symm hX)
      dsimp [cyclicTangent]
      rw [hs']
      have hid : planarDet (P (lastIndex hn)-P (penultimateIndex hn)) (X-P (penultimateIndex hn)) =
          -planarDet (P (penultimateIndex hn)-P (lastIndex hn)) (X-P (lastIndex hn)) := by
        simp [planarDet]; ring
      rw [hid, h, neg_zero]
    · have hi : 0  <  e.val := by omega
      have hi' : e.val+1  <  n := he
      have hs0 : 0  <  (cyclicSuccessor e).val := by rw [hs]; simp
      have hs1 : (cyclicSuccessor e).val+1  <  n := by rw [hs]; simp only [zeroIndex, firstIndex, lastIndex, penultimateIndex, Fin.val_mk]; omega
      change OnOpenSegment _ _ X at hX
      rw [extendedWord_interior hn P ε e hi hi', extendedWord_interior hn P ε _ hs0 hs1] at hX
      exact onOpenSegment_carrier_det_zero hX

/-- Explicit minimum of carrier clearances at one original vertex. -/
noncomputable def vertexClearanceRadius {n : ℕ} (P : Fin n → Point) (v : Fin n) (w : Point) : ℝ := by
  classical
  exact finiteRadius (fun e : Fin n => if v ≠ e ∧ v ≠ cyclicSuccessor e then
    carrierRadius (P e) (P (cyclicSuccessor e)) (P v) w else 1)

theorem vertexClearanceRadius_pos {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : cyclicNoncollinear P) (v : Fin n) (w : Point) : 0  <  vertexClearanceRadius P v w := by
  classical
  apply finiteRadius_pos
  intro e
  split_ifs with h
  · apply carrierRadius_pos
    exact cyclic_vertex_carrier_det_ne_zero hn P hP e v h.1 h.2
  · norm_num

theorem vertexClearanceRadius_le {n : ℕ} (P : Fin n → Point) (v : Fin n) (w : Point)
    (e : Fin n) (hve : v ≠ e) (hvs : v ≠ cyclicSuccessor e) :
    vertexClearanceRadius P v w ≤ carrierRadius (P e) (P (cyclicSuccessor e)) (P v) w := by
  classical
  have h := finiteRadius_le (fun e : Fin n => if v ≠ e ∧ v ≠ cyclicSuccessor e then
    carrierRadius (P e) (P (cyclicSuccessor e)) (P v) w else 1) e
  simpa [hve, hvs] using h

noncomputable def returnClearanceRadius {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point) : ℝ :=
  min (vertexClearanceRadius P (zeroIndex hn) (P (zeroIndex hn)-P (firstIndex hn)))
      (vertexClearanceRadius P (lastIndex hn) (P (lastIndex hn)-P (penultimateIndex hn)))

theorem returnClearanceRadius_pos {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : cyclicNoncollinear P) : 0  <  returnClearanceRadius hn P :=
  lt_min (vertexClearanceRadius_pos hn P hP _ _) (vertexClearanceRadius_pos hn P hP _ _)

/-- A crossing of two distinct extended return edges is already in the
original interior of either edge. No G2 assumption is used in this step. -/
theorem extended_intersection_pullback {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : cyclicNoncollinear P) (ε : ℝ) (hε : 0 ≤ ε)
    (hbound : ε  <  returnClearanceRadius hn P)
    (e f : Fin n) (he : e.val+1 < n) (hf : f.val+1 < n) (hef : e ≠ f) (X : Point)
    (hXe : edgeInterior (extendedWord hn P ε) e X)
    (hXf : edgeInterior (extendedWord hn P ε) f X) : edgeInterior P e X := by
  have hcarrier := extended_return_carrier hn P ε f hf X hXf
  have hs := return_successor_eq e he
  have hsf := return_successor_eq f hf
  by_cases hfirst : e.val = 0
  · have heq : e = (zeroIndex hn) := Fin.ext hfirst
    subst e
    have hs' : cyclicSuccessor ((zeroIndex hn) : Fin n) = (firstIndex hn) := by simpa using hs
    have hvs : ((zeroIndex hn) : Fin n) ≠ cyclicSuccessor f := by
      intro h; have hv := congrArg Fin.val h; rw [hsf] at hv; simp at hv
    have hdet := cyclic_vertex_carrier_det_ne_zero hn P hP f (zeroIndex hn) hef hvs
    have hrad := vertexClearanceRadius_le P (zeroIndex hn) (P (zeroIndex hn)-P (firstIndex hn)) f hef hvs
    have hb : ε  <  carrierRadius (P f) (P (cyclicSuccessor f)) (P (zeroIndex hn))
        (P (zeroIndex hn)-P (firstIndex hn)) :=
      lt_of_lt_of_le (lt_of_lt_of_le hbound (min_le_left _ _)) hrad
    change OnOpenSegment _ _ X at hXe ⊢
    rw [hs', extendedWord_first, extendedWord_interior hn P ε _ (by norm_num) (by change 1+1 < n; omega)] at hXe
    rw [hs']
    exact extended_first_intersection_pullback _ _ _ _ X hdet ε hε hb hXe hcarrier
  · by_cases hlast : e.val+2=n
    · have heq : e = (penultimateIndex hn) := by apply Fin.ext; simp only [penultimateIndex, Fin.val_mk]; omega
      subst e
      have hs' : cyclicSuccessor ((penultimateIndex hn) : Fin n) = (lastIndex hn) := by
        apply Fin.ext; rw [hs]; simp only [zeroIndex, firstIndex, lastIndex, penultimateIndex, Fin.val_mk]; omega
      have hve : ((lastIndex hn) : Fin n) ≠ f := by
        intro h; have hv := congrArg Fin.val h; simp only [zeroIndex, firstIndex, lastIndex, penultimateIndex, Fin.val_mk] at hv; omega
      have hvs : ((lastIndex hn) : Fin n) ≠ cyclicSuccessor f := by
        intro h; have hv := congrArg Fin.val h; rw [hsf] at hv; simp only [zeroIndex, firstIndex, lastIndex, penultimateIndex, Fin.val_mk] at hv
        apply hef; apply Fin.ext; simp only [zeroIndex, firstIndex, lastIndex, penultimateIndex, Fin.val_mk]; omega
      have hdet := cyclic_vertex_carrier_det_ne_zero hn P hP f (lastIndex hn) hve hvs
      have hrad := vertexClearanceRadius_le P (lastIndex hn) (P (lastIndex hn)-P (penultimateIndex hn)) f hve hvs
      have hb : ε  <  carrierRadius (P f) (P (cyclicSuccessor f)) (P (lastIndex hn))
          (P (lastIndex hn)-P (penultimateIndex hn)) :=
        lt_of_lt_of_le (lt_of_lt_of_le hbound (min_le_right _ _)) hrad
      change OnOpenSegment _ _ X at hXe ⊢
      rw [hs', extendedWord_last, extendedWord_interior hn P ε _ (by omega) (by omega)] at hXe
      rw [hs']
      exact extended_last_intersection_pullback _ _ _ _ X hdet ε hε hb hXe hcarrier
    · have hi : 0  <  e.val := by omega
      have hs0 : 0  <  (cyclicSuccessor e).val := by rw [hs]; simp
      have hs1 : (cyclicSuccessor e).val+1  <  n := by rw [hs]; simp only [zeroIndex, firstIndex, lastIndex, penultimateIndex, Fin.val_mk]; omega
      change OnOpenSegment _ _ X at hXe
      rw [extendedWord_interior hn P ε e hi he, extendedWord_interior hn P ε _ hs0 hs1] at hXe
      exact hXe

theorem extended_return_G2 {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : CyclicGeneric P) (ε : ℝ) (hε : 0 ≤ ε) (hbound : ε  <  returnClearanceRadius hn P)
    (e f g : Fin n) (he : e.val+1 < n) (hf : f.val+1 < n) (hg : g.val+1 < n)
    (hef : e ≠ f) (hfg : f ≠ g) (heg : e ≠ g) (X : Point) :
    ¬(edgeInterior (extendedWord hn P ε) e X ∧ edgeInterior (extendedWord hn P ε) f X ∧
      edgeInterior (extendedWord hn P ε) g X) := by
  rintro ⟨hXe, hXf, hXg⟩
  have he' := extended_intersection_pullback hn P hP.g1 ε hε hbound e f he hf hef X hXe hXf
  have hf' := extended_intersection_pullback hn P hP.g1 ε hε hbound f e hf he hef.symm X hXf hXe
  have hg' := extended_intersection_pullback hn P hP.g1 ε hε hbound g e hg he heg.symm X hXg hXe
  exact hP.g2 e f g X hef hfg heg ⟨he', hf', hg'⟩

theorem original_interior_off_line {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : cyclicNoncollinear P) (hzero : (P (zeroIndex hn)).2 = 0)
    (hlast : (P (lastIndex hn)).2 = 0) (i : Fin n) (hi : 0  <  i.val) (hi' : i.val+1 < n) :
    (P i).2 ≠ 0 := by
  have h0L : zeroIndex hn ≠ lastIndex hn := by
    intro h; have hv := congrArg Fin.val h; simp only [zeroIndex, lastIndex, Fin.val_mk] at hv; omega
  have hLi : lastIndex hn ≠ i := by
    intro h; have hv := congrArg Fin.val h; simp only [lastIndex, Fin.val_mk] at hv; omega
  have h0i : zeroIndex hn ≠ i := by
    intro h; have hv := congrArg Fin.val h; simp only [zeroIndex, Fin.val_mk] at hv; omega
  have h := hP (zeroIndex hn) (lastIndex hn) i h0L hLi h0i
  intro hi0
  apply h
  simp [planarDet, hzero, hlast, hi0]

/-- Every fixed vertex of the extended arc is off the height-zero return line.
This needs only positive epsilon, with no smallness condition. -/
theorem extendedWord_off_line {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : cyclicNoncollinear P) (hzero : (P (zeroIndex hn)).2 = 0)
    (hlast : (P (lastIndex hn)).2 = 0) (ε : ℝ) (hε : 0  <  ε) (i : Fin n) :
    (extendedWord hn P ε i).2 ≠ 0 := by
  by_cases hi0 : i.val=0
  · have hi : i = zeroIndex hn := Fin.ext hi0
    rw [hi, extendedWord_first]
    have hfirst := original_interior_off_line hn P hP hzero hlast (firstIndex hn)
      (by norm_num) (by change 1+1 < n; omega)
    simpa [extendBack, hzero] using mul_ne_zero (ne_of_gt hε) (neg_ne_zero.mpr hfirst)
  · by_cases hiL : i.val+1=n
    · have hi : i = lastIndex hn := by apply Fin.ext; change i.val=n-1; omega
      rw [hi, extendedWord_last]
      have hprev := original_interior_off_line hn P hP hzero hlast (penultimateIndex hn)
        (by change 0 < n-2; omega) (by change n-2+1 < n; omega)
      simpa [extendBack, hlast] using mul_ne_zero (ne_of_gt hε) (neg_ne_zero.mpr hprev)
    · have hi : 0 < i.val := by omega
      have hi' : i.val+1 < n := by have := i.isLt; omega
      rw [extendedWord_interior hn P ε i hi hi']
      exact original_interior_off_line hn P hP hzero hlast i hi hi'

/-- The explicit positive geometric epsilon bound combines G1 stability and
clearance of the two new terminal pieces from all nonincident carriers. -/
noncomputable def geometricRadius {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point) : ℝ :=
  min (wordG1Radius P (endpointVelocity hn P)) (returnClearanceRadius hn P)

theorem geometricRadius_pos {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : cyclicNoncollinear P) : 0  <  geometricRadius hn P :=
  lt_min (wordG1Radius_pos P _ hP) (returnClearanceRadius_pos hn P hP)

/-- Total natural-index arc: moving basepoint has label zero; the n extended
vertices have labels 1 through n. Values after n are never used. -/
noncomputable def arcFromWord {n : ℕ} (u : Point) (E : Fin n → Point) (k : ℕ) : Point :=
  if hk : 0  <  k ∧ k ≤ n then E ⟨k-1, by omega⟩ else u

theorem arcFromWord_zero {n : ℕ} (u : Point) (E : Fin n → Point) : arcFromWord u E 0 = u := by
  simp [arcFromWord]

theorem arcFromWord_positive {n : ℕ} (u : Point) (E : Fin n → Point) (k : ℕ)
    (hk : 0 < k) (hkn : k≤n) : arcFromWord u E k = E ⟨k-1, by omega⟩ := by
  simp [arcFromWord, hk, hkn]

theorem positiveWord_arcFromWord {n : ℕ} (u : Point) (E : Fin n → Point) :
    positiveWord (arcFromWord u E) n = E := by
  funext i
  simp [positiveWord, arcFromWord, i.isLt, Nat.lt_iff_add_one_le]

theorem arcFromWord_positive_G1 {n : ℕ} (u : Point) (E : Fin n → Point)
    (hE : cyclicNoncollinear E) (i j k : ℕ) (hi : 0 < i) (hij : i < j) (hjk : j < k) (hkn : k≤n) :
    polygonHDet (arcFromWord u E) i j k ≠ 0 := by
  have hj : 0 < j := by omega
  have hk : 0 < k := by omega
  dsimp [polygonHDet]
  rw [arcFromWord_positive u E i hi (by omega), arcFromWord_positive u E j hj (by omega),
    arcFromWord_positive u E k hk hkn]
  apply hE
  all_goals intro h; have hv := congrArg Fin.val h; simp only [Fin.val_mk] at hv; omega

noncomputable def extendedArc {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point) (ε : ℝ) : ℕ → Point :=
  arcFromWord (P (zeroIndex hn)) (extendedWord hn P ε)

theorem extendedArc_zero {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point) (ε : ℝ) :
    extendedArc hn P ε 0 = P (zeroIndex hn) := arcFromWord_zero _ _

theorem extendedArc_first {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point) (ε : ℝ) :
    extendedArc hn P ε 1 = extendBack (P (zeroIndex hn)) (P (firstIndex hn)) ε := by
  rw [extendedArc, arcFromWord_positive _ _ 1 (by norm_num) (by omega)]
  exact extendedWord_first hn P ε

theorem extendedArc_last {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point) (ε : ℝ) :
    extendedArc hn P ε n = extendBack (P (lastIndex hn)) (P (penultimateIndex hn)) ε := by
  rw [extendedArc, arcFromWord_positive _ _ n (by omega) (le_refl _)]
  exact extendedWord_last hn P ε

theorem extendedArc_interior {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point) (ε : ℝ)
    (i : Fin n) (hi : 0 < i.val) (hi' : i.val+1 < n) : extendedArc hn P ε (i.val+1) = P i := by
  rw [extendedArc, arcFromWord_positive _ _ (i.val+1) (by omega) (by omega)]
  simpa using extendedWord_interior hn P ε i hi hi'

/-- Concrete endpoint extension supplies the exact local-cap hypothesis from
original G1–G2, for every epsilon below the displayed finite geometric bound.
Neither distinct critical roots nor selected-cap G1 is asserted or assumed. -/
theorem extendedArc_localCaps {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : CyclicGeneric P) (hzero : (P (zeroIndex hn)).2 = 0)
    (hlast : (P (lastIndex hn)).2 = 0) (ε : ℝ) (hε : 0 < ε)
    (hbound : ε  <  geometricRadius hn P) (t : ℝ) :
    ∃ δ : ℝ, 0  <  δ ∧ ∀ s : ℝ, 0  <  |s| → |s|  <  δ →
      ∀ a b : Fin n, a.val  <  b.val →
        CyclicGeneric (GlobalCapEntry.lineCapCore
          (CapCrossingEvent.horizontalMove (extendedArc hn P ε) (t+s)) a b) := by
  have hG1 : cyclicNoncollinear (extendedWord hn P ε) :=
    affineWord_G1 P _ hP.g1 ε (le_of_lt hε) (lt_of_lt_of_le hbound (min_le_left _ _))
  have hclear : ε  <  returnClearanceRadius hn P := lt_of_lt_of_le hbound (min_le_right _ _)
  apply localCaps_of_openArcG2 (extendedArc hn P ε) n hn
  · simpa [extendedArc, arcFromWord_zero] using hzero
  · intro i hi hin
    rw [extendedArc, arcFromWord_positive _ _ i hi hin]
    exact extendedWord_off_line hn P hP.g1 hzero hlast ε hε _
  · intro i j hi hin hj hjn hij heq
    rw [extendedArc, arcFromWord_positive _ _ i hi hin, arcFromWord_positive _ _ j hj hjn] at heq
    have hidx := cyclicNoncollinear_injective hn _ hG1 heq
    have hv := congrArg Fin.val hidx
    simp only [Fin.val_mk] at hv
    omega
  · exact arcFromWord_positive_G1 _ _ hG1
  · unfold OpenArcG2
    rw [extendedArc, positiveWord_arcFromWord]
    exact fun i j k hi hj hk hij hjk hik X => extended_return_G2 hn P hP ε
      (le_of_lt hε) hclear i j k hi hj hk hij hjk hik X































end DirectGLSSW.ExtendedReturnArcGeometry
