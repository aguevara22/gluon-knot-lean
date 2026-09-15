import SM.SoftGenericLemma
import SM.SoftSourceSectors
import SM.RotationTheorem
import SM.AngleScaling

/-! Towards lem:soft-rotation (sm-5-transport.tex:317). Written 2026-09-13 by a Claude Code prover subagent of the pod
executor (workflow prove-transport-lane / prove:soft-rotation), checked with `lake env lean` (sorry-free, standard axioms) and
ported verbatim from work/drafts/SoftRotation.lean (only this header added and #print lines removed). -/

/-! Source lem:soft-rotation (reference/SM/sm-5-transport.tex:317, frame SM15): rotation of a
soft insertion. Main declaration: `SM.soft_rotation`.

Notation (def:soft, lem:soft-generic). `P` generic (def:generic), `j` a vertex, `q` admissible
(`SoftAdmissible P j q`), `softInsertion P j q ε = P_ε = P^{(j,q)}_ε` with the old vertex `μ_k`
at the label `softOldIndex j k` and the new vertex `μ_j + ε q` at `softNewIndex j`;
`edge P k = ℓ_k`, so `u = edge P (j-1) = ℓ_{j-1}`, `v = edge P j = ℓ_j`;
`softAttachmentMinus P j q = χ_- = -sgn det(ℓ_{j-1}, q)`,
`softAttachmentPlus P j q = χ_+ = -sgn det(q, ℓ_j)`, `turn P j = τ_j(P)`;
`rotationNumber = rot = Σ principalTurn / 2π` (def:regular, lem:rot), `principalAngle u v =
Arg(v/u) ∈ (-π, π)` the principal turn from `u` to `v`. The sectors are those of
lem:soft-generic (iv): same-sign `χ_- = χ_+ = -τ_j`, mixed `χ_- ≠ χ_+`, loop `χ_- = χ_+ = τ_j`.
"ε small (lem:soft-generic)" is rendered as: there is `ε₀ > 0` such that for every
`0 < ε < ε₀` the polygon `P_ε` is generic and the rotation identities hold; the stronger form
`soft_rotation_of_regular_interval` gives the identities on every interval `(0, δ)` on which
the family is regular (in particular on the whole interval of lem:soft-generic).
The "open cone of directions strictly between `u` and `v`" is `openCone u v =
{a • u + b • v | a, b > 0}` (the wedge of the turn: `u, v` are independent since `τ_j ≠ 0`),
the loop cone is `openCone (-u) (-v)`, and the mixed sector is the complement of the
(topological) closures of these two cones. -/

namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-! ### Elementary determinant and cone facts -/

/-- The open cone of directions strictly between `u` and `v`: `{a u + b v | a, b > 0}`. -/
def openCone (u v : Plane) : Set Plane :=
  {x | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ x = a • u + b • v}

theorem mem_openCone (u v x : Plane) :
    x ∈ openCone u v ↔ ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ x = a • u + b • v := Iff.rfl

theorem det_neg_left (u v : Plane) : det (-u) v = -det u v := by
  simp [det]; ring

theorem det_neg_right (u v : Plane) : det u (-v) = -det u v := by
  simp [det]; ring

theorem det_neg_neg (u v : Plane) : det (-u) (-v) = det u v := by
  simp [det]

theorem det_add_smul_right (u v : Plane) (a b : ℝ) :
    det u (a • u + b • v) = b * det u v := by
  simp [det]; ring

theorem det_add_smul_left (u v : Plane) (a b : ℝ) :
    det (a • u + b • v) v = a * det u v := by
  simp [det]; ring

/-- Cramer's rule in the plane. -/
theorem det_cramer (u v q : Plane) : det u v • q = det q v • u + det u q • v := by
  ext <;> simp [det] <;> ring

theorem continuous_det_left (u : Plane) : Continuous (fun x : Plane => det u x) := by
  unfold det; fun_prop

theorem continuous_det_right (v : Plane) : Continuous (fun x : Plane => det x v) := by
  unfold det; fun_prop

theorem regularPair_of_det_ne_zero {u v : Plane} (h : det u v ≠ 0) : RegularPair u v := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl; exact h (by simp [det])
  · rintro rfl; exact h (by simp [det])
  · rintro ⟨r, _, rfl⟩; exact h (det_smul_self u r)

theorem signType_mul_eq_one_iff (a b : SignType) (hb : b ≠ 0) : a * b = 1 ↔ a = b := by
  revert a b; decide

theorem sign_eq_sign_iff_mul_pos {x y : ℝ} (hy : y ≠ 0) :
    SignType.sign x = SignType.sign y ↔ 0 < x * y := by
  rw [← sign_eq_one_iff, sign_mul]
  exact (signType_mul_eq_one_iff _ _ (sign_ne_zero.mpr hy)).symm

theorem mem_openCone_iff {u v : Plane} (huv : det u v ≠ 0) (q : Plane) :
    q ∈ openCone u v ↔ 0 < det u q * det u v ∧ 0 < det q v * det u v := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    rw [det_add_smul_right, det_add_smul_left, mul_assoc, mul_assoc]
    exact ⟨mul_pos hb (mul_self_pos.mpr huv), mul_pos ha (mul_self_pos.mpr huv)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨det q v / det u v, det u q / det u v, div_pos_iff.mpr (mul_pos_iff.mp h2),
      div_pos_iff.mpr (mul_pos_iff.mp h1), ?_⟩
    calc q = (det u v)⁻¹ • (det u v • q) := by
            rw [smul_smul, inv_mul_cancel₀ huv, one_smul]
      _ = (det q v / det u v) • u + (det u q / det u v) • v := by
            rw [det_cramer, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]

/-- The closure of the open cone lies in the closed cone given by the two weak determinant
inequalities. -/
theorem closure_openCone_subset (u v : Plane) :
    closure (openCone u v) ⊆ {x | 0 ≤ det u x * det u v ∧ 0 ≤ det x v * det u v} := by
  apply closure_minimal
  · rintro x ⟨a, b, ha, hb, rfl⟩
    show 0 ≤ det u (a • u + b • v) * det u v ∧ 0 ≤ det (a • u + b • v) v * det u v
    rw [det_add_smul_right, det_add_smul_left, mul_assoc, mul_assoc]
    exact ⟨mul_nonneg hb.le (mul_self_nonneg _), mul_nonneg ha.le (mul_self_nonneg _)⟩
  · exact (isClosed_le continuous_const ((continuous_det_left u).mul continuous_const)).inter
      (isClosed_le continuous_const ((continuous_det_right v).mul continuous_const))

/-- Off the four boundary rays, membership in the closure of the open cone is membership in
the open cone. -/
theorem mem_closure_openCone_iff {u v q : Plane} (huv : det u v ≠ 0)
    (h1 : det u q ≠ 0) (h2 : det q v ≠ 0) :
    q ∈ closure (openCone u v) ↔ q ∈ openCone u v := by
  constructor
  · intro hq
    obtain ⟨hw1, hw2⟩ := closure_openCone_subset u v hq
    exact (mem_openCone_iff huv q).mpr
      ⟨hw1.lt_of_ne (mul_ne_zero h1 huv).symm, hw2.lt_of_ne (mul_ne_zero h2 huv).symm⟩
  · exact fun hq => subset_closure hq

/-! ### Labels of the soft insertion -/

theorem softOldIndex_pred (j k : ZMod n) (hk : k - 1 ≠ j) :
    softOldIndex j k - 1 = softOldIndex j (k - 1) := by
  have h := softOldIndex_next j (k - 1) hk
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem softOldIndex_succ_pred (j : ZMod n) :
    softOldIndex j (j + 1) - 1 = softNewIndex j := by
  rw [← softNewIndex_next, add_sub_cancel_right]

theorem softNewIndex_pred (j : ZMod n) : softNewIndex j - 1 = softOldIndex j j := by
  rw [← softOldIndex_attachment_next, add_sub_cancel_right]

theorem soft_univ_eq (j : ZMod n) :
    (Finset.univ : Finset (ZMod (n + 1))) =
      insert (softNewIndex j) (Finset.univ.image (softOldIndex j)) := by
  classical
  ext a
  constructor
  · intro _
    rcases soft_indices_exhaust j a with ha | ⟨k, hk⟩
    · exact Finset.mem_insert.mpr (Or.inl ha)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk.symm⟩))
  · intro _
    exact Finset.mem_univ a

theorem softNewIndex_not_mem_image (j : ZMod n) :
    softNewIndex j ∉ Finset.univ.image (softOldIndex j) := by
  classical
  intro h
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
  exact softOldIndex_ne_new j k hk

/-- A sum over the labels of `P_ε` is the new-label term plus the sum over the old labels. -/
theorem sum_soft_indices {A : Type*} [AddCommMonoid A] (j : ZMod n) (f : ZMod (n + 1) → A) :
    (∑ a : ZMod (n + 1), f a) = f (softNewIndex j) + ∑ k : ZMod n, f (softOldIndex j k) := by
  classical
  rw [soft_univ_eq j, Finset.sum_insert (softNewIndex_not_mem_image j),
    Finset.sum_image (fun _ _ _ _ he => softOldIndex_injective j he)]

/-! ### Principal turns of the soft insertion -/

/-- Every old corner other than `j` and its successor keeps its principal turn. -/
theorem principalTurn_softInsertion_old (P : LabelledTuple n) (j k : ZMod n) (q : Plane)
    (ε : ℝ) (hk : k ≠ j) (hk1 : k ≠ j + 1) :
    principalTurn (softInsertion P j q ε) (softOldIndex j k) = principalTurn P k := by
  have hp : k - 1 ≠ j := fun h => hk1 (by rw [← h, sub_add_cancel])
  rw [principalTurn, softOldIndex_pred j k hp, edge_softInsertion_old P j (k - 1) q ε hp,
    edge_softInsertion_old P j k q ε hk, principalTurn]

/-- The turn at `μ_j` is `α = Arg(q/u)`, independent of `ε > 0`. -/
theorem principalTurn_softInsertion_soft (hn : 3 ≤ n) (P : LabelledTuple n) (j : ZMod n)
    (q : Plane) {ε : ℝ} (hε : 0 < ε) :
    principalTurn (softInsertion P j q ε) (softOldIndex j j) =
      principalAngle (edge P (j - 1)) q := by
  have : Fact (1 < n) := ⟨by omega⟩
  have hj : j - 1 ≠ j := by
    intro h
    have h1 : (1 : ZMod n) = 0 := by linear_combination -h
    exact one_ne_zero h1
  rw [principalTurn, softOldIndex_pred j j hj, edge_softInsertion_old P j (j - 1) q ε hj,
    edge_softInsertion_soft]
  have h := principalAngle_smul one_pos hε (edge P (j - 1)) q
  rwa [one_smul] at h

/-- The turn at the new vertex is `β_ε = Arg((v - ε q)/q)`. -/
theorem principalTurn_softInsertion_new (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    {ε : ℝ} (hε : 0 < ε) :
    principalTurn (softInsertion P j q ε) (softNewIndex j) =
      principalAngle q (edge P j - ε • q) := by
  rw [principalTurn, softNewIndex_pred, edge_softInsertion_soft, edge_softInsertion_return]
  have h := principalAngle_smul hε one_pos q (edge P j - ε • q)
  rwa [one_smul] at h

/-- The turn at the successor vertex has incoming direction `v - ε q`. -/
theorem principalTurn_softInsertion_succ (hn : 3 ≤ n) (P : LabelledTuple n) (j : ZMod n)
    (q : Plane) (ε : ℝ) :
    principalTurn (softInsertion P j q ε) (softOldIndex j (j + 1)) =
      principalAngle (edge P j - ε • q) (edge P (j + 1)) := by
  have : Fact (1 < n) := ⟨by omega⟩
  have h1 : j + 1 ≠ j := by
    intro h
    have h1 : (1 : ZMod n) = 0 := by linear_combination h
    exact one_ne_zero h1
  rw [principalTurn, softOldIndex_succ_pred, edge_softInsertion_return,
    edge_softInsertion_old P j (j + 1) q ε h1]

/-- `β_ε → β_0 = Arg(v/q)` as `ε → 0⁺`. -/
theorem tendsto_principalTurn_softInsertion_new (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (hqv : det q (edge P j) ≠ 0) :
    Tendsto (fun ε : ℝ => principalTurn (softInsertion P j q ε) (softNewIndex j)) (𝓝[>] 0)
      (𝓝 (principalAngle q (edge P j))) := by
  have hc : ContinuousAt (fun ε : ℝ => principalAngle q (edge P j - ε • q)) 0 := by
    apply continuousAt_principalAngle (u := fun _ => q) (v := fun ε : ℝ => edge P j - ε • q)
    · exact continuousAt_const
    · fun_prop
    · simpa using regularPair_of_det_ne_zero hqv
  have ht := hc.tendsto
  simp only [zero_smul, sub_zero] at ht
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (principalTurn_softInsertion_new P j q hε).symm

/-- The successor turn converges to its old value: the old corner is regular. -/
theorem tendsto_principalTurn_softInsertion_succ (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Regular P) (j : ZMod n) (q : Plane) :
    Tendsto (fun ε : ℝ => principalTurn (softInsertion P j q ε) (softOldIndex j (j + 1)))
      (𝓝 0) (𝓝 (principalTurn P (j + 1))) := by
  have hc : ContinuousAt (fun ε : ℝ => principalAngle (edge P j - ε • q) (edge P (j + 1))) 0 := by
    apply continuousAt_principalAngle (u := fun ε : ℝ => edge P j - ε • q)
      (v := fun _ => edge P (j + 1))
    · fun_prop
    · exact continuousAt_const
    · have h := hP (j + 1)
      simpa [add_sub_cancel_right] using h
  have ht := hc.tendsto
  simp only [zero_smul, sub_zero] at ht
  simp_rw [principalTurn_softInsertion_succ hn P j q]
  rw [principalTurn, add_sub_cancel_right]
  exact ht

/-- The full sum of turns of `P_ε` converges, as `ε → 0⁺`, to the sum for `P` plus
`α + β_0 - θ` (the replaced turn `θ` at `j` removed, `α`, `β_0` added). -/
theorem tendsto_sum_principalTurn_softInsertion (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    Tendsto (fun ε : ℝ => ∑ a : ZMod (n + 1), principalTurn (softInsertion P j q ε) a) (𝓝[>] 0)
      (𝓝 ((∑ i : ZMod n, principalTurn P i) +
        (principalAngle (edge P (j - 1)) q + principalAngle q (edge P j) - principalTurn P j))) := by
  have hreg : Regular P := generic_regular hn hP
  have hsum : ∀ ε : ℝ, (∑ a : ZMod (n + 1), principalTurn (softInsertion P j q ε) a) =
      principalTurn (softInsertion P j q ε) (softNewIndex j) +
        ∑ k : ZMod n, principalTurn (softInsertion P j q ε) (softOldIndex j k) :=
    fun ε => sum_soft_indices j _
  simp_rw [hsum]
  have hold : Tendsto
      (fun ε : ℝ => ∑ k : ZMod n, principalTurn (softInsertion P j q ε) (softOldIndex j k))
      (𝓝[>] 0)
      (𝓝 (∑ k : ZMod n,
        if k = j then principalAngle (edge P (j - 1)) q else principalTurn P k)) := by
    apply tendsto_finsetSum
    intro k _
    by_cases hkj : k = j
    · simp only [hkj, ite_true]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (principalTurn_softInsertion_soft hn P j q hε).symm
    · simp only [hkj, ite_false]
      by_cases hk1 : k = j + 1
      · rw [hk1]
        exact (tendsto_principalTurn_softInsertion_succ hn hreg j q).mono_left nhdsWithin_le_nhds
      · apply tendsto_const_nhds.congr'
        exact Eventually.of_forall
          (fun ε => (principalTurn_softInsertion_old P j k q ε hkj hk1).symm)
  have hnew := tendsto_principalTurn_softInsertion_new P j q hq.2.1
  have hsplit : (∑ k : ZMod n,
      (if k = j then principalAngle (edge P (j - 1)) q else principalTurn P k)) =
      (∑ k : ZMod n, principalTurn P k) +
        (principalAngle (edge P (j - 1)) q - principalTurn P j) := by
    have h : ∀ k : ZMod n,
        (if k = j then principalAngle (edge P (j - 1)) q else principalTurn P k) =
          principalTurn P k +
            (if k = j then principalAngle (edge P (j - 1)) q - principalTurn P j else 0) := by
      intro k
      split_ifs with h
      · rw [h]; ring
      · ring
    simp_rw [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have heq : (∑ i : ZMod n, principalTurn P i) +
      (principalAngle (edge P (j - 1)) q + principalAngle q (edge P j) - principalTurn P j) =
      principalAngle q (edge P j) + ∑ k : ZMod n,
        (if k = j then principalAngle (edge P (j - 1)) q else principalTurn P k) := by
    rw [hsplit]; ring
  rw [heq]
  exact hnew.add hold

/-! ### Constancy on a regular interval and the limit identity -/

/-- On an interval `(0, δ)` where the family is regular, the rotation number is constant
(lem:rot (ii): the interval is connected and the rotation number is a continuous integer). -/
theorem rotationNumber_softInsertion_constant (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    {δ : ℝ} (hreg : ∀ ε : ℝ, 0 < ε → ε < δ → Regular (softInsertion P j q ε))
    {ε ε' : ℝ} (hε : 0 < ε) (hεδ : ε < δ) (hε' : 0 < ε') (hε'δ : ε' < δ) :
    rotationNumber (softInsertion P j q ε) = rotationNumber (softInsertion P j q ε') := by
  have : PreconnectedSpace (Set.Ioo (0 : ℝ) δ) := Subtype.preconnectedSpace isPreconnected_Ioo
  exact rotationNumber_family_constant
    (f := fun t : Set.Ioo (0 : ℝ) δ => softInsertion P j q t.val)
    ((continuous_softInsertion P j q).comp continuous_subtype_val)
    (fun t => hreg t.val t.property.1 t.property.2) ⟨ε, hε, hεδ⟩ ⟨ε', hε', hε'δ⟩

/-- eq:soft-rotation-limit: `2π (rot(P_ε) - rot(P)) = α + β_0 - θ` on every interval
`(0, δ)` on which the family is regular. -/
theorem soft_rotation_limit_identity (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) {δ : ℝ} (hδ : 0 < δ)
    (hreg : ∀ ε : ℝ, 0 < ε → ε < δ → Regular (softInsertion P j q ε))
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε < δ) :
    2 * Real.pi * (rotationNumber (softInsertion P j q ε) - rotationNumber P) =
      principalAngle (edge P (j - 1)) q + principalAngle q (edge P j) - principalTurn P j := by
  have hconst : Tendsto (fun ε' : ℝ => rotationNumber (softInsertion P j q ε')) (𝓝[>] 0)
      (𝓝 (rotationNumber (softInsertion P j q ε))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε' hε'
    exact rotationNumber_softInsertion_constant P j q hreg hε hεδ hε'.1 hε'.2
  have hlim : Tendsto (fun ε' : ℝ => rotationNumber (softInsertion P j q ε')) (𝓝[>] 0)
      (𝓝 (((∑ i : ZMod n, principalTurn P i) +
        (principalAngle (edge P (j - 1)) q + principalAngle q (edge P j) - principalTurn P j)) /
          (2 * Real.pi))) :=
    (tendsto_sum_principalTurn_softInsertion hn hP j q hq).div_const _
  have huniq := tendsto_nhds_unique hconst hlim
  rw [huniq, rotationNumber]
  field_simp
  ring

/-! ### Pinning the integer -/

theorem int_lt_of_mul_lt {d m : ℤ} {c : ℝ} (hc : 0 < c) (h : (d : ℝ) * c < (m : ℝ) * c) :
    d < m := by
  have h' := lt_of_mul_lt_mul_right h hc.le
  exact_mod_cast h'

/-- Same-sign sector: `α, β_0, θ` all have the sign `τ`, so `α + β_0 - θ ∈ 2π ℤ` forces `0`. -/
theorem soft_integer_same_sign {α β θ : ℝ} {d : ℤ} {τ : SignType}
    (hα : -Real.pi < α ∧ α < Real.pi) (hβ : -Real.pi < β ∧ β < Real.pi)
    (hθ : -Real.pi < θ ∧ θ < Real.pi)
    (hsα : SignType.sign α = τ) (hsβ : SignType.sign β = τ) (hsθ : SignType.sign θ = τ)
    (hτ : τ ≠ 0) (hd : 2 * Real.pi * d = α + β - θ) : d = 0 := by
  have hpi := Real.pi_pos
  rcases signType_nonzero_cases hτ with rfl | rfl
  · simp only [sign_eq_neg_one_iff] at hsα hsβ hsθ
    have h1 := int_lt_of_mul_lt (m := 1) Real.two_pi_pos (by push_cast; linarith)
    have h2 := int_lt_of_mul_lt (d := -1) Real.two_pi_pos (by push_cast; linarith)
    omega
  · simp only [sign_eq_one_iff] at hsα hsβ hsθ
    have h1 := int_lt_of_mul_lt (m := 1) Real.two_pi_pos (by push_cast; linarith)
    have h2 := int_lt_of_mul_lt (d := -1) Real.two_pi_pos (by push_cast; linarith)
    omega

/-- Mixed sector: `α, β_0` have opposite (nonzero) signs, so `|α + β_0| < π` and the multiple
of `2π` is `0`. -/
theorem soft_integer_mixed {α β θ : ℝ} {d : ℤ}
    (hα : -Real.pi < α ∧ α < Real.pi) (hβ : -Real.pi < β ∧ β < Real.pi)
    (hθ : -Real.pi < θ ∧ θ < Real.pi)
    (hsα : SignType.sign α ≠ 0) (hsβ : SignType.sign β = -SignType.sign α)
    (hd : 2 * Real.pi * d = α + β - θ) : d = 0 := by
  have hpi := Real.pi_pos
  rcases signType_nonzero_cases hsα with h | h
  · rw [h] at hsβ
    simp only [sign_eq_neg_one_iff, neg_neg, sign_eq_one_iff] at h hsβ
    have h1 := int_lt_of_mul_lt (m := 1) Real.two_pi_pos (by push_cast; linarith)
    have h2 := int_lt_of_mul_lt (d := -1) Real.two_pi_pos (by push_cast; linarith)
    omega
  · rw [h] at hsβ
    simp only [sign_eq_one_iff, sign_eq_neg_one_iff] at h hsβ
    have h1 := int_lt_of_mul_lt (m := 1) Real.two_pi_pos (by push_cast; linarith)
    have h2 := int_lt_of_mul_lt (d := -1) Real.two_pi_pos (by push_cast; linarith)
    omega

/-- Loop sector: `α, β_0` have the sign `-τ` and `θ` the sign `τ`; the multiple is `-τ`. -/
theorem soft_integer_loop {α β θ : ℝ} {d : ℤ} {τ : SignType}
    (hα : -Real.pi < α ∧ α < Real.pi) (hβ : -Real.pi < β ∧ β < Real.pi)
    (hθ : -Real.pi < θ ∧ θ < Real.pi)
    (hsα : SignType.sign α = -τ) (hsβ : SignType.sign β = -τ) (hsθ : SignType.sign θ = τ)
    (hτ : τ ≠ 0) (hd : 2 * Real.pi * d = α + β - θ) : (d : ℝ) = -(τ : ℝ) := by
  have hpi := Real.pi_pos
  rcases signType_nonzero_cases hτ with rfl | rfl
  · simp only [neg_neg, sign_eq_one_iff, sign_eq_neg_one_iff] at hsα hsβ hsθ
    have h1 := int_lt_of_mul_lt (m := 2) Real.two_pi_pos (by push_cast; linarith)
    have h2 := int_lt_of_mul_lt (d := 0) Real.two_pi_pos (by push_cast; linarith)
    have hd1 : d = 1 := by omega
    rw [hd1]; simp
  · simp only [sign_eq_neg_one_iff, sign_eq_one_iff] at hsα hsβ hsθ
    have h1 := int_lt_of_mul_lt (m := 0) Real.two_pi_pos (by push_cast; linarith)
    have h2 := int_lt_of_mul_lt (d := -2) Real.two_pi_pos (by push_cast; linarith)
    have hd1 : d = -1 := by omega
    rw [hd1]; simp

/-! ### Sign data of the three principal angles -/

omit [NeZero n] in
theorem soft_sign_alpha {P : LabelledTuple n} {j : ZMod n} {q : Plane}
    (hq : SoftAdmissible P j q) :
    SignType.sign (principalAngle (edge P (j - 1)) q) = -softAttachmentMinus P j q := by
  rw [principalAngle_sign (regularPair_of_det_ne_zero hq.1), softAttachmentMinus, neg_neg]

omit [NeZero n] in
theorem soft_sign_beta {P : LabelledTuple n} {j : ZMod n} {q : Plane}
    (hq : SoftAdmissible P j q) :
    SignType.sign (principalAngle q (edge P j)) = -softAttachmentPlus P j q := by
  rw [principalAngle_sign (regularPair_of_det_ne_zero hq.2.1), softAttachmentPlus, neg_neg]

omit [NeZero n] in
theorem soft_sign_theta {P : LabelledTuple n} (hP : Regular P) (j : ZMod n) :
    SignType.sign (principalTurn P j) = turn P j := by
  rw [principalTurn, principalAngle_sign (hP j), turn_det]

theorem soft_turn_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P) (j : ZMod n) :
    turn P j ≠ 0 := by
  have : Fact (1 < n) := ⟨by omega⟩
  rw [turn_det]
  exact sign_ne_zero.mpr (g1_turn_nonzero hn hP j)

/-! ### The rotation law on a regular interval -/

/-- lem:soft-rotation, rotation clauses, on every interval `(0, δ)` on which the soft family is
regular (in particular on the interval of lem:soft-generic, where it is generic). -/
theorem soft_rotation_of_regular_interval (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) {δ : ℝ} (hδ : 0 < δ)
    (hreg : ∀ ε : ℝ, 0 < ε → ε < δ → Regular (softInsertion P j q ε))
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε < δ) :
    (((softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) ∨
        softAttachmentMinus P j q ≠ softAttachmentPlus P j q) →
      rotationNumber (softInsertion P j q ε) = rotationNumber P) ∧
    ((softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) →
      rotationNumber (softInsertion P j q ε) = rotationNumber P - (turn P j : ℝ)) := by
  have hregP : Regular P := generic_regular hn hP
  have hid := soft_rotation_limit_identity hn hP j q hq hδ hreg hε hεδ
  obtain ⟨k, hk⟩ := rotationNumber_integer (hreg ε hε hεδ)
  obtain ⟨m, hm⟩ := rotationNumber_integer hregP
  have hd : 2 * Real.pi * ((k - m : ℤ) : ℝ) =
      principalAngle (edge P (j - 1)) q + principalAngle q (edge P j) - principalTurn P j := by
    rw [← hid, hk, hm]; push_cast; ring
  have hα := principalAngle_bounds (regularPair_of_det_ne_zero hq.1)
  have hβ := principalAngle_bounds (regularPair_of_det_ne_zero hq.2.1)
  have hθ : -Real.pi < principalTurn P j ∧ principalTurn P j < Real.pi :=
    principalAngle_bounds (hregP j)
  have hsα := soft_sign_alpha hq
  have hsβ := soft_sign_beta hq
  have hsθ := soft_sign_theta hregP j
  have hτ := soft_turn_ne_zero hn hP.1 j
  have hχ := softAttachment_signs_nonzero hq
  constructor
  · intro hsector
    have hd0 : k - m = 0 := by
      rcases hsector with ⟨h1, h2⟩ | hne
      · rw [h1, neg_neg] at hsα
        rw [h2, neg_neg] at hsβ
        exact soft_integer_same_sign hα hβ hθ hsα hsβ hsθ hτ hd
      · have hsα0 : SignType.sign (principalAngle (edge P (j - 1)) q) ≠ 0 := by
          rw [hsα]; exact fun h => hχ.1 (SignType.neg_eq_zero_iff.mp h)
        have hopp : SignType.sign (principalAngle q (edge P j)) =
            -SignType.sign (principalAngle (edge P (j - 1)) q) := by
          rw [hsα, hsβ, neg_neg]
          rcases signType_nonzero_cases hχ.1 with h1 | h1 <;>
            rcases signType_nonzero_cases hχ.2 with h2 | h2 <;>
            simp_all
        exact soft_integer_mixed hα hβ hθ hsα0 hopp hd
    have hkm : k = m := by omega
    rw [hk, hm, hkm]
  · rintro ⟨h1, h2⟩
    rw [h1] at hsα
    rw [h2] at hsβ
    have hd1 := soft_integer_loop hα hβ hθ hsα hsβ hsθ hτ hd
    rw [hk, hm]
    push_cast at hd1
    linarith

/-! ### The sector cones -/

/-- The same-sign sector is the open cone strictly between `ℓ_{j-1}` and `ℓ_j`. -/
theorem soft_same_sign_sector_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    (softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) ↔
      q ∈ openCone (edge P (j - 1)) (edge P j) := by
  have : Fact (1 < n) := ⟨by omega⟩
  have hD : det (edge P (j - 1)) (edge P j) ≠ 0 := g1_turn_nonzero hn hP j
  rw [mem_openCone_iff hD, softAttachmentMinus, softAttachmentPlus, turn_det, neg_inj, neg_inj,
    sign_eq_sign_iff_mul_pos hD, sign_eq_sign_iff_mul_pos hD]

/-- The loop sector is the open cone strictly between `-ℓ_{j-1}` and `-ℓ_j`. -/
theorem soft_loop_sector_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) ↔
      q ∈ openCone (-edge P (j - 1)) (-edge P j) := by
  have : Fact (1 < n) := ⟨by omega⟩
  have hD : det (edge P (j - 1)) (edge P j) ≠ 0 := g1_turn_nonzero hn hP j
  have hD' : det (-edge P (j - 1)) (-edge P j) ≠ 0 := by rwa [det_neg_neg]
  rw [mem_openCone_iff hD', det_neg_neg, det_neg_left, det_neg_right, softAttachmentMinus,
    softAttachmentPlus, turn_det, ← Left.sign_neg, ← Left.sign_neg,
    sign_eq_sign_iff_mul_pos hD, sign_eq_sign_iff_mul_pos hD]

/-- The mixed sector is the complement of the closures of the two cones. -/
theorem soft_mixed_sector_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    softAttachmentMinus P j q ≠ softAttachmentPlus P j q ↔
      q ∉ closure (openCone (edge P (j - 1)) (edge P j)) ∧
      q ∉ closure (openCone (-edge P (j - 1)) (-edge P j)) := by
  have : Fact (1 < n) := ⟨by omega⟩
  have hD : det (edge P (j - 1)) (edge P j) ≠ 0 := g1_turn_nonzero hn hP j
  have hD' : det (-edge P (j - 1)) (-edge P j) ≠ 0 := by rwa [det_neg_neg]
  have h1' : det (-edge P (j - 1)) q ≠ 0 := by rw [det_neg_left]; exact neg_ne_zero.mpr hq.1
  have h2' : det q (-edge P j) ≠ 0 := by rw [det_neg_right]; exact neg_ne_zero.mpr hq.2.1
  rw [mem_closure_openCone_iff hD hq.1 hq.2.1, mem_closure_openCone_iff hD' h1' h2',
    ← soft_same_sign_sector_iff hn hP j q, ← soft_loop_sector_iff hn hP j q]
  constructor
  · intro hne
    refine ⟨fun h => hne (h.1.trans h.2.symm), fun h => hne (h.1.trans h.2.symm)⟩
  · rintro ⟨hsame, hloop⟩
    rcases soft_attachment_sectors hn hP j q hq with h | h | h
    · exact absurd h hloop
    · exact absurd h hsame
    · exact h

omit [NeZero n] in
/-- The sector conditions unfolded to the printed determinant signs
`χ_- = -sgn det(ℓ_{j-1}, q)`, `χ_+ = -sgn det(q, ℓ_j)`, `τ_j = sgn det(ℓ_{j-1}, ℓ_j)`. -/
theorem soft_sectors_det_signs (P : LabelledTuple n) (j : ZMod n) (q : Plane) :
    ((softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) ↔
      (SignType.sign (det (edge P (j - 1)) q) = SignType.sign (det (edge P (j - 1)) (edge P j)) ∧
        SignType.sign (det q (edge P j)) = SignType.sign (det (edge P (j - 1)) (edge P j)))) ∧
    ((softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) ↔
      (SignType.sign (det (edge P (j - 1)) q) = -SignType.sign (det (edge P (j - 1)) (edge P j)) ∧
        SignType.sign (det q (edge P j)) = -SignType.sign (det (edge P (j - 1)) (edge P j)))) ∧
    (softAttachmentMinus P j q ≠ softAttachmentPlus P j q ↔
      SignType.sign (det (edge P (j - 1)) q) ≠ SignType.sign (det q (edge P j))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [softAttachmentMinus, softAttachmentPlus, turn_det, neg_inj, neg_inj]
  · rw [softAttachmentMinus, softAttachmentPlus, turn_det, neg_eq_iff_eq_neg, neg_eq_iff_eq_neg]
  · rw [softAttachmentMinus, softAttachmentPlus, ne_eq, neg_inj]

/-! ### lem:soft-rotation -/

/-- lem:soft-rotation (rotation of a soft insertion), as printed on SM15.
`P` generic, `q` admissible at `j`, `ε` small (lem:soft-generic): there is `ε₀ > 0` such that
for every `0 < ε < ε₀` the polygon `P_ε` is generic, `rot(P_ε) = rot(P)` in the same-sign and
mixed sectors, and `rot(P_ε) = rot(P) - τ_j(P)` in the loop sector. Moreover the same-sign
sector is the open cone strictly between `ℓ_{j-1}` and `ℓ_j` (`q = a ℓ_{j-1} + b ℓ_j`,
`a, b > 0`), the loop sector the open cone strictly between `-ℓ_{j-1}` and `-ℓ_j`, and the
mixed sector the complement of the closures of these two cones. -/
theorem soft_rotation (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    (∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Generic (softInsertion P j q ε) ∧
      (((softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) ∨
          softAttachmentMinus P j q ≠ softAttachmentPlus P j q) →
        rotationNumber (softInsertion P j q ε) = rotationNumber P) ∧
      ((softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) →
        rotationNumber (softInsertion P j q ε) = rotationNumber P - (turn P j : ℝ))) ∧
    ((softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) ↔
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ q = a • edge P (j - 1) + b • edge P j) ∧
    ((softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) ↔
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ q = a • (-edge P (j - 1)) + b • (-edge P j)) ∧
    (softAttachmentMinus P j q ≠ softAttachmentPlus P j q ↔
      q ∉ closure (openCone (edge P (j - 1)) (edge P j)) ∧
      q ∉ closure (openCone (-edge P (j - 1)) (-edge P j))) := by
  refine ⟨?_, soft_same_sign_sector_iff hn hP.1 j q, soft_loop_sector_iff hn hP.1 j q,
    soft_mixed_sector_iff hn hP.1 j q hq⟩
  obtain ⟨-, δ, hδ, _B, hfam⟩ := soft_family_regular_data hn hP j q hq
  have hgen : ∀ ε : ℝ, 0 < ε → ε < δ → Generic (softInsertion P j q ε) :=
    fun ε hε hεδ => (hfam ε hε hεδ).1
  have hreg : ∀ ε : ℝ, 0 < ε → ε < δ → Regular (softInsertion P j q ε) :=
    fun ε hε hεδ => generic_regular (by omega) (hgen ε hε hεδ)
  refine ⟨δ, hδ, fun ε hε hεδ => ⟨hgen ε hε hεδ, ?_⟩⟩
  exact soft_rotation_of_regular_interval hn hP j q hq hδ hreg hε hεδ

end
end SM
