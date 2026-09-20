import SM.PositiveLiftDefinition
import SM.UniformDefinition
import SM.DecompositionDefinition
import SM.LinkInterfaces

/-! Ported verbatim 2026-09-13 from work/drafts/CornerStateSum.lean (implementer subagent of the pod executor; checked with `lake env lean`, no placeholder, axioms propext/Classical.choice/Quot.sound/SM.lit_homfly); only this header added and `#print axioms` lines removed. Row def:C → `SM.corner_state_sum_definition`. -/

/-! Source def:C (reference/SM/sm-3-statesum.tex:1688-1700, frame SM15): the corner coefficient
`c(Q)` and the corner state sum `C(P)`. Main declaration: `SM.corner_state_sum_definition`.

Printed text. "For a subpolygon `Q` of a decomposition of the generic polygon `P`, let `H⁺_Q` be
the HOMFLY–PT polynomial of its positive lift and put `d_Q = 1 − m_Q − |r_Q|`,
`c(Q) = [a^{d_Q} z^0] H⁺_Q(a, z) ∈ ℤ`, the coefficient of `a^{d_Q} z^0` (zero if that monomial is
absent). The corner state sum of `P` is
`C(P) = (−1)^{ℓ(P)} Σ_{S ∈ Ind(G_P), S uniform} (−1)^{|S|} ∏_{Q subpolygon of S} c(Q)`."

Notation, all accepted or ported (design record work/reports/design-decision-diagram-record-20260913.md,
def:C entries at lines 93, 174, 217, 240). `P` is a generic polygon with `n ≥ 3` vertices
(`hn : 3 ≤ n`, `hP : Generic P`, `[NeZero n]` as in def:uniform). A decomposition is an independent
set `S ∈ Ind(G_P) = independentSupports hn hP` (def:decomposition, `IsDecomposition hn hP S`). A
subpolygon `Q` of `S` is a carrier `q : Carrier.Component hn hP S` (def:smoothing, lem:carriers; a
`Fintype`), read as its corner polygon `ccpCornerPolygon hn hP S q`; its crossing number is
`m_Q = carrierCrossingCount hn hP S q : ℕ` (def:smoothing) and its rotation is
`r_Q = carrierRotation hn hP S q : ℝ` (def:uniform, `rotationNumber` of the corner polygon), an
integer by lem:rot (`rotationNumber_integer`) since the corner polygon is regular
(`ccpCornerPolygon_regular`, lem:carriers (ii)). "`S` uniform" is `UniformDecomposition hn hP S`
(def:uniform). `ℓ(P) = leftTurns P = #{i : τ_i(P) = 1}` (def:chirotope, sm-1-polygons.tex:69). The
positive lift of `Q` is `Link.positiveLift hn hP S q hS : Link.Diagram` (def:positive-lift), which
needs the decomposition hypothesis `hS`; `homfly : Diagram → R` is the HOMFLY–PT polynomial of
lit:homfly on the ring `R = ℤ[a^{±1}, z^{±1}]` (SM.LinkInterfaces, SM.LinkLaurentRing), and
`[a^d z^k] f = coeffAt d k f = f.coeff (d, k)` (Finsupp evaluation, zero off the support).

Rendering decisions (see work/drafts/CornerStateSum_PLAN.md).
1. `r_Q` is accepted as a real; the exponent `d_Q` must be an integer for `coeffAt`. We put
   `carrierRotationInt := round carrierRotation : ℤ` (hypothesis-free) and prove that it casts back to
   `carrierRotation` on decompositions (`carrierRotationInt_cast`), so `cornerSlot = d_Q` is stated in
   `ℤ` and the printed real formula `d_Q = 1 − m_Q − |r_Q|` is a theorem (`cornerSlot_cast`).
2. `c(Q)` is printed only for subpolygons of decompositions and its positive lift needs `hS`, so
   `cornerCoefficientWith H hn hP S q hS` and `cornerCoefficient hn hP S q hS` carry `hS` explicitly;
   following the design record, the coefficient is first defined for an arbitrary `H : Diagram → R`
   and then instantiated at `homfly`.
3. The index set "`S ∈ Ind(G_P)`, `S` uniform" is `uniformDecompositions hn hP :=
   (independentSupports hn hP).filter (UniformDecomposition hn hP)` (classical decidability, as in
   SM.InterlaceSupports); the sum runs over its `attach`, so the summand receives the membership
   proof and hence `hS`. `cornerStateSum_eq_sum_independentSupports` gives the equivalent `if`-form
   over all of `Ind(G_P)` for consumers (lem:C-X1). -/

namespace SM

open Link Carrier

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

/-! ### `r_Q` as an integer -/

/-- `r_Q` read as an integer: `round` of the accepted real rotation `carrierRotation`. On
decompositions the rotation is an integer (lem:rot), so this is that integer
(`carrierRotationInt_cast`). -/
noncomputable def carrierRotationInt (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : ℤ :=
  round (carrierRotation hn hP S q)

/-- lem:rot on a subpolygon of a decomposition: `r_Q` is an integer (the corner polygon is regular
by lem:carriers (ii)). -/
theorem carrierRotation_exists_int (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S) :
    ∃ k : ℤ, carrierRotation hn hP S q = (k : ℝ) :=
  rotationNumber_integer (ccpCornerPolygon_regular hn hP hS q)

/-- On decompositions the integer rotation casts back to the accepted real rotation. -/
theorem carrierRotationInt_cast (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S) :
    ((carrierRotationInt hn hP S q : ℤ) : ℝ) = carrierRotation hn hP S q := by
  obtain ⟨k, hk⟩ := carrierRotation_exists_int hn hP hS q
  rw [carrierRotationInt, hk, round_intCast]

/-! ### The exponent `d_Q` and the coefficient `c(Q)` -/

/-- `d_Q = 1 − m_Q − |r_Q|`, the `a`-exponent read off the positive lift's polynomial. -/
noncomputable def cornerSlot (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : ℤ :=
  1 - (carrierCrossingCount hn hP S q : ℤ) - |carrierRotationInt hn hP S q|

/-- The printed formula `d_Q = 1 − m_Q − |r_Q|` with the accepted real `r_Q`, on decompositions. -/
theorem cornerSlot_cast (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S) :
    ((cornerSlot hn hP S q : ℤ) : ℝ) =
      1 - (carrierCrossingCount hn hP S q : ℝ) - |carrierRotation hn hP S q| := by
  rw [cornerSlot, Int.cast_sub, Int.cast_sub, Int.cast_one, Int.cast_natCast, Int.cast_abs,
    carrierRotationInt_cast hn hP hS q]

/-- `H⁺_Q`: the HOMFLY–PT polynomial of the positive lift of the subpolygon `Q` of the
decomposition `S`. -/
noncomputable def cornerHomfly (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S) : R :=
  homfly (positiveLift hn hP S q hS)

/-- The corner coefficient with respect to an arbitrary diagram invariant `H : Diagram → R`:
`[a^{d_Q} z^0] H(positive lift of Q)`. The design record defines this first so that the body can be
reviewed independently of the axiom `lit_homfly`. -/
noncomputable def cornerCoefficientWith (H : Diagram → R) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (q : Component hn hP S)
    (hS : IsDecomposition hn hP S) : ℤ :=
  coeffAt (cornerSlot hn hP S q) 0 (H (positiveLift hn hP S q hS))

/-- `c(Q) = [a^{d_Q} z^0] H⁺_Q(a, z) ∈ ℤ`, the coefficient of `a^{d_Q} z^0` in the HOMFLY–PT
polynomial of the positive lift (zero if that monomial is absent). -/
noncomputable def cornerCoefficient (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S) : ℤ :=
  cornerCoefficientWith homfly hn hP S q hS

theorem cornerCoefficient_eq_coeffAt (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S) :
    cornerCoefficient hn hP S q hS = coeffAt (cornerSlot hn hP S q) 0 (cornerHomfly hn hP S q hS) :=
  rfl

/-- "zero if that monomial is absent". -/
theorem cornerCoefficient_eq_zero_of_notMem_support (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (q : Component hn hP S)
    (hS : IsDecomposition hn hP S)
    (h : (cornerSlot hn hP S q, (0 : ℤ)) ∉ (cornerHomfly hn hP S q hS).coeff.support) :
    cornerCoefficient hn hP S q hS = 0 :=
  coeffAt_eq_zero_of_notMem_support h

theorem cornerCoefficient_ne_zero_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S) :
    cornerCoefficient hn hP S q hS ≠ 0 ↔
      (cornerSlot hn hP S q, (0 : ℤ)) ∈ (cornerHomfly hn hP S q hS).coeff.support :=
  mem_support_iff_coeffAt_ne_zero.symm

/-! ### The index set `{S ∈ Ind(G_P) : S uniform}` and the state sum -/

/-- The uniform decompositions of `P`: `{S ∈ Ind(G_P) : S uniform}`. -/
noncomputable def uniformDecompositions (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    Finset (Finset (Crossing P)) :=
  (independentSupports hn hP).filter (UniformDecomposition hn hP)

theorem mem_uniformDecompositions (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) :
    S ∈ uniformDecompositions hn hP ↔
      S ∈ independentSupports hn hP ∧ UniformDecomposition hn hP S :=
  Finset.mem_filter

theorem isDecomposition_of_mem_uniformDecompositions (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (h : S ∈ uniformDecompositions hn hP) :
    IsDecomposition hn hP S :=
  (Finset.mem_filter.1 h).1

theorem uniform_of_mem_uniformDecompositions (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (h : S ∈ uniformDecompositions hn hP) :
    UniformDecomposition hn hP S :=
  (Finset.mem_filter.1 h).2

/-- `∏_{Q subpolygon of S} c(Q)`: the product over the carriers (a `Fintype`) of the
decomposition `S`. -/
noncomputable def cornerProduct (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) : ℤ :=
  ∏ q : Component hn hP S, cornerCoefficient hn hP S q hS

/-- The corner state sum
`C(P) = (−1)^{ℓ(P)} Σ_{S ∈ Ind(G_P), S uniform} (−1)^{|S|} ∏_{Q subpolygon of S} c(Q)`.
The sum runs over the attached index set so that each summand receives the membership proof, from
which the decomposition hypothesis of the positive lift is read off. -/
noncomputable def cornerStateSum (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) : ℤ :=
  (-1) ^ leftTurns P *
    ∑ S ∈ (uniformDecompositions hn hP).attach,
      (-1) ^ S.1.card *
        cornerProduct hn hP S.1 (isDecomposition_of_mem_uniformDecompositions hn hP S.2)

/-- Consumer form (lem:C-X1): the same sum over all of `Ind(G_P)`, the non-uniform decompositions
contributing `0`. -/
theorem cornerStateSum_eq_sum_independentSupports (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) :
    cornerStateSum hn hP =
      (-1) ^ leftTurns P *
        ∑ S ∈ (independentSupports hn hP).attach,
          if UniformDecomposition hn hP S.1 then (-1) ^ S.1.card * cornerProduct hn hP S.1 S.2
          else 0 := by
  unfold cornerStateSum
  congr 1
  -- the dependent summand as a total function of the underlying set
  set g : Finset (Crossing P) → ℤ := fun S =>
    if h : S ∈ independentSupports hn hP ∧ UniformDecomposition hn hP S then
      (-1) ^ S.card * cornerProduct hn hP S h.1
    else 0 with hg
  have h1 : (∑ S ∈ (uniformDecompositions hn hP).attach,
      (-1) ^ S.1.card *
        cornerProduct hn hP S.1 (isDecomposition_of_mem_uniformDecompositions hn hP S.2)) =
      ∑ S ∈ (uniformDecompositions hn hP).attach, g S.1 := by
    refine Finset.sum_congr rfl fun S _ => ?_
    have hm := (mem_uniformDecompositions hn hP S.1).1 S.2
    simp only [hg]
    rw [dite_eq_left hm]
  have h2 : (∑ S ∈ (independentSupports hn hP).attach,
      if UniformDecomposition hn hP S.1 then (-1) ^ S.1.card * cornerProduct hn hP S.1 S.2
      else 0) = ∑ S ∈ (independentSupports hn hP).attach, g S.1 := by
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [hg]
    by_cases hu : UniformDecomposition hn hP S.1
    · rw [ite_eq_left hu, dite_eq_left (And.intro S.2 hu)]
    · rw [ite_eq_right hu, dite_eq_right (not_and.mpr fun _ => hu)]
  rw [h1, h2, Finset.sum_attach, Finset.sum_attach, uniformDecompositions, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hu : UniformDecomposition hn hP S
  · rw [ite_eq_left hu]
  · rw [ite_eq_right hu]
    simp only [hg]
    rw [dite_eq_right (not_and.mpr fun _ => hu)]

/-! ### def:C as printed -/

/-- def:C as printed on SM15, one field per printed clause, on the accepted carrier, positive-lift
and HOMFLY layers. -/
structure CornerStateSumDefinitionData : Prop where
  /-- "For a subpolygon `Q` of a decomposition of the generic polygon `P`, let `H⁺_Q` be the
  HOMFLY–PT polynomial of its positive lift": `H⁺_Q = homfly (positiveLift …)`, where the positive
  lift is the diagram of def:positive-lift — every crossing positive, writhe `m_Q` (accepted). -/
  positive_lift : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S),
    cornerHomfly hn hP S q hS = homfly (positiveLift hn hP S q hS) ∧
    (∀ x, (positiveLift hn hP S q hS).IsPositive x) ∧
    (positiveLift hn hP S q hS).writhe = carrierCrossingCount hn hP S q
  /-- `r_Q` is an integer on the subpolygons of a decomposition (lem:rot, lem:carriers (ii)), and
  `carrierRotationInt` is that integer. -/
  rotation_integer : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)), IsDecomposition hn hP S → ∀ q : Component hn hP S,
    (∃ k : ℤ, carrierRotation hn hP S q = (k : ℝ)) ∧
    ((carrierRotationInt hn hP S q : ℤ) : ℝ) = carrierRotation hn hP S q
  /-- "put `d_Q = 1 − m_Q − |r_Q|`": in `ℤ` with the integer rotation, and, on decompositions, as
  the printed real identity with the accepted `r_Q = carrierRotation`. -/
  slot : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)), IsDecomposition hn hP S → ∀ q : Component hn hP S,
    cornerSlot hn hP S q = 1 - (carrierCrossingCount hn hP S q : ℤ) - |carrierRotationInt hn hP S q| ∧
    ((cornerSlot hn hP S q : ℤ) : ℝ) =
      1 - (carrierCrossingCount hn hP S q : ℝ) - |carrierRotation hn hP S q|
  /-- "`c(Q) = [a^{d_Q} z^0] H⁺_Q(a, z) ∈ ℤ`, the coefficient of `a^{d_Q} z^0`". -/
  coefficient : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S),
    cornerCoefficient hn hP S q hS = coeffAt (cornerSlot hn hP S q) 0 (cornerHomfly hn hP S q hS) ∧
    cornerCoefficient hn hP S q hS = (cornerHomfly hn hP S q hS).coeff (cornerSlot hn hP S q, 0)
  /-- "(zero if that monomial is absent)", and conversely the coefficient is nonzero exactly when
  the monomial is present. -/
  coefficient_absent : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) (hS : IsDecomposition hn hP S),
    ((cornerSlot hn hP S q, (0 : ℤ)) ∉ (cornerHomfly hn hP S q hS).coeff.support →
      cornerCoefficient hn hP S q hS = 0) ∧
    (cornerCoefficient hn hP S q hS ≠ 0 ↔
      (cornerSlot hn hP S q, (0 : ℤ)) ∈ (cornerHomfly hn hP S q hS).coeff.support)
  /-- The coefficient with respect to an arbitrary `H : Diagram → R` (design record), and `c(Q)`
  is its instance at `homfly`. -/
  coefficient_with : ∀ (H : Diagram → R) (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Generic P) (S : Finset (Crossing P)) (q : Component hn hP S)
    (hS : IsDecomposition hn hP S),
    cornerCoefficientWith H hn hP S q hS =
      coeffAt (cornerSlot hn hP S q) 0 (H (positiveLift hn hP S q hS)) ∧
    cornerCoefficient hn hP S q hS = cornerCoefficientWith homfly hn hP S q hS
  /-- The index set of the sum: "`S ∈ Ind(G_P)`, `S` uniform" (def:decomposition, def:uniform). -/
  uniform_index_set : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)),
    (S ∈ uniformDecompositions hn hP ↔
      S ∈ independentSupports hn hP ∧ UniformDecomposition hn hP S) ∧
    (S ∈ uniformDecompositions hn hP ↔
      IsDecomposition hn hP S ∧ ∀ q : Component hn hP S, CarrierUniform hn hP S q)
  /-- "`∏_{Q subpolygon of S} c(Q)`": the product over the carriers of `S`. -/
  product : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S),
    cornerProduct hn hP S hS = ∏ q : Component hn hP S, cornerCoefficient hn hP S q hS
  /-- "`ℓ(P)`", the number of left turns of `P` (def:chirotope): `#{i : τ_i(P) = 1}`. -/
  left_turns : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n),
    leftTurns P = (Finset.univ.filter fun i => turn P i = 1).card
  /-- "The corner state sum of `P` is
  `C(P) = (−1)^{ℓ(P)} Σ_{S ∈ Ind(G_P), S uniform} (−1)^{|S|} ∏_{Q subpolygon of S} c(Q)`",
  and its equivalent form as a sum over all of `Ind(G_P)` with the non-uniform terms `0`. -/
  state_sum : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
    cornerStateSum hn hP =
      (-1) ^ leftTurns P *
        ∑ S ∈ (uniformDecompositions hn hP).attach,
          (-1) ^ S.1.card *
            ∏ q : Component hn hP S.1,
              cornerCoefficient hn hP S.1 q
                (isDecomposition_of_mem_uniformDecompositions hn hP S.2) ∧
    cornerStateSum hn hP =
      (-1) ^ leftTurns P *
        ∑ S ∈ (independentSupports hn hP).attach,
          if UniformDecomposition hn hP S.1 then (-1) ^ S.1.card * cornerProduct hn hP S.1 S.2
          else 0

theorem corner_state_sum_definition : CornerStateSumDefinitionData where
  positive_lift := fun _ _ hn _ hP S q hS =>
    ⟨rfl, fun x => positiveLift_isPositive hn hP S q hS x,
      positiveLift_writhe_eq_carrierCrossingCount hn hP S q hS⟩
  rotation_integer := fun _ _ hn _ hP _ hS q =>
    ⟨carrierRotation_exists_int hn hP hS q, carrierRotationInt_cast hn hP hS q⟩
  slot := fun _ _ hn _ hP _ hS q => ⟨rfl, cornerSlot_cast hn hP hS q⟩
  coefficient := fun _ _ _ _ _ _ _ _ => ⟨rfl, rfl⟩
  coefficient_absent := fun _ _ hn _ hP S q hS =>
    ⟨cornerCoefficient_eq_zero_of_notMem_support hn hP S q hS,
      cornerCoefficient_ne_zero_iff hn hP S q hS⟩
  coefficient_with := fun _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl⟩
  uniform_index_set := fun _ _ hn _ hP S =>
    ⟨mem_uniformDecompositions hn hP S, mem_uniformDecompositions hn hP S⟩
  product := fun _ _ _ _ _ _ _ => rfl
  left_turns := fun _ _ _ => rfl
  state_sum := fun _ _ hn _ hP => ⟨rfl, cornerStateSum_eq_sum_independentSupports hn hP⟩

end SM
