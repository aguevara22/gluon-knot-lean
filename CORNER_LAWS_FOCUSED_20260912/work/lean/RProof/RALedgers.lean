-- Ported 18:08Z 2026-09-15 from work/drafts/cvtail/Wave1_Assembled.lean lines 1772-2536, 2622-3470, 3485-4191, 4206-4218, 4239-4244 (CV/R tail lane, LIBRARY MATERIAL, no row: RowShape and rowShape_170/172/173; unit U-174's gsc_ interface Props and PROVED ledger gsc_ledger / gsc_generic_selected_of_moves; unit U-176's est_ interface Props and PROVED ledger est_ledger / est_extreme_transport_of; unit U-177's esc_ interface Props and PROVED ledger esc_ledger; cvt_chamberInvII, cv_R_of_rows; Bridge.sm_R_of_rows) by the pod executor; body verbatim except this header, the import block, the module docstring (new; the §3/§4 headings of Wave1 lines 1769-1770 and 4230 omitted), and the omitted row theorems RProof.generic_selected / extreme_transport / extreme_selected / cv_R and Bridge.sm_R (lines 2538-2550, 3472-3483, 4193-4204, 4220-4226, 4234-4237: still unproved or depending on an unproved row — NOT ported). No unproved declaration; no interface Prop asserted.
import RProof.X1Rows
import RProof.X1Rows2
import RProof.GenericTransport
import CV.ChamberInvRow
import CV.FullTwist
import CV.HomflyRows
import CV.CarrierFloor
import Bridge.SmR

/-! # CV/R tail — the RA rows' interface Props and PROVED ledgers (rows 174, 176, 177) and the row-178/183 assemblies

Library material of the CV/R tail lane (work/drafts/cvtail/PLAN_FINAL.md §4-§6, WAVE1_ASSEMBLY_REPORT.md §3): the
fixed row shape `RowShape`, the accepted rows 170/172/173 in that shape, and for each of the three open R rows the
explicit interface Props (D-F11: stated, consumed, NEVER asserted — `gsc_moves`, `est_port_relation`,
`esc_interface`) with the PROVED ledger of `RowShape` type (`gsc_ledger`, `est_ledger`, `esc_ledger`) from
`CV.CarrierSlotFloor`.  `cv_R_of_rows` and `Bridge.sm_R_of_rows` assemble rows 178 and 183 from the four rows as
hypotheses.  The row theorems `RProof.generic_selected`, `extreme_transport`, `extreme_selected`, `cv_R`, `Bridge.sm_R`
are NOT here (open: the three interface Props are unrealised); `RProof.extreme_pair_zero` is in
RProof/ExtremePairZero.lean.  Every declaration here is proved on standard + literature axioms. -/

namespace RProof

open SM SM.GeoCarrier

/-- The fixed shape of an X₁-dependent R row (the accepted siblings' signature: `exterior`
X1Rows2.lean:1966, `availability_zero_one` :3619, `generic_selector` X1Rows.lean:1309,
`generic_transport` GenericTransport.lean:11157). -/
def RowShape (D : ∀ {n : ℕ} [NeZero n], 3 ≤ n → CV.Event n → ZMod n → ZMod n → ZMod n → ℝ → Prop) :
    Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f),
    E.IsSimpleRIII e f g h3 h4e h4f h4g → ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ D hn E e f g δ

theorem rowShape_170 : RowShape @AvailabilityZeroOneData :=
  fun _ _ hn E e f g h3 h4e h4f h4g hE => availability_zero_one hn E e f g h3 h4e h4f h4g hE
theorem rowShape_172 : RowShape @GenericSelectorData :=
  fun _ _ hn E e f g h3 h4e h4f h4g hE => generic_selector hn E e f g h3 h4e h4f h4g hE
theorem rowShape_173 : RowShape @GenericTransportData :=
  fun _ _ hn E e f g h3 h4e h4f h4g hE => generic_transport hn E e f g h3 h4e h4f h4g hE

variable {n : ℕ} [NeZero n]

/-! ## Unit U-174 (prefix `gsc_`) — the generic selected complementary couple
(R_GENERIC_SELECTED_COUPLE_PROOF.md, (GSC) `T_E(b) = T_P(b) + T_P(ac)`)

Pattern D-F11: the Reidemeister move and the diagram identifications the RA argument needs are stated
as explicit interface Props (`gsc_fulltwist_triple` — the G10 RII deletion of the switched empty pair
`a, c`; `gsc_smoothing_split` — the two-component smoothing carries the pair-row records; the bundle
`gsc_Ledger` — the carrier/selector/rotation ledger of GSC §1–§3; the event-level interface
`gsc_moves`), the RA ledger of GSC §4–§5 is PROVED from them and from `CV.CarrierSlotFloor`
(`gsc_ledger : gsc_moves → CV.CarrierSlotFloor → RowShape @GenericSelectedData`), and the moves are
realised as far as the accepted library allows (`gsc_wall_of_endpoint`, `gsc_Ind_*`, the sign
facts; see U_R174_REPORT.md for what remains).  Nothing here is mapped; the interface Props are never
asserted. -/

section GSC

open SM.Carrier SM.Link

/-! ### GSC §4 (12)–(13): the Laurent-polynomial coefficient extraction (pure algebra, PROVED) -/

/-- Floors multiply: if every monomial of `f` has exponent `≥ dA` and every monomial of `g` has
exponent `≥ dB`, the `a^{dA+dB}` coefficient of `f * g` is the product of the two floor
coefficients ("the coefficient at `D = d_A + d_B` is the product of the two first coefficients"). -/
theorem gsc_coeff_mul_floor {f g : LaurentPolynomial ℤ} {dA dB : ℤ}
    (hf : ∀ i, f.coeff i ≠ 0 → dA ≤ i) (hg : ∀ j, g.coeff j ≠ 0 → dB ≤ j) :
    (f * g).coeff (dA + dB) = f.coeff dA * g.coeff dB := by
  classical
  rw [AddMonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum]
  rw [Finset.sum_eq_single dA, Finset.sum_eq_single dB, ite_eq_left rfl]
  · intro j hj hne
    rw [ite_eq_right]
    intro he
    have := hg j (Finsupp.mem_support_iff.mp hj)
    omega
  · intro h
    rw [Finsupp.notMem_support_iff.mp h, mul_zero, ite_eq_left rfl]
  · intro i hi hne
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [ite_eq_right]
    intro he
    have h1 := hf i (Finsupp.mem_support_iff.mp hi)
    have h2 := hg j (Finsupp.mem_support_iff.mp hj)
    omega
  · intro h
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.notMem_support_iff.mp h, zero_mul, ite_self]

/-- Below the sum of the floors every coefficient of the product vanishes ("no exponent below `d_A`
occurs in `f_A`, and none below `d_B` occurs in `f_B`. Therefore the first coefficient in (12) is
zero"). -/
theorem gsc_coeff_mul_eq_zero_of_lt {f g : LaurentPolynomial ℤ} {dA dB : ℤ}
    (hf : ∀ i, f.coeff i ≠ 0 → dA ≤ i) (hg : ∀ j, g.coeff j ≠ 0 → dB ≤ j) {k : ℤ}
    (hk : k < dA + dB) : (f * g).coeff k = 0 := by
  classical
  rw [AddMonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  rw [ite_eq_right]
  intro he
  have h1 := hf i (Finsupp.mem_support_iff.mp hi)
  have h2 := hg j (Finsupp.mem_support_iff.mp hj)
  omega

/-- The `a^k` coefficient of `(a − a⁻¹) a^{−2ℓ} h` is `[a^{k+2ℓ−1}] h − [a^{k+2ℓ+1}] h` ("the factor
`a^(-2 ell)(a-a^(-1))`"). -/
theorem gsc_coeff_shift (ℓ k : ℤ) (h : LaurentPolynomial ℤ) :
    ((aPow 1 - aPow (-1)) * aPow (-(2 * ℓ)) * h).coeff k =
      h.coeff (k + 2 * ℓ - 1) - h.coeff (k + 2 * ℓ + 1) := by
  have e1 : (aPow 1 - aPow (-1)) * aPow (-(2 * ℓ)) =
      (LaurentPolynomial.T (1 + -(2 * ℓ)) : LaurentPolynomial ℤ) -
        LaurentPolynomial.T (-1 + -(2 * ℓ)) := by
    rw [LaurentPolynomial.T_add, LaurentPolynomial.T_add, sub_mul]
  rw [e1, sub_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, LaurentPolynomial.T,
    LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_apply,
    AddMonoidAlgebra.coeff_single_mul_apply, one_mul, one_mul]
  congr 2 <;> ring

/-- **GSC (12)–(13), the coefficient extraction.**  From lem:fulltwist's coefficient display, the
two-component `z^{-1}` row of lem:homflyrows (ii) (already in product-of-rows form, knot parity
included), the slot identity (11) `d_A + d_B = d_L + 2ℓ` and the two floors of thm:carrierfloor,
`Ω_H − Ω_L = −ω_A ω_B`. -/
theorem gsc_omega_jump_alg {ΩH ΩL dL dA dB ℓ : ℤ} {F0 QA QB : R}
    (hfull : ΩH - ΩL = coeffAt (dL - 1) (-1) F0)
    (hrow : zRow (-1) F0 = (aPow 1 - aPow (-1)) * aPow (-(2 * ℓ)) * (zRow 0 QA * zRow 0 QB))
    (hD : dA + dB = dL + 2 * ℓ)
    (hA : ∀ d, coeffAt d 0 QA ≠ 0 → dA ≤ d) (hB : ∀ d, coeffAt d 0 QB ≠ 0 → dB ≤ d) :
    ΩH - ΩL = -(coeffAt dA 0 QA * coeffAt dB 0 QB) := by
  have hA' : ∀ i, (zRow 0 QA).coeff i ≠ 0 → dA ≤ i := fun i hi => hA i (by rwa [coeff_zRow] at hi)
  have hB' : ∀ j, (zRow 0 QB).coeff j ≠ 0 → dB ≤ j := fun j hj => hB j (by rwa [coeff_zRow] at hj)
  rw [hfull, ← coeff_zRow, hrow, gsc_coeff_shift]
  have e2 : dL - 1 + 2 * ℓ + 1 = dA + dB := by omega
  rw [e2, gsc_coeff_mul_floor hA' hB',
    gsc_coeff_mul_eq_zero_of_lt hA' hB' (k := dL - 1 + 2 * ℓ - 1) (by omega), coeff_zRow, coeff_zRow]
  ring

/-! ### The def:X1 objects of a carrier as lem:fulltwist's `d`, `Ω` of its grouped diagram
(cor:groupedknot (B): `D_L`, `D_H` are the positive lifts `carrierDiagram`) -/

variable {P P' : LabelledTuple n}

/-- A grouped carrier diagram is carried by a single closed plane curve (cor:groupedknot (B)). -/
theorem gsc_carrierDiagram_componentCount (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    (CV.carrierDiagram hn hG hS q).componentCount = 1 :=
  ((CV.groupedknot hn hG hS q).retain_all).1

/-- `w(D(W)) = w_{S,L}` for every carrier (cor:groupedknot (B) `grouped_writhe`; `0 = 0` when
piece-free). -/
theorem gsc_carrierDiagram_writhe (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    (CV.carrierDiagram hn hG hS q).writhe = CV.groupedWrithe hG q := by
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings hG hS q]
  exact geoPositiveLift_writhe hn _ _ q

/-- `R(Γ_{D(W)}) = R(L)`: the underlying curve of the grouped diagram is the carrier's corner polygon
(cor:groupedknot (B) `underlying_curve`, definitional). -/
theorem gsc_carrierDiagram_absRot (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (h1 : (CV.carrierDiagram hn hG hS q).componentCount = 1) :
    CV.absRot (CV.carrierDiagram hn hG hS q) h1 = (CV.carrierR hn hG hS q : ℤ) := rfl

/-- lem:fulltwist's `d(D(W)) = 1 − w − R` is def:X1's slot of the carrier. -/
theorem gsc_d_carrierDiagram (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (h1 : (CV.carrierDiagram hn hG hS q).componentCount = 1) :
    CV.d (CV.carrierDiagram hn hG hS q) h1 = CV.slot hn hG hS q := by
  unfold CV.d CV.slot
  rw [gsc_carrierDiagram_writhe, gsc_carrierDiagram_absRot]

/-- lem:fulltwist's `Ω(D(W))` is def:X1's factor `Ω₁(S,L)` ("The two bindings agree wherever both
apply"). -/
theorem gsc_Omega_carrierDiagram (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (h1 : (CV.carrierDiagram hn hG hS q).componentCount = 1) :
    CV.Omega (CV.carrierDiagram hn hG hS q) h1 = CV.Omega1 hn hG hS q := by
  unfold CV.Omega CV.Omega1
  rw [gsc_d_carrierDiagram, GT_groupedPoly_eq_homfly]

/-! ### A uniform carrier satisfies the alternative of thm:carrierfloor (C)/(D) -/

/-- "The nonzero-selector assumption and (4) make each such carrier uniform with turn sign `−σ`; after
a possible global orientation reversal, thm:carrierfloor (C) applies": a uniform carrier (def:wind) is
all-positive or, after reversal, all-positive (`UniformOrOneDissentCV` of its corner polygon). -/
theorem gsc_alt_of_uniform (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (hu : CV.CarrierUniform hG.crossingGeometry S q) :
    CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry S q) := by
  obtain ⟨τ, hτ, hk⟩ := hu
  have hsm : SM.Regular (geoCornerPolygon hG.crossingGeometry S q) :=
    (CV.regular_iff_sm _).mp (CV.carrierPolygon_cvRegular hn hG hS q)
  cases τ with
  | zero => exact absurd rfl hτ
  | pos =>
    left; left
    intro i
    have h : SignType.sign (det (edge (geoCornerPolygon hG.crossingGeometry S q) (i - 1))
        (edge (geoCornerPolygon hG.crossingGeometry S q) i)) = 1 := by
      rw [← turn_det]; exact hk i
    exact (CV.principalAngle_pos_iff (hsm i)).mpr (sign_eq_one_iff.mp h)
  | neg =>
    right; left
    intro i
    have h : SignType.sign (det (edge (geoCornerPolygon hG.crossingGeometry S q) (2 - i - 1))
        (edge (geoCornerPolygon hG.crossingGeometry S q) (2 - i))) = -1 := by
      rw [← turn_det]; exact hk (2 - i)
    have hneg : SM.principalTurn (geoCornerPolygon hG.crossingGeometry S q) (2 - i) < 0 :=
      (principalAngle_neg_iff _ _).mpr (sign_eq_neg_one_iff.mp h)
    rw [CV.principalTurn_eq_sm, principalTurn_reversal hsm i]
    linarith

/-- The floor of thm:carrierfloor (C)/(D) in support form, at a carrier of nonzero weight. -/
theorem gsc_floor_of_weight_ne_zero (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n) (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (hw : CV.weight hG.crossingGeometry S q ≠ 0) (d : ℤ)
    (hd : coeffAt d 0 (CV.groupedPoly hn hG hS q) ≠ 0) : CV.slot hn hG hS q ≤ d :=
  hF.coeff_zero hn hG hS q
    (gsc_alt_of_uniform hn hG hS q ((CV.weight_ne_zero_iff hG.crossingGeometry S q).mp hw)) d hd

/-! ### The interface Props (D-F11): the G10 move and the diagram identifications of GSC §3 -/

/-- **Interface (G10): the full-twist triple of GSC §3.**  "In (3), choose the positive crossing `a` and
let `D_0` be its oriented smoothing.  Switching `a` makes `a, c` an empty oppositely signed oriented RII
pair; deleting that pair gives `D_L`.  Thus `(D_L, D_H, D_0)` satisfies (T1)–(T2) of lem:fulltwist":
`q` (the retained crossing `a` of `D_H`) is positive, `D₀` is an oriented smoothing of `D_H` at `q`
(T1), and the switched diagram is carried by RII moves (T2) to a diagram `D_L'` with the polynomial of
`D_L` — the RII deletion of the switched empty pair is the one move of this unit.  `D_L` is the grouped
diagram of the `P-b` carrier, which lives on the OTHER side of the wall, so the RII deletion (performed
on the `E`-side lift `D_H`) lands on a diagram with the RECORD of `D_L` (lem:carrierword, def:record),
whose polynomial is `P_{D_L}` by ax:gausscode (`CV.gausscode_polynomial`); the printed (T2) "gives a
diagram carried to `D_L`" is read through that identification (`homfly D_L' = homfly D_L`), which is all
lem:fulltwist's first display consumes (`CV.fulltwist_skein` at `D_L'`). -/
def gsc_fulltwist_triple (D_L D_H D₀ : Diagram) (q : D_H.Γ.Crossing) : Prop :=
  D_H.IsPositive q ∧ IsOrientedSmoothing D_H q D₀ ∧
    ∃ D_L' : Diagram, Relation.ReflTransGen RII (D_H.switch q) D_L' ∧ homfly D_L' = homfly D_L

/-- **Interface: the smoothing identification of GSC §3.**  "Smoothing `a` in (3) gives two ordered
components.  The first inherits the `A` successor string and the second the `B` string … After deleting
those mixed crossings from the component records, the retained visits, cyclic order, over/under
designations, and positive crossing signs are exactly the records on the `P-ac` `A` and `B` carriers
… By lem:carrierword, def:record, ax:gausscode, and cor:groupedknot, the two component polynomials are
the pair-row grouped polynomials `Q_A, Q_B`": `D₀` has two components `i ≠ j`, whose knot restrictions
have the grouped polynomials `QA`, `QB` (ax:gausscode on the record isomorphisms), and `ℓ` is their
linking number (lem:homflyrows (ii)'s `2λ = mixedSignSum`). -/
def gsc_smoothing_split (D₀ : Diagram) (i j : Fin D₀.Γ.c) (QA QB : R) (ℓ : ℤ) : Prop :=
  D₀.componentCount = 2 ∧ i ≠ j ∧ homfly (D₀.knotRestrict i) = QA ∧ homfly (D₀.knotRestrict j) = QB ∧
    CV.IsLinkingNumber D₀ i j ℓ

/-- **The ledger data of the generic selected couple on an abstract configuration** (GSC §1–§3):
two CV-generic polygons `P` (the two-edge side, local words `P = a b A a c B b c C`) and `P'` (the
one-edge side, `E = b a A c a B c b C`) with the same crossing set, an outside support `Q`, the centre
`m` (= `b`) and the selected pair `x, w` (= `a, c`); the rows `S_m = Q ∪ {m}` (present on both sides)
and `S_xw = Q ∪ {x, w}` (present on `P`).  Fields, by GSC section:
* §1 (2) the successor carriers: `qC`, `qAB` on `P-b`; `qC'`, `qA`, `qB` on `P-ac`; the wall bijection
  `τ` of the centre row (rows 164/173: `GT_Wall`, `GT_carrierEquiv`) and the bijection `ρ` of the
  carriers of `P-b` onto those of `P-ac` other than `B` (`AB ↦ A`, `C ↦ C'`, every other carrier "identical");
* §2 (4)–(7) the selector and rotation ledger: `weight_wall`, `carrierR_wall` (the `P-b`/`E-b` carriers
  "form a path in `R_c` through the RIII family"), `weight_C` (`wt(C_ac) = −σ wt(C_b)`), `weight_AB`
  (`wt(A) wt(B) = σ wt(AB)`), `carrierR_add` ((8) `R(A)+R(B) = R(AB)` under a nonzero selector),
  `spectator_*` and `omega_wall`/`omega_C` (the common spectator reads and `Ω_C`);
* §3 the grouped full-twist triple: `writhe_wall` ((9) `w_H = w_L + 2`), `fulltwist` (the G10 RII
  deletion), `smoothing` (the two-component smoothing carries the `P-ac` records), `writhe_count`
  ((10) `w_L = w_A + w_B + 2ℓ − 1`).
`σ = ±1` is the canonical sign (1). -/
structure gsc_WallData (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (Q : Finset (Crossing P)) (m : Crossing P)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry) where
  /-- (2) `E-b : C | AB`: the carriers of the centre row correspond across the wall. -/
  τ : GeoComponent hG.crossingGeometry (Q ∪ {m}) ≃
    GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m}))
  /-- (6) the local corner signs of `P-b` and `E-b` agree carrier by carrier. -/
  weight_wall : ∀ q, CV.weight hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) (τ q) =
    CV.weight hG.crossingGeometry (Q ∪ {m}) q
  /-- (7) `rot(C_b) = rot(C_E)`, `rot(AB) = rot(AB_E)`. -/
  carrierR_wall : ∀ q, CV.carrierR hn hG' hSm' (τ q) = CV.carrierR hn hG hSm q

/-! ### REALISED: the wall part of the ledger (GSC §1 (2), §2 (6)–(7) for the `P-b`/`E-b` carriers),
from the accepted row-173 toolkit (`GT_Wall`, `GT_carrierEquiv`, `GT_weight_eq`, `GT_carrierR_eq`) on
a `GT_Endpoint` configuration -/

/-- The wall data of the centre row `Q ∪ {m}`: as `GT_Endpoint.wall` for the row `Q ∪ {x}`, with the
one selected triangle crossing now the centre `m` (`corners_apart`: two corners of `Q ∪ {m}` that are
both triangle crossings are both `m`). -/
theorem gsc_wall_of_endpoint (hG : CV.Generic P) (hG' : CV.Generic P')
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
    {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
    (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry) :
    GT_Wall hG.crossingGeometry hG'.crossingGeometry hs (triangleCrossings P e f g) (Q ∪ {m}) where
  indep := CV.geoIndependent_of_mem_Ind _ hSm
  indep' := CV.geoIndependent_of_mem_Ind _ hSm'
  key_lt v w hvw := AV_key_lt_of_gauss _ _ hs D.hef D.heg D.hfg D.gauss v w hvw
  corners_apart v w hrev := by
    rintro ⟨hvS, hwS⟩
    have key : ∀ y : Crossing P, y ∈ Q ∪ {m} → y.val ∈ triangleSupports e f g → y = m := by
      intro y hy hyT
      rcases Finset.mem_union.mp hy with hyQ | hym
      · exact absurd hyT (D.Q_out y hyQ)
      · exact Finset.mem_singleton.mp hym
    have h1 := key v.1 hvS ((F1.mem_triangleCrossings e f g v.1).mp hrev.1)
    have h2 := key w.1 hwS ((F1.mem_triangleCrossings e f g w.1).mp hrev.2.1)
    exact hrev.2.2.1 (h1.trans h2.symm)
  turn_eq := D.turn_eq
  sign_eq := D.sign_eq
  ray := D.ray

/-- **The wall part of the ledger is realised**: `τ` is the corner-cycle correspondence
`GT_carrierEquiv`, the selectors and rotations are carried (`GT_weight_eq`, `GT_carrierR_eq`). -/
noncomputable def gsc_wallData_of_endpoint (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
    {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
    (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry) :
    gsc_WallData hn hG hG' hs Q m hSm hSm' where
  τ := GT_carrierEquiv (gsc_wall_of_endpoint hG hG' D hSm hSm')
  weight_wall := GT_weight_eq hn hG hG' (gsc_wall_of_endpoint hG hG' D hSm hSm')
  carrierR_wall := GT_carrierR_eq hn hG hG' (gsc_wall_of_endpoint hG hG' D hSm hSm') hSm hSm'


/-- **The canonical sign is realised**: `σ = sgn det(u₁,u₂)` is `±1` on a CV-generic polygon at an
actual crossing (genericity (G5), `CV.Generic.g5` through `crosses_iff`). -/
theorem gsc_sigma_of_generic (hG : CV.Generic P) {i j : ZMod n} (h : IsCrossing P {i, j}) :
    ((crossingSign P i j : SignType) : ℤ) = 1 ∨ ((crossingSign P i j : SignType) : ℤ) = -1 := by
  have hne : crossingSign P i j ≠ 0 := by
    rw [← strandSign_eq_crossingSign]
    exact sign_ne_zero.mpr (hG.g5 ((hG.crosses_iff i j).mpr h))
  cases hc : crossingSign P i j with
  | zero => exact absurd hc hne
  | pos => left; rfl
  | neg => right; rfl

/-- On a `GT_Endpoint` configuration the sign `crossingSign ℓ₁ ℓ₂` is `±1`. -/
theorem gsc_sigma_of_endpoint (hG : CV.Generic P) {hP' : CrossingGeometry P'}
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
    {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
    (D : GT_Endpoint hG.crossingGeometry hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃) :
    ((crossingSign P ℓ₁ ℓ₂ : SignType) : ℤ) = 1 ∨ ((crossingSign P ℓ₁ ℓ₂ : SignType) : ℤ) = -1 :=
  gsc_sigma_of_generic hG (GT_isCrossing_of_mem D.x1 D.x2 D.l12)

/-- The ledger data proper, over the REALISED wall data `W` (`gsc_wallData_of_endpoint`): these
fields are the interface. -/
structure gsc_Ledger (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (Q : Finset (Crossing P)) (m x w : Crossing P)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry) (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (W : gsc_WallData hn hG hG' hs Q m hSm hSm') where
  /-- (1) the canonical sign `σ`. -/
  σ : ℤ
  hσ : σ = 1 ∨ σ = -1
  /-- (2) `P-b : C | AB`. -/
  qC : GeoComponent hG.crossingGeometry (Q ∪ {m})
  qAB : GeoComponent hG.crossingGeometry (Q ∪ {m})
  hCAB : qC ≠ qAB
  /-- (2) `P-ac : C | A | B`. -/
  qC' : GeoComponent hG.crossingGeometry (Q ∪ {x, w})
  qA : GeoComponent hG.crossingGeometry (Q ∪ {x, w})
  qB : GeoComponent hG.crossingGeometry (Q ∪ {x, w})
  hC'A : qC' ≠ qA
  hC'B : qC' ≠ qB
  hAB : qA ≠ qB
  /-- "The `C` carrier in (2) owns the same residual labels in all three rows … Every other carrier is
  a common spectator with the same data": every carrier but `AB` has the same read across the wall. -/
  omega_wall : ∀ q, q ≠ qAB → CV.Omega1 hn hG' hSm' (W.τ q) = CV.Omega1 hn hG hSm q
  /-- (9) "`D_H` has exactly the two additional positive residual crossings `a, c`": `w_H = w_L + 2`. -/
  writhe_wall : CV.groupedWrithe hG' (W.τ qAB) = CV.groupedWrithe hG qAB + 2
  /-- (2) the carriers of `P-b` against those of `P-ac`: `AB ↦ A`, `C ↦ C'`, spectators to themselves;
  `B` is the extra carrier of the pair row. -/
  ρ : GeoComponent hG.crossingGeometry (Q ∪ {m}) ≃
    {q' : GeoComponent hG.crossingGeometry (Q ∪ {x, w}) // q' ≠ qB}
  ρ_AB : (ρ qAB).1 = qA
  ρ_C : (ρ qC).1 = qC'
  spectator_weight : ∀ q, q ≠ qAB → q ≠ qC →
    CV.weight hG.crossingGeometry (Q ∪ {x, w}) (ρ q).1 = CV.weight hG.crossingGeometry (Q ∪ {m}) q
  spectator_omega : ∀ q, q ≠ qAB → q ≠ qC → CV.Omega1 hn hG hSxw (ρ q).1 = CV.Omega1 hn hG hSm q
  /-- "its retained signed cyclic record, grouped writhe, rotation, slot, and read are the same". -/
  omega_C : CV.Omega1 hn hG hSxw qC' = CV.Omega1 hn hG hSm qC
  /-- (5) `wt(C_ac) = −σ wt(C_b)`. -/
  weight_C : CV.weight hG.crossingGeometry (Q ∪ {x, w}) qC' = -σ * CV.weight hG.crossingGeometry (Q ∪ {m}) qC
  /-- (5) `wt(A) wt(B) = σ wt(AB)` ("including the mixed cases"). -/
  weight_AB : CV.weight hG.crossingGeometry (Q ∪ {x, w}) qA * CV.weight hG.crossingGeometry (Q ∪ {x, w}) qB =
    σ * CV.weight hG.crossingGeometry (Q ∪ {m}) qAB
  /-- (7)–(8) `R(A) + R(B) = R(AB)` when the selector is nonzero (turnlift (ii) + uniformrot (i)). -/
  carrierR_add : CV.weight hG.crossingGeometry (Q ∪ {m}) qAB ≠ 0 →
    CV.carrierR hn hG hSm qAB = CV.carrierR hn hG hSxw qA + CV.carrierR hn hG hSxw qB
  /-- §3 the oriented smoothing `D_0` of `D_H` at `a`. -/
  D₀ : Diagram
  /-- the positive crossing `a` of `D_H`. -/
  qx : (CV.carrierDiagram hn hG' hSm' (W.τ qAB)).Γ.Crossing
  /-- (T1)–(T2): the G10 RII deletion (interface `gsc_fulltwist_triple`). -/
  fulltwist : gsc_fulltwist_triple (CV.carrierDiagram hn hG hSm qAB) (CV.carrierDiagram hn hG' hSm' (W.τ qAB)) D₀ qx
  /-- the two ordered components of `D_0`. -/
  i : Fin D₀.Γ.c
  j : Fin D₀.Γ.c
  /-- the linking number `ℓ`. -/
  ℓ : ℤ
  /-- the smoothing identification (interface `gsc_smoothing_split`). -/
  smoothing : gsc_smoothing_split D₀ i j (CV.groupedPoly hn hG hSxw qA) (CV.groupedPoly hn hG hSxw qB) ℓ
  /-- (10) `w_L = w_A + w_B + 2ℓ − 1`. -/
  writhe_count : CV.groupedWrithe hG qAB = CV.groupedWrithe hG qA + CV.groupedWrithe hG qB + 2 * ℓ - 1

/-! ### The RA ledger on an abstract configuration (GSC §4–§5), PROVED from the interface -/

/-- A present row is the product over its carriers of `wt(L) Ω₁(S,L)` (def:wind + def:X1). -/
theorem gsc_rowTerm_eq_prod (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) :
    rowTerm hn hG S = ∏ q : GeoComponent hG.crossingGeometry S,
      CV.weight hG.crossingGeometry S q * CV.Omega1 hn hG hS q := by
  rw [rowTerm_of_mem_Ind hn hG hS]
  unfold CV.wind
  rw [Finset.prod_mul_distrib]

/-- Splitting two distinguished factors off a product over a `Fintype`. -/
theorem gsc_prod_split {α : Type*} [Fintype α] [DecidableEq α] (F : α → ℤ) (a b : α) (hab : a ≠ b) :
    ∏ q, F q = F a * (F b * ∏ q ∈ (Finset.univ.erase a).erase b, F q) := by
  rw [Finset.mul_prod_erase (Finset.univ.erase a) F
    (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)]
  rw [Finset.mul_prod_erase Finset.univ F (Finset.mem_univ a)]

/-- **GSC (13) on the ledger: `Ω_H − Ω_L = −ω_A ω_B`** under a nonzero selector.  lem:fulltwist's
coefficient display at the triple `(D_L, D_H, D_0)` with `d_H = d_L − 2` from (9) and (7); lem:homflyrows
(ii) with knot parity on the two components; (10)+(8) give (11); the two floors from
`CV.CarrierSlotFloor` at the uniform carriers `A`, `B` (their weights are nonzero by (5)). -/
theorem gsc_omega_jump (hF : CV.CarrierSlotFloor) {hn : 3 ≤ n} {hG : CV.Generic P} {hG' : CV.Generic P'}
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {Q : Finset (Crossing P)} {m x w : Crossing P}
    {hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry} {hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry}
    {hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry}
    {W : gsc_WallData hn hG hG' hs Q m hSm hSm'} (L : gsc_Ledger hn hG hG' hs Q m x w hSm hSxw hSm' W)
    (h0 : CV.weight hG.crossingGeometry (Q ∪ {m}) L.qAB ≠ 0) :
    CV.Omega1 hn hG' hSm' (W.τ L.qAB) - CV.Omega1 hn hG hSm L.qAB =
      -(CV.Omega1 hn hG hSxw L.qA * CV.Omega1 hn hG hSxw L.qB) := by
  -- the selectors of `A` and `B` are nonzero (5)
  have hσ0 : L.σ ≠ 0 := by rcases L.hσ with h | h <;> rw [h] <;> decide
  have hprod : CV.weight hG.crossingGeometry (Q ∪ {x, w}) L.qA *
      CV.weight hG.crossingGeometry (Q ∪ {x, w}) L.qB ≠ 0 := by
    rw [L.weight_AB]; exact mul_ne_zero hσ0 h0
  have hA0 := left_ne_zero_of_mul hprod
  have hB0 := right_ne_zero_of_mul hprod
  -- the floors
  have hFA := gsc_floor_of_weight_ne_zero hF hn hG hSxw L.qA hA0
  have hFB := gsc_floor_of_weight_ne_zero hF hn hG hSxw L.qB hB0
  -- lem:fulltwist's first display at the grouped triple, the switched diagram read through the
  -- record identification `homfly D_L' = homfly D_L`
  obtain ⟨hpos, T1, D_L', T2, hLL'⟩ := L.fulltwist
  have hsk := CV.fulltwist_skein D_L' _ L.D₀ L.qx hpos T1 T2
  rw [hLL', ← GT_groupedPoly_eq_homfly, ← GT_groupedPoly_eq_homfly] at hsk
  -- (9): `d_H = d_L − 2`
  have hd : CV.slot hn hG' hSm' (W.τ L.qAB) = CV.slot hn hG hSm L.qAB - 2 := by
    unfold CV.slot
    rw [L.writhe_wall, W.carrierR_wall]
    ring
  -- lem:fulltwist's second display, as printed (d6:2039–2044): `Ω_H = [a^{d_L−2} z^0] F_H`, the first
  -- term contributes `[a^{d_L} z^0] F_L = Ω_L`, the second `[a^{d_L−1} z^{−1}] F_A`
  have hfull : CV.Omega1 hn hG' hSm' (W.τ L.qAB) - CV.Omega1 hn hG hSm L.qAB =
      coeffAt (CV.slot hn hG hSm L.qAB - 1) (-1) (homfly L.D₀) := by
    unfold CV.Omega1
    rw [hd, hsk, coeffAt_add, CV.R.aInv_sq, CV.R.aInv_mul_z, CV.coeffAt_single_mul,
      CV.coeffAt_single_mul]
    have e1 : CV.slot hn hG hSm L.qAB - 2 - -2 = CV.slot hn hG hSm L.qAB := by ring
    have e2 : CV.slot hn hG hSm L.qAB - 2 - -1 = CV.slot hn hG hSm L.qAB - 1 := by ring
    rw [e1, e2]
    norm_num
  -- lem:homflyrows (ii) with knot parity
  obtain ⟨h2, hij, hQA, hQB, hlink⟩ := L.smoothing
  have hrow := CV.two_component_row_rows L.D₀ L.i L.j h2 hij L.ℓ hlink
  rw [hQA, hQB] at hrow
  -- (11) from (10) and (8)
  have hD : CV.slot hn hG hSxw L.qA + CV.slot hn hG hSxw L.qB = CV.slot hn hG hSm L.qAB + 2 * L.ℓ := by
    unfold CV.slot
    rw [L.writhe_count, L.carrierR_add h0]
    push_cast
    ring
  exact gsc_omega_jump_alg hfull hrow hD hFA hFB

/-- **The generic selected complementary couple on an abstract configuration** (GSC §5):
`T_E(b) − T_P(b) = wind_P(Q ∪ b) V Ω_C (Ω_H − Ω_L) = −wind_P(Q ∪ b) V Ω_C ω_A ω_B = T_P(ac)`, "including
the mixed cases rather than cancelling a possibly zero weight … no exterior factor was divided out". -/
theorem gsc_couple_of_ledger (hF : CV.CarrierSlotFloor) {hn : 3 ≤ n} {hG : CV.Generic P}
    {hG' : CV.Generic P'} {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {Q : Finset (Crossing P)}
    {m x w : Crossing P} {hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry}
    {hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry}
    {hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry}
    {W : gsc_WallData hn hG hG' hs Q m hSm hSm'} (L : gsc_Ledger hn hG hG' hs Q m x w hSm hSxw hSm' W) :
    rowTerm hn hG' (transportSupport hs (Q ∪ {m})) =
      rowTerm hn hG (Q ∪ {m}) + rowTerm hn hG (Q ∪ {x, w}) := by
  classical
  -- the three rows as products of `wt · Ω₁`
  set F : GeoComponent hG.crossingGeometry (Q ∪ {m}) → ℤ :=
    fun q => CV.weight hG.crossingGeometry (Q ∪ {m}) q * CV.Omega1 hn hG hSm q with hF_def
  set F' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) → ℤ :=
    fun q => CV.weight hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q *
      CV.Omega1 hn hG' hSm' q with hF'_def
  set G : GeoComponent hG.crossingGeometry (Q ∪ {x, w}) → ℤ :=
    fun q => CV.weight hG.crossingGeometry (Q ∪ {x, w}) q * CV.Omega1 hn hG hSxw q with hG_def
  have e1 : rowTerm hn hG (Q ∪ {m}) = ∏ q, F q := gsc_rowTerm_eq_prod hn hG hSm
  have e2 : rowTerm hn hG' (transportSupport hs (Q ∪ {m})) = ∏ q, F' q := gsc_rowTerm_eq_prod hn hG' hSm'
  have e3 : rowTerm hn hG (Q ∪ {x, w}) = ∏ q, G q := gsc_rowTerm_eq_prod hn hG hSxw
  -- the common spectator product `V`
  set V : ℤ := ∏ q ∈ (Finset.univ.erase L.qAB).erase L.qC, F q with hV
  -- (i) the centre row on `P`
  have h1 : ∏ q, F q = F L.qAB * (F L.qC * V) := gsc_prod_split F L.qAB L.qC L.hCAB.symm
  -- (ii) the centre row on `P'`, reindexed along `τ`
  have h2 : ∏ q, F' q = (CV.weight hG.crossingGeometry (Q ∪ {m}) L.qAB *
      CV.Omega1 hn hG' hSm' (W.τ L.qAB)) * (F L.qC * V) := by
    rw [← Fintype.prod_equiv W.τ (fun q => F' (W.τ q)) F' (fun _ => rfl),
      gsc_prod_split (fun q => F' (W.τ q)) L.qAB L.qC L.hCAB.symm]
    have hC : F' (W.τ L.qC) = F L.qC := by
      simp only [hF'_def, hF_def]
      rw [W.weight_wall, L.omega_wall L.qC L.hCAB]
    have hAB : F' (W.τ L.qAB) = CV.weight hG.crossingGeometry (Q ∪ {m}) L.qAB *
        CV.Omega1 hn hG' hSm' (W.τ L.qAB) := by
      simp only [hF'_def]
      rw [W.weight_wall]
    have hV' : ∏ q ∈ (Finset.univ.erase L.qAB).erase L.qC, F' (W.τ q) = V := by
      refine Finset.prod_congr rfl fun q hq => ?_
      have hqAB : q ≠ L.qAB := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
      simp only [hF'_def, hF_def]
      rw [W.weight_wall, L.omega_wall q hqAB]
    rw [hC, hAB, hV']
  -- (iii) the pair row on `P`, `B` split off and the rest reindexed along `ρ`
  have h3' : ∏ q' ∈ Finset.univ.erase L.qB, G q' = ∏ q, G (L.ρ q).1 := by
    symm
    refine Finset.prod_bij' (fun q _ => (L.ρ q).1)
      (fun q' hq' => L.ρ.symm ⟨q', (Finset.mem_erase.mp hq').1⟩)
      (fun q _ => Finset.mem_erase.mpr ⟨(L.ρ q).2, Finset.mem_univ _⟩) (fun _ _ => Finset.mem_univ _)
      (fun q _ => ?_) (fun q' hq' => ?_) (fun q _ => rfl)
    · rw [Subtype.coe_eta, Equiv.symm_apply_apply]
    · rw [Equiv.apply_symm_apply]
  have hV3 : ∏ q ∈ (Finset.univ.erase L.qAB).erase L.qC, G (L.ρ q).1 = V := by
    refine Finset.prod_congr rfl fun q hq => ?_
    have hqC : q ≠ L.qC := (Finset.mem_erase.mp hq).1
    have hqAB : q ≠ L.qAB := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
    simp only [hG_def, hF_def]
    rw [L.spectator_weight q hqAB hqC, L.spectator_omega q hqAB hqC]
  have h3 : ∏ q, G q = G L.qB * (G L.qA * (G L.qC' * V)) := by
    rw [← Finset.mul_prod_erase Finset.univ G (Finset.mem_univ L.qB), h3',
      gsc_prod_split (fun q => G (L.ρ q).1) L.qAB L.qC L.hCAB.symm, L.ρ_AB, L.ρ_C, hV3]
  -- the key identity (13), with the selector kept as a factor (the zero-selector case is trivial)
  have hkey : CV.weight hG.crossingGeometry (Q ∪ {m}) L.qAB *
      (CV.Omega1 hn hG' hSm' (W.τ L.qAB) - CV.Omega1 hn hG hSm L.qAB) =
      -(CV.weight hG.crossingGeometry (Q ∪ {m}) L.qAB *
        (CV.Omega1 hn hG hSxw L.qA * CV.Omega1 hn hG hSxw L.qB)) := by
    by_cases h0 : CV.weight hG.crossingGeometry (Q ∪ {m}) L.qAB = 0
    · rw [h0]; ring
    · rw [gsc_omega_jump hF L h0]; ring
  have hσ2 : L.σ * L.σ = 1 := by rcases L.hσ with h | h <;> rw [h] <;> norm_num
  rw [e1, e2, e3, h1, h2, h3]
  simp only [hF_def, hG_def]
  rw [L.weight_C, L.omega_C]
  linear_combination
    (CV.weight hG.crossingGeometry (Q ∪ {m}) L.qC * CV.Omega1 hn hG hSm L.qC * V) * hkey +
    (CV.weight hG.crossingGeometry (Q ∪ {m}) L.qC * CV.Omega1 hn hG hSm L.qC * V *
      CV.Omega1 hn hG hSxw L.qA * CV.Omega1 hn hG hSxw L.qB * L.σ) * L.weight_AB +
    (CV.weight hG.crossingGeometry (Q ∪ {m}) L.qC * CV.Omega1 hn hG hSm L.qC * V *
      CV.Omega1 hn hG hSxw L.qA * CV.Omega1 hn hG hSxw L.qB *
      CV.weight hG.crossingGeometry (Q ∪ {m}) L.qAB) * hσ2

end GSC

/-! ### The event-level interface and the row from it -/

/-- **Interface (G10 + the identifications of GSC §1–§3), event level.**  On every two-edge-side
configuration of the generic orbit at full availability (`GT_Endpoint`: `x, w` the selected pair, `m`
the centre, `ℓ₁` shared by `x, m`, `ℓ₂` by `x, w`, `ℓ₃` by `w, m`; R-LOC (2)–(4), lem:guardconst, the
masks) in the canonical sign branch (1) (`crossingSign ℓ₁ ℓ₂ = crossingSign ℓ₁ ℓ₃`, together with
`GT_Endpoint.sgn`: all three strand-determinant signs equal `σ`), the ledger data of `gsc_Ledger` exist
over the REALISED wall data `gsc_wallData_of_endpoint` (the corner-cycle correspondence `τ` with its
selector and rotation transport).  NEVER mapped: this is the obligation the realisation of the unit
discharges (report U_R174_REPORT.md). -/
def gsc_moves : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (e f g : ZMod n) (Q : Finset (Crossing P))
    (x w m : Crossing P) (ℓ₁ ℓ₂ ℓ₃ : ZMod n)
    (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃),
    crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃ →
    ∀ (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry) (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
      (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry),
      Nonempty (gsc_Ledger hn hG hG' hs Q m x w hSm hSxw hSm' (gsc_wallData_of_endpoint hn hG hG' D hSm hSm'))

section GSCEvent

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- The centre row `Q ∪ {m}` is present on the two-edge side (full availability). -/
theorem gsc_Ind_centre {t : E.Parameter} (ht : Punctured E δ t) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    {m : Crossing (E.curve t)} (hm : m.val ∈ triangleSupports e f g) :
    Q ∪ {m} ∈ CV.Ind (geomAt E t ht.1) :=
  PRE_union_mem_Ind_of_fullAvail hQ hfull
    (Finset.singleton_subset_iff.mpr ((F1.mem_triangleCrossings e f g m).mpr hm))
    (PRE_mem_Ind_of_card_le_one _ (by simp))

/-- The pair row `Q ∪ {x, w}` of a nonadjacent pair is present on the two-edge side. -/
theorem gsc_Ind_pair {t : E.Parameter} (ht : Punctured E δ t) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    {x w : Crossing (E.curve t)} (hx : x.val ∈ triangleSupports e f g)
    (hw : w.val ∈ triangleSupports e f g) (hxw : ¬ GeometricInterlaces (geomAt E t ht.1) x w) :
    Q ∪ {x, w} ∈ CV.Ind (geomAt E t ht.1) := by
  refine PRE_union_mem_Ind_of_fullAvail hQ hfull ?_ ?_
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact (F1.mem_triangleCrossings e f g _).mpr hx
    · exact (F1.mem_triangleCrossings e f g _).mpr hw
  · rw [CV.mem_Ind_iff]
    intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact hxw
    · exact fun h => hxw (geometricInterlaces_symm _ h)
    · exact absurd rfl hab

/-- The centre row is present on the one-edge side too (the transported `Q` is an outside support at
full availability, rows 164/173). -/
theorem gsc_Ind_centre' (hL : LocalizationData E e f g δ) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    {m : Crossing (E.curve t)} (hm : m.val ∈ triangleSupports e f g) :
    transportSupport hs (Q ∪ {m}) ∈ CV.Ind (geomAt E t' ht'.1) := by
  rw [GT_transportSupport_S]
  exact gsc_Ind_centre ht' (GT_outsideSupports_transport hL ht ht' hop hs hQ)
    (GT_fullAvail_transport hL ht ht' hop hs hQ hfull) (m := crossingTransport hs m) hm

/-- **The couple on an event configuration**, from the interface: the two-edge side `t` carries the
path with centre `m`, `Q` is an outside support at full availability, the sign branch is canonical. -/
theorem gsc_couple_event (hmove : gsc_moves) (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (x w m : Crossing (E.curve t)) (ℓ₁ ℓ₂ ℓ₃ : ZMod n)
    (hx : x.val ∈ triangleSupports e f g) (hw : w.val ∈ triangleSupports e f g)
    (hm : m.val ∈ triangleSupports e f g) (hxw : x ≠ w) (hxm : x ≠ m) (hwm : w ≠ m)
    (x1 : ℓ₁ ∈ x.val) (m1 : ℓ₁ ∈ m.val) (x2 : ℓ₂ ∈ x.val) (w2 : ℓ₂ ∈ w.val) (w3 : ℓ₃ ∈ w.val)
    (m3 : ℓ₃ ∈ m.val) (l12 : ℓ₁ ≠ ℓ₂) (l13 : ℓ₁ ≠ ℓ₃) (l23 : ℓ₂ ≠ ℓ₃)
    (hIxw : ¬ GeometricInterlaces (geomAt E t ht.1) x w) (hIxm : GeometricInterlaces (geomAt E t ht.1) x m)
    (hIwm : GeometricInterlaces (geomAt E t ht.1) w m)
    (hsgn : crossingSign (E.curve t) ℓ₂ ℓ₃ = crossingSign (E.curve t) ℓ₁ ℓ₃)
    (hsgn' : crossingSign (E.curve t) ℓ₁ ℓ₂ = crossingSign (E.curve t) ℓ₁ ℓ₃) :
    rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {m})) =
      rowTerm hn (genericAt E t ht.1) (Q ∪ {m}) + rowTerm hn (genericAt E t ht.1) (Q ∪ {x, w}) := by
  have D := GT_endpointData hL hG hR hef heg hfg ht ht' hop hs hQ hfull x w m ℓ₁ ℓ₂ ℓ₃ hx hw hm hxw hxm
    hwm x1 m1 x2 w2 w3 m3 l12 l13 l23 hIxw hIxm hIwm hsgn
  obtain ⟨L⟩ := hmove n hn (genericAt E t ht.1) (genericAt E t' ht'.1) hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃ D hsgn'
    (gsc_Ind_centre ht hQ hfull hm) (gsc_Ind_pair ht hQ hfull hx hw hIxw)
    (gsc_Ind_centre' hL ht ht' hop hs hQ hfull hm)
  exact gsc_couple_of_ledger hF L

/-- **Field `couple_canonical`** (`x = a`, `w = c`, `m = b`; `ℓ₁ = e`, `ℓ₂ = f`, `ℓ₃ = g`). -/
theorem gsc_couple_canonical (hmove : gsc_moves) (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
      (hfg' : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef' heg' hfg' →
    strandSign (E.curve t) e f = strandSign (E.curve t) e g →
    strandSign (E.curve t) e g = strandSign (E.curve t) f g →
    EdgeAB (geomAt E t ht.1) hef' heg' → EdgeBC (geomAt E t ht.1) heg' hfg' →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair heg'})) =
        rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg'}) +
          rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef', xPair hfg'}) := by
  intro t t' ht ht' hop hs hef' heg' hfg' hgen hsab hsbc hAB hBC Q hQ hfull
  exact gsc_couple_event hmove hF hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
    (xPair hef') (xPair hfg') (xPair heg') e f g GT_tri_ef GT_tri_fg GT_tri_eg
    (P1.xPair_ef_ne_fg hef' heg' hfg') (P1.xPair_ef_ne_eg hef' heg' hfg')
    (P1.xPair_eg_ne_fg hef' heg' hfg').symm
    GT_mem_pair_l GT_mem_pair_l GT_mem_pair_r GT_mem_pair_l GT_mem_pair_r GT_mem_pair_r hef heg hfg
    (GT_not_all_edges _ hgen hAB hBC) hAB (geometricInterlaces_symm _ hBC) hsbc.symm hsab

/-- **Field `couple_relabelled`**: the branches `ab` (centre `c`; `x = a`, `w = b`, `m = c`; `ℓ₁ = f`,
`ℓ₂ = e`, `ℓ₃ = g`) and `bc` (centre `a`; `x = b`, `w = c`, `m = a`; `ℓ₁ = e`, `ℓ₂ = g`, `ℓ₃ = f`). -/
theorem gsc_couple_relabelled (hmove : gsc_moves) (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
      (hfg' : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef' heg' hfg' →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    (SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) →
      EdgeAC (geomAt E t ht.1) hef' hfg' → EdgeBC (geomAt E t ht.1) heg' hfg' →
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hfg'})) =
        rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hfg'}) +
          rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef', xPair heg'})) ∧
    (SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g) →
      EdgeAB (geomAt E t ht.1) hef' heg' → EdgeAC (geomAt E t ht.1) hef' hfg' →
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef'})) =
        rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef'}) +
          rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg', xPair hfg'})) := by
  intro t t' ht ht' hop hs hef' heg' hfg' hgen Q hQ hfull
  obtain ⟨h1, h2, h3, -⟩ := hG.nonzero t ht
  have hna := (hG.generic_iff_nonalternating t ht hef' heg' hfg').mp hgen
  have hz1 : strandSign (E.curve t) e f ≠ 0 := sign_ne_zero.mpr h1
  have hz2 : strandSign (E.curve t) e g ≠ 0 := sign_ne_zero.mpr h2
  have hz3 : strandSign (E.curve t) f g ≠ 0 := sign_ne_zero.mpr h3
  constructor
  · intro hsel hAC hBC
    have hsbc := GT_signs_of_selectedAB _ _ _ hz1 hz2 hz3 hna hsel
    -- `x = a`, `w = b`, `m = c`; `ℓ₁ = f`, `ℓ₂ = e`, `ℓ₃ = g`
    refine gsc_couple_event hmove hF hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
      (xPair hef') (xPair heg') (xPair hfg') f e g GT_tri_ef GT_tri_eg GT_tri_fg
      (P1.xPair_ef_ne_eg hef' heg' hfg') (P1.xPair_ef_ne_fg hef' heg' hfg')
      (P1.xPair_eg_ne_fg hef' heg' hfg')
      GT_mem_pair_r GT_mem_pair_l GT_mem_pair_l GT_mem_pair_l GT_mem_pair_r GT_mem_pair_r
      hef.symm hfg heg (GT_not_all_edges' _ hgen hAC hBC) hAC hBC hsbc ?_
    -- `crossingSign f e = crossingSign f g ⟸ s_a = −s_b, s_b = s_c`
    show crossingSign (E.curve t) f e = crossingSign (E.curve t) f g
    rw [crossingSign_swap (E.curve t) e f]
    show -strandSign (E.curve t) e f = strandSign (E.curve t) f g
    rw [hsel, neg_neg, hsbc]
  · intro hsel hAB hAC
    have hsab := GT_signs_of_selectedBC _ _ _ hz1 hz2 hz3 hna hsel
    -- `x = b`, `w = c`, `m = a`; `ℓ₁ = e`, `ℓ₂ = g`, `ℓ₃ = f`
    refine gsc_couple_event hmove hF hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
      (xPair heg') (xPair hfg') (xPair hef') e g f GT_tri_eg GT_tri_fg GT_tri_ef
      (P1.xPair_eg_ne_fg hef' heg' hfg') (P1.xPair_ef_ne_eg hef' heg' hfg').symm
      (P1.xPair_ef_ne_fg hef' heg' hfg').symm
      GT_mem_pair_l GT_mem_pair_l GT_mem_pair_r GT_mem_pair_r GT_mem_pair_l GT_mem_pair_r
      heg hef hfg.symm (GT_not_all_edges'' _ hgen hAB hAC) (geometricInterlaces_symm _ hAB)
      (geometricInterlaces_symm _ hAC) ?_ ?_
    · -- `crossingSign g f = crossingSign e f ⟸ s_a = s_b, s_b = −s_c`
      show crossingSign (E.curve t) g f = crossingSign (E.curve t) e f
      rw [crossingSign_swap (E.curve t) f g]
      show -strandSign (E.curve t) f g = strandSign (E.curve t) e f
      rw [hsab, hsel]
    · -- `crossingSign e g = crossingSign e f ⟸ s_a = s_b`
      exact hsab.symm

/-- **The bundle of row 174 from the interface** at a radius carrying rows 164, 172's table and the
event sign data. -/
theorem gsc_genericSelectedData (hmove : gsc_moves) (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) : GenericSelectedData hn E e f g δ where
  couple_canonical := gsc_couple_canonical hmove hF hn hL hG hR hef heg hfg
  couple_relabelled := gsc_couple_relabelled hmove hF hn hL hG hR hef heg hfg

end GSCEvent

/-- **The RA ledger of row 174** (D-F11): from the interface `gsc_moves` and the carrier floor
`CV.CarrierSlotFloor` (thm:carrierfloor (C)+(D) in def:X1's symbols), the row in its fixed shape.  The
radius is the common one of rows 164 (`localization`), 172's table (`generic_table`) and the event sign
data (`AV_exists_eventRadius`), as for row 173. -/
theorem gsc_ledger (hmove : gsc_moves) (hF : CV.CarrierSlotFloor) : RowShape @GenericSelectedData := by
  intro n _ hn E e f g h3 h4e h4f h4g hE
  obtain ⟨δL, hδL, hδLr, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  obtain ⟨δG, hδG, -, hGT⟩ := generic_table E e f g h3 h4e h4f h4g hE
  obtain ⟨δR, hδR, -, hR⟩ := AV_exists_eventRadius hE
  have hef : e ≠ f := AV_ne_of_remote h3.1
  have hfg : f ≠ g := AV_ne_of_remote h3.2.1
  have heg : e ≠ g := AV_ne_of_remote h3.2.2.1
  refine ⟨min δL (min δG δR), lt_min hδL (lt_min hδG hδR), (min_le_left _ _).trans hδLr, ?_⟩
  have hL' := F1.localizationData_mono (min_le_left δL (min δG δR)) hL
  have hGT' := SEL_genericTableData_mono ((min_le_right δL (min δG δR)).trans (min_le_left δG δR)) hGT
  have hR' := AV_eventRadius_mono ((min_le_right δL (min δG δR)).trans (min_le_right δG δR)) hR
  exact gsc_genericSelectedData hmove hF hn hL' hGT' hR' hef heg hfg


/-- The row in the exact signature of the leaf `generic_selected`, from the interface and the carrier
floor: once `gsc_moves` is realised (`hmove`), the leaf is
`gsc_generic_selected_of_moves hmove (carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC) hn E e f g h3 h4e h4f h4g hE`. -/
theorem gsc_generic_selected_of_moves (hmove : gsc_moves) (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n)
    (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectedData hn E e f g δ :=
  gsc_ledger hmove hF n hn E e f g h3 h4e h4f h4g hE

/-! ### Unit U-176 (prefix `est_`) — R:extreme_transport: interface Props, ledger, realisation status

Written 2026-09-15 by the U-176 prover. Source: reference/R/RA/R_EXTREME_SINGLETON_TRANSPORT_PROOF.md
("Statement and canonical data", §1–§4). Pattern (PLAN_FINAL §4 174/176/177, D-F11): the RII port
relation and the diagram identifications the printed proof establishes by geometry are stated as an
explicit INTERFACE (`est_PortData` per affected carrier, `est_port_relation` over the event data); the RA
ledger — lem:fulltwist (`CV.fulltwist_coefficient`), lem:homflyrows (ii) (`CV.homflyrows.two_component_row`),
the floor `CV.CarrierSlotFloor` at the two clean outer carriers, knot parity through `mindegAZ_mul`, and the
carrier-by-carrier transport of the unaffected carriers (`EXT_homfly_wall`) — is PROVED from it
(`est_ledger`). The interface is never mapped. -/

section EST

open SM.Carrier SM.Link

/-! #### A. Laurent-ring bookkeeping for (11) and (16) -/

/-- `(p − q)_d = p_d − q_d` in `ℤ[a^{±1}]`. -/
theorem est_coeff_sub (p q : LaurentPolynomial ℤ) (d : ℤ) : (p - q).coeff d = p.coeff d - q.coeff d := by
  simp

/-- (16): "Extracting the two monomials of `a − a^{-1}`" from the `[z^{-1}]` row (11)
`[z^{-1}] P(D_A) = (a − a^{-1}) a^{-2ℓ} [z^0] G`: `[a^{s-1} z^{-1}] P(D_A) = [a^{s-2+2ℓ}] G − [a^{s+2ℓ}] G`. -/
theorem est_coeffAt_of_zRow (F G : R) (s ℓ : ℤ)
    (h : zRow (-1) F = (aPow 1 - aPow (-1)) * aPow (-(2 * ℓ)) * zRow 0 G) :
    coeffAt (s - 1) (-1) F = coeffAt (s - 2 + 2 * ℓ) 0 G - coeffAt (s + 2 * ℓ) 0 G := by
  rw [← coeff_zRow, h, sub_mul, sub_mul, est_coeff_sub, mul_assoc, mul_assoc,
    coeff_T_mul', coeff_T_mul', coeff_T_mul', coeff_T_mul', coeff_zRow, coeff_zRow]
  congr 2 <;> ring

/-- "Therefore `f_1 f_2` has no `a`-exponent below `D`" (§3): a coefficient of a product of two nonzero
Laurent polynomials below the sum of their floors vanishes (`mindegAZ_mul`, the corner lane's FR-CC-3 route). -/
theorem est_coeffAt_mul_eq_zero (f g : R) (hf : f ≠ 0) (hg : g ≠ 0) (a b d : ℤ)
    (ha : a ≤ mindegAZ f) (hb : b ≤ mindegAZ g) (hd : d < a + b) : coeffAt d 0 (f * g) = 0 := by
  by_contra hne
  have := (mindegAZ_spec (mul_ne_zero hf hg)).2 d 0 hne
  rw [mindegAZ_mul hf hg] at this
  omega

/-! #### B. The def:X1 data of a carrier read on its grouped diagram `D(W) = carrierDiagram`
(cor:groupedknot (B), `GT_groupedPoly_eq_homfly`): `w(D) = w_{S,L}`, `R(Γ_D) = R(L)`, `d(D) = slot`,
`Ω(D) = Ω₁(S,L)` — the "two bindings agree" sentence of lem:fulltwist (d6:2020–2022). -/

/-- `w(D(W)) = w_{S,L}` (def:positive-lift: the writhe of the positive lift is its crossing count;
`groupedWrithe_eq_card_geoCarrierCrossings`). -/
theorem est_carrierDiagram_writhe (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    (CV.carrierDiagram hn hG hS q).writhe = CV.groupedWrithe hG q := by
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings hG hS q]
  exact geoPositiveLift_writhe hn _ _ q

/-- `d(D(W)) = 1 − w_{S,L} − R(L) = slot` (`absRot` of the lift IS `carrierR`: the unique component of the
lift is the corner polygon, `geoPositiveLift_comp`, definitionally). -/
theorem est_carrierDiagram_d (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    CV.d (CV.carrierDiagram hn hG hS q) rfl = CV.slot hn hG hS q := by
  unfold CV.d CV.slot
  rw [est_carrierDiagram_writhe]
  rfl

/-- `Ω(D(W)) = Ω₁(S,L)`. -/
theorem est_carrierDiagram_Omega (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    CV.Omega (CV.carrierDiagram hn hG hS q) rfl = CV.Omega1 hn hG hS q := by
  unfold CV.Omega CV.Omega1
  rw [est_carrierDiagram_d, GT_groupedPoly_eq_homfly]

/-! #### C. The interface: the RII port relation and the auxiliary components (§1–§3 of the RA text)

For one row `j` of the full-availability fibre, `q` the affected carrier of `S = Q ∪ {j}` on the `K3`
side `H` (its grouped diagram `D_0 = carrierDiagram q`, "clean": the two other triangle crossings are
dominated), `q'` its copy on the empty side `L` (grouped diagram `D_+ = carrierDiagram q'`, which
retains the two other triangle crossings as "the two positive self-crossings `q, r`"), and `y` the lift
crossing of the one to be switched ("`q`" of the text). -/

/-- **The RII port data of an affected singleton carrier** (R_EXTREME_SINGLETON_TRANSPORT_PROOF.md §1–§3),
field by field: (T2) "Switching `q` makes it negative; the adjacent local port pairs then make `q, r` an
empty opposite-sign oriented RII pair. Deleting it leaves exactly `D_0`" (`port`); (T1) "`D_A =
smooth_q(D_+)`" (`smooth`), "Smoothing `q` splits `D_+` into two components" (`two`, `i`, `j`); (9a)/(10)
"the exact component data" — the two components have the polynomials of the two clean outer carriers
`Λ₁, Λ₂` of the full support `S_full = Q ∪ {x, y, z}` on `L` (`Sf`, `poly₁`, `poly₂`: cor:groupedknot (A)(B),
lc:single-crossing for the kink `r`); "`ell` the linking number of the two components" (`link`); (14)
`w_0 = w_1 + w_2 + 2ℓ` (`writhe`); (13) `R_1 + R_2 + 1 = R` (`rot`, turnlift (ii) + the corner ledger (12));
(12) each clean outer carrier is uniform or exactly one-dissent after a possible reversal (`alt₁`, `alt₂`). -/
structure est_PortData (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
    {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) (q' : GeoComponent hG'.crossingGeometry S')
    (y : (CV.carrierDiagram hn hG' hS' q').Γ.Crossing) where
  /-- (T2) the RII port relation: the switched `D_+` is carried to `D_0` by oriented RII moves -/
  port : Relation.ReflTransGen RII ((CV.carrierDiagram hn hG' hS' q').switch y) (CV.carrierDiagram hn hG hS q)
  /-- `D_A = smooth_q(D_+)` -/
  DA : Diagram
  /-- (T1) -/
  smooth : IsOrientedSmoothing (CV.carrierDiagram hn hG' hS' q') y DA
  /-- "Smoothing `q` splits `D_+` into two components" -/
  two : DA.componentCount = 2
  i : Fin DA.Γ.c
  j : Fin DA.Γ.c
  ij : i ≠ j
  /-- `S_full = Q ∪ {x, y, z}`, "an independent `L`-side support" -/
  Sf : Finset (Crossing P')
  hSf : Sf ∈ CV.Ind hG'.crossingGeometry
  /-- the two clean outer carriers of (10) -/
  Λ₁ : GeoComponent hG'.crossingGeometry Sf
  Λ₂ : GeoComponent hG'.crossingGeometry Sf
  /-- (9a) "polynomials `(Q_C, Q_B)`" (resp. `(Q_A, Q_B)`, `(Q_C, Q_A)`) -/
  poly₁ : homfly (DA.knotRestrict i) = CV.groupedPoly hn hG' hSf Λ₁
  poly₂ : homfly (DA.knotRestrict j) = CV.groupedPoly hn hG' hSf Λ₂
  /-- "`ell` … the linking number of the two components" -/
  ℓ : ℤ
  link : CV.IsLinkingNumber DA i j ℓ
  /-- (14) `w_0 = w_1 + w_2 + 2ℓ` -/
  writhe : CV.groupedWrithe hG q = CV.groupedWrithe hG' Λ₁ + CV.groupedWrithe hG' Λ₂ + 2 * ℓ
  /-- (13) `R_1 + R_2 + 1 = R` -/
  rot : (CV.carrierR hn hG hS q : ℤ) = CV.carrierR hn hG' hSf Λ₁ + CV.carrierR hn hG' hSf Λ₂ + 1
  /-- (12) "each clean outer carrier … is exactly one-dissent, never uniform with the wrong sign" -/
  alt₁ : CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₁)
  alt₂ : CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₂)

/-! #### D. The ledger of the affected carrier: (7), (8), (11), (15), (16) -/

/-- **(16) `Ω_+ = Ω_0`**: from the port data, `w_+ = w_0 + 2` and `R(D_+) = R(D_0)` (7), lem:fulltwist gives
`Ω_+ − Ω_0 = [a^{d_0 − 1} z^{-1}] P(D_A)` (8); lem:homflyrows (ii) with knot parity gives the `[z^{-1}]`
row (11); the two extracted monomials sit at `a^{D−4}` and `a^{D−2}` with `D = d_1 + d_2 = d_0 + 2 + 2ℓ` (15),
below the floor `D` of `f_1 f_2` (thm:carrierfloor (C)+(D) at the two clean outer carriers, `CarrierSlotFloor`
+ `mindegAZ_mul`): both vanish. "The last equality is exactly the floor, not an assumed sharpness statement." -/
theorem est_omega1_eq_of_port (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n) {P P' : LabelledTuple n}
    (hG : CV.Generic P) (hG' : CV.Generic P')
    {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) (q' : GeoComponent hG'.crossingGeometry S')
    (y : (CV.carrierDiagram hn hG' hS' q').Γ.Crossing)
    (D : est_PortData hn hG hG' hS hS' q q' y)
    (hw : CV.groupedWrithe hG' q' = CV.groupedWrithe hG q + 2)
    (hR : CV.carrierR hn hG' hS' q' = CV.carrierR hn hG hS q) :
    CV.Omega1 hn hG' hS' q' = CV.Omega1 hn hG hS q := by
  have hpos : (CV.carrierDiagram hn hG' hS' q').IsPositive y := geoPositiveLift_isPositive hn _ _ q' y
  -- (7) `d_+ = d_0 − 2`
  have hd : CV.d (CV.carrierDiagram hn hG' hS' q') rfl = CV.d (CV.carrierDiagram hn hG hS q) rfl - 2 := by
    rw [est_carrierDiagram_d, est_carrierDiagram_d]
    unfold CV.slot
    rw [hw, hR]; ring
  -- (8) lem:fulltwist
  have hft := CV.fulltwist_coefficient (CV.carrierDiagram hn hG hS q) (CV.carrierDiagram hn hG' hS' q')
    D.DA y hpos D.smooth D.port rfl rfl hd
  rw [est_carrierDiagram_Omega, est_carrierDiagram_Omega, est_carrierDiagram_d] at hft
  -- (11) lem:homflyrows (ii)
  have hrow := CV.homflyrows.two_component_row D.DA D.i D.j D.two D.ij D.ℓ D.link
  rw [D.poly₁, D.poly₂] at hrow
  have hcoef := est_coeffAt_of_zRow _ _ (CV.slot hn hG hS q) D.ℓ hrow
  -- the floor at the two clean outer carriers
  have hne₁ := CV.cvt_groupedPoly_ne_zero hn hG' D.hSf D.Λ₁
  have hne₂ := CV.cvt_groupedPoly_ne_zero hn hG' D.hSf D.Λ₂
  have h₁ := hF hn hG' D.hSf D.Λ₁ D.alt₁
  have h₂ := hF hn hG' D.hSf D.Λ₂ D.alt₂
  -- (15) `D = d_0 + 2 + 2ℓ`
  have hsum : CV.slot hn hG' D.hSf D.Λ₁ + CV.slot hn hG' D.hSf D.Λ₂ =
      CV.slot hn hG hS q + 2 + 2 * D.ℓ := by
    unfold CV.slot
    have := D.writhe
    have := D.rot
    omega
  -- (16)
  have hz₁ := est_coeffAt_mul_eq_zero _ _ hne₁ hne₂ _ _ (CV.slot hn hG hS q - 2 + 2 * D.ℓ) h₁ h₂ (by omega)
  have hz₂ := est_coeffAt_mul_eq_zero _ _ hne₁ hne₂ _ _ (CV.slot hn hG hS q + 2 * D.ℓ) h₁ h₂ (by omega)
  rw [hcoef, hz₁, hz₂, sub_zero] at hft
  linarith

/-! #### E. The event-level configuration of a singleton row (R-LOC-2, R-PAR, the sign radius)

Side `t` is the `K3` side `H` (`CompleteLocal`), `t'` the empty side `L`; `j` the selected triangle
crossing, `u, v` the two others; `S = Q ∪ {j}`, `S' = transportSupport hs S`. -/

section ESTEvent

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- Three distinct triangle crossings exhaust the triangle. -/
theorem est_tri_exhaust {t : E.Parameter} (hef' : IsCrossing (E.curve t) {e, f})
    (heg' : IsCrossing (E.curve t) {e, g}) (hfg' : IsCrossing (E.curve t) {f, g})
    {j u v : Crossing (E.curve t)} (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g)
    (hv : v.val ∈ triangleSupports e f g) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    (c : Crossing (E.curve t)) (hc : c.val ∈ triangleSupports e f g) : c = j ∨ c = u ∨ c = v := by
  rcases GT_tri_cases t hef' heg' hfg' j hj with hj' | hj' | hj' <;>
  rcases GT_tri_cases t hef' heg' hfg' u hu with hu' | hu' | hu' <;>
  rcases GT_tri_cases t hef' heg' hfg' v hv with hv' | hv' | hv' <;>
  first
  | exact absurd (hj'.trans hu'.symm) hju
  | exact absurd (hj'.trans hv'.symm) hjv
  | exact absurd (hu'.trans hv'.symm) huv
  | (rcases GT_tri_cases t hef' heg' hfg' c hc with h | h | h <;> first
      | exact Or.inl (h.trans hj'.symm)
      | exact Or.inr (Or.inl (h.trans hu'.symm))
      | exact Or.inr (Or.inr (h.trans hv'.symm)))

/-- On the `K3` side any two distinct triangle crossings interlace. -/
theorem est_interlaces_of_complete {t : E.Parameter} (ht : t.val ≠ 0)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht) hef' heg' hfg')
    {u v : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hv : v.val ∈ triangleSupports e f g)
    (huv : u ≠ v) : GeometricInterlaces (geomAt E t ht) u v := by
  obtain ⟨hAB, hAC, hBC⟩ := hcomp
  rcases GT_tri_cases t hef' heg' hfg' u hu with rfl | rfl | rfl <;>
  rcases GT_tri_cases t hef' heg' hfg' v hv with rfl | rfl | rfl <;>
  first
  | exact absurd rfl huv
  | exact hAB
  | exact hAC
  | exact hBC
  | exact geometricInterlaces_symm _ hAB
  | exact geometricInterlaces_symm _ hAC
  | exact geometricInterlaces_symm _ hBC

/-- A crossing of `S = Q ∪ {j}` in the triangle is `j`. -/
theorem est_eq_j_of_mem_S_T {t : E.Parameter} (ht : t.val ≠ 0) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht) e f g) {j c : Crossing (E.curve t)}
    (hcS : c ∈ Q ∪ {j}) (hcT : c.val ∈ triangleSupports e f g) : c = j := by
  rcases Finset.mem_union.mp hcS with h | h
  · exact absurd ((F1.mem_triangleCrossings e f g c).mpr hcT)
      (Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 h)
  · exact Finset.mem_singleton.mp h

/-- `S = Q ∪ {j}` is independent (full availability; `PRE_union_mem_Ind_of_fullAvail`). -/
theorem est_S_ind {t : E.Parameter} (ht : t.val ≠ 0) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht) e f g) (hfull : FullAvail (geomAt E t ht) e f g Q)
    {j : Crossing (E.curve t)} (hj : j.val ∈ triangleSupports e f g) :
    Q ∪ {j} ∈ CV.Ind (geomAt E t ht) :=
  PRE_union_mem_Ind_of_fullAvail hQ hfull
    (Finset.singleton_subset_iff.mpr ((F1.mem_triangleCrossings e f g j).mpr hj))
    (PRE_mem_Ind_of_card_le_one _ (by rw [Finset.card_singleton]))

/-- `S' = Q' ∪ {j'}` is independent on the far side (`Q'` outside with full availability, R-LOC-2 (4)). -/
theorem est_S'_ind (hL : LocalizationData E e f g δ) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) :
    transportSupport hs (Q ∪ {j}) ∈ CV.Ind (geomAt E t' ht'.1) := by
  rw [GT_transportSupport_S]
  exact est_S_ind ht'.1 (GT_outsideSupports_transport hL ht ht' hop hs hQ)
    (GT_fullAvail_transport hL ht ht' hop hs hQ hfull) hj

/-- **The wall data of a singleton row** `S = Q ∪ {j}` (as `GT_Endpoint.wall`: the only triangle crossing
of `S` is `j`, so no two corners form a reversed pair). -/
theorem est_wall (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g)
    (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t') (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) :
    GT_Wall (geomAt E t ht.1) (geomAt E t' ht'.1) hs (triangleCrossings (E.curve t) e f g) (Q ∪ {j}) where
  indep := CV.geoIndependent_of_mem_Ind _ (est_S_ind ht.1 hQ hfull hj)
  indep' := CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj)
  key_lt v w hvw := AV_key_lt_of_gauss _ _ hs hef heg hfg (hL.gauss_words t t' ht ht' hop hs) v w hvw
  corners_apart v w hrev := by
    rintro ⟨hvS, hwS⟩
    have h1 := est_eq_j_of_mem_S_T ht.1 hQ hvS ((F1.mem_triangleCrossings e f g v.1).mp hrev.1)
    have h2 := est_eq_j_of_mem_S_T ht.1 hQ hwS ((F1.mem_triangleCrossings e f g w.1).mp hrev.2.1)
    exact hrev.2.2.1 (h1.trans h2.symm)
  turn_eq := hR.turn_eq t t' ht ht'
  sign_eq := hR.sign_eq t t' ht ht'
  ray := by
    obtain ⟨r, hr⟩ := hR.ray
    refine ⟨r, fun h => ⟨(hr t ht h).1, ?_⟩⟩
    rw [(hr t' ht' h).2, (hr t ht h).2]

/-- On `H` the two unselected triangle crossings are dominated by `j` ("the other two local crossings are
dominated"). -/
theorem est_not_mem_U_H {t : E.Parameter} (ht : t.val ≠ 0)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) {j u : Crossing (E.curve t)} (hj : j.val ∈ triangleSupports e f g)
    (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u) : u ∉ CV.U (geomAt E t ht) (Q ∪ {j}) := by
  rw [CV.mem_U_iff]
  rintro ⟨-, h⟩
  exact h j (Finset.mem_union_right _ (Finset.mem_singleton_self j))
    (est_interlaces_of_complete ht hcomp hu hj hju.symm)

/-- On `L` the two unselected triangle crossings survive ("On `L` they survive as the two positive
self-crossings `q, r`"): `u' ∉ S'`, `u'` interlaces neither `j'` (empty local graph, R-LOC-2 corollary) nor
any member of `Q'` (full availability, R-LOC-2 (4)). -/
theorem est_mem_U_L (hL : LocalizationData E e f g δ) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j u : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u) :
    crossingTransport hs u ∈ CV.U (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) := by
  rw [CV.mem_U_iff]
  constructor
  · rw [mem_transportSupport_iff]
    intro huS
    exact hju (est_eq_j_of_mem_S_T ht.1 hQ huS hu).symm
  · intro x' hx'
    obtain ⟨x, rfl⟩ := (crossingTransport hs).surjective x'
    rw [mem_transportSupport_iff] at hx'
    rcases Finset.mem_union.mp hx' with hxQ | hxj
    · have hxT : x.val ∉ triangleSupports e f g := fun h =>
        Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hxQ
          ((F1.mem_triangleCrossings e f g x).mpr h)
      rw [hL.interlace_toggle t t' ht ht' hop hs u x, L.xor_iff_of_not_right (fun h => hxT h.2.2)]
      have huA : u ∈ avail (geomAt E t ht.1) e f g Q := by
        rw [hfull]; exact (F1.mem_triangleCrossings e f g u).mpr hu
      exact fun h => ((F1.mem_avail _ e f g Q u).mp huA).2 x hxQ (geometricInterlaces_symm _ h)
    · obtain rfl := Finset.mem_singleton.mp hxj
      rw [hL.complement_on_triangle t t' ht ht' hop hs u x hu hj hju.symm]
      exact fun h => h (est_interlaces_of_complete ht.1 hcomp hu hj hju.symm)

end ESTEvent

/-! #### F. Retained crossings across the wall: the common carrier, the spectators and the affected carrier

(5)/(§1): on `H` the two unselected local crossings `u, v` are dominated, so every carrier of `S` retains
only outside crossings; on `L` they are the two positive self-crossings of ONE carrier — the copy of the
carrier `q₀` owning their two visits on the edge they share (adjacent visits, R-LOC-2 (2)). Every other
carrier's retained set is carried by the edge-pair transport. -/

section ESTRetained

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

omit [NeZero n] in
/-- The label shared by two triangle crossings is not a label of the third. -/
theorem est_shared_not_mem_third (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {P : LabelledTuple n}
    {j u v : Crossing P} (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g)
    (hv : v.val ∈ triangleSupports e f g) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    {ℓ : ZMod n} (hℓu : ℓ ∈ u.val) (hℓv : ℓ ∈ v.val) : ℓ ∉ j.val := by
  have hmem : ∀ {s : Finset (ZMod n)}, s ∈ triangleSupports e f g →
      s = {e, f} ∨ s = {e, g} ∨ s = {f, g} := by
    intro s hs; simpa [triangleSupports] using hs
  have hju' : j.val ≠ u.val := fun h => hju (Subtype.ext h)
  have hjv' : j.val ≠ v.val := fun h => hjv (Subtype.ext h)
  have huv' : u.val ≠ v.val := fun h => huv (Subtype.ext h)
  intro hℓj
  rcases hmem hj with h1 | h1 | h1 <;> rcases hmem hu with h2 | h2 | h2 <;>
    rcases hmem hv with h3 | h3 | h3 <;>
    first
    | exact hju' (h1.trans h2.symm)
    | exact hjv' (h1.trans h3.symm)
    | exact huv' (h2.trans h3.symm)
    | (rw [h1] at hℓj; rw [h2] at hℓu; rw [h3] at hℓv
       simp only [Finset.mem_insert, Finset.mem_singleton] at hℓj hℓu hℓv
       rcases hℓj with rfl | rfl <;> rcases hℓu with h | h <;> rcases hℓv with h' | h' <;>
         first
         | exact hef h | exact hef h' | exact hef h.symm | exact hef h'.symm
         | exact heg h | exact heg h' | exact heg h.symm | exact heg h'.symm
         | exact hfg h | exact hfg h' | exact hfg h.symm | exact hfg h'.symm)

/-- A visit on an edge that is not an edge of `j` is a good mark of `S = Q ∪ {j}` (its reversed partners are
visits of the other triangle crossings, none of which is a corner). -/
theorem est_good_of_edge {t : E.Parameter} (ht : t.val ≠ 0) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht) e f g) {j : Crossing (E.curve t)} {w : Visit (E.curve t)}
    (hw : w.2.val ∉ j.val) : GT_Good (triangleCrossings (E.curve t) e f g) (Q ∪ {j}) (Sum.inr w) := by
  intro v' hv' u hrev hu
  obtain rfl := Sum.inr.inj hv'
  have huS : u.1 ∈ Q ∪ {j} := hu
  have huj : u.1 = j := est_eq_j_of_mem_S_T ht hQ huS ((F1.mem_triangleCrossings e f g u.1).mp hrev.2.1)
  apply hw
  rw [hrev.2.2.2, ← huj]
  exact u.2.property

/-- An unselected triangle crossing is not in `S`. -/
theorem est_not_mem_S {t : E.Parameter} (ht : t.val ≠ 0) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht) e f g) {j u : Crossing (E.curve t)}
    (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u) : u ∉ Q ∪ {j} :=
  fun h => hju (est_eq_j_of_mem_S_T ht hQ h hu).symm

/-- On `H` the two visits of `u, v` on their shared edge lie on one carrier of `S` (adjacent visits of two
unselected crossings, `GT_owner_eq_of_adjacent`). -/
theorem est_owner_shared_eq (hL : LocalizationData E e f g δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t : E.Parameter} (ht : Punctured E δ t) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) {j u v : Crossing (E.curve t)}
    (hu : u.val ∈ triangleSupports e f g) (hv : v.val ∈ triangleSupports e f g)
    (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v) {ℓ : ZMod n} (hℓu : ℓ ∈ u.val) (hℓv : ℓ ∈ v.val) :
    geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) =
      geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn v ℓ hℓv)) :=
  GT_owner_eq_of_adjacent _ _ (GT_adjacent_of_shared hL hef heg hfg t ht hu hv huv hℓu hℓv) rfl
    (est_not_mem_S ht.1 hQ hu hju) (est_not_mem_S ht.1 hQ hv hjv)

/-- On `H` no triangle crossing is retained by any carrier of `S`. -/
theorem est_not_retained_H {t : E.Parameter} (ht : Punctured E δ t)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)} (hj : j.val ∈ triangleSupports e f g)
    (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})) {c : Crossing (E.curve t)}
    (hc : c ∈ geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q) : c.val ∉ triangleSupports e f g := by
  intro hcT
  have hcU : c ∈ CV.U (geomAt E t ht.1) (Q ∪ {j}) := by
    have := geoCarrierCrossings_subset_U _ (CV.geoIndependent_of_mem_Ind _ (est_S_ind ht.1 hQ hfull hj)) q hc
    rw [mem_geoSupportUnselected_iff] at this
    exact (CV.mem_U_iff _ _ c).mpr this
  by_cases hcj : c = j
  · subst hcj
    exact ((CV.mem_U_iff _ _ c).mp hcU).1 (Finset.mem_union_right _ (Finset.mem_singleton_self c))
  · exact est_not_mem_U_H ht.1 hcomp Q hj hcT (Ne.symm hcj) hcU

/-- An outside crossing is retained by the copy of a carrier iff it is retained by the carrier (all its visits
are good marks; `GT_owner_transport`). -/
theorem est_retained_outside_iff (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f)
    (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t') (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)} (hj : j.val ∈ triangleSupports e f g)
    (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})) {c : Crossing (E.curve t)}
    (hcT : c.val ∉ triangleSupports e f g) :
    crossingTransport hs c ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) ↔
      c ∈ geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q := by
  set W := est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj
  have hgood : ∀ v : Visit (E.curve t), v.1 = c →
      GT_Good (triangleCrossings (E.curve t) e f g) (Q ∪ {j}) (Sum.inr v) := fun v hv =>
    GT_good_of_not_mem _ _ (by rw [hv]; exact fun h => hcT ((F1.mem_triangleCrossings e f g c).mp h))
  rw [mem_geoCarrierCrossings, mem_geoCarrierCrossings, mem_transportSupport_iff]
  constructor
  · rintro ⟨hcS, hall⟩
    refine ⟨hcS, fun v hv => ?_⟩
    have := hall (visitTransport hs v) (by rw [visitTransport_crossing, hv])
    rw [← markTransport_visit, GT_owner_transport W (hgood v hv)] at this
    exact (GT_carrierEquiv W).injective this
  · rintro ⟨hcS, hall⟩
    refine ⟨hcS, fun w hw => ?_⟩
    obtain ⟨v, rfl⟩ := (visitTransport hs).surjective w
    rw [visitTransport_crossing] at hw
    have hvc : v.1 = c := (crossingTransport hs).injective hw
    rw [← markTransport_visit, GT_owner_transport W (hgood v hvc), hall v hvc]

/-- An unselected triangle crossing `u` is retained on `L` by the copy of `q` iff `q` owns the visit of `u`
on the edge `ℓ` it shares with the other unselected crossing (that visit is good; `u' ∈ U(S')`). -/
theorem est_retained_u_iff (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f)
    (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t') (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j u : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    {ℓ : ZMod n} (hℓu : ℓ ∈ u.val) (hℓj : ℓ ∉ j.val)
    (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})) :
    crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) ↔
      geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) = q := by
  set W := est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj
  have huU' := est_mem_U_L hL ht ht' hop hs hcomp hQ hfull hj hu hju
  have hgood : GT_Good (triangleCrossings (E.curve t) e f g) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) :=
    est_good_of_edge ht.1 hQ hℓj
  rw [mem_geoCarrierCrossings]
  constructor
  · rintro ⟨-, hall⟩
    have := hall (visitTransport hs (visitOn u ℓ hℓu)) rfl
    rw [← markTransport_visit, GT_owner_transport W hgood] at this
    exact (GT_carrierEquiv W).injective this
  · intro hq
    refine ⟨((CV.mem_U_iff _ _ _).mp huU').1, fun w hw => ?_⟩
    rw [CV.owner_eq_of_mem_U _ (est_S'_ind hL ht ht' hop hs hQ hfull hj) huU' w
      (visitTransport hs (visitOn u ℓ hℓu)) hw rfl, ← markTransport_visit, GT_owner_transport W hgood, hq]

/-- **The retained set of an unaffected carrier is carried** (the common carrier and every spectator). -/
theorem est_retained_eq_of_ne (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f)
    (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t') (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j u v : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g)
    (hv : v.val ∈ triangleSupports e f g) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    {ℓ : ZMod n} (hℓu : ℓ ∈ u.val) (hℓv : ℓ ∈ v.val)
    (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hne : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) ≠ q) :
    geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) =
      (geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q).map (crossingTransport hs).toEmbedding := by
  have hℓj := est_shared_not_mem_third hef heg hfg hj hu hv hju hjv huv hℓu hℓv
  ext c'
  obtain ⟨c, rfl⟩ := (crossingTransport hs).surjective c'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  by_cases hcT : c.val ∈ triangleSupports e f g
  · have hcH : c ∉ geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q :=
      fun h => est_not_retained_H ht hcomp hQ hfull hj q h hcT
    refine iff_of_false ?_ hcH
    rcases est_tri_exhaust hef' heg' hfg' hj hu hv hju hjv huv c hcT with rfl | rfl | rfl
    · intro h
      exact ((mem_geoCarrierCrossings _ _ _ _).mp h).1
        ((mem_transportSupport_iff hs _ c).mpr (Finset.mem_union_right _ (Finset.mem_singleton_self c)))
    · rw [est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hju hℓu hℓj q]
      exact hne
    · rw [est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hv hjv hℓv hℓj q,
        ← est_owner_shared_eq hL hef heg hfg ht hQ hu hv hju hjv huv hℓu hℓv]
      exact hne
  · exact est_retained_outside_iff hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hcT

/-- **The retained set of the affected carrier** `q₀` (the owner of the shared-edge visits of `u, v`): the
carried outside survivors together with the two positive self-crossings `u', v'`. -/
theorem est_retained_affected (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f)
    (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t') (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j u v : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g)
    (hv : v.val ∈ triangleSupports e f g) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    {ℓ : ZMod n} (hℓu : ℓ ∈ u.val) (hℓv : ℓ ∈ v.val)
    (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hq : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) = q) :
    geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) =
      (geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q).map (crossingTransport hs).toEmbedding ∪
        {crossingTransport hs u, crossingTransport hs v} := by
  have hℓj := est_shared_not_mem_third hef heg hfg hj hu hv hju hjv huv hℓu hℓv
  ext c'
  obtain ⟨c, rfl⟩ := (crossingTransport hs).surjective c'
  rw [Finset.mem_union, Finset.mem_map_equiv, Equiv.symm_apply_apply, Finset.mem_insert, Finset.mem_singleton,
    (crossingTransport hs).injective.eq_iff, (crossingTransport hs).injective.eq_iff]
  by_cases hcT : c.val ∈ triangleSupports e f g
  · have hcH : c ∉ geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q :=
      fun h => est_not_retained_H ht hcomp hQ hfull hj q h hcT
    rcases est_tri_exhaust hef' heg' hfg' hj hu hv hju hjv huv c hcT with rfl | rfl | rfl
    · refine iff_of_false ?_ ?_
      · intro h
        exact ((mem_geoCarrierCrossings _ _ _ _).mp h).1
          ((mem_transportSupport_iff hs _ c).mpr (Finset.mem_union_right _ (Finset.mem_singleton_self c)))
      · rintro (h | h | h)
        · exact hcH h
        · exact hju h
        · exact hjv h
    · rw [est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hju hℓu hℓj q]
      exact iff_of_true hq (Or.inr (Or.inl rfl))
    · rw [est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hv hjv hℓv hℓj q,
        ← est_owner_shared_eq hL hef heg hfg ht hQ hu hv hju hjv huv hℓu hℓv]
      exact iff_of_true hq (Or.inr (Or.inr rfl))
  · rw [est_retained_outside_iff hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hcT]
    constructor
    · exact Or.inl
    · rintro (h | rfl | rfl)
      · exact h
      · exact absurd hu hcT
      · exact absurd hv hcT

end ESTRetained

/-! #### G. The unaffected carriers ("the common carrier read, every triangle-disjoint spectator read, and
all weights are identical across the wall", §4) and the affected carrier's writhe shift (7) -/

section ESTCarriers

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- `P_{S,L}` of an unaffected carrier is carried: its retained crossings are outside crossings whose visit
orders and divide signs are carried, so the two positive lifts are record-isomorphic (`EXT_homfly_wall`,
CV:ax:gausscode). -/
theorem est_groupedPoly_eq_of_ne (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j u v : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g)
    (hv : v.val ∈ triangleSupports e f g) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    {ℓ : ZMod n} (hℓu : ℓ ∈ u.val) (hℓv : ℓ ∈ v.val)
    (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hne : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) ≠ q) :
    CV.groupedPoly hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) =
      CV.groupedPoly hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q := by
  set W := est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj
  have hX := est_retained_eq_of_ne hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hne
  have hdet : ∀ i j : ZMod n, IsCrossing (E.curve t) {i, j} →
      (0 < det (edge (E.curve t) i) (edge (E.curve t) j) ↔
        0 < det (edge (E.curve t') i) (edge (E.curve t') j)) :=
    fun i j hij => GT_det_pos_iff_of_sign (hR.sign_eq t t' ht ht' i j hij)
  rw [GT_groupedPoly_eq_homfly, GT_groupedPoly_eq_homfly]
  unfold CV.carrierDiagram
  refine EXT_homfly_wall hn _ _ hs _ _ q _ hX ?_ ?_
  · intro v w hv _
    have hvT := est_not_retained_H ht hcomp hQ hfull hj q hv
    exact W.key_lt v w (GT_not_rev_of_not_mem_left
      (fun h => hvT ((F1.mem_triangleCrossings e f g v.1).mp h)))
  · intro v _
    exact hdet _ _ (by rw [← visit_crossing_val_eq_pair v]; exact v.1.property)

/-- `Ω₁(S,L)` of an unaffected carrier is carried (`w_{S,L}`, `R(L)`, `P_{S,L}` all carried). -/
theorem est_omega1_eq_of_ne (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j u v : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g)
    (hv : v.val ∈ triangleSupports e f g) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    {ℓ : ZMod n} (hℓu : ℓ ∈ u.val) (hℓv : ℓ ∈ v.val)
    (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hne : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) ≠ q) :
    CV.Omega1 hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) =
      CV.Omega1 hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q := by
  set W := est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj
  have hS := est_S_ind ht.1 hQ hfull hj
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  unfold CV.Omega1 CV.slot
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hS', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hS,
    est_retained_eq_of_ne hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hne,
    Finset.card_map, GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W hS hS' q,
    est_groupedPoly_eq_of_ne hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hne]

/-- (7) `w_+ = w_0 + 2`: the affected carrier's copy retains the two extra positive self-crossings `u', v'`. -/
theorem est_groupedWrithe_affected (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j u v : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g)
    (hv : v.val ∈ triangleSupports e f g) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    {ℓ : ZMod n} (hℓu : ℓ ∈ u.val) (hℓv : ℓ ∈ v.val)
    (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hq : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) = q) :
    CV.groupedWrithe (genericAt E t' ht'.1)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) =
      CV.groupedWrithe (genericAt E t ht.1) q + 2 := by
  have hS := est_S_ind ht.1 hQ hfull hj
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hS', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hS,
    est_retained_affected hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hq,
    Finset.card_union_of_disjoint, Finset.card_map, Finset.card_pair ((crossingTransport hs).injective.ne huv)]
  · push_cast; ring
  · rw [Finset.disjoint_left]
    intro c' hc' hcuv
    obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hc'
    have hcT := est_not_retained_H ht hcomp hQ hfull hj q hc
    rcases Finset.mem_insert.mp hcuv with h | h
    · exact hcT (((crossingTransport hs).injective h) ▸ hu)
    · exact hcT (((crossingTransport hs).injective (Finset.mem_singleton.mp h)) ▸ hv)

end ESTCarriers

/-! #### H. The interface Prop and the ledger -/

/-- The crossing of the grouped diagram `D(W)` sitting at a retained crossing `c` of the carrier
(`geoCarrierCrossingEquiv`, def:positive-lift). -/
noncomputable def est_liftCrossing (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    {c : Crossing P} (hc : c ∈ geoCarrierCrossings hG.crossingGeometry S q) :
    (CV.carrierDiagram hn hG hS q).Γ.Crossing :=
  (geoCarrierCrossingEquiv hn (CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn))
    (CV.geoIndependent_of_mem_Ind _ hS) q).symm ⟨c, hc⟩

/-- **The RII port relation of row 176 — INTERFACE Prop (D-F11), never mapped.** For every simple RIII
event, radius carrying R-LOC-2 and the sign data, `K3` side `t`, empty side `t'`, outside support `Q` at
full availability, selected triangle crossing `j` and affected carrier `q` of `Q ∪ {j}` (its copy on `L`
retains one of the two other triangle crossings), there is a choice `u` of the retained unselected crossing
whose lift crossing carries the port data `est_PortData` (§1–§3 of the RA text: the RII port relation after
the switch, the two-component smoothing and its exact owner map, the linking number, the writhe and rotation
ledgers (13)/(14), the one-dissent sign ledger (12)). This is the G10-scale geometric content of row 176. -/
def est_port_relation : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})),
    (∃ u : Crossing (E.curve t), u.val ∈ triangleSupports e f g ∧ u ≠ j ∧
      crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) →
    ∃ (u : Crossing (E.curve t)) (_ : u.val ∈ triangleSupports e f g) (_ : u ≠ j)
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (est_PortData hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))

section ESTLedger

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- Two present rows with equal selectors and a carrier bijection carrying `Ω₁` are equal
(`rowTerm_of_mem_Ind`, `Fintype.prod_equiv`; the `Ω₁`-only form of `AV_rowTerm_eq_of_summandTransport`,
since `P_{S,L}` and `w_{S,L}` of the affected carrier are NOT carried). -/
theorem est_rowTerm_eq_of_omega (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
    {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (hwind : CV.wind hG'.crossingGeometry S' = CV.wind hG.crossingGeometry S)
    (τ : GeoComponent hG.crossingGeometry S ≃ GeoComponent hG'.crossingGeometry S')
    (hΩ : ∀ q, CV.Omega1 hn hG' hS' (τ q) = CV.Omega1 hn hG hS q) :
    rowTerm hn hG S = rowTerm hn hG' S' := by
  rw [rowTerm_of_mem_Ind hn hG hS, rowTerm_of_mem_Ind hn hG' hS', hwind]
  congr 1
  exact Fintype.prod_equiv τ _ _ fun q => (hΩ q).symm

/-- The two other triangle crossings of a selected one. -/
theorem est_others {t : E.Parameter}
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) {j : Crossing (E.curve t)} (hj : j.val ∈ triangleSupports e f g) :
    ∃ u v : Crossing (E.curve t), u.val ∈ triangleSupports e f g ∧ v.val ∈ triangleSupports e f g ∧
      j ≠ u ∧ j ≠ v ∧ u ≠ v := by
  have h1 : (xPair hef').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inl rfl)
  have h2 : (xPair heg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl))
  have h3 : (xPair hfg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl))
  have n12 := P1.xPair_ef_ne_eg hef' heg' hfg'
  have n13 := P1.xPair_ef_ne_fg hef' heg' hfg'
  have n23 := P1.xPair_eg_ne_fg hef' heg' hfg'
  rcases GT_tri_cases t hef' heg' hfg' j hj with rfl | rfl | rfl
  · exact ⟨_, _, h2, h3, n12, n13, n23⟩
  · exact ⟨_, _, h1, h3, n12.symm, n23, n13⟩
  · exact ⟨_, _, h1, h2, n13.symm, n23.symm, n12⟩

/-- **The singleton row is carried, `t` the `K3` side** (§4 of the RA text: "Multiplying these equalities
proves all three identities (2), including selector-zero, coefficient-zero, empty-carrier, `ell = 0`, and
`C_Q = 0` cases. No factor was cancelled or divided out."): the selector is carried (`GT_wind_eq`), the
carriers correspond (`GT_carrierEquiv`), every unaffected carrier's `Ω₁` is carried (`est_omega1_eq_of_ne`)
and the affected carrier's by the port ledger (`est_omega1_eq_of_port`). -/
theorem est_row_H (hF : CV.CarrierSlotFloor) (hport : est_port_relation) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {j}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) := by
  set W := est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj
  have hS := est_S_ind ht.1 hQ hfull hj
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  refine est_rowTerm_eq_of_omega hn _ _ hS hS'
    (GT_wind_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W) (GT_carrierEquiv W) fun q => ?_
  obtain ⟨u, v, hu, hv, hju, hjv, huv⟩ := est_others hef' heg' hfg' hj
  obtain ⟨ℓ, hℓu, hℓv⟩ := GT_shared_label hu hv huv
  have hℓj := est_shared_not_mem_third hef heg hfg hj hu hv hju hjv huv hℓu hℓv
  by_cases hq : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) = q
  · -- the affected carrier: the port ledger
    have hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv W q) :=
      (est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hju hℓu hℓj q).mpr hq
    obtain ⟨u₁, -, -, hu₁', ⟨D⟩⟩ := hport n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg'
      hcomp Q hQ hfull j hj q ⟨u, hu, hju.symm, hu'⟩
    exact est_omega1_eq_of_port hF hn _ _ hS hS' q _ _ D
      (est_groupedWrithe_affected hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hq)
      (GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W hS hS' q)
  · exact est_omega1_eq_of_ne hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hq

/-- **The singleton row is carried, either side extreme** ("separately and without a symmetry assumption",
symmetric in the sides): the `K3` side directly, the empty side by applying the `K3` case to `(t', t)`
(`graphs_complementary`). -/
theorem est_row (hF : CV.CarrierSlotFloor) (hport : est_port_relation) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hext : ExtremeLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {j}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) := by
  rcases hext with hcomp | hemp
  · exact est_row_H hF hport hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj
  · have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
    have hop' : OppositeSides E t' t := by
      unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
    obtain ⟨hef'', heg'', hfg''⟩ := hL.triangle_crossings t' ht'
    have hcomp' : CompleteLocal (geomAt E t' ht'.1) hef'' heg'' hfg'' :=
      (PRE_176_graphs_complementary hL t' t ht' ht hop' hef'' heg'' hfg'' hef' heg' hfg').mpr hemp
    have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
    have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
    have hj' : (crossingTransport hs j).val ∈ triangleSupports e f g := hj
    have h := est_row_H hF hport hn hL hR hef heg hfg ht' ht hop' hs' hcomp' hQ' hfull' hj'
    rw [← GT_transportSupport_S hs Q j, EXT_transportSupport_symm hs (Q ∪ {j})] at h
    exact h.symm

/-- **The bundle of row 176 from the interface and the floor**: the three PRE fields (accepted) and the
three transports (2) at `x = x_ef`, `y = x_eg`, `z = x_fg`. -/
theorem est_extremeTransportData (hF : CV.CarrierSlotFloor) (hport : est_port_relation) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) : ExtremeTransportData hn E e f g δ where
  singleton_rows_present := PRE_176_singleton_rows_present E e f g δ
  graphs_complementary := PRE_176_graphs_complementary hL
  sign_branch := PRE_176_sign_branch hGT
  transport_x := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    est_row hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inl rfl))
  transport_y := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    est_row hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl)))
  transport_z := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    est_row hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl)))

end ESTLedger

/-- **The RA ledger of row 176 (U-176)**: `R:extreme_transport` in the fixed row shape from
`CV.CarrierSlotFloor` (thm:carrierfloor (C)+(D) in def:X1's symbols, §1.3) and the RII port relation
interface `est_port_relation`; the radius is the common radius of rows 164 (`localization`), 172
(`generic_table`) and the sign data (`AV_exists_eventRadius`), exactly as the accepted row 173. PROVED. -/
theorem est_ledger (hF : CV.CarrierSlotFloor) (hport : est_port_relation) :
    RowShape @ExtremeTransportData := by
  intro n _ hn E e f g h3 h4e h4f h4g hE
  obtain ⟨δL, hδL, hδLr, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  obtain ⟨δG, hδG, -, hGT⟩ := generic_table E e f g h3 h4e h4f h4g hE
  obtain ⟨δR, hδR, -, hR⟩ := AV_exists_eventRadius hE
  have hef : e ≠ f := AV_ne_of_remote h3.1
  have hfg : f ≠ g := AV_ne_of_remote h3.2.1
  have heg : e ≠ g := AV_ne_of_remote h3.2.2.1
  refine ⟨min δL (min δG δR), lt_min hδL (lt_min hδG hδR), (min_le_left _ _).trans hδLr, ?_⟩
  have hL' := F1.localizationData_mono (min_le_left δL (min δG δR)) hL
  have hGT' := SEL_genericTableData_mono ((min_le_right δL (min δG δR)).trans (min_le_left δG δR)) hGT
  have hR' := AV_eventRadius_mono ((min_le_right δL (min δG δR)).trans (min_le_right δG δR)) hR
  exact est_extremeTransportData hF hport hn hL' hGT' hR' hef heg hfg

/-- The row statement itself from the ledger (the shape of the leaf below). PROVED. -/
theorem est_extreme_transport_of (hF : CV.CarrierSlotFloor) (hport : est_port_relation) (hn : 3 ≤ n)
    (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeTransportData hn E e f g δ :=
  est_ledger hF hport n hn E e f g h3 h4e h4f h4g hE

/-! #### I. Consistency of the interface (sanity, for the realiser) -/

/-- Writhe consistency of the port relation (T2): switching the positive crossing `y` of `D_+` drops the
writhe by `2`, so the switched diagram has writhe `w_+ − 2 = w_0` — as it must, RII moves preserving the
writhe (`switch_writhe`, `geoPositiveLift_sign`). -/
theorem est_switch_writhe (hn : 3 ≤ n) {P' : LabelledTuple n} (hG' : CV.Generic P') {S' : Finset (Crossing P')}
    (hS' : S' ∈ CV.Ind hG'.crossingGeometry) (q' : GeoComponent hG'.crossingGeometry S')
    (y : (CV.carrierDiagram hn hG' hS' q').Γ.Crossing) :
    ((CV.carrierDiagram hn hG' hS' q').switch y).writhe = CV.groupedWrithe hG' q' - 2 := by
  rw [Diagram.switch_writhe, est_carrierDiagram_writhe, geoPositiveLift_sign]
  rfl

end EST

/-! ### Unit U-177 (prefix `esc_`) — the interface Props and the RA ledger of row 177
(R_EXTREME_SELECTED_COUPLE_PROOF.md §1–§5; PLAN_FINAL §4 "174 / 176 / 177", D-F11 interface-first).

Route.  The `couple` field is reduced, with accepted tools only, to an identity on the single
triangle-touching carrier of the empty row (`rowTerm = exteriorFactor · touchingFactor`, row 168's
`EXT_exteriorFactor_wall` / `EXT_exteriorFactor_eq_base`; `GT_empty_tri_subset` for the uniqueness of the
contact carrier on each side; the `GT_Wall` transports of `wt`, `R(L)`, `w_{S,L}`).  The two
Reidemeister moves of the printed proof — (4) the matched switch + RIII through the wall, (6) the RII
bigon deletion after one smoothing and a matched switch — the one- or three-component identifications of the
double smoothings ((8) and the lowest row (12)), and the carrier split of `Q ∪ T` on the empty side
((14)–(17), the central carrier) are stated as explicit interface Props and NEVER mapped; the ledger
`esc_ledger` proves the row from them and from `CV.CarrierSlotFloor` (the (C)+(D) corollary, §1.3):
(5)/(7) by the two HOMFLY skein equations, (8) by knot parity, (13) → (18)–(20) → (2). -/

section ESC

open SM.Link AddMonoidAlgebra

/-! #### A. Laurent-ring helpers (CV/FullTwist.lean is not imported here; `esc_` copies) -/

/-- Coefficient shift: `[a^d z^k] (c a^p z^q · f) = c · [a^{d−p} z^{k−q}] f`. -/
theorem esc_coeffAt_single_mul (d k p q c : ℤ) (f : R) :
    coeffAt d k (single (p, q) c * f) = c * coeffAt (d - p) (k - q) f := by
  unfold coeffAt
  rw [coeff_single_mul_apply]
  congr 2
  ext <;> simp [neg_add_eq_sub]

theorem esc_a_mul_a : R.a * R.a = (single (2, 0) 1 : R) := by
  rw [R.a, single_mul_single]; norm_num

theorem esc_aInv_mul_aInv : R.aInv * R.aInv = (single (-2, 0) 1 : R) := by
  rw [R.aInv, single_mul_single]; norm_num

/-- `a^{−2} z^{2} = single (−2, 2) 1`. -/
theorem esc_aInv_aInv_z_z : R.aInv * R.aInv * (R.z * R.z) = (single (-2, 2) 1 : R) := by
  rw [R.aInv, R.z, single_mul_single, single_mul_single, single_mul_single]; norm_num

/-- `(a − a⁻¹)² K = a² K + a⁻² K − 2K` ("Expand `(a−a^(−1))^2=a^2−2+a^(−2)`", ESC §4). -/
theorem esc_sq_expand (K : R) :
    (R.a - R.aInv) ^ 2 * K = single (2, 0) 1 * K + single (-2, 0) 1 * K - (K + K) := by
  have h1 := R.a_mul_aInv
  rw [← esc_a_mul_a, ← esc_aInv_mul_aInv]
  linear_combination (-2 * K) * h1

/-- The `[a^m z^0]` coefficient of `(a − a⁻¹)² K` samples `K` at `m − 2`, `m`, `m + 2`. -/
theorem esc_coeffAt_sq_mul (m : ℤ) (K : R) :
    coeffAt m 0 ((R.a - R.aInv) ^ 2 * K) =
      coeffAt (m - 2) 0 K + coeffAt (m + 2) 0 K - 2 * coeffAt m 0 K := by
  rw [esc_sq_expand, coeffAt_sub, coeffAt_add, coeffAt_add, esc_coeffAt_single_mul,
    esc_coeffAt_single_mul]
  simp only [one_mul, sub_zero, sub_neg_eq_add]
  ring

/-- `f` lives in the quadrant `a`-degree `≥ m`, `z`-degree `≥ 0` ("no exponent below `d_i` occurs in
`f_i`" together with knot parity). -/
def esc_Quadrant (m : ℤ) (f : R) : Prop := ∀ e ∈ f.coeff.support, m ≤ e.1 ∧ 0 ≤ e.2

theorem esc_Quadrant.coeffAt_eq_zero {m : ℤ} {f : R} (hf : esc_Quadrant m f) {p k : ℤ} (hp : p < m) :
    coeffAt p k f = 0 := by
  by_contra h
  exact absurd (hf (p, k) (Finsupp.mem_support_iff.2 h)).1 (not_le.mpr hp)

theorem esc_quadrant_mul {m n : ℤ} {f g : R} (hf : esc_Quadrant m f) (hg : esc_Quadrant n g) :
    esc_Quadrant (m + n) (f * g) := by
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset f g he)
  obtain ⟨h1, h2⟩ := hf a ha
  obtain ⟨h3, h4⟩ := hg b hb
  exact ⟨by rw [Prod.fst_add]; omega, by rw [Prod.snd_add]; omega⟩

/-- The corner coefficient of a product of two quadrant elements is the product of the corner
coefficients ("`[a^D]K = omega_A omega_B omega_C`", ESC (19)). -/
theorem esc_coeffAt_corner {m n : ℤ} {f g : R} (hf : esc_Quadrant m f) (hg : esc_Quadrant n g) :
    coeffAt (m + n) 0 (f * g) = coeffAt m 0 f * coeffAt n 0 g := by
  have e : ((m + n, 0) : ℤ × ℤ) = (m, 0) + (n, 0) := by simp
  unfold coeffAt
  rw [e]
  apply coeff_mul_add_of_uniqueAdd
  intro a b ha hb hab
  obtain ⟨h1, h2⟩ := hf a ha
  obtain ⟨h3, h4⟩ := hg b hb
  have e1 := congrArg Prod.fst hab
  have e2 := congrArg Prod.snd hab
  simp only [Prod.fst_add, Prod.snd_add] at e1 e2
  refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩ <;> simp only <;> omega

/-- Knot parity (CV:ax:homfly, ESC (8)): a one-component diagram has no `z^{−2}` row. -/
theorem esc_knot_coeff_neg_two (J : Diagram) (hJ : J.componentCount = 1) (p : ℤ) :
    coeffAt p (-2) (homfly J) = 0 := by
  by_contra h
  obtain ⟨j, hj⟩ := CV.ax_homfly_knot_parity_coeffAt J hJ p (-2) h
  omega

/-- The floor + knot parity of a grouped polynomial as a quadrant (`CarrierSlotFloor`,
`cvt_groupedPoly_inSupportM`): "no exponent below `d_i` occurs in `f_i`". -/
theorem esc_quadrant_groupedPoly (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hG : CV.Generic P) {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S)
    (halt : CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry S q)) :
    esc_Quadrant (CV.slot hn hG hS q) (CV.groupedPoly hn hG hS q) := by
  intro e he
  have hne : coeffAt e.1 e.2 (CV.groupedPoly hn hG hS q) ≠ 0 := Finsupp.mem_support_iff.1 he
  refine ⟨le_trans (hF hn hG hS q halt)
    ((mindegAZ_spec (CV.cvt_groupedPoly_ne_zero hn hG hS q)).2 e.1 e.2 hne), ?_⟩
  obtain ⟨j, hj⟩ := CV.cvt_groupedPoly_inSupportM hn hG hS q e he
  rw [hj]; push_cast; omega

/-! #### B. The contact carrier of the empty row -/

theorem esc_not_triangleDisjoint_iff {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (e f g : ZMod n) (q : GeoComponent hP S) :
    ¬ TriangleDisjoint hP S e f g q ↔
      ∃ v : Visit P, v.1.val ∈ triangleSupports e f g ∧ geoOwner hP S (Sum.inr v) = q := by
  unfold TriangleDisjoint
  constructor
  · intro h
    by_contra hne
    exact h fun v hv hvq => hne ⟨v, hv, hvq⟩
  · rintro ⟨v, hv, hvq⟩ h
    exact h v hv hvq

/-- "all six visits lie on one `Q`-carrier" (ESC §1): two triangle-touching carriers of the empty row
coincide (`GT_empty_tri_subset`, on either side). -/
theorem esc_contact_unique {E : CV.Event n} {e f g : ZMod n} {δ : ℝ} (hL : LocalizationData E e f g δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t : E.Parameter} (ht : Punctured E δ t)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {q q' : GeoComponent (geomAt E t ht.1) Q}
    (hq : ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q)
    (hq' : ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q') : q = q' := by
  obtain ⟨v, hv, hvq⟩ := (esc_not_triangleDisjoint_iff _ _ _ _ _ _).1 hq
  obtain ⟨v', hv', hvq'⟩ := (esc_not_triangleDisjoint_iff _ _ _ _ _ _).1 hq'
  have h1 := GT_empty_tri_subset hL hef heg hfg ht hQ hfull q hv hvq
  have h2 := GT_empty_tri_subset hL hef heg hfg ht hQ hfull q' hv' hvq'
  have hvT : v.1 ∈ triangleCrossings (E.curve t) e f g := (F1.mem_triangleCrossings e f g v.1).mpr hv
  have hm1 := (mem_geoCarrierCrossings _ Q q v.1).mp (h1 hvT)
  have hm2 := (mem_geoCarrierCrossings _ Q q' v.1).mp (h2 hvT)
  exact (hm1.2 v rfl).symm.trans (hm2.2 v rfl)

/-- The carrier owning the `e`-visit of `x_ef` is triangle-touching. -/
theorem esc_contact_exists {E : CV.Event n} {e f g : ZMod n} {δ : ℝ} {t : E.Parameter}
    (ht : Punctured E δ t) (hef : IsCrossing (E.curve t) {e, f}) (Q : Finset (Crossing (E.curve t))) :
    ∃ q : GeoComponent (geomAt E t ht.1) Q, ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q :=
  ⟨geoOwner _ Q (Sum.inr (visitOn (xPair hef) e (mem_pair_left e f))),
    (esc_not_triangleDisjoint_iff _ _ _ _ _ _).2
      ⟨_, (P1.mem_triangleSupports _).mpr (Or.inl rfl), rfl⟩⟩

/-- A triangle-touching carrier of the empty row owns every visit of every triangle crossing. -/
theorem esc_contact_owns {E : CV.Event n} {e f g : ZMod n} {δ : ℝ} (hL : LocalizationData E e f g δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t : E.Parameter} (ht : Punctured E δ t)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {q : GeoComponent (geomAt E t ht.1) Q}
    (hq : ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q) :
    triangleCrossings (E.curve t) e f g ⊆ geoCarrierCrossings (geomAt E t ht.1) Q q := by
  obtain ⟨v, hv, hvq⟩ := (esc_not_triangleDisjoint_iff _ _ _ _ _ _).1 hq
  exact GT_empty_tri_subset hL hef heg hfg ht hQ hfull q hv hvq

/-- The touching factor of a row with exactly one touching carrier `q₀` is `wt(q₀) Ω₁(S, q₀)`. -/
theorem esc_touchingFactor_eq_of_unique (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (e f g : ZMod n)
    (q₀ : GeoComponent hG.crossingGeometry S)
    (hq₀ : ∀ q, ¬ TriangleDisjoint hG.crossingGeometry S e f g q ↔ q = q₀) :
    touchingFactor hn hG hS e f g = CV.weight hG.crossingGeometry S q₀ * CV.Omega1 hn hG hS q₀ := by
  classical
  unfold touchingFactor
  refine (Finset.prod_congr (s₂ := {q₀}) ?_ fun _ _ => rfl).trans (Finset.prod_singleton _ _)
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact hq₀ q

/-- The touching factor of a row with exactly the four touching carriers `A, B, C, Z`. -/
theorem esc_touchingFactor_eq_of_four (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (e f g : ZMod n)
    (A B C Z : GeoComponent hG.crossingGeometry S)
    (hdist : A ≠ B ∧ A ≠ C ∧ A ≠ Z ∧ B ≠ C ∧ B ≠ Z ∧ C ≠ Z)
    (h : ∀ q, ¬ TriangleDisjoint hG.crossingGeometry S e f g q ↔ (q = A ∨ q = B ∨ q = C ∨ q = Z)) :
    touchingFactor hn hG hS e f g =
      (CV.weight hG.crossingGeometry S A * CV.Omega1 hn hG hS A) *
      (CV.weight hG.crossingGeometry S B * CV.Omega1 hn hG hS B) *
      (CV.weight hG.crossingGeometry S C * CV.Omega1 hn hG hS C) *
      (CV.weight hG.crossingGeometry S Z * CV.Omega1 hn hG hS Z) := by
  classical
  obtain ⟨hAB, hAC, hAZ, hBC, hBZ, hCZ⟩ := hdist
  unfold touchingFactor
  refine (Finset.prod_congr (s₂ := {A, B, C, Z}) ?_ fun _ _ => rfl).trans ?_
  · ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    exact h q
  · have h1 : A ∉ ({B, C, Z} : Finset (GeoComponent hG.crossingGeometry S)) := by
      simp [hAB, hAC, hAZ]
    have h2 : B ∉ ({C, Z} : Finset (GeoComponent hG.crossingGeometry S)) := by simp [hBC, hBZ]
    have h3 : C ∉ ({Z} : Finset (GeoComponent hG.crossingGeometry S)) := by simp [hCZ]
    rw [Finset.prod_insert h1, Finset.prod_insert h2, Finset.prod_insert h3, Finset.prod_singleton]
    ring

/-! #### C. Diagram-level helpers: the crossings of the grouped knot diagram, and a crossing carried
through an oriented smoothing at another crossing -/

/-- Every retained crossing `c` of the carrier is a positive crossing of `D(W)` at the double point of
`c` (cor:groupedknot (A) `retain_all`, `geoCarrierCrossingEquiv`). -/
theorem esc_lift_crossing (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (c : Crossing P) (hc : c ∈ geoCarrierCrossings hG.crossingGeometry S q) :
    ∃ x : (CV.carrierDiagram hn hG hS q).Γ.Crossing,
      (CV.carrierDiagram hn hG hS q).Γ.crossingPoint x = crossingPoint c ∧
        (CV.carrierDiagram hn hG hS q).IsPositive x := by
  let hG' := CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn)
  let hT := CV.geoIndependent_of_mem_Ind hG.crossingGeometry hS
  refine ⟨(geoCarrierCrossingEquiv hn hG' hT q).symm ⟨c, hc⟩, ?_,
    geoPositiveLift_isPositive hn hG' hT q _⟩
  have h := crossingPoint_geoCarrierCrossingEquiv hn hG' hT q
    ((geoCarrierCrossingEquiv hn hG' hT q).symm ⟨c, hc⟩)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- A crossing `y ≠ x` of `D` is carried by any oriented smoothing `D₀` of `D` at `x` to a crossing of
`D₀` at the same double point and with the same sign (the outside match `ψ` of the smoothing site). -/
theorem esc_smoothing_outer {D D₀ : Diagram} {x : D.Γ.Crossing} (h : IsOrientedSmoothing D x D₀)
    (y : D.Γ.Crossing) (hyx : y ≠ x) :
    ∃ y₀ : D₀.Γ.Crossing, D₀.Γ.crossingPoint y₀ = D.Γ.crossingPoint y ∧
      (D₀.IsPositive y₀ ↔ D.IsPositive y) := by
  obtain ⟨U, ⟨dat⟩⟩ := h
  have hout : D.Γ.crossingPoint y ∉ interior U := fun hin => hyx ((dat.inner_iff y).mp hin)
  have hU : D.Γ.crossingPoint y ∉ U := by
    intro hin
    have hcl : D.Γ.crossingPoint y ∈ closure U := subset_closure hin
    rw [closure_eq_interior_union_frontier] at hcl
    rcases hcl with h | h
    · exact hout h
    · exact dat.frame.clean.crossingPoint_not_mem_frontier y h
  let yo : D.OuterCrossing U := ⟨y, hout⟩
  refine ⟨(dat.out.ψ yo).1, ?_, ?_⟩
  · have h1 := dat.out.eval_eq (D.outerOverPt yo)
    rw [dat.out.over_eq] at h1
    rw [Diagram.outerOverPt_val, Diagram.outerOverPt_val, Diagram.eval_visitPt, Diagram.eval_visitPt] at h1
    exact h1
  · have hpo : D.Γ.eval (D.outerOverPt yo).1 ∉ U := by
      rw [Diagram.outerOverPt_val, Diagram.eval_visitPt]
      exact hU
    have hpu : D.Γ.eval (D.outerUnderPt yo).1 ∉ U := by
      rw [Diagram.outerUnderPt_val, Diagram.eval_visitPt]
      exact hU
    obtain ⟨l, hl, hdo⟩ := dat.out.dir_pos _ hpo
    obtain ⟨m, hm, hdu⟩ := dat.out.dir_pos _ hpu
    rw [dat.out.over_eq] at hdo
    rw [dat.out.under_eq] at hdu
    have e1 : D₀.Γ.dir (D₀.overStrand (dat.out.ψ yo).1) = l • D.Γ.dir (D.overStrand y) := hdo
    have e2 : D₀.Γ.dir (D₀.underStrand (dat.out.ψ yo).1) = m • D.Γ.dir (D.underStrand y) := hdu
    unfold Diagram.IsPositive
    rw [e1, e2, det_smul_smul]
    exact mul_pos_iff_of_pos_left (mul_pos hl hm)

/-! #### D. The interface Props (D-F11: stated, consumed by the ledger, never mapped) -/

/-- **(4) The matched switch + RIII through the wall** (ESC §2): "switching `x` breaks the cyclic
over-order and makes it transitive … Apply the ordinary oriented RIII change … an isomorphism of the
full oriented traversal records of `D_H^{x-}` and `D_L^{x-}` … `ax:gausscode` identifies their oriented
knots and `ax:homfly` gives `P(D_H^{x-}) = P(D_L^{x-})`", for the crossings `x_H`, `x_L` of the two
grouped contact diagrams at the double points of `x`. -/
def esc_switch_riii (D_H D_L : Diagram) (x_H : D_H.Γ.Crossing) (x_L : D_L.Γ.Crossing) : Prop :=
  homfly (D_H.switch x_H) = homfly (D_L.switch x_L)

/-- **(6) The RII after one smoothing and a matched switch** (ESC §2): in the oriented smoothings
`D_H^x`, `D_L^x`, "switch `y` … on each side they bound an empty oriented RII bigon. Delete that bigon …
this path extends through the wall as an ambient isotopy from `E_H` to `E_L`. Reidemeister-II invariance
… and isotopy invariance in `ax:homfly` therefore give `P((D_H^x)^{y-}) = P((D_L^x)^{y-})`". -/
def esc_rii_after_smoothing (D_H0 D_L0 : Diagram) (y_H : D_H0.Γ.Crossing) (y_L : D_L0.Γ.Crossing) :
    Prop :=
  homfly (D_H0.switch y_H) = homfly (D_L0.switch y_L)

/-- **(9)–(11) The three components of the double smoothing `J = D_L^{xy}`** (ESC §3): "The three
components of `J=D_L^{xy}` have successor skeletons `A, C, zBz`" … "the self-crossing knot polynomials
of the first two components in (9) are the grouped full-state polynomials `f_A,f_C`. For the third …
By `cor:groupedknot`, clauses (A) and (B), its grouped knot polynomial is `P_{zBz}(a,0) = P_{ {z} }(a,0)
f_B(a) = f_B(a)`, because the one-crossing positive piece is an unknot"; "Put `Lambda=lk(J)`, the sum
of its three pairwise linking numbers": three components, `2Λ` the total mixed sign sum (mp:lowest's
`twoLambda`), and an indexing of the components by `A, B, C` with the knot polynomials `f_A, f_B, f_C`
(mp:lowest's intrinsic knot diagrams `knotRestrict`). -/
def esc_three_components (J : Diagram) (Λ : ℕ) (fA fB fC : R) : Prop :=
  J.componentCount = 3 ∧ twoLambda J = 2 * (Λ : ℤ) ∧
    ∃ σ : Fin 3 ≃ Fin J.Γ.c, homfly (J.knotRestrict (σ 0)) = fA ∧ homfly (J.knotRestrict (σ 1)) = fB ∧
      homfly (J.knotRestrict (σ 2)) = fC

/-- **(12) The three-component lowest `z`-row, PROVED** from mp:lowest (`SM.lowest.lowest_value` at
`c = 3`; "the exact three-component lowest row `[z^(-2)] P(J) = a^(-2 Lambda) (a-a^(-1))^2 K(a)`",
`K = f_A f_B f_C`): as a coefficient identity, the `a^{−2Λ}` shift written on the right-hand exponent.
The `[z^0]` row of `(a − a⁻¹)² K` is `(a − a⁻¹)² ∏ [z^0] f_i` by knot parity of the three knot
polynomials (`P_knotRestrict_inSupportM_one`, `CV.zRow_zero_mul_of_inSupportM_one`). -/
theorem esc_three_component_row {J : Diagram} {Λ : ℕ} {fA fB fC : R}
    (h : esc_three_components J Λ fA fB fC) (p : ℤ) :
    coeffAt p (-2) (homfly J) = coeffAt (p + 2 * (Λ : ℤ)) 0 ((R.a - R.aInv) ^ 2 * (fA * fB * fC)) := by
  obtain ⟨hc, hΛ, σ, hA, hB, hC⟩ := h
  have hlow := SM.lowest.lowest_value J
  rw [hc, hΛ, P_eq_homfly, show (3 : ℕ) - 1 = 2 from rfl, show (1 : ℤ) - ((3 : ℕ) : ℤ) = -2 by norm_num]
    at hlow
  have hprod : ∏ i : Fin J.Γ.c, zRow 0 (P (J.knotRestrict i)) = zRow 0 fA * zRow 0 fB * zRow 0 fC := by
    rw [← σ.prod_comp, Fin.prod_univ_three, P_eq_homfly, P_eq_homfly, P_eq_homfly, hA, hB, hC]
  have hMA : InSupportM 1 fA := by rw [← hA, ← P_eq_homfly]; exact P_knotRestrict_inSupportM_one J _
  have hMB : InSupportM 1 fB := by rw [← hB, ← P_eq_homfly]; exact P_knotRestrict_inSupportM_one J _
  have hMC : InSupportM 1 fC := by rw [← hC, ← P_eq_homfly]; exact P_knotRestrict_inSupportM_one J _
  have hsq : zRow 0 ((R.a - R.aInv) ^ 2 * (fA * fB * fC)) =
      (aPow 1 - aPow (-1)) ^ 2 * (zRow 0 fA * zRow 0 fB * zRow 0 fC) := by
    have e : (R.a - R.aInv) ^ 2 * (fA * fB * fC) =
        R.a * (R.a * (fA * fB * fC)) - R.a * (R.aInv * (fA * fB * fC)) -
          R.aInv * (R.a * (fA * fB * fC)) + R.aInv * (R.aInv * (fA * fB * fC)) := by ring
    rw [e]
    simp only [zRow_add, zRow_sub, zRow_a_mul, zRow_aInv_mul]
    rw [CV.zRow_zero_mul_of_inSupportM_one (hMA.one_mul_one hMB) hMC,
      CV.zRow_zero_mul_of_inSupportM_one hMA hMB]
    ring
  rw [← coeff_zRow, ← coeff_zRow, hsq, hlow, hprod, mul_assoc, coeff_T_mul']
  congr 1
  ring

/-- The move data of one configuration: the grouped contact diagrams `D_H`, `D_L` (cor:groupedknot (B)
on the two contact carriers), the double points `pxH, pyH` of `x, y` on the `K3` side and `pxL, pyL` on
the empty side, the linking number `Λ`, and the three outer grouped polynomials `f_A, f_B, f_C`.
Crossings of the diagrams are identified by their double points; smoothings are the library's
relational `IsOrientedSmoothing` (any smoothing site). -/
structure esc_MoveData (D_H D_L : Diagram) (pxH pyH pxL pyL : Plane) (Λ : ℕ) (fA fB fC : R) : Prop where
  /-- (4), for the crossings at the double points of `x`. -/
  switch_riii : ∀ (x_H : D_H.Γ.Crossing) (x_L : D_L.Γ.Crossing),
    D_H.Γ.crossingPoint x_H = pxH → D_L.Γ.crossingPoint x_L = pxL → esc_switch_riii D_H D_L x_H x_L
  /-- (6), for every pair of oriented smoothings at `x` and the crossings at the double points of `y`. -/
  rii_after_smoothing : ∀ (x_H : D_H.Γ.Crossing) (x_L : D_L.Γ.Crossing),
    D_H.Γ.crossingPoint x_H = pxH → D_L.Γ.crossingPoint x_L = pxL →
    ∀ (D_H0 D_L0 : Diagram), IsOrientedSmoothing D_H x_H D_H0 → IsOrientedSmoothing D_L x_L D_L0 →
    ∀ (y_H : D_H0.Γ.Crossing) (y_L : D_L0.Γ.Crossing),
      D_H0.Γ.crossingPoint y_H = pyH → D_L0.Γ.crossingPoint y_L = pyL →
      esc_rii_after_smoothing D_H0 D_L0 y_H y_L
  /-- "Smoothing `x` in the `K3` word splits the contact knot into two components; there `y` is mixed,
  so smoothing `y` joins them and `D_H^{xy}` is a knot" (ESC §2). -/
  knot_after_two : ∀ (x_H : D_H.Γ.Crossing), D_H.Γ.crossingPoint x_H = pxH →
    ∀ D_H0 : Diagram, IsOrientedSmoothing D_H x_H D_H0 →
    ∀ (y_H : D_H0.Γ.Crossing), D_H0.Γ.crossingPoint y_H = pyH →
    ∀ J_H : Diagram, IsOrientedSmoothing D_H0 y_H J_H → J_H.componentCount = 1
  /-- (9)–(11) for the double smoothing `D_L^{xy}` ("`D_L^{xy}` has three components", ESC §2–§3): its
  three components are the grouped knots of the outer carriers, `Λ = lk(J)`. -/
  three_components : ∀ (x_L : D_L.Γ.Crossing), D_L.Γ.crossingPoint x_L = pxL →
    ∀ D_L0 : Diagram, IsOrientedSmoothing D_L x_L D_L0 →
    ∀ (y_L : D_L0.Γ.Crossing), D_L0.Γ.crossingPoint y_L = pyL →
    ∀ J_L : Diagram, IsOrientedSmoothing D_L0 y_L J_L → esc_three_components J_L Λ fA fB fC

/-- **The carrier split of the full row `Q ∪ T` on the empty side** (ESC §1, §4): the four
triangle-touching carriers — the three outer carriers `A, B, C` ("All nonlocal corners of the empty
contact carrier partition among the three outer carriers") and the central triangle `Z` — of the
support `Q ∪ T`, relative to the contact carrier `q₀` of the empty row `Q`; `Λ = lk(J)` of (12)/(17). -/
structure esc_FullSplitData (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P) (e f g : ZMod n)
    {Q : Finset (Crossing P)} (hQ : Q ∈ CV.Ind hG.crossingGeometry)
    (hS : Q ∪ triangleCrossings P e f g ∈ CV.Ind hG.crossingGeometry)
    (q₀ : GeoComponent hG.crossingGeometry Q)
    (A B C Z : GeoComponent hG.crossingGeometry (Q ∪ triangleCrossings P e f g)) (Λ : ℕ) : Prop where
  /-- the triangle-touching carriers of `Q ∪ T` are exactly `A, B, C, Z` -/
  touching_iff : ∀ q, ¬ TriangleDisjoint hG.crossingGeometry (Q ∪ triangleCrossings P e f g) e f g q ↔
    (q = A ∨ q = B ∨ q = C ∨ q = Z)
  distinct : A ≠ B ∧ A ≠ C ∧ A ≠ Z ∧ B ≠ C ∧ B ≠ Z ∧ C ≠ Z
  /-- "the central carrier's empty polynomial" (ESC §5): the central triangle carries no piece -/
  central_no_piece : CV.piecesOn hG.crossingGeometry (Q ∪ triangleCrossings P e f g) Z = ∅
  /-- "`lem:uniformrot(i)` gives it absolute rotation one" (ESC §4) -/
  central_rot : CV.carrierR hn hG hS Z = 1
  /-- (17) "`w = 3 + w_A + w_B + w_C + 2Λ`" -/
  writhe : CV.groupedWrithe hG q₀ =
    3 + CV.groupedWrithe hG A + CV.groupedWrithe hG B + CV.groupedWrithe hG C + 2 * (Λ : ℤ)
  /-- "If the empty contact carrier is mixed, then `W = 0`. The full selector is also zero" -/
  mixed : CV.CarrierMixed hG.crossingGeometry Q q₀ →
    CV.weight hG.crossingGeometry _ A * CV.weight hG.crossingGeometry _ B *
      CV.weight hG.crossingGeometry _ C * CV.weight hG.crossingGeometry _ Z = 0
  /-- "Each outer carrier is uniform in the live branch and exactly one-dissent in the dead branch …
  after a possible orientation reversal, `thm:carrierfloor` applies" (ESC §4) -/
  outer_alternative : CV.CarrierUniform hG.crossingGeometry Q q₀ →
    CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry _ A) ∧
    CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry _ B) ∧
    CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry _ C)
  /-- the two exhaustive branches of a uniform contact carrier: live `χ = 1` — (16) "`R_A+R_B+R_C = R+1`"
  and (14) "`W_full = -W`"; dead `χ = 0` — (16) "`R_A+R_B+R_C = R-1`" and "`W_full = 0`" -/
  uniform : CV.CarrierUniform hG.crossingGeometry Q q₀ →
    (CV.carrierR hn hG hS A + CV.carrierR hn hG hS B + CV.carrierR hn hG hS C = CV.carrierR hn hG hQ q₀ + 1 ∧
      CV.weight hG.crossingGeometry _ A * CV.weight hG.crossingGeometry _ B *
        CV.weight hG.crossingGeometry _ C * CV.weight hG.crossingGeometry _ Z =
        -CV.weight hG.crossingGeometry Q q₀) ∨
    (CV.carrierR hn hG hS A + CV.carrierR hn hG hS B + CV.carrierR hn hG hS C + 1 = CV.carrierR hn hG hQ q₀ ∧
      CV.weight hG.crossingGeometry _ A * CV.weight hG.crossingGeometry _ B *
        CV.weight hG.crossingGeometry _ C * CV.weight hG.crossingGeometry _ Z = 0)

/-- **The interface of row 177** (never mapped): at every configuration of the row's `couple` field —
`t` the `K3` side, `t'` the empty side, `Q` an outside support at full availability, `q₀`/`q₀'` the
triangle-touching carriers of the empty row on the two sides — the carrier split of `Q ∪ T` on the empty
side and the move data of the two grouped contact diagrams exist with a common `Λ` and with the
outer grouped polynomials `f_A, f_B, f_C`. -/
def esc_interface : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ (A B C Z : GeoComponent (geomAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)) (Λ : ℕ),
        esc_FullSplitData hn (genericAt E t' ht'.1) e f g hQi' hS' q₀' A B C Z Λ ∧
        esc_MoveData (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀)
          (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')
          (crossingPoint (xPair hef)) (crossingPoint (xPair heg))
          (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg))) Λ
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' A) (CV.groupedPoly hn (genericAt E t' ht'.1) hS' B)
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' C)

/-! #### E. The ledger -/

/-- **(7) and (13) in one step**: from the two skein equations at `x` and at `y` on each side, the two
move identities (4), (6), knot parity (8) and the three-component row (12),
"`Omega_H - Omega_L = -[a^(d+2+2Λ)] (a-a^(-1))^2 K(a)`" — for any positive crossings `x_H, x_L` of two
diagrams `D_H, D_L`, and any positive crossings `y_H, y_L` of oriented smoothings there. -/
theorem esc_coefficient_identity {D_H D_L D_H0 D_L0 J_H J_L : Diagram}
    {x_H : D_H.Γ.Crossing} {x_L : D_L.Γ.Crossing} {y_H : D_H0.Γ.Crossing} {y_L : D_L0.Γ.Crossing}
    (hxH : D_H.IsPositive x_H) (hxL : D_L.IsPositive x_L)
    (hsmH : IsOrientedSmoothing D_H x_H D_H0) (hsmL : IsOrientedSmoothing D_L x_L D_L0)
    (hyH : D_H0.IsPositive y_H) (hyL : D_L0.IsPositive y_L)
    (hsmJH : IsOrientedSmoothing D_H0 y_H J_H) (hsmJL : IsOrientedSmoothing D_L0 y_L J_L)
    (m4 : esc_switch_riii D_H D_L x_H x_L) (m6 : esc_rii_after_smoothing D_H0 D_L0 y_H y_L)
    (hJH : J_H.componentCount = 1) {Λ : ℕ} {K : R}
    (h12 : ∀ p : ℤ, coeffAt p (-2) (homfly J_L) = coeffAt (p + 2 * (Λ : ℤ)) 0 ((R.a - R.aInv) ^ 2 * K))
    (d : ℤ) :
    coeffAt d 0 (homfly D_H - homfly D_L) =
      -coeffAt (d + 2 + 2 * (Λ : ℤ)) 0 ((R.a - R.aInv) ^ 2 * K) := by
  have sk1 := CV.ax_homfly.skein D_H (D_H.switch x_H) D_H0 ⟨x_H, hxH, rfl, hsmH⟩
  have sk2 := CV.ax_homfly.skein D_L (D_L.switch x_L) D_L0 ⟨x_L, hxL, rfl, hsmL⟩
  have sk3 := CV.ax_homfly.skein D_H0 (D_H0.switch y_H) J_H ⟨y_H, hyH, rfl, hsmJH⟩
  have sk4 := CV.ax_homfly.skein D_L0 (D_L0.switch y_L) J_L ⟨y_L, hyL, rfl, hsmJL⟩
  unfold esc_switch_riii at m4
  unfold esc_rii_after_smoothing at m6
  have u := R.aInv_mul_a
  -- (7): `F_H − F_L = a^{−2} z^{2} (P(J_H) − P(J_L))`
  have h7 : homfly D_H - homfly D_L = single (-2, 2) 1 * (homfly J_H - homfly J_L) := by
    rw [← esc_aInv_aInv_z_z]
    linear_combination (R.aInv * R.aInv * R.z) * (sk3 - sk4) + R.aInv * (sk1 - sk2) +
      (R.aInv * R.aInv) * m4 + (R.aInv * R.aInv * R.aInv * R.z) * m6 -
      ((homfly D_H - homfly D_L) + R.aInv * R.z * (homfly D_H0 - homfly D_L0)) * u
  rw [h7, esc_coeffAt_single_mul, one_mul, coeffAt_sub, show d - -2 = d + 2 by ring,
    show (0 : ℤ) - 2 = -2 by norm_num, esc_knot_coeff_neg_two J_H hJH, zero_sub, h12]

/-- **The contact identity**: the difference of the two touching factors of the empty row is the
touching factor of the full row on the empty side (ESC §1–§5 at one configuration), from the interface
data and `CarrierSlotFloor`. -/
theorem esc_contact_identity (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n}
    {δ : ℝ} (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef₀ : e ≠ f) (heg₀ : e ≠ g) (hfg₀ : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) (_hK : CompleteLocal (geomAt E t ht.1) hef heg hfg)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
    (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
    (hI : ∀ (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ (A B C Z : GeoComponent (geomAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)) (Λ : ℕ),
        esc_FullSplitData hn (genericAt E t' ht'.1) e f g hQi' hS' q₀' A B C Z Λ ∧
        esc_MoveData (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀)
          (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')
          (crossingPoint (xPair hef)) (crossingPoint (xPair heg))
          (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg))) Λ
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' A) (CV.groupedPoly hn (genericAt E t' ht'.1) hS' B)
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' C)) :
    touchingFactor hn (genericAt E t ht.1) hQi e f g -
        touchingFactor hn (genericAt E t' ht'.1) hQi' e f g =
      touchingFactor hn (genericAt E t' ht'.1) hS' e f g := by
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  -- the contact carrier on the `K3` side
  obtain ⟨q₀, hq₀⟩ := esc_contact_exists ht hef Q
  have huniq : ∀ q, ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q ↔ q = q₀ :=
    fun q => ⟨fun hq => esc_contact_unique hL hef₀ heg₀ hfg₀ ht hQ hfull hq hq₀, fun h => h ▸ hq₀⟩
  have hTq₀ := esc_contact_owns hL hef₀ heg₀ hfg₀ ht hQ hfull hq₀
  -- the wall and the transported contact carrier on the empty side
  have W := GT_empty_wall hL hR hef₀ heg₀ hfg₀ ht ht' hop hs hQ
  have hX := GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q₀
  have hq₀' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g
      (GT_carrierEquiv W q₀) := by
    rw [esc_not_triangleDisjoint_iff]
    have hmem : crossingTransport hs (xPair hef) ∈
        geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs Q) (GT_carrierEquiv W q₀) := by
      rw [hX, Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact hTq₀ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl))
    obtain ⟨i, -, -⟩ := crossing_visits_exist (crossingTransport hs (xPair hef))
    exact ⟨⟨_, i⟩, (P1.mem_triangleSupports _).mpr (Or.inl rfl),
      ((mem_geoCarrierCrossings _ _ _ _).mp hmem).2 _ rfl⟩
  have huniq' : ∀ q, ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q ↔
      q = GT_carrierEquiv W q₀ :=
    fun q => ⟨fun hq => esc_contact_unique hL hef₀ heg₀ hfg₀ ht' hQ' hfull' hq hq₀', fun h => h ▸ hq₀'⟩
  have hT'q₀' := esc_contact_owns hL hef₀ heg₀ hfg₀ ht' hQ' hfull' hq₀'
  -- the interface data
  obtain ⟨A, B, C, Z, Λ, hsplit, hmove⟩ := hI q₀ (GT_carrierEquiv W q₀) hq₀ hq₀'
  -- notation
  set hG := genericAt E t ht.1
  set hG' := genericAt E t' ht'.1
  set q₀' := GT_carrierEquiv W q₀
  set D_H := CV.carrierDiagram hn hG hQi q₀
  set D_L := CV.carrierDiagram hn hG' hQi' q₀'
  set fA := CV.groupedPoly hn hG' hS' A
  set fB := CV.groupedPoly hn hG' hS' B
  set fC := CV.groupedPoly hn hG' hS' C
  -- the transported data of the contact carrier
  have hw : CV.weight hG'.crossingGeometry (transportSupport hs Q) q₀' = CV.weight hG.crossingGeometry Q q₀ :=
    GT_weight_eq hn hG hG' W q₀
  have hRq : CV.carrierR hn hG' hQi' q₀' = CV.carrierR hn hG hQi q₀ := GT_carrierR_eq hn hG hG' W hQi hQi' q₀
  have hwr : CV.groupedWrithe hG' q₀' = CV.groupedWrithe hG q₀ := by
    rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi,
      hX, Finset.card_map]
  have hslot : CV.slot hn hG' hQi' q₀' = CV.slot hn hG hQi q₀ := by
    unfold CV.slot; rw [hRq, hwr]
  -- the two touching factors of the empty row and the one of the full row
  rw [esc_touchingFactor_eq_of_unique hn hG hQi e f g q₀ huniq,
    esc_touchingFactor_eq_of_unique hn hG' hQi' e f g q₀' huniq',
    esc_touchingFactor_eq_of_four hn hG' hS' e f g A B C Z hsplit.distinct hsplit.touching_iff, ← hw,
    ← mul_sub]
  -- the central carrier: `Ω₁ = 1`
  have hΩZ : CV.Omega1 hn hG' hS' Z = 1 := by
    unfold CV.Omega1 CV.slot
    rw [CV.groupedPoly_of_piecesOn_eq_empty hn hG' hS' Z hsplit.central_no_piece,
      CV.groupedWrithe_of_piecesOn_eq_empty hG' Z hsplit.central_no_piece, hsplit.central_rot]
    simp [coeffAt_one]
  rw [hΩZ]
  -- `Ω_H − Ω_L = [a^d z^0](F_H − F_L)`, `d` the common slot
  have hΩ : CV.Omega1 hn hG hQi q₀ - CV.Omega1 hn hG' hQi' q₀' =
      coeffAt (CV.slot hn hG' hQi' q₀') 0 (homfly D_H - homfly D_L) := by
    unfold CV.Omega1
    rw [hslot, GT_groupedPoly_eq_homfly, GT_groupedPoly_eq_homfly, coeffAt_sub]
  -- the crossings `x`, `y` on the grouped contact diagrams, the smoothings, the moves
  have hxT : xPair hef ∈ triangleCrossings (E.curve t) e f g :=
    (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl)
  have hyT : xPair heg ∈ triangleCrossings (E.curve t) e f g :=
    (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inl rfl))
  have hef' : IsCrossing (E.curve t') {e, f} := (hs _).mp hef
  have heg' : IsCrossing (E.curve t') {e, g} := (hs _).mp heg
  have hfg' : IsCrossing (E.curve t') {f, g} := (hs _).mp hfg
  have hxT' : xPair hef' ∈ triangleCrossings (E.curve t') e f g :=
    (P1.mem_triangleCrossings_iff hef' heg' hfg' _).mpr (Or.inl rfl)
  have hyT' : xPair heg' ∈ triangleCrossings (E.curve t') e f g :=
    (P1.mem_triangleCrossings_iff hef' heg' hfg' _).mpr (Or.inr (Or.inl rfl))
  obtain ⟨x_H, hxH_pt, hxH_pos⟩ := esc_lift_crossing hn hG hQi q₀ (xPair hef) (hTq₀ hxT)
  obtain ⟨y_H, hyH_pt, hyH_pos⟩ := esc_lift_crossing hn hG hQi q₀ (xPair heg) (hTq₀ hyT)
  obtain ⟨x_L, hxL_pt, hxL_pos⟩ := esc_lift_crossing hn hG' hQi' q₀' (xPair hef') (hT'q₀' hxT')
  obtain ⟨y_L, hyL_pt, hyL_pos⟩ := esc_lift_crossing hn hG' hQi' q₀' (xPair heg') (hT'q₀' hyT')
  have hyxH : y_H ≠ x_H := by
    intro h
    apply P1.xPair_ef_ne_eg hef heg hfg
    apply crossingPoint_injective_of_geometry (geomAt E t ht.1)
    rw [← hxH_pt, ← hyH_pt, h]
  have hyxL : y_L ≠ x_L := by
    intro h
    apply P1.xPair_ef_ne_eg hef' heg' hfg'
    apply crossingPoint_injective_of_geometry (geomAt E t' ht'.1)
    rw [← hxL_pt, ← hyL_pt, h]
  obtain ⟨D_H0, hsmH, -⟩ := exists_smoothing_record_visit D_H x_H (D_H.overVisit x_H) rfl
  obtain ⟨D_L0, hsmL, -⟩ := exists_smoothing_record_visit D_L x_L (D_L.overVisit x_L) rfl
  obtain ⟨y_H0, hyH0_pt, hyH0_pos⟩ := esc_smoothing_outer hsmH y_H hyxH
  obtain ⟨y_L0, hyL0_pt, hyL0_pos⟩ := esc_smoothing_outer hsmL y_L hyxL
  rw [hyH_pt] at hyH0_pt
  rw [hyL_pt] at hyL0_pt
  obtain ⟨J_H, hsmJH, -⟩ := exists_smoothing_record_visit D_H0 y_H0 (D_H0.overVisit y_H0) rfl
  obtain ⟨J_L, hsmJL, -⟩ := exists_smoothing_record_visit D_L0 y_L0 (D_L0.overVisit y_L0) rfl
  have m4 := hmove.switch_riii x_H x_L hxH_pt hxL_pt
  have m6 := hmove.rii_after_smoothing x_H x_L hxH_pt hxL_pt D_H0 D_L0 hsmH hsmL y_H0 y_L0 hyH0_pt hyL0_pt
  have hJH := hmove.knot_after_two x_H hxH_pt D_H0 hsmH y_H0 hyH0_pt J_H hsmJH
  have h12 := esc_three_component_row (hmove.three_components x_L hxL_pt D_L0 hsmL y_L0 hyL0_pt J_L hsmJL)
  -- (13)
  have h13 := esc_coefficient_identity hxH_pos hxL_pos hsmH hsmL (hyH0_pos.mpr hyH_pos)
    (hyL0_pos.mpr hyL_pos) hsmJH hsmJL m4 m6 hJH h12 (CV.slot hn hG' hQi' q₀')
  rw [hΩ, h13, esc_coeffAt_sq_mul]
  -- the three selector branches on the empty contact carrier
  set d := CV.slot hn hG' hQi' q₀' with hd
  set K := fA * fB * fC with hK
  have hprod : (CV.weight hG'.crossingGeometry _ A * CV.Omega1 hn hG' hS' A) *
      (CV.weight hG'.crossingGeometry _ B * CV.Omega1 hn hG' hS' B) *
      (CV.weight hG'.crossingGeometry _ C * CV.Omega1 hn hG' hS' C) *
      (CV.weight hG'.crossingGeometry _ Z * 1) =
      (CV.weight hG'.crossingGeometry _ A * CV.weight hG'.crossingGeometry _ B *
        CV.weight hG'.crossingGeometry _ C * CV.weight hG'.crossingGeometry _ Z) *
      (CV.Omega1 hn hG' hS' A * CV.Omega1 hn hG' hS' B * CV.Omega1 hn hG' hS' C) := by ring
  rw [hprod]
  by_cases huni : CV.CarrierUniform hG'.crossingGeometry (transportSupport hs Q) q₀'
  · -- the uniform contact carrier: the outer floors
    obtain ⟨haltA, haltB, haltC⟩ := hsplit.outer_alternative huni
    have hqA := esc_quadrant_groupedPoly hF hn hG' hS' A haltA
    have hqB := esc_quadrant_groupedPoly hF hn hG' hS' B haltB
    have hqC := esc_quadrant_groupedPoly hF hn hG' hS' C haltC
    have hqK := esc_quadrant_mul (esc_quadrant_mul hqA hqB) hqC
    -- (19)
    have h19 : coeffAt (CV.slot hn hG' hS' A + CV.slot hn hG' hS' B + CV.slot hn hG' hS' C) 0 K =
        CV.Omega1 hn hG' hS' A * CV.Omega1 hn hG' hS' B * CV.Omega1 hn hG' hS' C := by
      rw [hK, esc_coeffAt_corner (esc_quadrant_mul hqA hqB) hqC, esc_coeffAt_corner hqA hqB]
      rfl
    have hwrq := hsplit.writhe
    have hdq : d = 1 - CV.groupedWrithe hG' q₀' - (CV.carrierR hn hG' hQi' q₀' : ℤ) := rfl
    rcases hsplit.uniform huni with ⟨hrot, hwf⟩ | ⟨hrot, hwf⟩
    · -- live branch `χ = 1`: (18) `D = d + 4 + 2Λ`; (20) `Ω_H − Ω_L = −ω_A ω_B ω_C`
      have hrot' : (CV.carrierR hn hG' hS' A : ℤ) + CV.carrierR hn hG' hS' B + CV.carrierR hn hG' hS' C =
          CV.carrierR hn hG' hQi' q₀' + 1 := by exact_mod_cast hrot
      have hD : CV.slot hn hG' hS' A + CV.slot hn hG' hS' B + CV.slot hn hG' hS' C = d + 4 + 2 * (Λ : ℤ) := by
        simp only [CV.slot] at hdq ⊢
        omega
      rw [hD] at h19 hqK
      rw [show d + 2 + 2 * (Λ : ℤ) - 2 = d + 2 * Λ by ring,
        show d + 2 + 2 * (Λ : ℤ) + 2 = d + 4 + 2 * Λ by ring, h19,
        hqK.coeffAt_eq_zero (by omega), hqK.coeffAt_eq_zero (by omega), hwf]
      ring
    · -- dead branch `χ = 0`: (18) `D = d + 6 + 2Λ`; every sample is below the floor
      have hrot' : (CV.carrierR hn hG' hS' A : ℤ) + CV.carrierR hn hG' hS' B + CV.carrierR hn hG' hS' C + 1 =
          CV.carrierR hn hG' hQi' q₀' := by exact_mod_cast hrot
      have hD : CV.slot hn hG' hS' A + CV.slot hn hG' hS' B + CV.slot hn hG' hS' C = d + 6 + 2 * (Λ : ℤ) := by
        simp only [CV.slot] at hdq ⊢
        omega
      rw [hD] at hqK
      rw [hqK.coeffAt_eq_zero (by omega), hqK.coeffAt_eq_zero (by omega),
        hqK.coeffAt_eq_zero (by omega), hwf]
      ring
  · -- the mixed contact carrier: `W = 0` and `W_full = 0`
    have hW0 : CV.weight hG'.crossingGeometry (transportSupport hs Q) q₀' = 0 :=
      CV.weight_of_mixed _ _ q₀' huni
    rw [hsplit.mixed huni, hW0]
    ring

/-- **The `couple` field of row 177** from the interface, `CarrierSlotFloor`, and the accepted data at a
common radius: (2) "`T_H(empty) - T_L(empty) = T_L(xyz)`" — the exterior factor `C_Q` is common to the
three rows (row 168: `EXT_exteriorFactor_wall`, `EXT_exteriorFactor_eq_base`), the rest is the contact
identity.  "No exterior scalar, selector, or coefficient was divided out." -/
theorem esc_couple (hI : esc_interface) (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n) {E : CV.Event n}
    {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hguard : ∀ u : E.Parameter, |u.val| < δ → EXT_GuardAt E u) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t ht.1) Q - rowTerm hn (genericAt E t' ht'.1) (transportSupport hs Q) =
        rowTerm hn (genericAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) := by
  intro t t' ht ht' hop hs hef heg hfg hK Q hQ hfull
  have hef₀ : e ≠ f := AV_ne_of_remote h3.1
  have hfg₀ : f ≠ g := AV_ne_of_remote h3.2.1
  have heg₀ : e ≠ g := AV_ne_of_remote h3.2.2.1
  have hef' : IsCrossing (E.curve t') {e, f} := (hs _).mp hef
  have heg' : IsCrossing (E.curve t') {e, g} := (hs _).mp heg
  have hfg' : IsCrossing (E.curve t') {f, g} := (hs _).mp hfg
  have hQi : Q ∈ CV.Ind (geomAt E t ht.1) := mem_Ind_of_mem_outsideSupports hQ
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1) := mem_Ind_of_mem_outsideSupports hQ'
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  have hEmpty : EmptyLocal (geomAt E t' ht'.1) hef' heg' hfg' :=
    (PRE_176_graphs_complementary hL t t' ht ht' hop hef heg hfg hef' heg' hfg').mp hK
  have hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1) :=
    PRE_177_full_present_on_empty E e f g δ t' ht' hef' heg' hfg' hEmpty _ hQ' hfull'
  -- the exterior factor `C_Q` of the three rows (row 168)
  have hQT : ∀ x ∈ Q, x.val ∉ triangleSupports e f g := fun x hx hxT =>
    Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hx
      ((P1.mem_triangleCrossings x).mpr hxT)
  have hQ'T : ∀ x ∈ transportSupport hs Q, x.val ∉ triangleSupports e f g := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact hQT y hy
  rw [rowTerm_eq_exterior_mul_touching hn (genericAt E t ht.1) hQi e f g,
    rowTerm_eq_exterior_mul_touching hn (genericAt E t' ht'.1) hQi' e f g,
    rowTerm_eq_exterior_mul_touching hn (genericAt E t' ht'.1) hS' e f g,
    EXT_exteriorFactor_wall hE hn hL hguard ht ht' hop hs hQi hQT hQi',
    ← EXT_exteriorFactor_eq_base hn (genericAt E t' ht'.1) hQ'T
      (fun x hx => (P1.mem_triangleCrossings x).mp hx) hS' hQi',
    EXT_exteriorFactor_wall hE hn hL hguard ht ht' hop hs hQi hQT hQi', ← mul_sub]
  congr 1
  exact esc_contact_identity hF hn hL hR hef₀ heg₀ hfg₀ ht ht' hop hs hef heg hfg hK hQ hfull hQi hQi' hS'
    (fun q₀ q₀' hq₀ hq₀' => hI hn E e f g δ hL t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS'
      q₀ q₀' hq₀ hq₀')

/-- **The RA ledger of row 177** (D-F11): the fixed row shape from the interface and `CarrierSlotFloor`;
the two presupposition fields are the accepted `PRE_177_*`, the radius is the minimum of the accepted
radii of rows 164 (`localization`), the sign data (`AV_exists_eventRadius`) and the guard
(`EXT_exists_guardRadius`). -/
theorem esc_ledger (hI : esc_interface) (hF : CV.CarrierSlotFloor) : RowShape @ExtremeSelectedData := by
  intro n _ hn E e f g h3 h4e h4f h4g hE
  obtain ⟨δL, hδL, hδLr, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  obtain ⟨δR, hδR, -, hR⟩ := AV_exists_eventRadius hE
  obtain ⟨δG, hδG, -, hguard⟩ := EXT_exists_guardRadius hE
  refine ⟨min δL (min δR δG), lt_min hδL (lt_min hδR hδG), (min_le_left _ _).trans hδLr, ?_⟩
  have hL' := F1.localizationData_mono (min_le_left δL (min δR δG)) hL
  have hR' := AV_eventRadius_mono ((min_le_right δL (min δR δG)).trans (min_le_left δR δG)) hR
  have hguard' : ∀ u : E.Parameter, |u.val| < min δL (min δR δG) → EXT_GuardAt E u :=
    fun u hu => hguard u (lt_of_lt_of_le hu ((min_le_right _ _).trans (min_le_right _ _)))
  exact { full_present_on_empty := PRE_177_full_present_on_empty E e f g _
          full_absent_on_complete := PRE_177_full_absent_on_complete E e f g _
          couple := esc_couple hI hF hn hE hL' hR' hguard' }

end ESC

/-- CV:prop:chamberinv (ii) (accepted row 147, `CV.chamberinv_ii`) in the R lane's `ChamberInvII` shape. PROVED. -/
theorem cvt_chamberInvII : ChamberInvII :=
  fun _ _ hn _ _ hP hQ h => (CV.chamberinv_ii hn hP hQ h).symm

/-- **Row 178 modulo rows 174-177**, PROVED: R_ASSEMBLY_SPEC.md (3)-(4) summed over the same outside
support set (`A2_cvRNear_of_rows`, accepted, with the accepted rows 170, 172, 173) and R6
`cv_R = cv_R_near + chamberinv(ii)` (`hyp_R_of_near_of_chamberinv`, accepted); the domain is
`E.IsSimpleRIII` (CV:def:event), "its entire printed simple/transversal forced-bundle domain". -/
theorem cv_R_of_rows (h174 : RowShape @GenericSelectedData) (h175 : RowShape @ExtremePairZeroData)
    (h176 : RowShape @ExtremeTransportData) (h177 : RowShape @ExtremeSelectedData) : CV.hyp_R :=
  hyp_R_of_near_of_chamberinv
    (A2_cvRNear_of_rows rowShape_170 rowShape_172 rowShape_173 h174 h175 h176 h177)
    cvt_chamberInvII

end RProof

namespace Bridge

/-- The same from the four open R rows (library form). PROVED. -/
theorem sm_R_of_rows (h174 : RProof.RowShape @RProof.GenericSelectedData)
    (h175 : RProof.RowShape @RProof.ExtremePairZeroData)
    (h176 : RProof.RowShape @RProof.ExtremeTransportData)
    (h177 : RProof.RowShape @RProof.ExtremeSelectedData) : SM.hyp_R :=
  SM.sm_R_of_cv_R (RProof.cv_R_of_rows h174 h175 h176 h177)

end Bridge
