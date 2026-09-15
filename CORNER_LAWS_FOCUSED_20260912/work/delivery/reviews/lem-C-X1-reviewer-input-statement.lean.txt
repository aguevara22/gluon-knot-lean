import SM.CornerStateSum

/-! Source lem:C-X1 (reference/SM/sm-3-statesum.tex:1787-1798, frame SM15): selector form of the carrier state
sum. Main declaration: `SM.C_X1`.

Notation (accepted rows def:uniform, lem:carriers, def:C; namespaces `SM.Carrier`, `SM.Link`): "a carrier `L` of
an independent support `S`" is `q : Component hn hP S` with `S ∈ independentSupports hn hP` (= Ind(G_P),
`IsDecomposition`); "its number of corners `k(L)`" is `ccpCornerCount hn hP S q`; its turns are
`turn (ccpCornerPolygon hn hP S q) j` (def:chirotope: `turn = sgn det(incoming, outgoing)`, a LEFT turn is `1`, a
RIGHT turn is `−1`; all carrier turns are nonzero by lem:carriers); "wt(L) = 1 if all its turns are right,
(−1)^{k(L)} if all are left, 0 if mixed" is `carrierWeight`; "wind(S) = ∏_L wt(L)" is `wind`; `C(P)` is
`cornerStateSum hn hP` and "c(L), the coefficient of the actual positive carrier lift in def:C" is
`cornerCoefficient hn hP S q hS` (their product over the carriers of `S` is `cornerProduct hn hP S hS`). -/

namespace SM

open Link Carrier

variable {n : ℕ} [NeZero n]

/-- "wt(L) = 1 if all its turns are right, (−1)^{k(L)} if all are left, and 0 if its turns are mixed." -/
noncomputable def carrierWeight (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : ℤ :=
  if ∀ j, turn (ccpCornerPolygon hn hP S q) j = -1 then 1
  else if ∀ j, turn (ccpCornerPolygon hn hP S q) j = 1 then (-1) ^ ccpCornerCount hn hP S q
  else 0

/-- "wind(S) = ∏_L wt(L)" over the carriers of `S`. -/
noncomputable def wind (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) : ℤ :=
  ∏ q : Component hn hP S, carrierWeight hn hP S q

/-- lem:C-X1 as printed. -/
structure CX1Data : Prop where
  /-- wt(L) = 1 if all turns of `L` are right -/
  weight_right : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S),
    (∀ j, turn (ccpCornerPolygon hn hP S q) j = -1) → carrierWeight hn hP S q = 1
  /-- wt(L) = (−1)^{k(L)} if all turns of `L` are left -/
  weight_left : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S),
    (∀ j, turn (ccpCornerPolygon hn hP S q) j = 1) →
    carrierWeight hn hP S q = (-1) ^ ccpCornerCount hn hP S q
  /-- wt(L) = 0 if the turns of `L` are mixed (neither all right nor all left) -/
  weight_mixed : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S),
    (¬ ∀ j, turn (ccpCornerPolygon hn hP S q) j = -1) → (¬ ∀ j, turn (ccpCornerPolygon hn hP S q) j = 1) →
    carrierWeight hn hP S q = 0
  /-- "Set wind(S) = ∏_L wt(L)." -/
  wind_eq : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)), wind hn hP S = ∏ q : Component hn hP S, carrierWeight hn hP S q
  /-- eq. C-selector-form: `C(P) = Σ_{S ∈ Ind(G_P)} wind(S) ∏_L c(L)`, where c(L) remains the coefficient of
  the actual positive carrier lift of def:C. -/
  selector_form : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
    cornerStateSum hn hP =
      ∑ S ∈ (independentSupports hn hP).attach, wind hn hP S.1 * cornerProduct hn hP S.1 S.2

theorem C_X1 : CX1Data := by
  sorry

end SM
