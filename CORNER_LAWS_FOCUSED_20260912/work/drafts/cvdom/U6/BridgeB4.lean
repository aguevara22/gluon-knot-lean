import Bridge.B3
import SM.GeoCarrierAgreement
import SM.CBProducts
import SM.GermSides
import CV.ChamberInvRow

/-! # Bridge/B4.lean — row Bridge:B4 (`Bridge.B4`), CV-DOM unit U6

Draft (work/drafts/cvdom/U6/BridgeB4.lean), intended home `work/lean/Bridge/B4.lean`.
Source: reference/BRIDGE/BRIDGE.md §2, B4 at lines 637-1441 ("Lemma B4. On every SM-generic labelled
representative, the two state sums have equal values. On either punctured side of a triple germ, this
equality identifies the SM side value with the value on its containing CV chamber."), displays (17) (line
1366) and (18) (line 1439).  Shape: DECISION_FINAL.md ruling R7 (`structure Bridge.B4Data : Prop` with the
fields `pointwise` = (17) and `sides` = (18); `theorem Bridge.B4 : B4Data`).

## The two fields

* `pointwise` — BRIDGE.md (17), "`C^SM(P) = X₁^CV(P)` for every `P ∈ 𝓤_n^SM`", on SM-generic labelled
  representatives as printed: for every `n`, `hn : 3 ≤ n`, `P : LabelledTuple n`, `hP : SM.Generic P`,
  `CV.X1 hn P (CV.generic_of_sm hn hP) = SM.cornerStateSum hn hP`.  `CV.X1` is evaluated through B1 (1)
  (`CV.generic_of_sm`, the inclusion `𝓤_n^SM ⊆ 𝓤_n^CV`); this is the shape `Bridge.sm_R` consumes
  (work/drafts/rlane2/Statements_FINAL.lean `smR_shape_of_hyp_R`).  Proof: SM/GeoCarrierAgreement.lean
  (`CV.X1_generic_of_sm_eq_cornerStateSum_of_cb`) with cb:products (`SM.cb_products`, row 102) at every
  decomposition — parts 1-4 of BRIDGE.md B4: common supports (`CV.Ind_eq_generic`), common carriers
  (`geoComponentEquivGeneric`), `∏_H P_H = H⁺_L` (cb:products, (13)), `w_{S,L} = m_L` ((13)), `R(L) = |r_L|`
  ((14)), slots ((15)), coefficients ((16)), selectors (`CV.wind_eq_generic`), sum over `Ind(G_P)` ((17)).
* `sides` — BRIDGE.md (18), "`C^SM(P_±^SM) = X₁^CV(P_±^CV)`", the equalities of **values on corresponding
  sides** of a type-`T` germ: for every SM wall germ `g` with `g.TripleAt e f k`, every side `b`, every SM
  side parameter `t` and every `Q` in the CV side chamber `(Bridge.eventOfTriple hn g h).sideChamber b`
  (CV def:event's "the chambers containing `P((0,ε))` / `P((−ε,0))`", the CV event of B1) with its
  genericity proof `hQ`, `SM.cornerStateSum hn (g.sideTuple b t).2 = CV.X1 hn Q hQ`.  The SM side value is
  read at an arbitrary side parameter `t` (it is independent of `t`: two instances of the field at `t`, `t'`
  with the same `Q` give `C(P(t)) = C(P(t'))`), the CV side value at an arbitrary point of the containing CV
  chamber.  Proof exactly as printed (BRIDGE.md 1429-1441): SM's chamber constancy `SM.prop_C_chamber`
  moves the SM side value along the connected punctured side (`WallGerm.sidePolygon_mem_side`: the side image
  lies in one SM chamber, def:germ / GermSides) to the base parameter; (17) identifies it with `X₁` there;
  CV's chamber constancy `CV.chamberinv_ii` (prop:chamberinv (ii), accepted row 147) identifies that with the
  value on the containing CV side chamber (`Event.sideChamber b = chamber (sideCurve b sideBase)`, and
  `(eventOfTriple hn g h).sideCurve b t = (g.sideTuple b t).val` definitionally, Bridge/B1.lean).
  "These are equalities of values on corresponding sides. They do not assert equality of a quotient SM
  chamber with a labelled CV chamber, or equality of their underlying generic loci."

## Review note (DECISION_FINAL §4, Bridge:B4)

Field `pointwise` is (17) on SM-generic labelled representatives, as printed; field `sides` is (18).
`CV.X1` at an SM-generic `P` is evaluated through `CV.generic_of_sm hn hP` (B1 (1)); the identification with
`cornerStateSum` goes through the agreement lemmas of SM/GeoCarrierAgreement.lean, lem:C-X1 (`SM.C_X1`) and
cb:products (`SM.cb_products`).  `B4_of_cb` isolates cb:products as the one hypothesis (DECISION_FINAL §7
risk 6); `B4` discharges it with the accepted row 102.

Checked (draft) with the agreement module compiled to an `.olean` under a temporary root shadowing the `SM`
package (work/drafts/cvdom/U5a/REPORT.md §1 recipe); once SM/GeoCarrierAgreement.lean is in work/lean the
plain `cd work/lean && lake env lean` check applies. -/

namespace Bridge

open SM

/-- **Bridge:B4 as printed** (BRIDGE.md 637-639, displays (17) and (18); ruling R7): one field per printed
sentence. -/
structure B4Data : Prop where
  /-- BRIDGE.md (17): "`C^SM(P) = X₁^CV(P)` for every `P ∈ 𝓤_n^SM`" — on every SM-generic labelled
  representative the two state sums have equal values (`X₁` read through B1 (1), `CV.generic_of_sm`). -/
  pointwise : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : SM.Generic P),
    CV.X1 hn P (CV.generic_of_sm hn hP) = SM.cornerStateSum hn hP
  /-- BRIDGE.md (18): "`C^SM(P_+^SM) = X₁^CV(P_+^CV)`, `C^SM(P_−^SM) = X₁^CV(P_−^CV)`" — on either punctured
  side `b` of a type-`T` germ `g`, the SM side value (the state sum at any side parameter `t`) equals the value
  of `X₁` at any point `Q` of the containing CV side chamber of the event `eventOfTriple hn g h` (B1). -/
  sides : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (e f k : ZMod n) (h : g.TripleAt e f k)
    (t : g.SideParameter) (b : Bool) (Q : LabelledTuple n),
    Q ∈ (eventOfTriple hn g h).sideChamber b → ∀ hQ : CV.Generic Q,
    SM.cornerStateSum hn (g.sideTuple b t).2 = CV.X1 hn Q hQ

variable {n : ℕ} [NeZero n]

/-- (17) from cb:products at every decomposition of every SM-generic polygon (the hypothesis-shaped form of
SM/GeoCarrierAgreement.lean; DECISION_FINAL §7 risk 6). -/
theorem B4_pointwise_of_cb
    (hcb : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : SM.Generic P)
      (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S), CbProductsData hn hP hS)
    (hn : 3 ≤ n) (P : LabelledTuple n) (hP : SM.Generic P) :
    CV.X1 hn P (CV.generic_of_sm hn hP) = SM.cornerStateSum hn hP :=
  CV.X1_generic_of_sm_eq_cornerStateSum_of_cb hn hP fun S hS => hcb n hn P hP S hS

/-- The SM side value is independent of the side parameter (BRIDGE.md 1431 "SM's chamber constancy
identifies `C(P(t_±))` with its corresponding SM side value"): the punctured side image lies in one SM
chamber (`WallGerm.sidePolygon_mem_side`, def:germ), on which `C` is constant (`SM.prop_C_chamber`,
prop:C-chamber, accepted). -/
theorem cornerStateSum_sideTuple_eq_base (hn : 3 ≤ n) (g : WallGerm n) (b : Bool)
    (t : g.SideParameter) :
    SM.cornerStateSum hn (g.sideTuple b t).2 = SM.cornerStateSum hn (g.sideTuple b g.sideBase).2 :=
  (SM.prop_C_chamber.constant n hn (g.sideTuple b g.sideBase) (g.sideTuple b t)
    (g.sidePolygon_mem_side b t)).symm

/-- The CV side chamber of the event of a type-`T` germ is the CV chamber of the germ's base side tuple
(`Event.sideChamber` unfolded on `eventOfTriple`: same radius, same curve, Bridge/B1.lean). -/
theorem sideChamber_eventOfTriple (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) (b : Bool) :
    (eventOfTriple hn g h).sideChamber b = CV.chamber (g.sideTuple b g.sideBase).val := rfl

/-- (18) from (17): the printed proof (BRIDGE.md 1429-1441), step by step — SM chamber constancy to the base
parameter (`cornerStateSum_sideTuple_eq_base`), (17) there (`pointwise`), CV chamber constancy to `Q`
(`CV.chamberinv_ii`). -/
theorem B4_sides_of_pointwise
    (hpw : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : SM.Generic P),
      CV.X1 hn P (CV.generic_of_sm hn hP) = SM.cornerStateSum hn hP)
    (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n} (h : g.TripleAt e f k) (b : Bool)
    (t : g.SideParameter) (Q : LabelledTuple n) (hQ : Q ∈ (eventOfTriple hn g h).sideChamber b)
    (hQG : CV.Generic Q) :
    SM.cornerStateSum hn (g.sideTuple b t).2 = CV.X1 hn Q hQG := by
  rw [sideChamber_eventOfTriple hn g h b] at hQ
  calc SM.cornerStateSum hn (g.sideTuple b t).2
      = SM.cornerStateSum hn (g.sideTuple b g.sideBase).2 := cornerStateSum_sideTuple_eq_base hn g b t
    _ = CV.X1 hn (g.sideTuple b g.sideBase).val (CV.generic_of_sm hn (g.sideTuple b g.sideBase).2) :=
        (hpw n hn _ (g.sideTuple b g.sideBase).2).symm
    _ = CV.X1 hn Q hQG := (CV.chamberinv_ii hn (CV.generic_of_sm hn (g.sideTuple b g.sideBase).2) hQG hQ).symm

/-- **Bridge:B4 from cb:products** (DECISION_FINAL §7 risk 6: cb:products isolated as the one hypothesis). -/
theorem B4_of_cb
    (hcb : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : SM.Generic P)
      (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S), CbProductsData hn hP hS) :
    B4Data where
  pointwise := fun _ _ hn P hP => B4_pointwise_of_cb hcb hn P hP
  sides := fun _ _ hn g _ _ _ h t b Q hQ hQG =>
    B4_sides_of_pointwise (fun _ _ hn P hP => B4_pointwise_of_cb hcb hn P hP) hn g h b t Q hQ hQG

/-- **Row Bridge:B4** (BRIDGE.md 637-639, (17) and (18)), with cb:products discharged by the accepted row 102
(`SM.cb_products`). -/
theorem B4 : B4Data :=
  B4_of_cb fun _ _ hn _ hP _ hS => SM.cb_products hn hP hS

end Bridge
