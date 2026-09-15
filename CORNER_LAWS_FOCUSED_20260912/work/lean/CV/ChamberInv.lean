import CV.Setup

/-! Ported verbatim 2026-09-13 from work/drafts/CV_ChamberInv.lean (implementer subagent of the pod executor; checked with `lake env lean`, no sorry, standard axioms); only this header added and `#print axioms` lines removed. Row 147 CV:prop:chamberinv clause (i); clause (ii) (X₁ constant on chambers) is blocked on CV:def:X1 and is not in this module. -/

/-! # CV lane, row 147 — CV:prop:chamberinv, clause (i) (reference/R/CV/d1_setup.tex:932–961)

Printed statement (d1_setup.tex:932–939): "Fix `n ≥ 3`. (i) The generic locus `𝓤_n` is open in
`(ℝ²)^n`, and every chamber — every connected component of it — is open and path connected.
(ii) `X_1` is constant on each chamber."

This module renders clause (i) only, as the bundle `CV.ChamberInvIData n` (one field per printed
clause) and the theorem `CV.chamberinv_i`. Clause (ii) is not treated here (it is blocked on the
`X_1` layer, see work/reports/cv-lane-plan-20260913.md, row 147).

The proof follows the printed one (d1_setup.tex:940–961) step by step:
* every unconditional member `G2_{e,i}` is relevant at every polygon, hence nonzero at a generic
  `P`; each is continuous, so on a neighbourhood `N` of `P` it keeps its sign
  (`Generic.eventually_sign_G2`);
* on `N` the crossing status of every pair of remote edges is constant, being "the four-sign
  condition of Definition def:guarded in exactly those members" (`crosses_iff_of_sign_G2`,
  `Generic.eventually_crosses_iff`); hence the activation of every conditional member, and the set
  of relevant members, is constant on `N` (`Member.relevant_iff_of_sign_G2`,
  `Generic.eventually_relevant_iff`);
* shrinking `N` so that the finitely many members relevant at `P` keep their signs — they are
  finitely many (`Member.finite`) and continuous (`Member.continuous_eval`) —
  (`Generic.eventually_relevant_ne_zero`), every point of `N` is generic
  (`Generic.eventually_generic`), so `𝓤_n` is open (`isOpen_genericLocus`);
* "A connected component of an open subset of `ℝ^N` is open, the space being locally connected,
  and an open connected subset of `ℝ^N` is path connected": `(ℝ²)^n = ZMod n → ℝ × ℝ` is a real
  normed space, hence locally path connected, and Mathlib's `IsOpen.connectedComponentIn` and
  `IsOpen.isConnected_iff_isPathConnected` give `isOpen_chamber` and `isPathConnected_chamber`.

Domain (decision F2, work/AUTHOR_NOTES.md): no narrowing. Everything is stated on CV's own guarded
genericity `CV.Generic` on labelled tuples, with `CV.chamber P = connectedComponentIn (genericLocus n) P`
exactly as in CV:def:generic (B). The printed "Fix `n ≥ 3`" is a standing convention of the section
and is not used by the proof of clause (i); the bundle is therefore stated for every `n` with
`[NeZero n]` (the hypothesis under which `Member n` is defined), and `chamberinv_i_of_three_le`
restates it on the printed domain `3 ≤ n`.

Written 2026-09-13 by a Claude Code implementer subagent of the pod executor; checked with
`lake env lean` (sorry-free, standard axioms). -/

namespace CV

open SM Filter Topology

variable {n : ℕ} [NeZero n] {P Q : LabelledTuple n}

/-! ## The unconditional layer controls activation (d1_setup.tex:946–957) -/

/-- "Every unconditional member — every `G1_i` and every `G2_{e,i}` — is relevant at every polygon,
so all of them are nonzero at `P`, they are finitely many, and they are polynomials; let `N` be a
neighbourhood of `P` on which each of them keeps its sign" (d1_setup.tex:946–950), for the `G2`
layer that activation reads. -/
theorem Generic.eventually_sign_G2 (hP : Generic P) :
    ∀ᶠ Q in 𝓝 P, ∀ e i : ZMod n, i ≠ e → i ≠ e + 1 →
      SignType.sign (G2 Q e i) = SignType.sign (G2 P e i) := by
  refine eventually_all.mpr fun e => eventually_all.mpr fun i => ?_
  by_cases h : i ≠ e ∧ i ≠ e + 1
  · have hc : ContinuousAt (fun Q : LabelledTuple n => SignType.sign (G2 Q e i)) P :=
      (continuousAt_sign_of_ne_zero (hP.g2 h.1 h.2)).comp
        (f := fun Q : LabelledTuple n => G2 Q e i) (continuous_G2 e i).continuousAt
    exact (hc.eventually_mem ((isOpen_discrete _).mem_nhds (Set.mem_singleton _))).mono
      fun Q hQ _ _ => hQ
  · exact Eventually.of_forall fun Q h0 h1 => (h ⟨h0, h1⟩).elim

/-- The sign of a product of two reals is determined by the signs of the factors. -/
theorem mul_neg_iff_of_sign_eq {a b a' b' : ℝ} (ha : SignType.sign a = SignType.sign a')
    (hb : SignType.sign b = SignType.sign b') : a * b < 0 ↔ a' * b' < 0 := by
  rw [← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, sign_mul, sign_mul, ha, hb]

omit [NeZero n] in
/-- "On `N` the crossing status of every pair of remote edges is constant, being the four-sign
condition of Definition def:guarded in exactly those members" (d1_setup.tex:950–952): two polygons
at which every unconditional `G2` member has the same sign have the same activation relation. -/
theorem crosses_iff_of_sign_G2
    (h : ∀ e i : ZMod n, i ≠ e → i ≠ e + 1 → SignType.sign (G2 Q e i) = SignType.sign (G2 P e i))
    (e f : ZMod n) : Crosses Q e f ↔ Crosses P e f := by
  by_cases hr : remote e f
  · obtain ⟨h0, h1, h2, h3⟩ := remote_endpoints e f hr
    unfold Crosses
    rw [mul_neg_iff_of_sign_eq (h e f h0 h1) (h e (f + 1) h2 h3),
      mul_neg_iff_of_sign_eq (h f e h0.symm h2.symm) (h f (e + 1) h1.symm h3.symm)]
  · exact ⟨fun hc => (hr hc.1).elim, fun hc => (hr hc.1).elim⟩

/-- "hence the activation of every conditional member is constant on `N`" (d1_setup.tex:952–953). -/
theorem Member.active_iff_of_sign_G2
    (h : ∀ e i : ZMod n, i ≠ e → i ≠ e + 1 → SignType.sign (G2 Q e i) = SignType.sign (G2 P e i))
    (m : Member n) : m.Active Q ↔ m.Active P := by
  cases m <;> simp only [Member.Active, crosses_iff_of_sign_G2 h]

/-- "and so is the set of members relevant at a point" (d1_setup.tex:953–954). -/
theorem Member.relevant_iff_of_sign_G2
    (h : ∀ e i : ZMod n, i ≠ e → i ≠ e + 1 → SignType.sign (G2 Q e i) = SignType.sign (G2 P e i))
    (m : Member n) : m.Relevant Q ↔ m.Relevant P := by
  unfold Member.Relevant
  rw [Member.active_iff_of_sign_G2 h m]

/-- Local constancy of activation at a generic polygon (d1_setup.tex:950–952). -/
theorem Generic.eventually_crosses_iff (hP : Generic P) :
    ∀ᶠ Q in 𝓝 P, ∀ e f : ZMod n, Crosses Q e f ↔ Crosses P e f :=
  hP.eventually_sign_G2.mono fun _ hQ => crosses_iff_of_sign_G2 hQ

/-- Local constancy of the relevant set at a generic polygon (d1_setup.tex:952–954). -/
theorem Generic.eventually_relevant_iff (hP : Generic P) :
    ∀ᶠ Q in 𝓝 P, ∀ m : Member n, m.Relevant Q ↔ m.Relevant P :=
  hP.eventually_sign_G2.mono fun _ hQ => Member.relevant_iff_of_sign_G2 hQ

/-! ## Openness of the generic locus (d1_setup.tex:954–957) -/

/-- "Shrinking `N` so that the finitely many members relevant at `P` — now the members relevant
everywhere on `N` — also keep their signs" (d1_setup.tex:954–956): the members relevant at `P`
stay nonzero near `P`. -/
theorem Generic.eventually_relevant_ne_zero (hP : Generic P) :
    ∀ᶠ Q in 𝓝 P, ∀ m : Member n, m.Relevant P → m.eval Q ≠ 0 := by
  refine eventually_all.mpr fun m => ?_
  by_cases hm : m.Relevant P
  · exact (m.continuous_eval.continuousAt.eventually_ne (hP.2 m hm)).mono fun _ hQ _ => hQ
  · exact Eventually.of_forall fun _ h => (hm h).elim

/-- The polygon condition `p_{i+1} ≠ p_i` (CV:def:polygon) is open. -/
theorem Generic.eventually_isPolygon (hP : Generic P) : ∀ᶠ Q in 𝓝 P, IsPolygon Q := by
  show ∀ᶠ Q in 𝓝 P, ∀ i, edge Q i ≠ 0
  exact eventually_all.mpr fun i =>
    (continuous_edge i).continuousAt.eventually_ne (hP.edge_ne_zero i)

/-- "every point of `N` is generic" (d1_setup.tex:956–957). -/
theorem Generic.eventually_generic (hP : Generic P) : ∀ᶠ Q in 𝓝 P, Generic Q := by
  filter_upwards [hP.eventually_isPolygon, hP.eventually_relevant_iff,
    hP.eventually_relevant_ne_zero] with Q hpoly hrel hne
  exact ⟨hpoly, fun m hm => hne m ((hrel m).mp hm)⟩

/-- "So `𝓤_n` is open" (d1_setup.tex:957). -/
theorem isOpen_genericLocus : IsOpen (genericLocus n) :=
  isOpen_iff_mem_nhds.mpr fun _ hP => Generic.eventually_generic hP

theorem genericLocus_mem_nhds (hP : Generic P) : genericLocus n ∈ 𝓝 P :=
  isOpen_genericLocus.mem_nhds hP

/-! ## Chambers are open and path connected (d1_setup.tex:958–961) -/

/-- "A connected component of an open subset of `ℝ^N` is open, the space being locally connected"
(d1_setup.tex:958–959). Stated for every labelled tuple: at a non-generic `P` the chamber is empty
(`chamber_eq_empty`). -/
theorem isOpen_chamber (P : LabelledTuple n) : IsOpen (chamber P) :=
  isOpen_genericLocus.connectedComponentIn

theorem chamber_mem_nhds (hP : Generic P) : chamber P ∈ 𝓝 P :=
  (isOpen_chamber P).mem_nhds (mem_chamber_self hP)

/-- "and an open connected subset of `ℝ^N` is path connected" (d1_setup.tex:959–961). -/
theorem isPathConnected_chamber (hP : Generic P) : IsPathConnected (chamber P) :=
  (isOpen_chamber P).isConnected_iff_isPathConnected.mp (isConnected_chamber hP)

/-- Two polygons of one chamber are joined by a path of generic polygons inside that chamber
(the form in which clause (i) is consumed by clause (ii), d1_setup.tex:963–965). -/
theorem chamber_joinedIn (hP : Generic P) (hQ : Q ∈ chamber P) : JoinedIn (chamber P) P Q :=
  (isPathConnected_chamber hP).joinedIn P (mem_chamber_self hP) Q hQ

/-! ## The row bundle -/

/-- CV prop:chamberinv (i) (d1_setup.tex:932–937), clause by clause: "The generic locus `𝓤_n` is
open in `(ℝ²)^n`, and every chamber — every connected component of it — is open and path
connected." Chambers are `CV.chamber P = connectedComponentIn (genericLocus n) P` (CV:def:generic
(B), d1_setup.tex:229–231); path connectedness is asserted for the chambers of generic polygons
(the components of `𝓤_n`), the set `chamber P` being empty when `P` is not generic. -/
structure ChamberInvIData (n : ℕ) [NeZero n] : Prop where
  /-- "The generic locus `𝓤_n` is open in `(ℝ²)^n`" (d1_setup.tex:934–935). -/
  open_locus : IsOpen (genericLocus n)
  /-- "every chamber — every connected component of it — is open" (d1_setup.tex:935–936). -/
  chamber_open : ∀ P : LabelledTuple n, IsOpen (chamber P)
  /-- "and path connected" (d1_setup.tex:936). -/
  chamber_pathConnected : ∀ P : LabelledTuple n, Generic P → IsPathConnected (chamber P)

/-- Row 147, clause (i): CV prop:chamberinv (i) (d1_setup.tex:932–937). -/
theorem chamberinv_i : ChamberInvIData n where
  open_locus := isOpen_genericLocus
  chamber_open := isOpen_chamber
  chamber_pathConnected := fun _ hP => isPathConnected_chamber hP

/-- The same on the printed domain "Fix `n ≥ 3`" (d1_setup.tex:933), which supplies `NeZero n`. -/
theorem chamberinv_i_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    haveI : NeZero n := ⟨by omega⟩
    ChamberInvIData n :=
  haveI : NeZero n := ⟨by omega⟩
  chamberinv_i

end CV
