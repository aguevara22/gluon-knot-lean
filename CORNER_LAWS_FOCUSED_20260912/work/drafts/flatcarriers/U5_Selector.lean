import SM.FlatCarriersDefs

/-! # U5 — Selector (cor:flat-carriers (iii))

Prover unit U5 of work/drafts/flatcarriers/PLAN_FINAL.md §5, written 2026-09-13. Proves the three
selector fields of `SM.FlatCarriersData` (SM/FlatCarriersDefs.lean):

* `selector_def` — the printed definition "a carrier's selector is `1` if all its turns are right,
  `(-1)^c` if all its `c` turns are left, and `0` if its turns are mixed" (sm-3:824-826), as the
  three defining clauses of `cornerSelector`, and `geoCarrierSelector = cornerSelector ∘ geoCornerPolygon`;
* `selector_identity` — eq. flatpr:selector-identity `W_right − W_left = W_del` for the carrier
  through `μ_j`, by the exhaustive table flatpr:selector-table (sm-3:893-905):
  surviving turns mixed → `0 − 0 = 0`; all right → `1 − 0 = 1`; all left with `c` surviving corners
  → `0 − (−1)^{c+1} = (−1)^c`;
* `other_selectors_agree` — "All other corresponding carrier selectors agree" (sm-3:831-832): every
  other carrier "retain[s] all [its] corner signs and counts" (sm-3:906-907), so the side copy's
  selector is the deletion copy's.

Interface. The three lemmas take as explicit hypotheses (never `sorry`) the fields of
`FlatCarriersData` proved by the units U2 (carrier correspondences and corner-cycle identities:
`correspond_sides`, `others_unchanged`, `central_vs_deletion_through_mu_j`) and U3 (turn transport:
`same_turn_signs`, `extra_corner`), stated verbatim as the fields so that the assembly (U1) can pass
`hD.correspond_sides` etc. (checked by the `example`s at the end). Not needed: `correspond_deletion`
(the corner-cycle identities already carry the corner correspondence), `turns_nonzero` (the table is
exhaustive over `SignType`, a zero turn counting as "mixed"), `hF`, and any hypothesis on `n, g, j`
beyond those in the fields' statements.

Everything is sorry-free; `#print axioms` at the end: `propext, Classical.choice, Quot.sound`. -/

namespace SM

open Carrier GeoCarrier

/-! ## 0. `List.erase` on marks

Under the classical decidability instance the `BEq` instance elaborated for `Mark P = ZMod n ⊕ Visit P`
(the `.erase (Sum.inl j)` of the fields `identify_deletion_marks`, `central_vs_deletion_through_mu_j`)
is `Sum.instBEq`, for which the toolchain has no `LawfulBEq` instance; the `List.erase` lemmas
(`List.Nodup.mem_erase_iff`, `List.length_erase_of_mem`, …) need one. -/

/-- `Sum.instBEq` is lawful when both component instances are. -/
instance instLawfulBEqSum {α β : Type*} [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] :
    LawfulBEq (α ⊕ β) where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> simp only [BEq.beq] at h
    · rw [eq_of_beq h]
    · exact absurd h Bool.false_ne_true
    · exact absurd h Bool.false_ne_true
    · rw [eq_of_beq h]
  rfl {a} := by
    cases a <;> simp [BEq.beq, Sum.instBEq.beq]

noncomputable section

/-! ## 1. `cornerSelector`: the three defining clauses (sm-3:824-826) -/

section SelectorClauses

variable {k : ℕ} [NeZero k]

/-- "1 if all its turns are right" (`turn = -1`). -/
theorem cornerSelector_of_all_right (Q : LabelledTuple k) (h : ∀ i, turn Q i = -1) :
    cornerSelector Q = 1 := by
  unfold cornerSelector
  rw [ite_eq_left h]

/-- "(−1)^c if all its c turns are left" (`turn = +1`, `c = k`). -/
theorem cornerSelector_of_all_left (Q : LabelledTuple k) (h : ∀ i, turn Q i = 1) :
    cornerSelector Q = (-1 : ℤ) ^ k := by
  unfold cornerSelector
  have hnr : ¬ ∀ i, turn Q i = -1 := by
    intro hr
    have h0 := (hr 0).symm.trans (h 0)
    exact absurd h0 (by decide)
  rw [ite_eq_right hnr, ite_eq_left h]

/-- "0 if its turns are mixed". -/
theorem cornerSelector_of_mixed (Q : LabelledTuple k) (h1 : ¬ ∀ i, turn Q i = -1)
    (h2 : ¬ ∀ i, turn Q i = 1) : cornerSelector Q = 0 := by
  unfold cornerSelector
  rw [ite_eq_right h1, ite_eq_right h2]

/-- A carrier's selector is the selector of its corner polygon (by definition). -/
theorem geoCarrierSelector_eq_cornerSelector {n : ℕ} [NeZero n] {P : LabelledTuple n}
    (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    geoCarrierSelector hP S q = cornerSelector (geoCornerPolygon hP S q) := rfl

end SelectorClauses

/-! ## 2. Turn bookkeeping: the turns of a corner polygon are the `geoCornerTurn`s at its corner
marks (certificate `geoCornerMark_geoCornerIndex`) -/

section TurnBookkeeping

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P)
  (S : Finset (Crossing P))

theorem geoCornerMark_mem (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    geoCornerMark hP S q k ∈ geoComponentCornerList hP S q :=
  List.getElem_mem _

theorem geoOwner_geoCornerMark (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    geoOwner hP S (geoCornerMark hP S q k) = q :=
  ((mem_geoComponentCornerList hP S q _).mp (geoCornerMark_mem hP S q k)).1

theorem isTrueCorner_geoCornerMark (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    IsTrueCorner S (geoCornerMark hP S q k) :=
  ((mem_geoComponentCornerList hP S q _).mp (geoCornerMark_mem hP S q k)).2

/-- The corner marks of a carrier are distinct (the corner list is duplicate-free). -/
theorem geoCornerMark_injective (q : GeoComponent hP S) :
    Function.Injective (geoCornerMark hP S q) := by
  intro k k' hkk'
  apply ZMod.val_injective
  exact ((geoComponentCornerList_nodup hP S q).getElem_inj_iff).mp hkk'

/-- The turn of a carrier at a corner mark `a` is the turn of its corner polygon at any index whose
corner is `a`. -/
theorem geoCornerTurn_eq_turn {a : Mark P} (ha : IsTrueCorner S a) {q : GeoComponent hP S}
    (hq : geoOwner hP S a = q) (k : ZMod (geoCornerCount hP S q))
    (hk : geoCornerMark hP S q k = a) :
    geoCornerTurn hP S a = turn (geoCornerPolygon hP S q) k := by
  subst hq
  unfold geoCornerTurn
  congr 1
  apply geoCornerMark_injective
  rw [geoCornerMark_geoCornerIndex hP S ha, hk]

/-- Conversely, an owned corner mark is some corner of its carrier, where the polygon's turn is the
carrier's turn at that mark. -/
theorem exists_turn_eq_geoCornerTurn {a : Mark P} (ha : IsTrueCorner S a) {q : GeoComponent hP S}
    (hq : geoOwner hP S a = q) :
    ∃ k : ZMod (geoCornerCount hP S q),
      geoCornerMark hP S q k = a ∧ turn (geoCornerPolygon hP S q) k = geoCornerTurn hP S a := by
  subst hq
  exact ⟨geoCornerIndex hP S a, geoCornerMark_geoCornerIndex hP S ha, rfl⟩

/-- The turn of a corner polygon at the index `k` is the carrier's turn at its `k`-th corner mark. -/
theorem turn_geoCornerPolygon_eq_geoCornerTurn (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    turn (geoCornerPolygon hP S q) k = geoCornerTurn hP S (geoCornerMark hP S q k) :=
  (geoCornerTurn_eq_turn hP S (isTrueCorner_geoCornerMark hP S q k)
    (geoOwner_geoCornerMark hP S q k) k rfl).symm

end TurnBookkeeping

/-! ## 3. Selector congruence: two polygons with the same number of corners and the same set of
turn values have the same selector -/

section SelectorCongr

/-- The selector depends only on the corner count and on the set of turn values. -/
theorem cornerSelector_congr {k k' : ℕ} [NeZero k] [NeZero k'] (Q : LabelledTuple k)
    (Q' : LabelledTuple k') (hk : k = k')
    (h1 : ∀ i, ∃ i', turn Q i = turn Q' i') (h2 : ∀ i', ∃ i, turn Q' i' = turn Q i) :
    cornerSelector Q = cornerSelector Q' := by
  subst hk
  have hall : ∀ s : SignType, (∀ i, turn Q i = s) ↔ (∀ i', turn Q' i' = s) := by
    intro s
    constructor
    · intro h i'
      obtain ⟨i, hi⟩ := h2 i'
      rw [hi, h i]
    · intro h i
      obtain ⟨i', hi'⟩ := h1 i
      rw [hi', h i']
  by_cases hR : ∀ i, turn Q i = -1
  · rw [cornerSelector_of_all_right Q hR, cornerSelector_of_all_right Q' ((hall _).mp hR)]
  · have hR' : ¬ ∀ i', turn Q' i' = -1 := fun h => hR ((hall _).mpr h)
    by_cases hL : ∀ i, turn Q i = 1
    · rw [cornerSelector_of_all_left Q hL, cornerSelector_of_all_left Q' ((hall _).mp hL)]
    · have hL' : ¬ ∀ i', turn Q' i' = 1 := fun h => hL ((hall _).mpr h)
      rw [cornerSelector_of_mixed Q hR hL, cornerSelector_of_mixed Q' hR' hL']

end SelectorCongr

/-! ## 4. The exhaustive table flatpr:selector-table (sm-3:893-905), abstractly

`QD` is the deletion copy (`c` corners, the surviving turns), `QR` / `QL` the right / left side
copies (`c + 1` corners each): one extra corner `kR` / `kL` with turn `-1` (right) / `+1` (left),
and the other corners' turns are exactly the surviving turns (in both directions). -/

section SelectorTable

theorem selector_table {c cR cL : ℕ} [NeZero c] [NeZero cR] [NeZero cL]
    (QD : LabelledTuple c) (QR : LabelledTuple cR) (QL : LabelledTuple cL)
    (hcR : cR = c + 1) (hcL : cL = c + 1) (kR : ZMod cR) (kL : ZMod cL)
    (hR : turn QR kR = -1) (hL : turn QL kL = 1)
    (hRD : ∀ k, k ≠ kR → ∃ k', turn QR k = turn QD k')
    (hDR : ∀ k', ∃ k, k ≠ kR ∧ turn QD k' = turn QR k)
    (hLD : ∀ k, k ≠ kL → ∃ k', turn QL k = turn QD k')
    (hDL : ∀ k', ∃ k, k ≠ kL ∧ turn QD k' = turn QL k) :
    cornerSelector QR - cornerSelector QL = cornerSelector QD := by
  subst hcR
  subst hcL
  -- the two extra corners spoil "all left" on the right side and "all right" on the left side
  have hR_not_left : ¬ ∀ k, turn QR k = 1 := fun h => absurd ((h kR).symm.trans hR) (by decide)
  have hL_not_right : ¬ ∀ k, turn QL k = -1 := fun h => absurd ((h kL).symm.trans hL) (by decide)
  by_cases hAR : ∀ k', turn QD k' = -1
  · -- row "all right": 1 − 0 = 1
    have hQR : ∀ k, turn QR k = -1 := by
      intro k
      by_cases hk : k = kR
      · rw [hk, hR]
      · obtain ⟨k', hk'⟩ := hRD k hk
        rw [hk', hAR k']
    have hQL_not_left : ¬ ∀ k, turn QL k = 1 := by
      intro h
      obtain ⟨k, -, hk⟩ := hDL 0
      have := (hAR 0).symm.trans (hk.trans (h k))
      exact absurd this (by decide)
    rw [cornerSelector_of_all_right QD hAR, cornerSelector_of_all_right QR hQR,
      cornerSelector_of_mixed QL hL_not_right hQL_not_left]
    norm_num
  · by_cases hAL : ∀ k', turn QD k' = 1
    · -- row "all left": 0 − (−1)^{c+1} = (−1)^c
      have hQL : ∀ k, turn QL k = 1 := by
        intro k
        by_cases hk : k = kL
        · rw [hk, hL]
        · obtain ⟨k', hk'⟩ := hLD k hk
          rw [hk', hAL k']
      have hQR_not_right : ¬ ∀ k, turn QR k = -1 := by
        intro h
        obtain ⟨k, -, hk⟩ := hDR 0
        have := (hAL 0).symm.trans (hk.trans (h k))
        exact absurd this (by decide)
      rw [cornerSelector_of_all_left QD hAL, cornerSelector_of_all_left QL hQL,
        cornerSelector_of_mixed QR hQR_not_right hR_not_left]
      rw [pow_succ]
      ring
    · -- row "mixed": 0 − 0 = 0
      push Not at hAR hAL
      obtain ⟨kr, hkr⟩ := hAR
      obtain ⟨kl, hkl⟩ := hAL
      have hQR_not_right : ¬ ∀ k, turn QR k = -1 := by
        intro h
        obtain ⟨k, -, hk⟩ := hDR kr
        exact hkr (hk.trans (h k))
      have hQL_not_left : ¬ ∀ k, turn QL k = 1 := by
        intro h
        obtain ⟨k, -, hk⟩ := hDL kl
        exact hkl (hk.trans (h k))
      have hQD_mixed : cornerSelector QD = 0 :=
        cornerSelector_of_mixed QD (fun h => hkr (h kr)) (fun h => hkl (h kl))
      rw [hQD_mixed, cornerSelector_of_mixed QR hQR_not_right hR_not_left,
        cornerSelector_of_mixed QL hL_not_right hQL_not_left]
      norm_num

end SelectorTable


/-! ## 5. Corner correspondences between two carriers (abstract)

A turn-preserving bijection of the corner marks of two carriers (in configurations of possibly
different sizes) gives equal corner counts and equal selectors; a bijection off one distinguished
corner gives the count `c + 1` and the turn data of the table. -/

section CornerCorrespondence

attribute [local instance] Classical.propDecidable

variable {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂] {P₁ : LabelledTuple m₁} {P₂ : LabelledTuple m₂}
  (h₁ : CrossingGeometry P₁) (S₁ : Finset (Crossing P₁)) (q₁ : GeoComponent h₁ S₁)
  (h₂ : CrossingGeometry P₂) (S₂ : Finset (Crossing P₂)) (q₂ : GeoComponent h₂ S₂)
  (f : Mark P₁ → Mark P₂) (g : Mark P₂ → Mark P₁)

/-- "All other carriers retain all their … counts": a bijection of corner marks gives equal corner
counts. -/
theorem geoCornerCount_eq_of_corner_bijection
    (hf : ∀ a ∈ geoComponentCornerList h₁ S₁ q₁,
      f a ∈ geoComponentCornerList h₂ S₂ q₂ ∧ g (f a) = a)
    (hg : ∀ b ∈ geoComponentCornerList h₂ S₂ q₂,
      g b ∈ geoComponentCornerList h₁ S₁ q₁ ∧ f (g b) = b) :
    geoCornerCount h₁ S₁ q₁ = geoCornerCount h₂ S₂ q₂ := by
  unfold geoCornerCount
  have hperm : ((geoComponentCornerList h₁ S₁ q₁).map f).Perm (geoComponentCornerList h₂ S₂ q₂) := by
    rw [List.perm_ext_iff_of_nodup ((geoComponentCornerList_nodup h₁ S₁ q₁).map_on ?_)
      (geoComponentCornerList_nodup h₂ S₂ q₂)]
    · intro b
      rw [List.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact (hf a ha).1
      · intro hb
        exact ⟨g b, (hg b hb).1, (hg b hb).2⟩
    · intro a ha a' ha' hfa
      rw [← (hf a ha).2, ← (hf a' ha').2, hfa]
  rw [← hperm.length_eq, List.length_map]

/-- "All other carriers retain all their corner signs and counts": a turn-preserving bijection of
corner marks gives equal selectors. -/
theorem geoCarrierSelector_eq_of_corner_bijection
    (hf : ∀ a ∈ geoComponentCornerList h₁ S₁ q₁,
      f a ∈ geoComponentCornerList h₂ S₂ q₂ ∧ g (f a) = a)
    (hg : ∀ b ∈ geoComponentCornerList h₂ S₂ q₂,
      g b ∈ geoComponentCornerList h₁ S₁ q₁ ∧ f (g b) = b)
    (hturn : ∀ a ∈ geoComponentCornerList h₁ S₁ q₁,
      geoCornerTurn h₁ S₁ a = geoCornerTurn h₂ S₂ (f a)) :
    geoCarrierSelector h₁ S₁ q₁ = geoCarrierSelector h₂ S₂ q₂ := by
  rw [geoCarrierSelector_eq_cornerSelector, geoCarrierSelector_eq_cornerSelector]
  apply cornerSelector_congr _ _ (geoCornerCount_eq_of_corner_bijection h₁ S₁ q₁ h₂ S₂ q₂ f g hf hg)
  · intro k
    have ha := geoCornerMark_mem h₁ S₁ q₁ k
    obtain ⟨hfa, -⟩ := hf _ ha
    obtain ⟨hown, hcor⟩ := (mem_geoComponentCornerList h₂ S₂ q₂ _).mp hfa
    obtain ⟨k', -, hk'⟩ := exists_turn_eq_geoCornerTurn h₂ S₂ hcor hown
    refine ⟨k', ?_⟩
    rw [hk', turn_geoCornerPolygon_eq_geoCornerTurn, hturn _ ha]
  · intro k'
    have hb := geoCornerMark_mem h₂ S₂ q₂ k'
    obtain ⟨hgb, hfgb⟩ := hg _ hb
    obtain ⟨hown, hcor⟩ := (mem_geoComponentCornerList h₁ S₁ q₁ _).mp hgb
    obtain ⟨k, -, hk⟩ := exists_turn_eq_geoCornerTurn h₁ S₁ hcor hown
    refine ⟨k, ?_⟩
    rw [hk, turn_geoCornerPolygon_eq_geoCornerTurn, hturn _ hgb, hfgb]

/-- The distinguished carrier: its corners other than one distinguished corner `a₀` correspond
bijectively, with the same turns, to the corners of a second carrier. Then it has `c + 1` corners
(`c` the second carrier's count), `a₀` is its corner `k₀`, and its turns away from `k₀` are exactly
the second carrier's turns (in both directions) — the hypotheses of `selector_table`. -/
theorem corner_data_of_extra_corner (a₀ : Mark P₁) (ha₀ : a₀ ∈ geoComponentCornerList h₁ S₁ q₁)
    (hf : ∀ a ∈ geoComponentCornerList h₁ S₁ q₁, a ≠ a₀ →
      f a ∈ geoComponentCornerList h₂ S₂ q₂ ∧ g (f a) = a)
    (hg : ∀ b ∈ geoComponentCornerList h₂ S₂ q₂,
      g b ∈ geoComponentCornerList h₁ S₁ q₁ ∧ g b ≠ a₀ ∧ f (g b) = b)
    (hturn : ∀ a ∈ geoComponentCornerList h₁ S₁ q₁, a ≠ a₀ →
      geoCornerTurn h₁ S₁ a = geoCornerTurn h₂ S₂ (f a)) :
    geoCornerCount h₁ S₁ q₁ = geoCornerCount h₂ S₂ q₂ + 1 ∧
    ∃ k₀ : ZMod (geoCornerCount h₁ S₁ q₁), geoCornerMark h₁ S₁ q₁ k₀ = a₀ ∧
      (∀ k, k ≠ k₀ → ∃ k',
        turn (geoCornerPolygon h₁ S₁ q₁) k = turn (geoCornerPolygon h₂ S₂ q₂) k') ∧
      (∀ k', ∃ k, k ≠ k₀ ∧
        turn (geoCornerPolygon h₂ S₂ q₂) k' = turn (geoCornerPolygon h₁ S₁ q₁) k) := by
  have hnd₁ := geoComponentCornerList_nodup h₁ S₁ q₁
  refine ⟨?_, ?_⟩
  · unfold geoCornerCount
    have hperm : (((geoComponentCornerList h₁ S₁ q₁).erase a₀).map f).Perm
        (geoComponentCornerList h₂ S₂ q₂) := by
      rw [List.perm_ext_iff_of_nodup ((hnd₁.erase a₀).map_on ?_)
        (geoComponentCornerList_nodup h₂ S₂ q₂)]
      · intro b
        rw [List.mem_map]
        constructor
        · rintro ⟨a, ha, rfl⟩
          rw [hnd₁.mem_erase_iff] at ha
          exact (hf a ha.2 ha.1).1
        · intro hb
          obtain ⟨hgb, hne, hfgb⟩ := hg b hb
          exact ⟨g b, hnd₁.mem_erase_iff.mpr ⟨hne, hgb⟩, hfgb⟩
      · intro a ha a' ha' hfa
        rw [hnd₁.mem_erase_iff] at ha ha'
        rw [← (hf a ha.2 ha.1).2, ← (hf a' ha'.2 ha'.1).2, hfa]
    rw [← hperm.length_eq, List.length_map, List.length_erase_of_mem ha₀]
    have := List.length_pos_of_mem ha₀
    omega
  · obtain ⟨hown, hcor⟩ := (mem_geoComponentCornerList h₁ S₁ q₁ a₀).mp ha₀
    obtain ⟨k₀, hk₀, -⟩ := exists_turn_eq_geoCornerTurn h₁ S₁ hcor hown
    refine ⟨k₀, hk₀, ?_, ?_⟩
    · intro k hk
      have ha := geoCornerMark_mem h₁ S₁ q₁ k
      have hne : geoCornerMark h₁ S₁ q₁ k ≠ a₀ := fun h =>
        hk (geoCornerMark_injective h₁ S₁ q₁ (h.trans hk₀.symm))
      obtain ⟨hfa, -⟩ := hf _ ha hne
      obtain ⟨hown', hcor'⟩ := (mem_geoComponentCornerList h₂ S₂ q₂ _).mp hfa
      obtain ⟨k', -, hk'⟩ := exists_turn_eq_geoCornerTurn h₂ S₂ hcor' hown'
      refine ⟨k', ?_⟩
      rw [hk', turn_geoCornerPolygon_eq_geoCornerTurn, hturn _ ha hne]
    · intro k'
      have hb := geoCornerMark_mem h₂ S₂ q₂ k'
      obtain ⟨hgb, hne, hfgb⟩ := hg _ hb
      obtain ⟨hown', hcor'⟩ := (mem_geoComponentCornerList h₁ S₁ q₁ _).mp hgb
      obtain ⟨k, hk, hkt⟩ := exists_turn_eq_geoCornerTurn h₁ S₁ hcor' hown'
      refine ⟨k, ?_, ?_⟩
      · intro hkk₀
        apply hne
        rw [← hk, hkk₀, hk₀]
      · rw [hkt, turn_geoCornerPolygon_eq_geoCornerTurn, hturn _ hgb hne, hfgb]

end CornerCorrespondence

/-! ## 6. The flat configurations: `IsTrueCorner` under the side identification -/

section FlatTransport

attribute [local instance] Classical.propDecidable

/-- `markTransport` fixes vertices (definitionally). -/
theorem markTransport_inl {m : ℕ} {P Q : LabelledTuple m}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (i : ZMod m) :
    markTransport hs (Sum.inl i) = Sum.inl i := rfl

/-- A mark is a corner (an original vertex or a selected visit) iff its transport to a polygon
with the same crossing supports is, for the transported support. -/
theorem isTrueCorner_markTransport {m : ℕ} [NeZero m] {P Q : LabelledTuple m}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (S : Finset (Crossing P)) (a : Mark P) :
    IsTrueCorner (transportSupport hs S) (markTransport hs a) ↔ IsTrueCorner S a := by
  cases a with
  | inl i => exact Iff.rfl
  | inr v =>
    change (visitTransport hs v).1 ∈ transportSupport hs S ↔ v.1 ∈ S
    rw [visitTransport_crossing]
    exact Finset.mem_map' _

end FlatTransport

/-! ## 7. The three selector fields of cor:flat-carriers (iii) -/

section FlatSelector

attribute [local instance] Classical.propDecidable

/-- Field `selector_def`: the three defining clauses of `cornerSelector` (sm-3:824-826) and
`geoCarrierSelector = cornerSelector ∘ geoCornerPolygon`. -/
theorem selector_def :
    (∀ {m : ℕ} [NeZero m] (Q : LabelledTuple m),
      ((∀ i, turn Q i = -1) → cornerSelector Q = 1) ∧
      ((∀ i, turn Q i = 1) → cornerSelector Q = (-1 : ℤ) ^ m) ∧
      (¬ (∀ i, turn Q i = -1) → ¬ (∀ i, turn Q i = 1) → cornerSelector Q = 0)) ∧
    (∀ {m : ℕ} [NeZero m] {P : LabelledTuple m} (hP : CrossingGeometry P)
      (S' : Finset (Crossing P)) (q : GeoComponent hP S'),
      geoCarrierSelector hP S' q = cornerSelector (geoCornerPolygon hP S' q)) := by
  refine ⟨?_, ?_⟩
  · intro m _ Q
    exact ⟨cornerSelector_of_all_right Q, cornerSelector_of_all_left Q, cornerSelector_of_mixed Q⟩
  · intro m _ P hP S' q
    rfl

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
  (hz : g.pointZeros = {turnSupport j})
  (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
  (hc : g.concurrences = ∅) (t : g.SideParameter) (hs : CommonSupports g t)
  (S : Finset (Crossing g.center))

omit [NeZero n] in
/-- Side copies: a centre mark is a corner of the centre carrier of `a₀` iff its transport is a
corner of the side copy (owner-iff of `correspond_sides` + `isTrueCorner_markTransport`). -/
theorem markTransport_mem_geoComponentCornerList_iff (b : Bool)
    (howner : ∀ a a' : Mark g.center,
      geoOwner (flatCentreCG hn g j hz hb hc) S a = geoOwner (flatCentreCG hn g j hz hb hc) S a' ↔
        geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
          geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a'))
    (a₀ a : Mark g.center) :
    markTransport (hs b) a ∈ geoComponentCornerList (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a₀)) ↔
      a ∈ geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S a₀) := by
  rw [mem_geoComponentCornerList, mem_geoComponentCornerList, ← howner a a₀,
    isTrueCorner_markTransport]

/-- Field `other_selectors_agree` ("All other corresponding carrier selectors agree"): for a carrier
not through `μ_j`, the side copy's selector is the deletion copy's. Hypotheses: the fields
`correspond_sides` (U2), `others_unchanged` (U2.5: the deletion copy's corner cycle is the centre
carrier's), `same_turn_signs` (U3.4), stated verbatim. Proof: the corner marks of the side copy and
of the deletion copy correspond bijectively through the centre (`delMark ∘ markTransport⁻¹` and
`markTransport ∘ fusionMark`), all away from `μ_j`, with equal turns; then
`geoCarrierSelector_eq_of_corner_bijection` ("retain all their corner signs and counts"). -/
theorem other_selectors_agree
    (correspond_sides : ∀ b : Bool,
      (∀ a : Mark g.center,
        geoSmoothingSuccessor (flatSideCG hn g b t) (transportSupport (hs b) S)
            (markTransport (hs b) a) =
          markTransport (hs b) (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a)) ∧
      (∀ a a' : Mark g.center,
        geoOwner (flatCentreCG hn g j hz hb hc) S a = geoOwner (flatCentreCG hn g j hz hb hc) S a' ↔
          geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
            geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a')))
    (others_unchanged : ∀ b : Mark (deleteVertex g.center j),
      geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) ≠
        centralCarrierThroughJ hn g j hz hb hc S →
      (((geoComponentMarkList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
            (fusionMark hn g j hz hb hc) : List (Mark g.center)) : Cycle (Mark g.center)) =
        (geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
          (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) :
            Cycle (Mark g.center)) ∧
      (((geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
            (fusionMark hn g j hz hb hc) : List (Mark g.center)) : Cycle (Mark g.center)) =
        (geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
          (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) :
            Cycle (Mark g.center)) ∧
      geoComponentPlaneCycle (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b) =
        geoComponentPlaneCycle (flatCentreCG hn g j hz hb hc) S
          (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)))
    (same_turn_signs : ∀ a : Mark g.center, a ≠ Sum.inl j → IsTrueCorner S a → ∀ b : Bool,
      geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
        geoCornerTurn (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (delMark hn g j hz hb hc a)) :
    ∀ (b : Bool) (b' : Mark (deleteVertex g.center j)),
      geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b') ≠
        centralCarrierThroughJ hn g j hz hb hc S →
      geoCarrierSelector (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S)
          (markTransport (hs b) (fusionMark hn g j hz hb hc b'))) =
      geoCarrierSelector (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b') := by
  intro b b' hne
  -- U2.5: the deletion copy's corner cycle, read at the centre, is the centre carrier's
  have hrot : ((geoComponentCornerList (flatDeletionCG hn g j hz hb hc)
      (deletionSupport hn g j hz hb hc S)
      (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b')).map
        (fusionMark hn g j hz hb hc)) ~r
      geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b')) :=
    Cycle.coe_eq_coe.mp (others_unchanged b' hne).2.1
  -- no corner of this centre carrier is `μ_j` (it is not the carrier through `μ_j`)
  have hmemC : ∀ a : Mark g.center,
      a ∈ geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b')) →
      a ≠ Sum.inl j := by
    intro a ha haj
    subst haj
    exact hne ((mem_geoComponentCornerList _ _ _ _).mp ha).1.symm
  -- a side corner mark, read at the centre, is a corner of the centre carrier
  have hside : ∀ m : Mark (g.sideTuple b t).val,
      m ∈ geoComponentCornerList (flatSideCG hn g b t) (transportSupport (hs b) S)
        (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S)
          (markTransport (hs b) (fusionMark hn g j hz hb hc b'))) →
      (markTransport (hs b)).symm m ∈ geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b')) := by
    intro m hm
    have h := markTransport_mem_geoComponentCornerList_iff hn g j hz hb hc t hs S b
      (correspond_sides b).2 (fusionMark hn g j hz hb hc b') ((markTransport (hs b)).symm m)
    rw [Equiv.apply_symm_apply] at h
    exact h.mp hm
  apply geoCarrierSelector_eq_of_corner_bijection _ _ _ _ _ _
    (fun m => delMark hn g j hz hb hc ((markTransport (hs b)).symm m))
    (fun b'' => markTransport (hs b) (fusionMark hn g j hz hb hc b''))
  · intro m hm
    have hm' := hside m hm
    have hne' := hmemC _ hm'
    obtain ⟨b'', hb'', hfb''⟩ := List.mem_map.mp (hrot.mem_iff.mpr hm')
    refine ⟨?_, ?_⟩
    · rw [← hfb'', delMark_fusionMark]
      exact hb''
    · rw [fusionMark_delMark hn g j hz hb hc _ hne', Equiv.apply_symm_apply]
  · intro b'' hb''
    have hC : fusionMark hn g j hz hb hc b'' ∈ geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b')) :=
      hrot.mem_iff.mp (List.mem_map.mpr ⟨b'', hb'', rfl⟩)
    refine ⟨?_, ?_⟩
    · exact (markTransport_mem_geoComponentCornerList_iff hn g j hz hb hc t hs S b
        (correspond_sides b).2 _ _).mpr hC
    · rw [Equiv.symm_apply_apply, delMark_fusionMark]
  · intro m hm
    have hm' := hside m hm
    have hne' := hmemC _ hm'
    have hcor : IsTrueCorner S ((markTransport (hs b)).symm m) :=
      ((mem_geoComponentCornerList _ _ _ _).mp hm').2
    have h := same_turn_signs _ hne' hcor b
    rwa [Equiv.apply_symm_apply] at h

/-- Field `selector_identity` (eq. flatpr:selector-identity, `W_right − W_left = W_del` for the
carrier through `μ_j`). Hypotheses: the fields `correspond_sides` (U2),
`central_vs_deletion_through_mu_j` (U2.5: the centre carrier's corner cycle with `μ_j` erased is the
deletion copy's), `same_turn_signs` and `extra_corner` (U3.4), stated verbatim. Proof: on each side
the corners other than `μ_j` correspond bijectively, with equal turns, to the deletion copy's
corners (`corner_data_of_extra_corner`, so each side copy has `c + 1` corners, `c` the deletion
copy's count), the extra corner turning right (`-1`) on the right side and left (`+1`) on the left
side; then the exhaustive table `selector_table` (sm-3:893-905). -/
theorem selector_identity
    (correspond_sides : ∀ b : Bool,
      (∀ a : Mark g.center,
        geoSmoothingSuccessor (flatSideCG hn g b t) (transportSupport (hs b) S)
            (markTransport (hs b) a) =
          markTransport (hs b) (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a)) ∧
      (∀ a a' : Mark g.center,
        geoOwner (flatCentreCG hn g j hz hb hc) S a = geoOwner (flatCentreCG hn g j hz hb hc) S a' ↔
          geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
            geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a')))
    (central_vs_deletion_through_mu_j :
      geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j) ≠ Sum.inl j ∧
      ((((geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
          (centralCarrierThroughJ hn g j hz hb hc S)).erase (Sum.inl j)).map
            (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
              Cycle (Mark (deleteVertex g.center j))) =
        (geoComponentMarkList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (deletionCopyThroughJ hn g j hz hb hc S) : Cycle (Mark (deleteVertex g.center j))) ∧
      ((((geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
          (centralCarrierThroughJ hn g j hz hb hc S)).erase (Sum.inl j)).map
            (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
              Cycle (Mark (deleteVertex g.center j))) =
        (geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (deletionCopyThroughJ hn g j hz hb hc S) : Cycle (Mark (deleteVertex g.center j))) ∧
      StrictBetween
        (traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
          ((geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j))))
        (g.center j)
        (traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
          (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)))) ∧
      (∃ r s : ℝ, 0 < r ∧ 0 < s ∧
        g.center j - traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
          ((geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j))) =
          r • edge (deleteVertex g.center j) (-1) ∧
        traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
          (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j))) - g.center j =
          s • edge (deleteVertex g.center j) (-1)))
    (same_turn_signs : ∀ a : Mark g.center, a ≠ Sum.inl j → IsTrueCorner S a → ∀ b : Bool,
      geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (markTransport (hs b) a) =
        geoCornerTurn (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (delMark hn g j hz hb hc a))
    (extra_corner : ∀ b : Bool,
      geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) =
        turn (g.sideTuple b t).val j ∧
      (IsRightSide g j b t →
        geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) = -1) ∧
      (IsLeftSide g j b t →
        geoCornerTurn (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j) = 1)) :
    ∀ bR bL : Bool, IsRightSide g j bR t → IsLeftSide g j bL t →
      geoCarrierSelector (flatSideCG hn g bR t) (transportSupport (hs bR) S)
          (geoOwner (flatSideCG hn g bR t) (transportSupport (hs bR) S) (Sum.inl j)) -
        geoCarrierSelector (flatSideCG hn g bL t) (transportSupport (hs bL) S)
          (geoOwner (flatSideCG hn g bL t) (transportSupport (hs bL) S) (Sum.inl j)) =
      geoCarrierSelector (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) := by
  intro bR bL hR hL
  -- U2.5: the centre carrier's corner cycle with `μ_j` erased is the deletion copy's
  have hrot : (((geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
      (centralCarrierThroughJ hn g j hz hb hc S)).erase (Sum.inl j)).map
        (delMark hn g j hz hb hc)) ~r
      geoComponentCornerList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) :=
    Cycle.coe_eq_coe.mp central_vs_deletion_through_mu_j.2.2.1
  have hndC := geoComponentCornerList_nodup (flatCentreCG hn g j hz hb hc) S
    (centralCarrierThroughJ hn g j hz hb hc S)
  -- per side: corner count `c + 1`, and the turns away from the corner `μ_j` are the deletion's
  have side : ∀ b : Bool,
      geoCornerCount (flatSideCG hn g b t) (transportSupport (hs b) S)
          (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j)) =
        geoCornerCount (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (deletionCopyThroughJ hn g j hz hb hc S) + 1 ∧
      ∃ k₀, geoCornerMark (flatSideCG hn g b t) (transportSupport (hs b) S)
          (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j)) k₀ = Sum.inl j ∧
        (∀ k, k ≠ k₀ → ∃ k',
          turn (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
            (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j))) k =
          turn (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
            (deletionCopyThroughJ hn g j hz hb hc S)) k') ∧
        (∀ k', ∃ k, k ≠ k₀ ∧
          turn (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
            (deletionCopyThroughJ hn g j hz hb hc S)) k' =
          turn (geoCornerPolygon (flatSideCG hn g b t) (transportSupport (hs b) S)
            (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j))) k) := by
    intro b
    -- a side corner mark, read at the centre, is a corner of the central carrier through `μ_j`
    have hside : ∀ m : Mark (g.sideTuple b t).val,
        m ∈ geoComponentCornerList (flatSideCG hn g b t) (transportSupport (hs b) S)
          (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j)) →
        (markTransport (hs b)).symm m ∈ geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
          (centralCarrierThroughJ hn g j hz hb hc S) := by
      intro m hm
      have h := markTransport_mem_geoComponentCornerList_iff hn g j hz hb hc t hs S b
        (correspond_sides b).2 (Sum.inl j) ((markTransport (hs b)).symm m)
      rw [Equiv.apply_symm_apply] at h
      exact h.mp hm
    have hsideC : ∀ a : Mark g.center,
        a ∈ geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
          (centralCarrierThroughJ hn g j hz hb hc S) →
        markTransport (hs b) a ∈ geoComponentCornerList (flatSideCG hn g b t)
          (transportSupport (hs b) S)
          (geoOwner (flatSideCG hn g b t) (transportSupport (hs b) S) (Sum.inl j)) := by
      intro a ha
      exact (markTransport_mem_geoComponentCornerList_iff hn g j hz hb hc t hs S b
        (correspond_sides b).2 (Sum.inl j) a).mpr ha
    apply corner_data_of_extra_corner _ _ _ _ _ _
      (fun m => delMark hn g j hz hb hc ((markTransport (hs b)).symm m))
      (fun b'' => markTransport (hs b) (fusionMark hn g j hz hb hc b'')) (Sum.inl j)
    · exact (mem_geoComponentCornerList _ _ _ _).mpr ⟨rfl, isTrueCorner_vertex _ j⟩
    · intro m hm hmj
      have hm' := hside m hm
      have hne' : (markTransport (hs b)).symm m ≠ Sum.inl j := by
        intro h
        apply hmj
        rw [← Equiv.apply_symm_apply (markTransport (hs b)) m, h]
        rfl
      have hmem : (markTransport (hs b)).symm m ∈
          (geoComponentCornerList (flatCentreCG hn g j hz hb hc) S
            (centralCarrierThroughJ hn g j hz hb hc S)).erase (Sum.inl j) :=
        hndC.mem_erase_iff.mpr ⟨hne', hm'⟩
      refine ⟨hrot.mem_iff.mp (List.mem_map.mpr ⟨_, hmem, rfl⟩), ?_⟩
      rw [fusionMark_delMark hn g j hz hb hc _ hne', Equiv.apply_symm_apply]
    · intro b'' hb''
      obtain ⟨a, ha, hab⟩ := List.mem_map.mp (hrot.mem_iff.mpr hb'')
      rw [hndC.mem_erase_iff] at ha
      obtain ⟨haj, haC⟩ := ha
      have hfa : fusionMark hn g j hz hb hc b'' = a := by
        rw [← hab, fusionMark_delMark hn g j hz hb hc a haj]
      refine ⟨?_, ?_, ?_⟩
      · rw [hfa]
        exact hsideC a haC
      · rw [hfa]
        intro h
        exact haj ((markTransport (hs b)).injective (a₁ := a) (a₂ := Sum.inl j) h)
      · rw [hfa, Equiv.symm_apply_apply, hab]
    · intro m hm hmj
      have hm' := hside m hm
      have hne' : (markTransport (hs b)).symm m ≠ Sum.inl j := by
        intro h
        apply hmj
        rw [← Equiv.apply_symm_apply (markTransport (hs b)) m, h]
        rfl
      have hcor : IsTrueCorner S ((markTransport (hs b)).symm m) :=
        ((mem_geoComponentCornerList _ _ _ _).mp hm').2
      have h := same_turn_signs _ hne' hcor b
      rwa [Equiv.apply_symm_apply] at h
  obtain ⟨hcR, kR, hkR, hRD, hDR⟩ := side bR
  obtain ⟨hcL, kL, hkL, hLD, hDL⟩ := side bL
  rw [geoCarrierSelector_eq_cornerSelector, geoCarrierSelector_eq_cornerSelector,
    geoCarrierSelector_eq_cornerSelector]
  refine selector_table _ _ _ hcR hcL kR kL ?_ ?_ hRD hDR hLD hDL
  · rw [turn_geoCornerPolygon_eq_geoCornerTurn, hkR]
    exact (extra_corner bR).2.1 hR
  · rw [turn_geoCornerPolygon_eq_geoCornerTurn, hkL]
    exact (extra_corner bL).2.2 hL

/-! ### Interface check: the hypotheses are the fields of `FlatCarriersData`, verbatim -/

example (hD : FlatCarriersData hn g j hz hb hc t hs S) :=
  other_selectors_agree hn g j hz hb hc t hs S hD.correspond_sides hD.others_unchanged
    hD.same_turn_signs

example (hD : FlatCarriersData hn g j hz hb hc t hs S) :=
  selector_identity hn g j hz hb hc t hs S hD.correspond_sides
    hD.central_vs_deletion_through_mu_j hD.same_turn_signs hD.extra_corner

end FlatSelector

end
end SM

#print axioms SM.selector_def
#print axioms SM.selector_identity
#print axioms SM.other_selectors_agree
#print axioms SM.instLawfulBEqSum
