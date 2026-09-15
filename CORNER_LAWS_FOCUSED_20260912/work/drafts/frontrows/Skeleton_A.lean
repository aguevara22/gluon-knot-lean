import SM.FrontRealizeGeometry
import SM.FrontRealizeDeform
import SM.FrontRealizeBase
import SM.FrontWordsBase
import SM.FrontGeomModel

/-! # Skeleton_A — proof plan of the eight front certificate rows (rows 76-83), leaves sorried

Architect A (maximal reuse), 2026-09-14.  The definitions and the eight bundles are byte-identical to
`Statements_A.lean`; every `sorry` below is a LEAF of the plan (PLAN_A.md §4 lists them by unit with the
accepted declarations each one consumes).  All glue is proved; the eight row theorems are assembled from the
leaves at the end of the file.

Units (PLAN_A.md §5): T-pl block placements (proved here), T-cnt letter-traced counts, T-deg degrees in `a`,
T-rec the record of a realization (RecordIso builders), T-arc block arcs / MoveMatch (inside the site leaves),
U76 (PL deformation invariance, commutation, 76b representation), U77 (curl vs zigzag RI), U78 (four RII
sites), U79 (RIII site), U80 (zigzag record, two crossed-cusp RI sites), U81 (circle record with a free
component, base), U82 (four smoothing sites + switch record), U83 (assembly, proved here).

Checked with `cd work/lean && lake env lean` on this file. -/

namespace SM

open SM.Link SM.FrontWord SM.FrontRealize

noncomputable section

/-! ## 0. Definitions and bundles (byte-identical to Statements_A.lean) -/

namespace PLFront

/-- A deformation of PL fronts "through fronts without a singular event" (ng:commutation, sm-3:1922-1923),
in the PL reading: a generic deformation of the two diagrams (the accepted `DeformData`: a continuous path of
vertex tuples, every intermediate polygon generic with literally the same crossing pairs — no crossing is
created, destroyed or has its strands exchanged) all of whose intermediate polygons are nonvertical.  In the PL
class a cusp is an x-reversal vertex; the x-sign of an edge cannot change along a continuous path without
passing through a vertical edge, so no cusp is born, dies or changes side, and "signs, cusp directions and
cyclic attachments cannot change" (sm-3:1934-1936) is the content of the invariance clause. -/
structure DeformData (F F' : PLFront) extends SM.Link.DeformData F.diagram F'.diagram where
  /-- every intermediate polygon is nonvertical (no vertical tangency: no cusp event) -/
  nonvertical : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s : F.Γ.Strand,
    ((F.Γ.withVertices (γ t)).dir s).1 ≠ 0

/-- `F'` is obtained from `F` by a deformation through PL fronts without a singular event. -/
def Deform (F F' : PLFront) : Prop := Nonempty (DeformData F F')

end PLFront

/-- **ng:commutation** (sm-3:1921-1925), one field per printed clause.  "Disjoint-gadget commutations and
deformations through fronts without a singular event preserve D, w, d, and hence B.  Every supplied finite
front can be represented by a finite elementary front word."  Reading: FR-5 (module docstring); a
disjoint-gadget commutation is `IsComm` (the two-strand index shift of sm-3:1929-1931 is in its definition);
a deformation without singular event is `PLFront.Deform`; `d(F) = deg_a P_{S(F)}` on the identity rounding. -/
structure NgCommutationData : Prop where
  /-- "Disjoint-gadget commutations ... preserve D, w, d": for closed oriented words `W`, `W'` related by a
  disjoint-gadget commutation, the fronts `realize W`, `realize W'` have the same `D`, `w` and `d`. -/
  commutation : ∀ W W' : OWord, IsComm W.letters W'.letters →
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe ∧
      degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  /-- "... and hence B" (commutations): `B(realize W) = B(realize W')`. -/
  commutation_B : ∀ W W' : OWord, IsComm W.letters W'.letters →
    (realize W).defect = (realize W').defect
  /-- "deformations through fronts without a singular event preserve D, w, d": for PL fronts `F`, `F'`
  joined by a deformation through nonvertical generic polygons, `D`, `w` and `d` agree. -/
  deformation : ∀ F F' : PLFront, PLFront.Deform F F' →
    F.downCount = F'.downCount ∧ F.writhe = F'.writhe ∧ degAZ (P F.diagram) = degAZ (P F'.diagram)
  /-- "... and hence B" (deformations): `B(F) = B(F')`. -/
  deformation_B : ∀ F F' : PLFront, PLFront.Deform F F' → F.defect = F'.defect
  /-- "Every supplied finite front can be represented by a finite elementary front word." (sm-3:1924-1925):
  every front `F` of Definition ng:front-domain (the smooth class, row 73) is represented by a closed oriented
  word `W` — the front `realize W` has the same `s`, `D`, `w`, and its diagram carries the named record of every
  rounding `S(F)` of `F` (so `P_{S(F)} = P_{realize W}` by rp:record-polynomial, and `d`, `B` agree).  This is
  the block's single analytic bridge (FINAL §3, §8 risk 1: unit 76b, attacked last). -/
  representation : ∀ F : SmoothFront, ∃ W : OWord,
    F.sCount = (realize W).sCount ∧ F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧
      ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record)

/-- **ng:front-I** (sm-3:1950-1952): "The front type-I moves preserve B."  The type-I move is the deletion of
the curl `l_m σ_{m−1} r_m` or `l_m σ_{m+1} r_m` on one through-strand (`IsTypeI W W'`, `W` the side with the
curl; FR-6: deletion direction, as the word procedure uses it).  Display ng:type-I-counts (`Δw = 1`, `ΔD = 1`,
`Δd = 0` in the direction creating the curl) is proof content: companion lemmas of the skeleton. -/
structure NgFrontIData : Prop where
  /-- "The front type-I moves preserve B." -/
  typeI_B : ∀ W W' : OWord, IsTypeI W.letters W'.letters → (realize W).defect = (realize W').defect

/-- **ng:front-II** (sm-3:1972-1974): "The front type-II moves preserve D, w, d, and hence B."  The type-II
move replaces `l_{m−1} σ_m σ_{m−1}` or `l_{m+1} σ_m σ_{m+1}` by `l_m` (and, "for right-cusp versions, follow
these same local strands backwards", sm-3:1988-1989: `σ_{m−1} σ_m r_{m−1}`, `σ_{m+1} σ_m r_{m+1}` by `r_m`);
`IsTypeII W W'`, `W` the side with the two crossings. -/
structure NgFrontIIData : Prop where
  /-- "The front type-II moves preserve D, w, d" -/
  typeII : ∀ W W' : OWord, IsTypeII W.letters W'.letters →
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe ∧
      degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  /-- "... and hence B." -/
  typeII_B : ∀ W W' : OWord, IsTypeII W.letters W'.letters → (realize W).defect = (realize W').defect

/-- **ng:front-III** (sm-3:1990-1992): "The front type-III moves preserve D, w, d, and hence B."  The type-III
move is `σ_{m+1} σ_m σ_{m+1} ↔ σ_m σ_{m+1} σ_m` (`IsTypeIII`, either direction). -/
structure NgFrontIIIData : Prop where
  /-- "The front type-III moves preserve D, w, d" -/
  typeIII : ∀ W W' : OWord, IsTypeIII W.letters W'.letters →
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe ∧
      degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  /-- "... and hence B." -/
  typeIII_B : ∀ W W' : OWord, IsTypeIII W.letters W'.letters → (realize W).defect = (realize W').defect

/-- **ng:deletions** (sm-3:2008-2011): "Deleting an empty zigzag lowers s by two and cannot increase B;
applying the crossed-cusp shortcut lowers s by one and cannot increase B."  The empty zigzag is
`l_m r_{m+1}` or `l_{m+1} r_m` deleted (`IsZigzagDeletion W W'`); the crossed-cusp shortcut replaces
`l_i σ_i` by the uncrossed cusp `l_i` with flipped direction bit ("the boundary arms exchange places",
sm-3:2031-2032) and `σ_i r_i` by `r_i` (`IsCrossedCuspShortcut W W'`).  The displays ng:zigzag-counts and
ng:crossed-cusp-counts are proof content (companion lemmas). -/
structure NgDeletionsData : Prop where
  /-- "Deleting an empty zigzag lowers s by two" -/
  zigzag_s : ∀ W W' : OWord, IsZigzagDeletion W.letters W'.letters →
    (realize W').sCount + 2 = (realize W).sCount
  /-- "[Deleting an empty zigzag] cannot increase B" -/
  zigzag_B : ∀ W W' : OWord, IsZigzagDeletion W.letters W'.letters →
    (realize W').defect ≤ (realize W).defect
  /-- "applying the crossed-cusp shortcut lowers s by one" -/
  crossedCusp_s : ∀ W W' : OWord, IsCrossedCuspShortcut W.letters W'.letters →
    (realize W').sCount + 1 = (realize W).sCount
  /-- "[applying the crossed-cusp shortcut] cannot increase B" -/
  crossedCusp_B : ∀ W W' : OWord, IsCrossedCuspShortcut W.letters W'.letters →
    (realize W').defect ≤ (realize W).defect

/-- **ng:circle** (sm-3:2046-2049): "Deleting a separated standard front circle with nonempty remainder
preserves B.  A single standard front circle, and any union of such circles, has B = 0."  A separated
standard front circle is the factor `l_m r_m` (no letter acts between its cusps: crossing-free, nesting
allowed) and `IsCircleDeletion W W'` requires the nonempty remainder `W' ≠ []`; "a single standard front
circle, and any union of such circles" is the geometric base predicate `PLFront.IsStandardCircles` on the
realization (no crossing, exactly one left and one right cusp per component; FINAL §2 G1 (iii)).  Display
ng:circle-counts (`d`, `D` drop by one, `w` unchanged) is proof content. -/
structure NgCircleData : Prop where
  /-- "Deleting a separated standard front circle with nonempty remainder preserves B." -/
  circle_deletion_B : ∀ W W' : OWord, IsCircleDeletion W.letters W'.letters →
    (realize W).defect = (realize W').defect
  /-- "A single standard front circle, and any union of such circles, has B = 0." -/
  standard_circles_B : ∀ W : OWord, (realize W).IsStandardCircles → (realize W).defect = 0

/-- **ng:cusp-skein** (sm-3:2076-2082): "For either principal direction of an oriented cusp-skein
interchange, B of the earlier branch is at least the minimum of B of the other principal branch and B of the
unique compatible smoothing.  The smoothing has one fewer singularity; the principal branches have the same
singularity count."  The interchange is eq. ng:cusp-words `A = l₂σ₁`, `A' = l₁σ₂` with the compatible
smoothing `C_top = l₁` or `C_bottom = l₂` fixed by the (t,u) table (`IsCuspSkeinStep`, spectator offset
`m − 1`, direction bits as in `SM/FrontWords.lean`); "either principal direction" is the symmetric relation
`IsCuspSkein A A' C := IsCuspSkeinStep A A' C ∨ IsCuspSkeinStep A' A C` (`Skein` on closed words), so the
field `skein_B` for all triples is both lines of display ng:skein-defect. -/
structure NgCuspSkeinData : Prop where
  /-- "For either principal direction of an oriented cusp-skein interchange, B of the earlier branch is at
  least the minimum of B of the other principal branch and B of the unique compatible smoothing." -/
  skein_B : ∀ A A' C : OWord, Skein A A' C →
    min (realize A').defect (realize C).defect ≤ (realize A).defect
  /-- "The smoothing has one fewer singularity" -/
  smoothing_s : ∀ A A' C : OWord, Skein A A' C → (realize C).sCount + 1 = (realize A).sCount
  /-- "the principal branches have the same singularity count." -/
  principal_s : ∀ A A' C : OWord, Skein A A' C → (realize A').sCount = (realize A).sCount

/-- **ng:local-front-bound** (sm-3:2305-2312): "For every front F on the domain of Definition
ng:front-domain, with the same polynomial evaluated on its actual ordinary cusp rounding,
`w(F) − D(F) ≤ −deg_a P_{S(F)} − 1`" (display ng:front-inequality), i.e. `B(F) ≥ 0` (display ng:defect,
sm-3:1899-1900 "We will prove B(F) ≥ 0 for each front").  Two fields: the inequality on every front
represented by a closed oriented word (`realize W` with its identity rounding — the statement the word
procedure proves: strong induction on `s` along the principal chains of `SM.ng_finite_word`, rows 76-82 as
the laws, `SM.ng_finite_word_bound`), and the printed clause on the smooth class for every rounding `S(F)`
(derived from the first through row 76's `representation` and rp:record-polynomial; the dependence of
`deg_a P_{S(F)}` on the rounding is settled by ng:smoothing-record, row 74).  The consumer fd:ng-bound (row 93)
reads `on_fronts`. -/
structure NgLocalFrontBoundData : Prop where
  /-- the printed inequality `w(F) − D(F) ≤ −deg_a P_{S(F)} − 1` for every front `F = realize W`
  represented by a closed oriented word, `S(F) = F.diagram` (FR-5 reading) -/
  on_words : ∀ W : OWord,
    (realize W).writhe - ((realize W).downCount : ℤ) ≤ -degAZ (P (realize W).diagram) - 1
  /-- "For every front F on the domain of Definition ng:front-domain, with the same polynomial evaluated on
  its actual ordinary cusp rounding, `w(F) − D(F) ≤ −deg_a P_{S(F)} − 1`." -/
  on_fronts : ∀ (F : SmoothFront) (S : Diagram), F.IsRounding S →
    F.writhe - (F.downCount : ℤ) ≤ -degAZ (P S) - 1

namespace FrontRows

/-! ## 1. Unit T-pl — block placements and block setups (proved) -/

/-- The placement of `X ++ P' ++ Y` matching the standard placement of `X ++ P ++ Y` outside the block
(β2 `PlAgree`): standard up to column `n = |X|`, the `b = |P'|` block columns share the width `a = |P|` of
the other block, then shifted by `a − b`. -/
def blockPlacement (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) : Placement where
  x k := if k ≤ n then (k : ℝ) else if k ≤ n + b then (n : ℝ) + ((k : ℝ) - n) * a / b else (k : ℝ) + a - b
  strictMono := by
    intro k l hkl
    have hkl' : (k : ℝ) < l := by exact_mod_cast hkl
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    have hq : (0 : ℝ) < (a : ℝ) / b := div_pos ha' hb'
    have hba : (b : ℝ) * (a / b) = a := by field_simp
    dsimp only
    by_cases hk1 : k ≤ n
    · rw [if_pos hk1]
      by_cases hl1 : l ≤ n
      · rw [if_pos hl1]; exact hkl'
      · rw [if_neg hl1]
        have hn : (k : ℝ) ≤ n := by exact_mod_cast hk1
        have hl : (n : ℝ) < l := by exact_mod_cast (not_le.1 hl1)
        by_cases hl2 : l ≤ n + b
        · rw [if_pos hl2]
          have : 0 < ((l : ℝ) - n) * a / b := by rw [mul_div_assoc]; exact mul_pos (by linarith) hq
          linarith
        · rw [if_neg hl2]
          have hl' : ((n : ℝ) + b) < l := by exact_mod_cast (not_le.1 hl2)
          linarith
    · rw [if_neg hk1]
      have hl1 : ¬ l ≤ n := by omega
      rw [if_neg hl1]
      have hkn : (n : ℝ) < k := by exact_mod_cast (not_le.1 hk1)
      by_cases hk2 : k ≤ n + b
      · rw [if_pos hk2]
        by_cases hl2 : l ≤ n + b
        · rw [if_pos hl2, mul_div_assoc, mul_div_assoc]
          have := mul_lt_mul_of_pos_right (sub_lt_sub_right hkl' (n : ℝ)) hq
          linarith
        · rw [if_neg hl2, mul_div_assoc]
          have hk : (k : ℝ) ≤ n + b := by exact_mod_cast hk2
          have hl : ((n : ℝ) + b) < l := by exact_mod_cast (not_le.1 hl2)
          have : ((k : ℝ) - n) * (a / b) ≤ b * (a / b) := mul_le_mul_of_nonneg_right (by linarith) hq.le
          linarith
      · rw [if_neg hk2]
        have hl2 : ¬ l ≤ n + b := by omega
        rw [if_neg hl2]
        linarith

@[simp] theorem blockPlacement_x_of_le (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) {k : ℕ} (hk : k ≤ n) :
    (blockPlacement n a b ha hb).x k = k := by
  simp [blockPlacement, hk]

theorem blockPlacement_x_after (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) (j : ℕ) :
    (blockPlacement n a b ha hb).x (n + b + j) = (n : ℝ) + a + j := by
  have h1 : ¬ n + b + j ≤ n := by omega
  simp only [blockPlacement, h1, if_false]
  by_cases hj : j = 0
  · subst hj
    simp only [le_refl, add_zero, if_true]
    push_cast
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    field_simp
    ring
  · have h2 : ¬ n + b + j ≤ n + b := by omega
    simp only [h2, if_false]
    push_cast; ring

/-- A closed word stays closed when a factor is replaced by one with the same typing effect. -/
theorem Closed.of_sameEffect {X P Y P' : Word} (hW : (X ++ P ++ Y).Closed) (hE : SameEffect X P P') :
    (X ++ P' ++ Y).Closed := by
  unfold Word.Closed at *
  rw [Word.run_append] at hW ⊢
  unfold SameEffect at hE
  rw [← hE]; exact hW

/-- The block setup of a factor replacement `X ++ P ++ Y ↦ X ++ P' ++ Y` with the same typing effect: the
`P` side gets the standard placement (so `B.F` is `realize` of that word), the `P'` side the block placement. -/
def BlockSetup.ofEffect (X P Y P' : Word) (hP : P ≠ []) (hP' : P' ≠ []) (hW : (X ++ P ++ Y).Closed)
    (hE : SameEffect X P P') : BlockSetup where
  X := X
  P := P
  Y := Y
  P' := P'
  hP := hP
  hP' := hP'
  hE := hE
  hW := hW
  hW' := Closed.of_sameEffect hW hE
  pl := .std
  pl' := blockPlacement X.length P.length P'.length (List.length_pos_iff_ne_nil.2 hP)
    (List.length_pos_iff_ne_nil.2 hP')
  hpl := plAgree_of X P P' .std _ hP (fun k hk => by simp [Placement.std, hk])
    (fun j => by rw [blockPlacement_x_after]; simp [Placement.std])

/-- The block setup of a rewrite whose factors have the same effect on EVERY cut (the shape of
`Word.Closed.replace`). -/
def BlockSetup.ofReplace (X P Y P' : Word) (hP : P ≠ []) (hP' : P' ≠ []) (hW : (X ++ P ++ Y).Closed)
    (h : ∀ c c' : Cuts, Word.run P c = some c' → Word.run P' c = some c') : BlockSetup :=
  BlockSetup.ofEffect X P Y P' hP hP' hW (sameEffect_of_replace X P Y P' hW h)

/-- `P` of the `P` side of a block setup is `P` of the standard realization (β2 `P_realizeAt_eq_realize`). -/
theorem blockP_F (B : BlockSetup) :
    P B.F.diagram = P (realize ⟨B.X ++ B.P ++ B.Y, B.hW⟩).diagram :=
  P_realizeAt_eq_realize B.pl ⟨_, B.hW⟩ B.hne

theorem blockP_F' (B : BlockSetup) :
    P B.F'.diagram = P (realize ⟨B.X ++ B.P' ++ B.Y, B.hW'⟩).diagram :=
  P_realizeAt_eq_realize B.pl' ⟨_, B.hW'⟩ B.hne'

/-- Glue: an RI site on a block setup (kink on the `P` side) gives `P` equality of the two standard realizations
(accepted `P_reidemeister_I`). -/
theorem P_eq_of_RI_site (B : BlockSetup) (h : Nonempty (RIData B.U B.F'.diagram B.F.diagram)) :
    P (realize ⟨B.X ++ B.P ++ B.Y, B.hW⟩).diagram = P (realize ⟨B.X ++ B.P' ++ B.Y, B.hW'⟩).diagram := by
  rw [← blockP_F B, ← blockP_F' B]
  exact P_reidemeister_I ⟨B.U, Or.inr h⟩

theorem P_eq_of_RII_site (B : BlockSetup) (h : Nonempty (RIIData B.U B.F'.diagram B.F.diagram)) :
    P (realize ⟨B.X ++ B.P ++ B.Y, B.hW⟩).diagram = P (realize ⟨B.X ++ B.P' ++ B.Y, B.hW'⟩).diagram := by
  rw [← blockP_F B, ← blockP_F' B]
  exact P_reidemeister_II ⟨B.U, Or.inr h⟩

theorem P_eq_of_RIII_site (B : BlockSetup) (h : Nonempty (RIIIData B.U B.F.diagram B.F'.diagram)) :
    P (realize ⟨B.X ++ B.P ++ B.Y, B.hW⟩).diagram = P (realize ⟨B.X ++ B.P' ++ B.Y, B.hW'⟩).diagram := by
  rw [← blockP_F B, ← blockP_F' B]
  exact P_reidemeister_III ⟨B.U, Or.inl h⟩

/-! ## 2. Unit T-cnt — the letter-traced counts under a factor replacement (leaves) -/

/-- LEAF T-cnt-1: `downCountFrom` over an append of typed words. -/
theorem downCountFrom_append (V V' : Word) (c c' : Cuts) (h : Word.run V c = some c') :
    (V ++ V').downCountFrom c = V.downCountFrom c + V'.downCountFrom c' := sorry

/-- LEAF T-cnt-2: `writheFrom` over an append of typed words. -/
theorem writheFrom_append (V V' : Word) (c c' : Cuts) (h : Word.run V c = some c') :
    (V ++ V').writheFrom c = V.writheFrom c + V'.writheFrom c' := sorry

/-- LEAF T-cnt-3: a factor replacement with the same typing effect changes the letter-traced counts only by
the factors' own contributions (the exterior letters see the same cuts: "an unchanged common exterior",
sm-3:1915-1916).  From T-cnt-1/2. -/
theorem counts_replace (X P Y P' : Word) (c₀ c₁ : Cuts) (hX : Word.run X [] = some c₀)
    (hP : Word.run P c₀ = some c₁) (hP' : Word.run P' c₀ = some c₁) (hY : Word.run Y c₁ = some []) :
    (X ++ P' ++ Y).downCountFrom [] + P.downCountFrom c₀ =
        (X ++ P ++ Y).downCountFrom [] + P'.downCountFrom c₀ ∧
      (X ++ P' ++ Y).writheFrom [] + P.writheFrom c₀ = (X ++ P ++ Y).writheFrom [] + P'.writheFrom c₀ := sorry

/-! ### Nonemptiness of the words of each pattern (proved) -/

theorem IsTypeI.ne_nil {W W' : Word} (h : IsTypeI W W') (hW : W.Closed) : W ≠ [] ∧ W' ≠ [] := by
  obtain ⟨X, Y, m, d, hpat, rfl⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hpat with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  · -- the curl needs a through-strand, so `X ++ Y ≠ []`
    intro hXY
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hXY
    rcases hpat with ⟨hm, rfl⟩ | ⟨hm, rfl⟩
    · change Word.run [Letter.l m d, Letter.σ (m - 1), Letter.r m] [] = some [] at hW
      rw [run_three_iff] at hW
      obtain ⟨c₁, h1, -⟩ := hW
      obtain ⟨A, L, L', -, hA, hc, -, -⟩ := Letter.step_eq_some_iff.1 h1
      simp only [Letter.idx] at hA
      have := congrArg List.length hc
      simp only [List.length_nil, List.length_append] at this
      omega
    · change Word.run [Letter.l m d, Letter.σ (m + 1), Letter.r m] [] = some [] at hW
      rw [run_three_iff] at hW
      obtain ⟨c₁, h1, c₂, h2, -⟩ := hW
      obtain ⟨A, L, L', -, hA, hc, hL, rfl⟩ := Letter.step_eq_some_iff.1 h1
      simp only [Letter.idx] at hA
      have hlen := congrArg List.length hc
      simp only [List.length_nil, List.length_append] at hlen
      simp only [Letter.act_l, Option.some.injEq] at hL
      subst hL
      obtain ⟨A', M, M', -, hA', hc', hM, -⟩ := Letter.step_eq_some_iff.1 h2
      simp only [Letter.idx] at hA'
      obtain ⟨p, q, M₀, hM₀, -⟩ := Letter.act_σ_eq_some_iff.1 hM
      have hlen' := congrArg List.length hc'
      rw [hM₀] at hlen'
      simp only [List.length_append, List.length_cons] at hlen'
      omega

theorem IsTypeII.ne_nil {W W' : Word} (h : IsTypeII W W') : W ≠ [] ∧ W' ≠ [] := by
  obtain ⟨X, Y, m, hpat⟩ := h
  rcases hpat with ⟨d, -, rfl, rfl⟩ | ⟨d, -, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;> exact ⟨by simp, by simp⟩

theorem IsTypeIII.ne_nil {W W' : Word} (h : IsTypeIII W W') : W ≠ [] ∧ W' ≠ [] := by
  obtain ⟨X, Y, m, -, hpat⟩ := h
  rcases hpat with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by simp, by simp⟩

theorem IsComm.ne_nil {W W' : Word} (h : IsComm W W') : W ≠ [] ∧ W' ≠ [] := by
  rcases h with ⟨X, Y, a, b, rfl, hpat⟩ | ⟨X, Y, a, b, rfl, hpat⟩ <;>
    rcases hpat with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨by simp, by simp⟩

theorem IsZigzagDeletion.ne_nil' {W W' : Word} (h : IsZigzagDeletion W W') (hW : W.Closed) :
    W ≠ [] ∧ W' ≠ [] := by
  refine ⟨?_, IsZigzagDeletion.ne_nil h hW⟩
  obtain ⟨X, Y, m, d, -, hpat, -⟩ := h
  rcases hpat with rfl | rfl <;> simp

theorem IsCrossedCuspShortcut.ne_nil {W W' : Word} (h : IsCrossedCuspShortcut W W') : W ≠ [] ∧ W' ≠ [] := by
  obtain ⟨X, Y, i, -, hpat⟩ := h
  rcases hpat with ⟨d, rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by simp, by simp⟩

theorem IsCircleDeletion.ne_nil {W W' : Word} (h : IsCircleDeletion W W') : W ≠ [] ∧ W' ≠ [] := by
  obtain ⟨X, Y, m, d, -, rfl, rfl, hne⟩ := h
  exact ⟨by simp, hne⟩

theorem IsCuspSkeinStep.ne_nil {A A' C : Word} (h : IsCuspSkeinStep A A' C) : A ≠ [] ∧ A' ≠ [] ∧ C ≠ [] := by
  obtain ⟨X, Y, m, d, a, Pc, L, -, -, -, rfl, rfl, hC⟩ := h
  refine ⟨by simp, by simp, ?_⟩
  rcases hC with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp

/-! ### The syntactic count facts of each pattern (leaves; from T-cnt-3 and the factor computations at the
symbolic cut `A ++ w ++ R` of `Letter.step_eq_some_iff` / `StepDecomp`) -/

/-- LEAF T-cnt-4 (ng:commutation, sm-3:1929-1936 "The cusp directions and crossing signs are unchanged, so
D and w are unchanged as well"): a disjoint-gadget commutation keeps the letter-traced `D` and `w`. -/
theorem comm_counts_syn (W W' : OWord) (h : IsComm W.letters W'.letters) :
    W.letters.downCountFrom [] = W'.letters.downCountFrom [] ∧
      W.letters.writheFrom [] = W'.letters.writheFrom [] := sorry

/-- LEAF T-cnt-5 (display ng:type-I-counts, sm-3:1964-1966, deletion direction): the curl carries exactly one
downward cusp and one positive crossing. -/
theorem typeI_counts_syn (W W' : OWord) (h : IsTypeI W.letters W'.letters) :
    W.letters.downCountFrom [] = W'.letters.downCountFrom [] + 1 ∧
      W.letters.writheFrom [] = W'.letters.writheFrom [] + 1 := sorry

/-- LEAF T-cnt-6 (ng:front-II, sm-3:1979-1987: "Their signs are opposite ... The same upper and lower cusp
arms remain after deletion. Thus Δw = ΔD = 0"). -/
theorem typeII_counts_syn (W W' : OWord) (h : IsTypeII W.letters W'.letters) :
    W.letters.downCountFrom [] = W'.letters.downCountFrom [] ∧
      W.letters.writheFrom [] = W'.letters.writheFrom [] := sorry

/-- LEAF T-cnt-7 (ng:front-III, sm-3:1997-2001: "Each physical pair crosses on both sides with the same
over/under bit and transported arrows"). -/
theorem typeIII_counts_syn (W W' : OWord) (h : IsTypeIII W.letters W'.letters) :
    W.letters.downCountFrom [] = W'.letters.downCountFrom [] ∧
      W.letters.writheFrom [] = W'.letters.writheFrom [] := sorry

/-- LEAF T-cnt-8 (display ng:zigzag-counts, sm-3:2020-2022: `Δw = 0`, `ΔD ∈ {0, −2}`; "Their directions are
both downward or both upward"). -/
theorem zigzag_counts_syn (W W' : OWord) (h : IsZigzagDeletion W.letters W'.letters) :
    W.letters.writheFrom [] = W'.letters.writheFrom [] ∧
      (W.letters.downCountFrom [] = W'.letters.downCountFrom [] ∨
        W.letters.downCountFrom [] = W'.letters.downCountFrom [] + 2) := sorry

/-- LEAF T-cnt-9 (display ng:crossed-cusp-counts, sm-3:2030-2036: "the old crossing has sign −1. Deletion
raises w by one and flips the cusp direction"). -/
theorem crossedCusp_counts_syn (W W' : OWord) (h : IsCrossedCuspShortcut W.letters W'.letters) :
    W.letters.writheFrom [] + 1 = W'.letters.writheFrom [] ∧
      (W.letters.downCountFrom [] + 1 = W'.letters.downCountFrom [] ∨
        W.letters.downCountFrom [] = W'.letters.downCountFrom [] + 1) := sorry

/-- LEAF T-cnt-10 (ng:circle, sm-3:2052-2053, 2066-2068: the circle has `D = 1`, `w = 0`; "The writhe is
unchanged"). -/
theorem circle_counts_syn (W W' : OWord) (h : IsCircleDeletion W.letters W'.letters) :
    W.letters.downCountFrom [] = W'.letters.downCountFrom [] + 1 ∧
      W.letters.writheFrom [] = W'.letters.writheFrom [] := sorry

/-- LEAF T-cnt-11 (ng:cusp-skein, the (t,u) table sm-3:2100-2118 and sm-3:2129-2131 "Their writhes are
`w₀+1, w₀−1, w₀`"; sm-3:2149-2150 "the same downward-cusp count in all three diagrams"): `sign(A) = −sign(A')
= ±1`, `D` common. -/
theorem skein_counts_syn (A A' C : OWord) (h : IsCuspSkeinStep A.letters A'.letters C.letters) :
    A.letters.downCountFrom [] = C.letters.downCountFrom [] ∧
      A'.letters.downCountFrom [] = C.letters.downCountFrom [] ∧
      ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ A.letters.writheFrom [] = C.letters.writheFrom [] + σ ∧
        A'.letters.writheFrom [] = C.letters.writheFrom [] - σ := sorry

/-! ### Transport of the syntactic counts to the realizations (proved; β2 `realize_downCount`, `realize_writhe`) -/

theorem realize_counts_eq_of_syn {W W' : OWord} (hW : W.letters ≠ []) (hW' : W'.letters ≠ [])
    (h : W.letters.downCountFrom [] = W'.letters.downCountFrom [] ∧
      W.letters.writheFrom [] = W'.letters.writheFrom []) :
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe := by
  rw [realize_downCount W hW, realize_downCount W' hW', realize_writhe W hW, realize_writhe W' hW']
  exact h

/-- `B` from `D`, `w` and `P` (display ng:defect). -/
theorem defect_eq_of_counts {F F' : PLFront} (hD : F.downCount = F'.downCount) (hw : F.writhe = F'.writhe)
    (hP : P F.diagram = P F'.diagram) : F.defect = F'.defect := by
  unfold PLFront.defect; rw [hD, hw, hP]

/-! ## 3. Unit T-deg — degrees in `a` (def:adeg; leaves) -/

/-- LEAF T-deg-1 (ng:circle, sm-3:2060: "The leading a coefficient of δ is z⁻¹, in degree one"). -/
theorem degAZ_delta : degAZ R.delta = 1 := sorry

/-- LEAF T-deg-2: `deg_a δ^n = n` (`degAZ_mul`, `R.delta ≠ 0` in the domain `R`). -/
theorem degAZ_delta_pow (n : ℕ) : degAZ (R.delta ^ n) = n := sorry

/-- LEAF T-deg-3 (ng:circle, sm-3:2061-2063: "Its product with the leading coefficient of P_after is nonzero
because the coefficient ring is an integral domain"): `deg_a (δ f) = deg_a f + 1` for `f ≠ 0`
(`degAZ_mul`). -/
theorem degAZ_delta_mul {f : R} (hf : f ≠ 0) : degAZ (R.delta * f) = degAZ f + 1 := sorry

/-- LEAF T-deg-4 (ng:cusp-skein, sm-3:2143-2146: "The degree of a nonzero sum is at most the maximum of the
summand degrees. Multiplication by a^k shifts degree by k, and multiplication by z does not change it";
display ng:skein-plus): from `degA_add_le`, `degAZ_mul`, `degA_aInv`, `degA_z`. -/
theorem degAZ_skein_pos {f g h : R} (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (e : h = R.aInv * R.aInv * f + R.aInv * R.z * g) : degAZ h ≤ max (degAZ f - 2) (degAZ g - 1) := sorry

/-- LEAF T-deg-5 (display ng:skein-minus, sm-3:2147-2148): the other direction. -/
theorem degAZ_skein_neg {f g h : R} (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (e : h = R.a * R.a * f - R.a * R.z * g) : degAZ h ≤ max (degAZ f + 2) (degAZ g + 1) := sorry

/-! ## 4. Unit T-rec — the named record of a grid realization (leaves)

The record (def:gauss-record, `Diagram.record`) of a realization is read on the slot layer: its occurrences
are the two slots of each `σ` letter (`σSlotA` over, `σSlotB` under; `crossingEquiv`), its successor is the
first `σ` slot along the iterates of `next` (β2 `toSlot_succ`: the parameter circle of a component IS the
cycle of `next`, and the visit point sits at parameter `1/2` of its piece, `crossingParam_eq_half`), its twin
is the other slot of the same column, its over bit is `σSlotA`, its sign is `bit k m = bit k (m+1)`
(`sign_crossingOf`).  Two realizations whose exterior `σ` columns correspond by the index shift (β2
`shiftIdx`, `next_ext`) and whose blocks connect the boundary slots identically (a finite computation with
`next_cases` per pattern) therefore have isomorphic records; the polynomial follows by the accepted
`presentations` (rp:record-polynomial).  This is the printed argument of ng:commutation ("the full named
records are the same"), ng:cusp-skein ("After gluing any same actual exterior, the full named records are
identical") and ng:circle (a separated circle is a free component of the record). -/

/-- LEAF T-rec-1 (ng:commutation, sm-3:1929-1933): the two realizations of a disjoint-gadget commutation have
isomorphic named records. -/
theorem comm_recordIso (W W' : OWord) (h : IsComm W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := sorry

/-- LEAF T-rec-2 (ng:deletions, sm-3:2017-2019: after rounding the zigzag "is a simple ordinary arc,
positively page isotopic relative to its endpoints to the straightened arc"): deleting an empty zigzag keeps
the named record (no crossing inside; every strand passes through the block; exterior visits and their cyclic
orders unchanged). -/
theorem zigzag_recordIso (W W' : OWord) (h : IsZigzagDeletion W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := sorry

/-- LEAF T-rec-3 (ng:circle, sm-3:2054-2059: "A standard circle separated by the word procedure has no
mixed crossings ... Lemma lp:split-circle permits this nesting"): the record of the word with the circle is
the record of the remainder with one free (crossing-free) component added (`Record.addFree`); the accepted
`P_addFree` then gives `P_before = δ P_after`. -/
theorem circle_recordIso_addFree (W W' : OWord) (h : IsCircleDeletion W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record.addFree) := sorry

/-! ## 5. Unit U76 — ng:commutation -/

/-- LEAF U76-1 (sm-3:1934-1936 "A deformation without a singular event preserves the records, D and w:
signs, cusp directions and cyclic attachments cannot change"): along a PL deformation the x-sign of every
edge is constant (nonvertical, continuous), so the cusps are the same vertices, and the cusp discriminant
`x_out · det(e_in, e_out)` is continuous and nonzero (`cusp_det_ne_zero` at every generic intermediate
polygon), so its sign — the down/up reading — is constant: `D` is preserved. -/
theorem _root_.SM.PLFront.Deform.downCount_eq {F F' : PLFront} (h : PLFront.Deform F F') : F.downCount = F'.downCount :=
  sorry

/-- LEAF U76-2: along a PL deformation the crossing pairs are literally the same (`DeformData.crossings`), the
slopes of the two strands never coincide (transverse, generic) so the over strand (smaller `dz/dx`) is the
same strand throughout, and `det(u_o, u_u)` is continuous and nonzero, so every crossing sign is constant:
`w` is preserved. -/
theorem _root_.SM.PLFront.Deform.writhe_eq {F F' : PLFront} (h : PLFront.Deform F F') : F.writhe = F'.writhe := sorry

/-- Glue (proved): a PL deformation is a generic deformation of the diagrams, so `P` is preserved
(sm-3:1936-1937 "Lemma rp:record-polynomial gives scalar equality"; accepted `P_planar`). -/
theorem _root_.SM.PLFront.Deform.P_eq {F F' : PLFront} (h : PLFront.Deform F F') : P F.diagram = P F'.diagram :=
  P_planar (PlanarIsotopic.of_deform ⟨h.some.toDeformData⟩)

/-- Companion (proved from the leaves): the three invariances of the deformation clause. -/
theorem _root_.SM.PLFront.Deform.counts_eq {F F' : PLFront} (h : PLFront.Deform F F') :
    F.downCount = F'.downCount ∧ F.writhe = F'.writhe ∧ degAZ (P F.diagram) = degAZ (P F'.diagram) :=
  ⟨h.downCount_eq, h.writhe_eq, by rw [h.P_eq]⟩

/-- LEAF U76-3 (companion, not a clause; β2 `deformData` made nonvertical): a change of placement is a PL
deformation — this is how the rows transport their block realizations, and the reason `Deform` is the right
PL reading of "deformations through fronts without a singular event". -/
theorem _root_.SM.PLFront.deform_realizeAt (pl pl' : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ []) :
    PLFront.Deform (realizeAt pl hW hne) (realizeAt pl' hW hne) := sorry

/-- LEAF U76-4 = THE REPRESENTATION THEOREM (76b; sm-3:1924-1925 and its proof 1938-1947: separate equal
x-coordinates by small local x-translations, read successive vertical cuts).  FINAL §8 risk 1: 7.5-11k lines
(PL model of a smooth front 5-7k + PL vertical sweep to a word 2.5-4k); attacked last; row 76 and the
field `on_fronts` of row 83 wait for it. -/
theorem representation_by_word (F : SmoothFront) : ∃ W : OWord,
    F.sCount = (realize W).sCount ∧ F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧
      ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record) := sorry

/-- Glue (proved): the commutation clause from T-cnt-4 and T-rec-1. -/
theorem comm_counts_and_P (W W' : OWord) (h : IsComm W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe ∧
      degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram) := by
  have hne := IsComm.ne_nil h
  obtain ⟨hD, hw⟩ := realize_counts_eq_of_syn hne.1 hne.2 (comm_counts_syn W W' h)
  exact ⟨hD, hw, by rw [presentations _ _ (comm_recordIso W W' h)]⟩

/-! ## 6. Unit U77 — ng:front-I: the curl against the empty zigzag (RI), then the zigzag record -/

/-- LEAF U77-1 (syntactic): the curl `l_m σ_{m−1} r_m` and the zigzag `l_m r_{m−1}` with the opposite cusp
bit have the same typing effect (both act as the identity on the cut; `run_typeI_left`). -/
theorem run_typeI_left_zigzag {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 2 ≤ m)
    (h : Word.run [Letter.l m d, Letter.σ (m - 1), Letter.r m] c = some c') : Word.run [Letter.l m (!d), Letter.r (m - 1)] c = some c' :=
  sorry

/-- LEAF U77-2 (syntactic): the curl `l_m σ_{m+1} r_m` and the zigzag `l_{m+1} d r_m`. -/
theorem run_typeI_right_zigzag {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 1 ≤ m)
    (h : Word.run [Letter.l m d, Letter.σ (m + 1), Letter.r m] c = some c') : Word.run [Letter.l (m + 1) d, Letter.r m] c = some c' :=
  sorry

/-- The block setups of the two curl-vs-zigzag comparisons (the `P` side is the curl). -/
def typeIBlockL (X Y : Word) (m : ℕ) (d : Bool) (hm : 2 ≤ m)
    (hW : (X ++ [Letter.l m d, Letter.σ (m - 1), Letter.r m] ++ Y).Closed) : BlockSetup :=
  BlockSetup.ofReplace X [Letter.l m d, Letter.σ (m - 1), Letter.r m] Y [Letter.l m (!d), Letter.r (m - 1)] (List.cons_ne_nil _ _)
    (List.cons_ne_nil _ _) hW (fun _ _ h => run_typeI_left_zigzag hm h)

def typeIBlockR (X Y : Word) (m : ℕ) (d : Bool) (hm : 1 ≤ m)
    (hW : (X ++ [Letter.l m d, Letter.σ (m + 1), Letter.r m] ++ Y).Closed) : BlockSetup :=
  BlockSetup.ofReplace X [Letter.l m d, Letter.σ (m + 1), Letter.r m] Y [Letter.l (m + 1) d, Letter.r m] (List.cons_ne_nil _ _)
    (List.cons_ne_nil _ _) hW (fun _ _ h => run_typeI_right_zigzag hm h)

/-- LEAF U77-3 (sm-3:1955-1963: "After rounding its two cusps, the unique crossing bounds an empty ordinary
monogon"): the RI site — the zigzag side has one crossing-free arc in the block rectangle, the curl side one
arc with the kink; `LocalFrame` from `isDisc_blockRect` + `clean_blockRect` (exit criterion: the through-strand
and every other component have exterior strands, `X ≠ []` by `IsTypeI.ne_nil`), `MoveMatch` from
`BlockSetup.outsideMatch` + the block traversal (T-arc), `ArcCover` of the block, `inner_iff'` from
`crossingPoint_mem_interior_iff`. -/
theorem typeI_site_left (X Y : Word) (m : ℕ) (d : Bool) (hm : 2 ≤ m)
    (hW : (X ++ [Letter.l m d, Letter.σ (m - 1), Letter.r m] ++ Y).Closed) :
    Nonempty (RIData (typeIBlockL X Y m d hm hW).U (typeIBlockL X Y m d hm hW).F'.diagram
      (typeIBlockL X Y m d hm hW).F.diagram) := sorry

theorem typeI_site_right (X Y : Word) (m : ℕ) (d : Bool) (hm : 1 ≤ m)
    (hW : (X ++ [Letter.l m d, Letter.σ (m + 1), Letter.r m] ++ Y).Closed) :
    Nonempty (RIData (typeIBlockR X Y m d hm hW).U (typeIBlockR X Y m d hm hW).F'.diagram
      (typeIBlockR X Y m d hm hW).F.diagram) := sorry

/-- Glue (proved): `P` is preserved by the type-I deletion — curl → zigzag by the RI site and
`P_reidemeister_I`, zigzag → nothing by T-rec-2 and `presentations`. -/
theorem typeI_P (W W' : OWord) (h : IsTypeI W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨Wl, Wc⟩ := W
  obtain ⟨W'l, W'c⟩ := W'
  obtain ⟨X, Y, m, d, hpat, hW'⟩ := h
  simp only at hpat hW'
  subst hW'
  rcases hpat with ⟨hm, hW⟩ | ⟨hm, hW⟩
  · subst hW
    have h1 := P_eq_of_RI_site (typeIBlockL X Y m d hm Wc) (typeI_site_left X Y m d hm Wc)
    have hZ : IsZigzagDeletion (X ++ [Letter.l m (!d), Letter.r (m - 1)] ++ Y) (X ++ Y) :=
      ⟨X, Y, m - 1, !d, by omega, Or.inr (by rw [show m - 1 + 1 = m by omega]), rfl⟩
    exact h1.trans (presentations _ _ (zigzag_recordIso ⟨_, (typeIBlockL X Y m d hm Wc).hW'⟩ ⟨_, W'c⟩ hZ))
  · subst hW
    have h1 := P_eq_of_RI_site (typeIBlockR X Y m d hm Wc) (typeI_site_right X Y m d hm Wc)
    have hZ : IsZigzagDeletion (X ++ [Letter.l (m + 1) d, Letter.r m] ++ Y) (X ++ Y) :=
      ⟨X, Y, m, d, hm, Or.inr rfl, rfl⟩
    exact h1.trans (presentations _ _ (zigzag_recordIso ⟨_, (typeIBlockR X Y m d hm Wc).hW'⟩ ⟨_, W'c⟩ hZ))

/-- Companion (proved from the leaves): display ng:type-I-counts on realizations, deletion direction. -/
theorem typeI_counts (W W' : OWord) (h : IsTypeI W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount + 1 ∧ (realize W).writhe = (realize W').writhe + 1 := by
  have hne := IsTypeI.ne_nil h W.closed
  obtain ⟨hD, hw⟩ := typeI_counts_syn W W' h
  rw [realize_downCount W hne.1, realize_downCount W' hne.2, realize_writhe W hne.1, realize_writhe W' hne.2]
  exact ⟨hD, hw⟩

/-! ## 7. Unit U78 — ng:front-II: four RII sites -/

def typeIIBlockLL (X Y : Word) (m : ℕ) (d : Bool) (hm : 2 ≤ m)
    (hW : (X ++ [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)] ++ Y).Closed) : BlockSetup :=
  BlockSetup.ofReplace X [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)] Y [Letter.l m d] (List.cons_ne_nil _ _)
    (List.cons_ne_nil _ _) hW (fun _ _ h => run_typeII_l_left hm h)

def typeIIBlockLR (X Y : Word) (m : ℕ) (d : Bool) (hm : 1 ≤ m)
    (hW : (X ++ [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)] ++ Y).Closed) : BlockSetup :=
  BlockSetup.ofReplace X [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)] Y [Letter.l m d] (List.cons_ne_nil _ _)
    (List.cons_ne_nil _ _) hW (fun _ _ h => run_typeII_l_right hm h)

def typeIIBlockRL (X Y : Word) (m : ℕ) (hm : 2 ≤ m)
    (hW : (X ++ [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)] ++ Y).Closed) : BlockSetup :=
  BlockSetup.ofReplace X [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)] Y [Letter.r m] (List.cons_ne_nil _ _)
    (List.cons_ne_nil _ _) hW (fun _ _ h => run_typeII_r_left hm h)

def typeIIBlockRR (X Y : Word) (m : ℕ) (hm : 1 ≤ m)
    (hW : (X ++ [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)] ++ Y).Closed) : BlockSetup :=
  BlockSetup.ofReplace X [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)] Y [Letter.r m] (List.cons_ne_nil _ _)
    (List.cons_ne_nil _ _) hW (fun _ _ h => run_typeII_r_right hm h)

/-- LEAF U78-1..4 (sm-3:1977-1985: "the through-strand is under at both crossings [or over at both]. The
other crossing branches are the oppositely directed arms of the same cusp ... an empty ordinary bigon with one
common over-strand: an oriented Reidemeister-II site"): the RII site of each variant — two arcs on each side
(the through-strand and the cusp arc) with the same ends, no crossing on the `l_m` side, exactly the two `σ`
crossings on the other side, both separating the two arcs, `same_over` from `overStrand_crossingOf`
(the descending strand is over: the through-strand at both, or the arms at both). -/
theorem typeII_site_ll (X Y : Word) (m : ℕ) (d : Bool) (hm : 2 ≤ m)
    (hW : (X ++ [Letter.l (m - 1) d, Letter.σ m, Letter.σ (m - 1)] ++ Y).Closed) :
    Nonempty (RIIData (typeIIBlockLL X Y m d hm hW).U (typeIIBlockLL X Y m d hm hW).F'.diagram
      (typeIIBlockLL X Y m d hm hW).F.diagram) := sorry

theorem typeII_site_lr (X Y : Word) (m : ℕ) (d : Bool) (hm : 1 ≤ m)
    (hW : (X ++ [Letter.l (m + 1) d, Letter.σ m, Letter.σ (m + 1)] ++ Y).Closed) :
    Nonempty (RIIData (typeIIBlockLR X Y m d hm hW).U (typeIIBlockLR X Y m d hm hW).F'.diagram
      (typeIIBlockLR X Y m d hm hW).F.diagram) := sorry

theorem typeII_site_rl (X Y : Word) (m : ℕ) (hm : 2 ≤ m)
    (hW : (X ++ [Letter.σ (m - 1), Letter.σ m, Letter.r (m - 1)] ++ Y).Closed) :
    Nonempty (RIIData (typeIIBlockRL X Y m hm hW).U (typeIIBlockRL X Y m hm hW).F'.diagram
      (typeIIBlockRL X Y m hm hW).F.diagram) := sorry

theorem typeII_site_rr (X Y : Word) (m : ℕ) (hm : 1 ≤ m)
    (hW : (X ++ [Letter.σ (m + 1), Letter.σ m, Letter.r (m + 1)] ++ Y).Closed) :
    Nonempty (RIIData (typeIIBlockRR X Y m hm hW).U (typeIIBlockRR X Y m hm hW).F'.diagram
      (typeIIBlockRR X Y m hm hW).F.diagram) := sorry

/-- Glue (proved): `P` is preserved by the type-II moves (`P_reidemeister_II` on the sites). -/
theorem typeII_P (W W' : OWord) (h : IsTypeII W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨Wl, Wc⟩ := W
  obtain ⟨W'l, W'c⟩ := W'
  obtain ⟨X, Y, m, hpat⟩ := h
  simp only at hpat
  rcases hpat with ⟨d, hm, hW, hW'⟩ | ⟨d, hm, hW, hW'⟩ | ⟨hm, hW, hW'⟩ | ⟨hm, hW, hW'⟩ <;> subst hW hW'
  · have h1 := P_eq_of_RII_site (typeIIBlockLL X Y m d hm Wc) (typeII_site_ll X Y m d hm Wc)
    exact h1
  · have h1 := P_eq_of_RII_site (typeIIBlockLR X Y m d hm Wc) (typeII_site_lr X Y m d hm Wc)
    exact h1
  · have h1 := P_eq_of_RII_site (typeIIBlockRL X Y m hm Wc) (typeII_site_rl X Y m hm Wc)
    exact h1
  · have h1 := P_eq_of_RII_site (typeIIBlockRR X Y m hm Wc) (typeII_site_rr X Y m hm Wc)
    exact h1

/-! ## 8. Unit U79 — ng:front-III: the RIII site -/

def typeIIIBlock (X Y : Word) (m : ℕ) (hm : 1 ≤ m)
    (hW : (X ++ [Letter.σ (m + 1), Letter.σ m, Letter.σ (m + 1)] ++ Y).Closed) : BlockSetup :=
  BlockSetup.ofReplace X [Letter.σ (m + 1), Letter.σ m, Letter.σ (m + 1)] Y [Letter.σ m, Letter.σ (m + 1), Letter.σ m] (List.cons_ne_nil _ _)
    (List.cons_ne_nil _ _) hW (fun _ _ h => by
      obtain ⟨A, p, q, r, L, hA, rfl, rfl⟩ := run_typeIII_aux hm h
      exact (run_typeIII_of_split hm hA).2)

/-- LEAF U79-1 (sm-3:1995-2003: "an actual ordinary Reidemeister-III configuration. Label the three physical
strands by their initial top-to-bottom order. The three over/under choices give one strict height order ...
Each physical pair crosses on both sides with the same over/under bit and transported arrows"): the RIII
site — three arcs (the strands entering at positions `m, m+1, m+2`, top `a` over both, `b` over `c`), the
three `σ` crossings named by their pairs, the same height order on both sides (`overStrand_crossingOf`: the
descending strand is over), the order of the two visits along every arc reversed (`BeforeOn` from the block
traversal). -/
theorem typeIII_site (X Y : Word) (m : ℕ) (hm : 1 ≤ m)
    (hW : (X ++ [Letter.σ (m + 1), Letter.σ m, Letter.σ (m + 1)] ++ Y).Closed) :
    Nonempty (RIIIData (typeIIIBlock X Y m hm hW).U (typeIIIBlock X Y m hm hW).F.diagram
      (typeIIIBlock X Y m hm hW).F'.diagram) := sorry

/-- Glue (proved): `P` is preserved by the type-III move, either direction (`P_reidemeister_III`). -/
theorem typeIII_P (W W' : OWord) (h : IsTypeIII W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨Wl, Wc⟩ := W
  obtain ⟨W'l, W'c⟩ := W'
  obtain ⟨X, Y, m, hm, hpat⟩ := h
  simp only at hpat
  rcases hpat with ⟨hW, hW'⟩ | ⟨hW, hW'⟩ <;> subst hW hW'
  · have h1 := P_eq_of_RIII_site (typeIIIBlock X Y m hm Wc) (typeIII_site X Y m hm Wc)
    exact h1
  · have h1 := P_eq_of_RIII_site (typeIIIBlock X Y m hm W'c) (typeIII_site X Y m hm W'c)
    exact h1.symm

/-! ## 9. Unit U80 — ng:deletions: the zigzag record (T-rec-2) and two crossed-cusp RI sites -/

def crossedCuspBlockL (X Y : Word) (i : ℕ) (d : Bool) (hi : 1 ≤ i)
    (hW : (X ++ [Letter.l i d, Letter.σ i] ++ Y).Closed) : BlockSetup :=
  BlockSetup.ofReplace X [Letter.l i d, Letter.σ i] Y [Letter.l i (!d)] (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) hW
    (fun _ _ h => run_crossedCusp_l hi h)

def crossedCuspBlockR (X Y : Word) (i : ℕ) (hi : 1 ≤ i)
    (hW : (X ++ [Letter.σ i, Letter.r i] ++ Y).Closed) : BlockSetup :=
  BlockSetup.ofReplace X [Letter.σ i, Letter.r i] Y [Letter.r i] (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) hW
    (fun _ _ h => run_crossedCusp_r hi h)

/-- LEAF U80-1/2 (sm-3:2027-2033: "a cusp whose own arms cross once. Replace it by the uncrossed cusp with the
same two oriented boundary attachments. After rounding, ordinary Reidemeister I deletes its empty monogon"):
the RI sites — one arc on each side (the cusp arc, entering and leaving through the right (left) boundary
of the block), the kink on the crossed side. -/
theorem crossedCusp_site_l (X Y : Word) (i : ℕ) (d : Bool) (hi : 1 ≤ i)
    (hW : (X ++ [Letter.l i d, Letter.σ i] ++ Y).Closed) :
    Nonempty (RIData (crossedCuspBlockL X Y i d hi hW).U (crossedCuspBlockL X Y i d hi hW).F'.diagram
      (crossedCuspBlockL X Y i d hi hW).F.diagram) := sorry

theorem crossedCusp_site_r (X Y : Word) (i : ℕ) (hi : 1 ≤ i)
    (hW : (X ++ [Letter.σ i, Letter.r i] ++ Y).Closed) :
    Nonempty (RIData (crossedCuspBlockR X Y i hi hW).U (crossedCuspBlockR X Y i hi hW).F'.diagram
      (crossedCuspBlockR X Y i hi hW).F.diagram) := sorry

/-- Glue (proved): `Δd = 0` for the crossed-cusp shortcut. -/
theorem crossedCusp_P (W W' : OWord) (h : IsCrossedCuspShortcut W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨Wl, Wc⟩ := W
  obtain ⟨W'l, W'c⟩ := W'
  obtain ⟨X, Y, i, hi, hpat⟩ := h
  simp only at hpat
  rcases hpat with ⟨d, hW, hW'⟩ | ⟨hW, hW'⟩ <;> subst hW hW'
  · have h1 := P_eq_of_RI_site (crossedCuspBlockL X Y i d hi Wc) (crossedCusp_site_l X Y i d hi Wc)
    exact h1
  · have h1 := P_eq_of_RI_site (crossedCuspBlockR X Y i hi Wc) (crossedCusp_site_r X Y i hi Wc)
    exact h1

/-- Glue (proved): `Δd = 0` for the zigzag deletion (T-rec-2 + `presentations`). -/
theorem zigzag_P (W W' : OWord) (h : IsZigzagDeletion W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram :=
  presentations _ _ (zigzag_recordIso W W' h)

/-- Glue (proved): the `s` clauses of ng:deletions from β1's syntactic counts and β2's `realize_sCount`. -/
theorem zigzag_s (W W' : OWord) (h : IsZigzagDeletion W.letters W'.letters) :
    (realize W').sCount + 2 = (realize W).sCount := by
  have hne := IsZigzagDeletion.ne_nil' h W.closed
  rw [realize_sCount W hne.1, realize_sCount W' hne.2]
  exact IsZigzagDeletion.sCount h

theorem crossedCusp_s (W W' : OWord) (h : IsCrossedCuspShortcut W.letters W'.letters) :
    (realize W').sCount + 1 = (realize W).sCount := by
  have hne := IsCrossedCuspShortcut.ne_nil h
  rw [realize_sCount W hne.1, realize_sCount W' hne.2]
  exact IsCrossedCuspShortcut.sCount h

/-- Glue (proved): display ng:zigzag-counts ⇒ "cannot increase B". -/
theorem zigzag_B (W W' : OWord) (h : IsZigzagDeletion W.letters W'.letters) :
    (realize W').defect ≤ (realize W).defect := by
  have hne := IsZigzagDeletion.ne_nil' h W.closed
  obtain ⟨hw, hD⟩ := zigzag_counts_syn W W' h
  have hP := zigzag_P W W' h
  unfold PLFront.defect
  rw [realize_downCount W hne.1, realize_downCount W' hne.2, realize_writhe W hne.1, realize_writhe W' hne.2,
    hP]
  unfold OWord.downCountSyn OWord.writheSyn
  rw [hw]
  rcases hD with hD | hD <;> rw [hD] <;> push_cast <;> omega

/-- Glue (proved): display ng:crossed-cusp-counts ⇒ "cannot increase B" (`ΔB ∈ {−2, 0}`). -/
theorem crossedCusp_B (W W' : OWord) (h : IsCrossedCuspShortcut W.letters W'.letters) :
    (realize W').defect ≤ (realize W).defect := by
  have hne := IsCrossedCuspShortcut.ne_nil h
  obtain ⟨hw, hD⟩ := crossedCusp_counts_syn W W' h
  have hP := crossedCusp_P W W' h
  unfold PLFront.defect
  rw [realize_downCount W hne.1, realize_downCount W' hne.2, realize_writhe W hne.1, realize_writhe W' hne.2,
    hP]
  unfold OWord.downCountSyn OWord.writheSyn
  rcases hD with hD | hD <;> omega

/-! ## 10. Unit U81 — ng:circle -/

/-- Glue (proved): display ng:circle-counts, `d_before = d_after + 1` (T-rec-3, `P_addFree`, T-deg-3,
`P_ne_zero`). -/
theorem circle_d (W W' : OWord) (h : IsCircleDeletion W.letters W'.letters) :
    degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram) + 1 := by
  rw [P_addFree _ _ (circle_recordIso_addFree W W' h)]
  exact degAZ_delta_mul (P_ne_zero _)

/-- Glue (proved): "Deleting a separated standard front circle with nonempty remainder preserves B"
(`D_before = D_after + 1`, `w` unchanged, `d_before = d_after + 1`). -/
theorem circle_deletion_B (W W' : OWord) (h : IsCircleDeletion W.letters W'.letters) :
    (realize W).defect = (realize W').defect := by
  have hne := IsCircleDeletion.ne_nil h
  obtain ⟨hD, hw⟩ := circle_counts_syn W W' h
  have hd := circle_d W W' h
  unfold PLFront.defect
  rw [realize_downCount W hne.1, realize_downCount W' hne.2, realize_writhe W hne.1, realize_writhe W' hne.2,
    hd]
  unfold OWord.downCountSyn OWord.writheSyn
  rw [hD, hw]; push_cast; ring

/-- Glue (proved): "A single standard front circle, and any union of such circles, has B = 0": `D = c`
(β2 planarity fact), `w = 0`, `P = δ^{c−1}` (accepted `P_crossingFree`), `deg_a δ^{c−1} = c − 1` (T-deg-2). -/
theorem standard_circles_B (W : OWord) (hstd : (realize W).IsStandardCircles) : (realize W).defect = 0 := by
  have hD : (realize W).downCount = (realize W).Γ.c := by
    by_cases h : W.letters = []
    · rw [realize_nil W h] at hstd ⊢
      exact IsStandardCircles.downCount_eq_c _ _ _ hstd
    · exact realize_downCount_eq_c_of_isStandardCircles W h hstd
  have hw := hstd.writhe_eq_zero
  have hP : P (realize W).diagram = R.delta ^ ((realize W).Γ.c - 1) := P_crossingFree hstd.1
  have hc := (realize W).Γ.hc
  unfold PLFront.defect
  rw [hD, hw, hP, degAZ_delta_pow]
  push_cast [Nat.cast_sub hc]
  ring

/-! ## 11. Unit U82 — ng:cusp-skein -/

/-- The data one principal direction of the interchange supplies for the earlier branch `A` (sm-3:2091-2099
"Exchanging over and under at that crossing makes their local ordered crossing records identical, including
the boundary attachments. After gluing any same actual exterior, the full named records are identical. Thus
their polynomial values are the two crossing choices at one ordinary skein site."; sm-3:2119-2126 the
compatible smoothing): the crossing `x` of the `σ` letter of `A`'s factor, an oriented smoothing `D₀` of
`realize A` at `x` (the block realization of `C` on `BlockSetup.ofEffect` with the effect equalities
`run_skein_A`/`run_skein_A'`/`run_skein_Ctop`/`run_skein_Cbottom`, hence `P D₀ = P (realize C)` by
`P_realizeAt_eq_realize`), the record isomorphism between `realize A'` and the switch of `realize A` at `x`
(T-rec: same exterior visits, the two paths through the block carry one visit each on both sides), and the
sign of `x` as the writhe difference (`sign_crossingOf`). -/
def SkeinSite (A A' C : OWord) : Prop :=
  ∃ (x : (realize A).Γ.Crossing) (D₀ : Diagram),
    IsOrientedSmoothing (realize A).diagram x D₀ ∧ P D₀ = P (realize C).diagram ∧
    Nonempty (RecordIso (realize A').diagram.record ((realize A).diagram.switch x).record) ∧
    ((realize A).diagram.sign x : ℤ) = (realize A).writhe - (realize C).writhe

/-- LEAF U82-1: the site for the printed direction (`A = l_{m+1} σ_m`, `A' = l_m σ_{m+1}`; two smoothing
sites `C_top`/`C_bottom` by the (t,u) table). -/
theorem skein_site (A A' C : OWord) (h : IsCuspSkeinStep A.letters A'.letters C.letters) : SkeinSite A A' C :=
  sorry

/-- LEAF U82-2 (sm-3:2164-2166 "Reflected and right-cusp templates follow by relabeling their actual
attachments and arrows in this local calculation"): the site for the other principal direction — here the
earlier branch `A` carries the factor `l_m σ_{m+1}` and `A'` the factor `l_{m+1} σ_m`; the crossing `x` is
the `σ_{m+1}` of `A`; again two smoothing sites. -/
theorem skein_site_refl (A A' C : OWord) (h : IsCuspSkeinStep A'.letters A.letters C.letters) :
    SkeinSite A A' C := sorry

/-- Glue (proved): display ng:skein-defect for the earlier branch `A` from a site, the counts and the degree
inequalities (sm-3:2127-2163). -/
theorem skein_B_of_site (A A' C : OWord) (hne : A.letters ≠ [] ∧ A'.letters ≠ [] ∧ C.letters ≠ [])
    (hcounts : A.letters.downCountFrom [] = C.letters.downCountFrom [] ∧
      A'.letters.downCountFrom [] = C.letters.downCountFrom [] ∧
      ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ A.letters.writheFrom [] = C.letters.writheFrom [] + σ ∧
        A'.letters.writheFrom [] = C.letters.writheFrom [] - σ)
    (hs : SkeinSite A A' C) :
    min (realize A').defect (realize C).defect ≤ (realize A).defect := by
  obtain ⟨hDA, hDA', σ, hσ, hwA, hwA'⟩ := hcounts
  obtain ⟨x, D₀, hsm, hPC, hrec, hsign⟩ := hs
  have hPA' : P (realize A').diagram = P ((realize A).diagram.switch x) := presentations _ _ hrec
  have hDA₁ := realize_downCount A hne.1
  have hDA'₁ := realize_downCount A' hne.2.1
  have hDC₁ := realize_downCount C hne.2.2
  have hwA₁ := realize_writhe A hne.1
  have hwA'₁ := realize_writhe A' hne.2.1
  have hwC₁ := realize_writhe C hne.2.2
  unfold OWord.downCountSyn OWord.writheSyn at *
  have hdsw : degAZ (P ((realize A).diagram.switch x)) = degAZ (P (realize A').diagram) := by rw [hPA']
  have hd0 : degAZ (P D₀) = degAZ (P (realize C).diagram) := by rw [hPC]
  unfold PLFront.defect
  rcases hσ with rfl | rfl
  · have hpos : (realize A).diagram.IsPositive x := by
      refine ((realize A).diagram.isPositive_iff_sign_eq_one x).2 ?_
      rcases (realize A).diagram.sign_eq_one_or_neg_one x with h1 | h1
      · exact h1
      · exfalso; rw [h1] at hsign; simp at hsign; omega
    have e := P_recursion_pos hsm hpos
    have hle := degAZ_skein_pos (P_ne_zero _) (P_ne_zero _) (P_ne_zero _) e
    rw [hdsw, hd0] at hle
    omega
  · have hneg : ¬ (realize A).diagram.IsPositive x := by
      intro hp
      have h1 := ((realize A).diagram.isPositive_iff_sign_eq_one x).1 hp
      rw [h1] at hsign; simp at hsign; omega
    have e := P_recursion_neg hsm hneg
    have hle := degAZ_skein_neg (P_ne_zero _) (P_ne_zero _) (P_ne_zero _) e
    rw [hdsw, hd0] at hle
    omega

/-- Glue (proved): "For either principal direction". -/
theorem skein_B (A A' C : OWord) (h : Skein A A' C) :
    min (realize A').defect (realize C).defect ≤ (realize A).defect := by
  rcases h with h | h
  · exact skein_B_of_site A A' C (IsCuspSkeinStep.ne_nil h) (skein_counts_syn A A' C h) (skein_site A A' C h)
  · obtain ⟨h1, h2, h3⟩ := IsCuspSkeinStep.ne_nil h
    obtain ⟨hDA', hDA, σ, hσ, hwA', hwA⟩ := skein_counts_syn A' A C h
    refine skein_B_of_site A A' C ⟨h2, h1, h3⟩ ⟨hDA, hDA', -σ, ?_, by omega, by omega⟩ (skein_site_refl A A' C h)
    omega

/-- Glue (proved): the two `s` clauses (β1 `IsCuspSkein.sCount`, β2 `realize_sCount`). -/
theorem skein_s (A A' C : OWord) (h : Skein A A' C) :
    (realize C).sCount + 1 = (realize A).sCount ∧ (realize A').sCount = (realize A).sCount := by
  have hne : A.letters ≠ [] ∧ A'.letters ≠ [] ∧ C.letters ≠ [] := by
    rcases h with h | h
    · exact IsCuspSkeinStep.ne_nil h
    · obtain ⟨h1, h2, h3⟩ := IsCuspSkeinStep.ne_nil h; exact ⟨h2, h1, h3⟩
  rw [realize_sCount A hne.1, realize_sCount A' hne.2.1, realize_sCount C hne.2.2]
  obtain ⟨h1, h2⟩ := IsCuspSkein.sCount h
  exact ⟨h2, h1⟩

/-! ## 12. Unit U83 — assembly: the laws, the word bound, the printed bound -/

/-- The seven laws of `Moves.Laws` for the word moves with `s`, `B` read on the realizations and the axiom's
syntactic base, from the row bundles (rows 76-82) and β2's `s`-laws. -/
theorem certificate_laws (h76 : NgCommutationData) (h77 : NgFrontIData) (h78 : NgFrontIIData)
    (h79 : NgFrontIIIData) (h80 : NgDeletionsData) (h81 : NgCircleData) (h82 : NgCuspSkeinData) :
    (wordMovesOf (fun W => (realize W).sCount) (fun W => (realize W).defect) OWord.IsStandardCircleBase).Laws where
  pres_B F F' h := by
    rcases h with h | h | h | h
    · exact h76.commutation_B F F' h
    · exact h77.typeI_B F F' h
    · exact h78.typeII_B F F' h
    · exact h79.typeIII_B F F' h
  pres_s F F' h := wordMoves_pres_s F F' h
  del_B F F' h := by
    rcases h with h | h | h
    · exact h80.zigzag_B F F' h
    · exact h80.crossedCusp_B F F' h
    · exact (h81.circle_deletion_B F F' h).symm.le
  del_s F F' h := wordMoves_del_s F F' h
  skein_B F F' C h := h82.skein_B F F' C h
  skein_s F F' C h := wordMoves_skein_s F F' C h
  base_B F hF := by
    show 0 ≤ (realize F).defect
    rw [h81.standard_circles_B F (realize_isStandardCircles_of_base F hF)]

/-- ng:local-front-bound on words (sm-3:2313-2343, the strong induction on `s` along the principal chains of
`SM.ng_finite_word`): `B(realize W) ≥ 0`.  Consumes the axiom through `ng_finite_word_bound`. -/
theorem word_bound (h76 : NgCommutationData) (h77 : NgFrontIData) (h78 : NgFrontIIData)
    (h79 : NgFrontIIIData) (h80 : NgDeletionsData) (h81 : NgCircleData) (h82 : NgCuspSkeinData) (W : OWord) :
    (realize W).writhe - ((realize W).downCount : ℤ) ≤ -degAZ (P (realize W).diagram) - 1 := by
  have h0 := ng_finite_word_bound _ _ (certificate_laws h76 h77 h78 h79 h80 h81 h82) W
  unfold PLFront.defect at h0
  omega

/-- The printed clause from the word bound and the representation clause of row 76 (FINAL `localFrontBound_of`):
`P_{S(F)} = P_{realize W}` by rp:record-polynomial (`presentations`), `D`, `w` equal. -/
theorem front_bound_of_word_bound (hrep : ∀ F : SmoothFront, ∃ W : OWord,
      F.sCount = (realize W).sCount ∧ F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧
        ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record))
    (hw : ∀ W : OWord, (realize W).writhe - ((realize W).downCount : ℤ) ≤ -degAZ (P (realize W).diagram) - 1)
    (F : SmoothFront) (S : Diagram) (hS : F.IsRounding S) :
    F.writhe - (F.downCount : ℤ) ≤ -degAZ (P S) - 1 := by
  obtain ⟨W, -, hD, hwr, hrec⟩ := hrep F
  rw [presentations _ _ (hrec S hS), hD, hwr]
  exact hw W

end FrontRows

open FrontRows

/-! ## 13. The eight rows, assembled -/

/-- **ng:commutation** (row 76). -/
theorem ng_commutation : NgCommutationData where
  commutation := comm_counts_and_P
  commutation_B W W' h := by
    obtain ⟨hD, hw, -⟩ := comm_counts_and_P W W' h
    exact defect_eq_of_counts hD hw (presentations _ _ (comm_recordIso W W' h))
  deformation _ _ h := h.counts_eq
  deformation_B _ _ h := defect_eq_of_counts h.downCount_eq h.writhe_eq h.P_eq
  representation := representation_by_word

/-- **ng:front-I** (row 77). -/
theorem ng_front_I : NgFrontIData where
  typeI_B W W' h := by
    obtain ⟨hD, hw⟩ := typeI_counts W W' h
    have hP := typeI_P W W' h
    unfold PLFront.defect
    rw [hD, hw, hP]; push_cast; ring

/-- **ng:front-II** (row 78). -/
theorem ng_front_II : NgFrontIIData where
  typeII W W' h := by
    have hne := IsTypeII.ne_nil h
    obtain ⟨hD, hw⟩ := realize_counts_eq_of_syn hne.1 hne.2 (typeII_counts_syn W W' h)
    exact ⟨hD, hw, by rw [typeII_P W W' h]⟩
  typeII_B W W' h := by
    have hne := IsTypeII.ne_nil h
    obtain ⟨hD, hw⟩ := realize_counts_eq_of_syn hne.1 hne.2 (typeII_counts_syn W W' h)
    exact defect_eq_of_counts hD hw (typeII_P W W' h)

/-- **ng:front-III** (row 79). -/
theorem ng_front_III : NgFrontIIIData where
  typeIII W W' h := by
    have hne := IsTypeIII.ne_nil h
    obtain ⟨hD, hw⟩ := realize_counts_eq_of_syn hne.1 hne.2 (typeIII_counts_syn W W' h)
    exact ⟨hD, hw, by rw [typeIII_P W W' h]⟩
  typeIII_B W W' h := by
    have hne := IsTypeIII.ne_nil h
    obtain ⟨hD, hw⟩ := realize_counts_eq_of_syn hne.1 hne.2 (typeIII_counts_syn W W' h)
    exact defect_eq_of_counts hD hw (typeIII_P W W' h)

/-- **ng:deletions** (row 80). -/
theorem ng_deletions : NgDeletionsData where
  zigzag_s := zigzag_s
  zigzag_B := zigzag_B
  crossedCusp_s := crossedCusp_s
  crossedCusp_B := crossedCusp_B

/-- **ng:circle** (row 81). -/
theorem ng_circle : NgCircleData where
  circle_deletion_B := circle_deletion_B
  standard_circles_B := standard_circles_B

/-- **ng:cusp-skein** (row 82). -/
theorem ng_cusp_skein : NgCuspSkeinData where
  skein_B := skein_B
  smoothing_s A A' C h := (skein_s A A' C h).1
  principal_s A A' C h := (skein_s A A' C h).2

/-- **ng:local-front-bound** (row 83). -/
theorem ng_local_front_bound : NgLocalFrontBoundData where
  on_words := word_bound ng_commutation ng_front_I ng_front_II ng_front_III ng_deletions ng_circle ng_cusp_skein
  on_fronts := front_bound_of_word_bound ng_commutation.representation
    (word_bound ng_commutation ng_front_I ng_front_II ng_front_III ng_deletions ng_circle ng_cusp_skein)

end

end SM
