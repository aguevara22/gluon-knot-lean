import SM.LinkDiagram
import SM.LinkRecord

/-! Chapter-3 representation layer, module LinkDiagramRecord: the bridge from polygonal diagrams to crossing records (Diagram.record: per-component cyclic successor of visits, twin pairing, over bits, signs), its sanity laws (writhe, crossing count), the switch and restrict bridges (RecordIso), IsRealizable, the one-polygon agreement with the accepted Gauss data (record_of_single_polygon), the cyclic-order equivalence of def:gauss-record, and the statement of the PL-extension clause. Implements the design adopted 2026-09-13
(work/reports/design-decision-diagram-record-20260913.md). Written 2026-09-13 by a Claude Code implementer subagent of the pod executor
(workflow implement-diagram-layer-phase2), checked with `lake env lean` (sorry-free, standard axioms) and ported verbatim from
work/drafts/LinkDiagramRecord.lean (only this header added and #print lines removed). Declarations live in `SM.Link`. -/

/-! # The crossing record of a polygonal oriented link diagram (`Diagram.record`)

Chapter-3 representation layer, module LinkDiagramRecord: the bridge from the diagram type of
`SM.LinkDiagram` to the combinatorial records of `SM.LinkRecord`.  Design:
work/reports/design-decision-diagram-record-20260913.md, section `record_type`, with the judges'
grafts (c) `record_of_single_polygon` and (d) `IsRealizable`.

Source: reference/SM/sm-3-statesum.tex, frame SM15, def:gauss-record (352-372) read through the
named-record bridge paragraph (337-351).  Printed words rendered here:

sm-3:349-351 "The named record defined next (crossing occurrences, successor, pairing, over/under
bits and signs) is what this section and Section knotlaws call the crossing record of a diagram."

sm-3:353-360 "Let γ : C → S² be an actual generic immersion of an oriented circle in an oriented
sphere, with over/under choices at its transverse double points. Its finite crossing-occurrence
set M has forward successor s, pairing involution τ without fixed points, an over/under bit at
each occurrence, and crossing signs σ(c) = sgn det(u_{c,O}, u_{c,U})."

sm-3:361-365 "A named record isomorphism is a bijection Φ : M → M' preserving successor, pairing,
over/under bits and these signs. The parametrizing circles are oriented; the finite bijection must
preserve their cyclic orders. It does not prescribe a map at every unmarked parameter and does not
permit traversal reversal."

sm-3:365-369 "After a finite subdivision we choose an orientation-preserving piecewise-linear
circle map Φ̄ : C → C' extending Φ: on each interval between successive marked points use the
positive affine map in oriented interval coordinates. If M is empty, choose any positive circle
parametrization."

What is definitional and what is a lemma (decision 6 of the design record): the data `(M, s, τ,
bits, σ)` and the notion of named record isomorphism are definitions (`Record`, `Diagram.record`,
`RecordIso`); "must preserve their cyclic orders ... does not permit traversal reversal" is the
content of successor preservation on an oriented finite mark set, proved as the equivalence
theorems of section G below; the PL extension Φ̄ is a construction on top of the finite data,
stated as the proposition `recordIso_extend_statement` (section H) and not part of the data.

The record is defined for every diagram (every component count), as rp:record-polynomial
(sm-3:1215-1229), lc:presentations (1306-1318) and mp:join (1370-1385) require; def:gauss-record's
own statement is the case `c = 1`, for which `record_of_single_polygon` (section F) checks the
successor and pairing against the accepted one-polygon Gauss-word data (`nextGaussVisit`,
`Carrier.visitTwin`).

Sections: A cyclic successors on real keys; B the per-component successor `nextVisit`/`visitSucc`;
C pairing, bits, `Diagram.record` and its sanity lemmas; D the switch bridge `switch_record`;
E `IsRealizable`; F the `c = 1` agreement theorem; G the cyclic-order equivalence; H the PL
extension statement (open); I the block-restriction bridge statement; J its proof
(`restrict_record`).

Every declaration lives in `SM.Link`; nothing here is an axiom; the file ends with
`#print axioms` for the main theorems. -/

namespace SM.Link

open SM Equiv

noncomputable section

/-! ## A. Cyclic successors on a finite set of real keys

The forward successor of def:gauss-record is "the next occurrence along the oriented parametrizing
circle".  On a component whose occurrences have pairwise distinct traversal keys in `[0, k)`, the
next occurrence after `v` is characterised by: it is not `v` (unless `v` is alone on its circle)
and no occurrence of the circle lies strictly between `v` and it in the oriented cyclic order.  This
section proves the uniqueness half of that characterisation and a list lemma used for the
"not `v`" half. -/

/-- Strict oriented cyclic betweenness of three real coordinates on a circle cut open at `0`
(the key form of the accepted `traversalBetween` of def:gauss): `b` lies strictly after `a` and
strictly before `c` going forward from `a`.  This is the "cyclic order" of the oriented
parametrizing circles in def:gauss-record (sm-3:361-362). -/
def cycBetween (a b c : ℝ) : Prop :=
  (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b)

theorem traversalBetween_iff_cycBetween {n : ℕ} (p q r : TraversalPoint n) :
    traversalBetween p q r ↔ cycBetween (traversalKey p) (traversalKey q) (traversalKey r) :=
  Iff.rfl

theorem not_cycBetween_self_right (a b : ℝ) : ¬ cycBetween a b a := by
  unfold cycBetween
  intro h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

theorem not_cycBetween_self_left (a c : ℝ) : ¬ cycBetween a a c := by
  unfold cycBetween
  intro h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

theorem not_cycBetween_self_mid (a b : ℝ) : ¬ cycBetween a b b := by
  unfold cycBetween
  intro h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

/-- Uniqueness of the cyclic successor on the set `p`: two `p`-elements `w₁ ≠ v`, `w₂ ≠ v` with no
`p`-element strictly between `v` and either of them coincide (keys injective on `p`). -/
theorem cycNext_unique_on {α : Type*} {p : α → Prop} {k : α → ℝ}
    (hk : ∀ a b, p a → p b → k a = k b → a = b) {v w₁ w₂ : α} (hv : p v) (hw₁ : p w₁) (hw₂ : p w₂)
    (h₁ : w₁ ≠ v) (h₂ : w₂ ≠ v) (n₁ : ∀ u, p u → ¬ cycBetween (k v) (k u) (k w₁))
    (n₂ : ∀ u, p u → ¬ cycBetween (k v) (k u) (k w₂)) : w₁ = w₂ := by
  by_contra hne
  have hv1 : k v ≠ k w₁ := fun h => h₁ (hk _ _ hw₁ hv h.symm)
  have hv2 : k v ≠ k w₂ := fun h => h₂ (hk _ _ hw₂ hv h.symm)
  have h12 : k w₁ ≠ k w₂ := fun h => hne (hk _ _ hw₁ hw₂ h)
  have a1 := n₁ w₂ hw₂
  have a2 := n₂ w₁ hw₁
  unfold cycBetween at a1 a2
  rcases lt_or_gt_of_ne hv1 with hv1 | hv1 <;> rcases lt_or_gt_of_ne hv2 with hv2 | hv2 <;>
    rcases lt_or_gt_of_ne h12 with h12 | h12 <;>
    first
    | exact a1 (Or.inl ⟨by linarith, by linarith⟩)
    | exact a1 (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact a1 (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
    | exact a2 (Or.inl ⟨by linarith, by linarith⟩)
    | exact a2 (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact a2 (Or.inr (Or.inr ⟨by linarith, by linarith⟩))

/-- Uniqueness of the cyclic successor (keys injective everywhere). -/
theorem cycNext_unique {α : Type*} {k : α → ℝ} (hk : Function.Injective k) {v w₁ w₂ : α}
    (h₁ : w₁ ≠ v) (h₂ : w₂ ≠ v) (n₁ : ∀ u, ¬ cycBetween (k v) (k u) (k w₁))
    (n₂ : ∀ u, ¬ cycBetween (k v) (k u) (k w₂)) : w₁ = w₂ :=
  cycNext_unique_on (p := fun _ => True) (fun _ _ _ _ h => hk h) trivial trivial trivial h₁ h₂
    (fun u _ => n₁ u) (fun u _ => n₂ u)

/-- In a duplicate-free list with at least two entries, the cyclic next entry differs from the
entry. -/
theorem list_next_ne_self {α : Type*} [DecidableEq α] (l : List α) (h : l.Nodup)
    (hl : 2 ≤ l.length) (x : α) (hx : x ∈ l) : l.next x hx ≠ x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.next_getElem l h i hi]
  intro heq
  rw [h.getElem_inj_iff] at heq
  rcases Nat.lt_or_ge (i + 1) l.length with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at heq
    omega
  · have hi1 : i + 1 = l.length := by omega
    rw [hi1, Nat.mod_self] at heq
    omega

/-! ## B. The forward successor of occurrences on a diagram

def:gauss-record (sm-3:355-356): "Its finite crossing-occurrence set M has forward successor s".
For a polygonal diagram the occurrence set is `D.Γ.Visit` (LinkDiagram), each occurrence sits at
the traversal point `D.visitPt v` of its component's parameter circle, and the forward successor is
the next occurrence of the same component in the oriented cyclic order of traversal keys.  The
construction lifts the accepted one-polygon construction (`gaussList` = `Finset.univ.sort` under
the key order, `nextGaussVisit` = `List.next`) to each component: sort the occurrences of component
`i` by `traversalKey (visitPt ·).2` and take the cyclic list successor.  A component carrying a
single occurrence has `succ v = v`. -/

namespace Diagram

variable (D : Diagram)

/-- The component (parametrizing circle) carrying an occurrence: the component of its strand.  This
is the `comp` field of `D.record` (def:gauss-record sm-3:355 "crossing-occurrence set M" on
"the parametrizing circles", sm-3:361-362; rp:record-polynomial sm-3:1220-1221 "The component
bijection must also include all components with no crossing occurrences"). -/
def compOf (v : D.Γ.Visit) : Fin D.Γ.c := v.2.val.1

@[simp] theorem compOf_mk (x : D.Γ.Crossing) (s : {s // s ∈ x.val}) :
    D.compOf ⟨x, s⟩ = s.val.1 := rfl

theorem compOf_eq_visitPt_fst (v : D.Γ.Visit) : D.compOf v = (D.visitPt v).1 := rfl

@[simp] theorem compOf_overVisit (x : D.Γ.Crossing) : D.compOf (D.overVisit x) = (D.overStrand x).1 :=
  rfl

@[simp] theorem compOf_underVisit (x : D.Γ.Crossing) :
    D.compOf (D.underVisit x) = (D.underStrand x).1 := rfl

/-- The traversal coordinate of an occurrence on its component's parameter circle `[0, k)`: the
accepted `traversalKey` of its traversal point (edge label plus crossing parameter).  Occurrences of
one component are ordered cyclically by this coordinate ("The parametrizing circles are oriented",
sm-3:361-362); for `c = 1` it is the accepted `SM.visitKey` (`singleDiagram_visitCoord`). -/
def visitCoord (v : D.Γ.Visit) : ℝ := traversalKey (D.visitPt v).2

theorem visitCoord_nonneg (v : D.Γ.Visit) : 0 ≤ D.visitCoord v := traversalKey_nonneg _

theorem visitCoord_lt (v : D.Γ.Visit) : D.visitCoord v < (D.Γ.comp (D.compOf v)).k :=
  traversalKey_lt_card _

/-- Distinct occurrences of one component have distinct keys (from `visitPt_injective`). -/
theorem visitCoord_injOn {v w : D.Γ.Visit} (hc : D.compOf v = D.compOf w)
    (hk : D.visitCoord v = D.visitCoord w) : v = w := by
  obtain ⟨x, ⟨⟨i, a⟩, hs⟩⟩ := v
  obtain ⟨y, ⟨⟨j, b⟩, ht⟩⟩ := w
  change i = j at hc
  subst hc
  apply D.visitPt_injective
  have h2 : (D.visitPt ⟨x, ⟨⟨i, a⟩, hs⟩⟩).2 = (D.visitPt ⟨y, ⟨⟨i, b⟩, ht⟩⟩).2 :=
    traversalKey_injective hk
  exact Sigma.ext rfl (heq_of_eq h2)

/-- The lexicographic key (component index, traversal coordinate): injective on all occurrences, so
it lifts a linear order to `D.Γ.Visit` whose restriction to each component is the traversal order
along the oriented circle (auxiliary to "forward successor s", sm-3:355). -/
def lexKey (v : D.Γ.Visit) : ℕ ×ₗ ℝ := toLex ((D.compOf v).val, D.visitCoord v)

theorem lexKey_injective : Function.Injective D.lexKey := by
  intro v w h
  have h' : ((D.compOf v).val, D.visitCoord v) = ((D.compOf w).val, D.visitCoord w) := toLex.injective h
  rw [Prod.mk.injEq] at h'
  exact D.visitCoord_injOn (Fin.ext h'.1) h'.2

/-- The auxiliary linear order on occurrences lifted from `lexKey` (component first, then traversal
coordinate), used only to sort each component's occurrences for "forward successor s"
(sm-3:355). -/
@[instance_reducible]
def visitOrder : LinearOrder D.Γ.Visit := LinearOrder.lift' D.lexKey D.lexKey_injective

/-- In the auxiliary order two occurrences of one component compare by traversal key. -/
theorem visitOrder_lt_iff {v w : D.Γ.Visit} (hc : D.compOf v = D.compOf w) :
    (letI := D.visitOrder; v < w) ↔ D.visitCoord v < D.visitCoord w := by
  let _ := D.visitOrder
  change D.lexKey v < D.lexKey w ↔ _
  unfold lexKey
  rw [Prod.Lex.lt_iff]
  simp only [ofLex_toLex, hc, lt_self_iff_false, false_or, true_and]

/-- The occurrences carried by component `i` (the marks of one "parametrizing circle",
sm-3:361-362). -/
def compVisits (i : Fin D.Γ.c) : Finset D.Γ.Visit := Finset.univ.filter (fun v => D.compOf v = i)

theorem mem_compVisits (i : Fin D.Γ.c) (v : D.Γ.Visit) : v ∈ D.compVisits i ↔ D.compOf v = i := by
  simp [compVisits]

/-- The occurrences of component `i` sorted by traversal coordinate (the accepted `gaussList`
pattern of def:gauss, `Finset.univ.sort` under the lifted order, applied to one component); its
cyclic list successor is "forward successor s" (sm-3:355). -/
def compList (i : Fin D.Γ.c) : List D.Γ.Visit :=
  letI := D.visitOrder
  (D.compVisits i).sort

theorem compList_nodup (i : Fin D.Γ.c) : (D.compList i).Nodup := by
  let _ := D.visitOrder
  exact Finset.sort_nodup _ _

theorem mem_compList (i : Fin D.Γ.c) (v : D.Γ.Visit) : v ∈ D.compList i ↔ D.compOf v = i := by
  let _ := D.visitOrder
  rw [compList, Finset.mem_sort, mem_compVisits]

theorem compList_length (i : Fin D.Γ.c) : (D.compList i).length = (D.compVisits i).card := by
  let _ := D.visitOrder
  exact Finset.length_sort _

theorem self_mem_compList (v : D.Γ.Visit) : v ∈ D.compList (D.compOf v) :=
  (D.mem_compList _ v).mpr rfl

/-- "forward successor s" (sm-3:355): the next occurrence of the same component in the cyclic
order of traversal keys (the cyclic list successor of the sorted component list; a component with
one occurrence returns it). -/
def nextVisit (v : D.Γ.Visit) : D.Γ.Visit :=
  (D.compList (D.compOf v)).next v (D.self_mem_compList v)

/-- The backward successor (cyclic list predecessor), the inverse of `nextVisit`; `s⁻¹` in the
smoothing formulas of sm-3:1092-1096. -/
def prevVisit (v : D.Γ.Visit) : D.Γ.Visit :=
  (D.compList (D.compOf v)).prev v (D.self_mem_compList v)

theorem nextVisit_eq (v : D.Γ.Visit) {i : Fin D.Γ.c} (hi : D.compOf v = i) (hv : v ∈ D.compList i) :
    D.nextVisit v = (D.compList i).next v hv := by
  subst hi; rfl

theorem prevVisit_eq (v : D.Γ.Visit) {i : Fin D.Γ.c} (hi : D.compOf v = i) (hv : v ∈ D.compList i) :
    D.prevVisit v = (D.compList i).prev v hv := by
  subst hi; rfl

/-- The successor stays on the component. -/
theorem compOf_nextVisit (v : D.Γ.Visit) : D.compOf (D.nextVisit v) = D.compOf v :=
  (D.mem_compList _ _).mp (List.next_mem _ _ _)

theorem compOf_prevVisit (v : D.Γ.Visit) : D.compOf (D.prevVisit v) = D.compOf v :=
  (D.mem_compList _ _).mp (List.prev_mem _ _ _)

theorem prevVisit_nextVisit (v : D.Γ.Visit) : D.prevVisit (D.nextVisit v) = v := by
  rw [D.prevVisit_eq (D.nextVisit v) (D.compOf_nextVisit v) (List.next_mem _ _ _)]
  exact List.prev_next _ (D.compList_nodup _) v _

theorem nextVisit_prevVisit (v : D.Γ.Visit) : D.nextVisit (D.prevVisit v) = v := by
  rw [D.nextVisit_eq (D.prevVisit v) (D.compOf_prevVisit v) (List.prev_mem _ _ _)]
  exact List.next_prev _ (D.compList_nodup _) v _

/-- The forward successor as a permutation of the occurrence set ("forward successor s"). -/
def visitSucc : Perm D.Γ.Visit where
  toFun := D.nextVisit
  invFun := D.prevVisit
  left_inv := D.prevVisit_nextVisit
  right_inv := D.nextVisit_prevVisit

@[simp] theorem visitSucc_apply (v : D.Γ.Visit) : D.visitSucc v = D.nextVisit v := rfl

@[simp] theorem visitSucc_symm_apply (v : D.Γ.Visit) : D.visitSucc.symm v = D.prevVisit v := rfl

theorem compOf_visitSucc (v : D.Γ.Visit) : D.compOf (D.visitSucc v) = D.compOf v :=
  D.compOf_nextVisit v

/-- The successor advances the sorted index modulo the component's occurrence count. -/
theorem nextVisit_getElem (i : Fin D.Γ.c) (j : ℕ) (hj : j < (D.compList i).length) :
    D.nextVisit ((D.compList i)[j]'hj) =
      (D.compList i)[(j + 1) % (D.compList i).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le j) hj)) := by
  rw [D.nextVisit_eq _ ((D.mem_compList i _).mp (List.getElem_mem hj)) (List.getElem_mem hj)]
  exact List.next_getElem (D.compList i) (D.compList_nodup i) j hj

/-- Every entry of a component's sorted list is reached from its first entry. -/
theorem visitSucc_sameCycle_getElem (i : Fin D.Γ.c) (j : ℕ) (hj : j < (D.compList i).length) :
    D.visitSucc.SameCycle ((D.compList i)[(0 : ℕ)]'(lt_of_le_of_lt (Nat.zero_le j) hj)) ((D.compList i)[j]'hj) := by
  revert hj
  induction j with
  | zero => intro hj; exact Perm.SameCycle.refl _ _
  | succ j ih =>
    intro hj
    have hj' : j < (D.compList i).length := (Nat.lt_succ_self j).trans hj
    have hc := Perm.sameCycle_apply_right.mpr (ih hj')
    rw [visitSucc_apply, D.nextVisit_getElem i j hj'] at hc
    simpa only [Nat.mod_eq_of_lt hj] using hc

/-- One successor cycle per component ("forward successor" along one oriented circle): two
occurrences of the same component lie on one cycle of `visitSucc`. -/
theorem visitSucc_sameCycle {v w : D.Γ.Visit} (h : D.compOf v = D.compOf w) :
    D.visitSucc.SameCycle v w := by
  obtain ⟨j, hj, hv⟩ := List.getElem_of_mem (D.self_mem_compList v)
  obtain ⟨k, hk, hw⟩ := List.getElem_of_mem ((D.mem_compList (D.compOf v) w).mpr h.symm)
  rw [← hv, ← hw]
  exact (D.visitSucc_sameCycle_getElem _ j hj).symm.trans (D.visitSucc_sameCycle_getElem _ k hk)

/-- No occurrence of the component lies strictly between an occurrence and its successor in the
oriented cyclic order of traversal keys (the accepted `sorted_next_no_cyclic_between`, lifted). -/
theorem nextVisit_no_between (v u : D.Γ.Visit) (hu : D.compOf u = D.compOf v) :
    ¬ cycBetween (D.visitCoord v) (D.visitCoord u) (D.visitCoord (D.nextVisit v)) := by
  classical
  let d : DecidableEq D.Γ.Visit := inferInstance
  let _ := D.visitOrder
  have hnext : @List.next D.Γ.Visit d (D.compVisits (D.compOf v)).sort v
      ((Finset.mem_sort _).mpr ((D.mem_compVisits _ v).mpr rfl)) = D.nextVisit v := rfl
  have hd : d = (fun a b : D.Γ.Visit => LinearOrder.toDecidableEq a b) := Subsingleton.elim _ _
  rw [hd] at hnext
  have hg := sorted_next_no_cyclic_between (D.compVisits (D.compOf v))
    ((D.mem_compVisits _ v).mpr rfl) ((D.mem_compVisits _ _).mpr (D.compOf_nextVisit v)) hnext u
    ((D.mem_compVisits _ u).mpr hu)
  have e1 := D.visitOrder_lt_iff (v := v) (w := u) hu.symm
  have e2 := D.visitOrder_lt_iff (v := u) (w := D.nextVisit v) (hu.trans (D.compOf_nextVisit v).symm)
  have e3 := D.visitOrder_lt_iff (v := D.nextVisit v) (w := v) (D.compOf_nextVisit v)
  unfold cycBetween
  rw [e1, e2, e3] at hg
  exact hg

/-- The successor differs from the occurrence unless the occurrence is alone on its component. -/
theorem nextVisit_ne_self (v w : D.Γ.Visit) (hw : D.compOf w = D.compOf v) (hne : w ≠ v) :
    D.nextVisit v ≠ v := by
  apply list_next_ne_self _ (D.compList_nodup _)
  have h1 : v ∈ D.compList (D.compOf v) := D.self_mem_compList v
  have h2 : w ∈ D.compList (D.compOf v) := (D.mem_compList _ w).mpr hw
  have hpos := List.length_pos_of_mem h1
  rcases Nat.lt_or_ge (D.compList (D.compOf v)).length 2 with hlt | hge
  · exfalso
    have hlen : (D.compList (D.compOf v)).length = 1 := by omega
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
    rw [ha, List.mem_singleton] at h1 h2
    exact hne (h2.trans h1.symm)
  · exact hge

/-- An occurrence alone on its component is its own successor ("a component with a single
occurrence has `succ v = v`"). -/
theorem nextVisit_eq_self (v : D.Γ.Visit) (h : ∀ w, D.compOf w = D.compOf v → w = v) :
    D.nextVisit v = v := by
  have hl : D.compList (D.compOf v) = [v] := by
    have hsub : ∀ w ∈ D.compList (D.compOf v), w = v := fun w hw => h w ((D.mem_compList _ w).mp hw)
    have hmem := D.self_mem_compList v
    obtain ⟨j, hj, hv⟩ := List.getElem_of_mem hmem
    have hlen : (D.compList (D.compOf v)).length = 1 := by
      have hnd := D.compList_nodup (D.compOf v)
      by_contra hne
      have h2 : 2 ≤ (D.compList (D.compOf v)).length := by omega
      have hne' := list_next_ne_self _ hnd h2 v hmem
      exact hne' (hsub _ (List.next_mem _ _ _))
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
    rw [ha] at hmem ⊢
    rw [List.mem_singleton] at hmem
    rw [hmem]
  have key : ∀ (l : List D.Γ.Visit) (hl' : l = [v]) (hv : v ∈ l), l.next v hv = v := by
    rintro l rfl hv
    exact List.next_singleton v v hv
  exact key _ hl _

theorem nextVisit_eq_self_iff (v : D.Γ.Visit) :
    D.nextVisit v = v ↔ ∀ w, D.compOf w = D.compOf v → w = v := by
  constructor
  · intro h w hw
    by_contra hne
    exact D.nextVisit_ne_self v w hw hne h
  · exact D.nextVisit_eq_self v

end Diagram

/-! ## C. Pairing, bits, signs: the crossing record of a diagram

def:gauss-record (sm-3:355-360): "pairing involution τ without fixed points, an over/under bit at
each occurrence, and crossing signs σ(c) = sgn det(u_{c,O}, u_{c,U})". -/

namespace Diagram

variable (D : Diagram)

/-- "pairing involution τ" (sm-3:355-356): the other occurrence of the same double point — the same
crossing with its other strand.  Multi-component copy of the accepted `Carrier.visitTwin`. -/
def twin (v : D.Γ.Visit) : D.Γ.Visit := ⟨v.1, ⟨D.Γ.other v.1 v.2.2, D.Γ.other_mem v.1 v.2.2⟩⟩

@[simp] theorem twin_fst (v : D.Γ.Visit) : (D.twin v).1 = v.1 := rfl

theorem twin_strand (v : D.Γ.Visit) : (D.twin v).2.val = D.Γ.other v.1 v.2.2 := rfl

/-- "without fixed points". -/
theorem twin_ne (v : D.Γ.Visit) : D.twin v ≠ v := fun h =>
  D.Γ.other_ne v.1 v.2.2 (congrArg (fun w : D.Γ.Visit => w.2.val) h)

/-- "involution". -/
theorem twin_twin (v : D.Γ.Visit) : D.twin (D.twin v) = v := by
  obtain ⟨x, s, hs⟩ := v
  show (⟨x, ⟨D.Γ.other x (D.Γ.other_mem x hs), _⟩⟩ : D.Γ.Visit) = ⟨x, ⟨s, hs⟩⟩
  exact congrArg (fun t : {s // s ∈ x.val} => (⟨x, t⟩ : D.Γ.Visit))
    (Subtype.ext (D.Γ.other_other x hs))

/-- The two occurrences of a crossing are an occurrence and its twin. -/
theorem eq_or_eq_twin (v w : D.Γ.Visit) (h : w.1 = v.1) : w = v ∨ w = D.twin v := by
  obtain ⟨x, s, hs⟩ := v
  obtain ⟨y, t, ht⟩ := w
  change y = x at h
  subst h
  rcases (D.Γ.mem_iff_eq_or_other y hs t).mp ht with h | h
  · left
    exact congrArg (fun t : {s // s ∈ y.val} => (⟨y, t⟩ : D.Γ.Visit)) (Subtype.ext h)
  · right
    exact congrArg (fun t : {s // s ∈ y.val} => (⟨y, t⟩ : D.Γ.Visit)) (Subtype.ext h)

theorem twin_unique (v w : D.Γ.Visit) (h : w.1 = v.1) (hne : w ≠ v) : w = D.twin v :=
  (D.eq_or_eq_twin v w h).resolve_left hne

theorem mem_pair_twin_iff (v w : D.Γ.Visit) :
    w ∈ ({v, D.twin v} : Finset D.Γ.Visit) ↔ w.1 = v.1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · rfl
    · rfl
  · exact D.eq_or_eq_twin v w

@[simp] theorem twin_overVisit (x : D.Γ.Crossing) : D.twin (D.overVisit x) = D.underVisit x := rfl

@[simp] theorem twin_underVisit (x : D.Γ.Crossing) : D.twin (D.underVisit x) = D.overVisit x := by
  rw [← twin_overVisit, twin_twin]

/-- The pairing involution as a permutation ("pairing involution τ"). -/
def pairPerm : Perm D.Γ.Visit where
  toFun := D.twin
  invFun := D.twin
  left_inv := D.twin_twin
  right_inv := D.twin_twin

@[simp] theorem pairPerm_apply (v : D.Γ.Visit) : D.pairPerm v = D.twin v := rfl

/-- "an over/under bit at each occurrence" (sm-3:356-357): `true` when the occurrence's strand is
the chosen over strand of its double point (the decidable form of the accepted `D.isOver`). -/
def overBit (v : D.Γ.Visit) : Bool := decide (v.2.val = D.overStrand v.1)

theorem overBit_eq_true_iff (v : D.Γ.Visit) : D.overBit v = true ↔ D.isOver v := decide_eq_true_iff

@[simp] theorem overBit_overVisit (x : D.Γ.Crossing) : D.overBit (D.overVisit x) = true :=
  decide_eq_true rfl

@[simp] theorem overBit_underVisit (x : D.Γ.Crossing) : D.overBit (D.underVisit x) = false :=
  decide_eq_false (D.under_ne_over x)

/-- The two occurrences of a crossing carry opposite bits. -/
theorem overBit_twin (v : D.Γ.Visit) : D.overBit (D.twin v) = !D.overBit v := by
  rcases D.visit_eq_over_or_under v with h | h <;> rw [h]
  · rw [twin_overVisit, overBit_underVisit, overBit_overVisit]; rfl
  · rw [twin_underVisit, overBit_overVisit, overBit_underVisit]; rfl

/-- The crossing record of a polygonal oriented link diagram (def:gauss-record, sm-3:352-360, for
every component count; the row's statement is the case `c = 1`):
* `comps := Fin c` — the parametrizing circles, crossing-free ones included;
* `M := D.Γ.Visit` — "Its finite crossing-occurrence set M";
* `comp` — the component of the occurrence's strand;
* `succ := visitSucc` — "forward successor s", the next occurrence of the same component in the
  oriented cyclic order of traversal keys (`nextVisit`);
* `pair := pairPerm` — "pairing involution τ without fixed points", the twin occurrence;
* `isOver := overBit` — "an over/under bit at each occurrence";
* `sgn v := D.sign v.1` — "crossing signs σ(c) = sgn det(u_{c,O}, u_{c,U})" (eq:gauss-cross-sign,
  with `Diagram.sign` the sign of `det(u_o, u_u)` on the over/under edge vectors), stored on both
  occurrences of the crossing.
The definition is reducible (`abbrev`) so that `D.record.M` unfolds to `D.Γ.Visit` for the
rewriting tactics of the consumer rows. -/
abbrev record : Record where
  comps := Fin D.Γ.c
  M := D.Γ.Visit
  comp := D.compOf
  succ := D.visitSucc
  pair := D.pairPerm
  isOver := D.overBit
  sgn := fun v => D.sign v.1
  succ_comp := D.compOf_visitSucc
  succ_cycle := fun _ _ h => D.visitSucc_sameCycle h
  pair_ne := D.twin_ne
  pair_invol := D.twin_twin
  bit_pair := D.overBit_twin
  sgn_pair := fun _ => rfl
  sgn_ne := fun v => D.sign_ne_zero v.1

/-! ### Sanity lemmas pinning the record's data -/

@[simp] theorem record_comps : D.record.comps = Fin D.Γ.c := rfl
@[simp] theorem record_M : D.record.M = D.Γ.Visit := rfl
theorem record_comp (v : D.Γ.Visit) : D.record.comp v = D.compOf v := rfl
theorem record_succ : D.record.succ = D.visitSucc := rfl
theorem record_succ_apply (v : D.Γ.Visit) : D.record.succ v = D.nextVisit v := rfl
theorem record_pair : D.record.pair = D.pairPerm := rfl
theorem record_pair_apply (v : D.Γ.Visit) : D.record.pair v = D.twin v := rfl
theorem record_isOver (v : D.Γ.Visit) : D.record.isOver v = D.overBit v := rfl
theorem record_sgn (v : D.Γ.Visit) : D.record.sgn v = D.sign v.1 := rfl

/-- The bit is the accepted `isOver` predicate. -/
theorem record_isOver_iff (v : D.Γ.Visit) : D.record.isOver v = true ↔ D.isOver v :=
  D.overBit_eq_true_iff v

/-- The stored sign is `1` exactly at positive crossings (def:positive-lift's convention). -/
theorem record_isPositive_iff (v : D.Γ.Visit) : D.record.IsPositive v ↔ D.IsPositive v.1 :=
  (D.isPositive_iff_sign_eq_one v.1).symm

/-- The record's component count is the diagram's `c`. -/
theorem record_componentCount : D.record.componentCount = D.componentCount := Fintype.card_fin _

/-- Two occurrences per crossing. -/
theorem card_visit_eq_two_mul : Fintype.card D.Γ.Visit = 2 * Fintype.card D.Γ.Crossing := by
  classical
  have h : Fintype.card (Σ x : D.Γ.Crossing, {s // s ∈ x.val}) = 2 * Fintype.card D.Γ.Crossing := by
    rw [Fintype.card_sigma]
    have h : ∀ x : D.Γ.Crossing, Fintype.card {s // s ∈ x.val} = 2 := fun x => by
      rw [Fintype.card_coe]; exact D.Γ.crossing_card_two x
    simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  exact (Fintype.card_congr (Equiv.refl _)).trans h

theorem record_card_M : Fintype.card D.record.M = 2 * Fintype.card D.Γ.Crossing := D.card_visit_eq_two_mul

/-- The record's crossing count is the number of double points. -/
theorem record_crossingCount : D.record.crossingCount = Fintype.card D.Γ.Crossing := by
  unfold Record.crossingCount
  rw [D.record_card_M]
  omega

/-- The sum of the signs over the over-occurrences is the sum over the crossings. -/
theorem sum_over_sign :
    ∑ v ∈ (Finset.univ : Finset D.Γ.Visit).filter (fun v => D.overBit v = true), (D.sign v.1 : ℤ) =
      ∑ x : D.Γ.Crossing, (D.sign x : ℤ) := by
  refine Finset.sum_nbij' (fun v => v.1) (fun x => D.overVisit x) ?_ ?_ ?_ ?_ ?_
  · intro v _; exact Finset.mem_univ _
  · intro x _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact D.overBit_overVisit x
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rcases D.visit_eq_over_or_under v with h | h
    · exact h.symm
    · exfalso
      rw [h, D.overBit_underVisit] at hv
      exact Bool.false_ne_true hv
  · intro x _; rfl
  · intro v _; rfl

/-- The record's writhe (half the sum of stored signs) is the diagram's writhe (def:positive-lift,
"the sum of crossing signs"). -/
theorem record_writhe : D.record.writhe = D.writhe := by
  rw [Record.writhe_eq_sum_over]
  exact D.sum_over_sign

/-- A self crossing of the record is a crossing whose two strands lie on one component. -/
theorem record_isSelfCrossing_iff (v : D.Γ.Visit) :
    D.record.IsSelfCrossing v ↔ (v.2.val).1 = (D.Γ.other v.1 v.2.2).1 := Iff.rfl

/-- The record's successor of an occurrence has no occurrence of its component strictly between
them (cyclic order of traversal keys), pinning `succ` as "the next occurrence along the circle". -/
theorem record_succ_no_between (v u : D.Γ.Visit) (hu : D.record.comp u = D.record.comp v) :
    ¬ cycBetween (D.visitCoord v) (D.visitCoord u) (D.visitCoord (D.record.succ v)) :=
  D.nextVisit_no_between v u hu

theorem record_succ_eq_self_iff (v : D.Γ.Visit) :
    D.record.succ v = v ↔ ∀ w, D.record.comp w = D.record.comp v → w = v :=
  D.nextVisit_eq_self_iff v

end Diagram

/-! ## D. The switch bridge: `record (switch D x) ≅ (record D).switch v`

lp:lm (sm-3:939-940) "order of required crossing switches"; rp:record-polynomial's induction uses
that the record of `D^{sw}` is the record of `D` with the two bits of the switched crossing flipped
and its sign negated (`Record.switch`).  On the diagram side the switch keeps the shadow, hence
every occurrence, traversal point, successor and pairing, definitionally. -/

namespace Diagram

variable (D : Diagram) (x₀ : D.Γ.Crossing)

theorem switch_visitPt : (D.switch x₀).visitPt = D.visitPt := rfl

theorem switch_compOf : (D.switch x₀).compOf = D.compOf := rfl

theorem switch_visitCoord : (D.switch x₀).visitCoord = D.visitCoord := rfl

theorem switch_nextVisit : (D.switch x₀).nextVisit = D.nextVisit := rfl

theorem switch_visitSucc : (D.switch x₀).visitSucc = D.visitSucc := rfl

theorem switch_twin : (D.switch x₀).twin = D.twin := rfl

/-- At the switched crossing both bits flip. -/
theorem switch_overBit_self (w : D.Γ.Visit) (hw : w.1 = x₀) :
    (D.switch x₀).overBit w = !D.overBit w := by
  subst hw
  rcases (D.mem_iff w.1 w.2.val).mp w.2.2 with h | h
  · have e1 : (D.switch w.1).overBit w = false :=
      decide_eq_false fun heq =>
        D.over_ne_under w.1 (h.symm.trans (heq.trans (D.switch_overStrand_self w.1)))
    have e2 : D.overBit w = true := decide_eq_true h
    rw [e1, e2]; rfl
  · have e1 : (D.switch w.1).overBit w = true :=
      decide_eq_true (h.trans (D.switch_overStrand_self w.1).symm)
    have e2 : D.overBit w = false :=
      decide_eq_false fun heq => D.under_ne_over w.1 (h.symm.trans heq)
    rw [e1, e2]; rfl

/-- Away from the switched crossing the bits are unchanged. -/
theorem switch_overBit_of_ne (w : D.Γ.Visit) (hw : w.1 ≠ x₀) :
    (D.switch x₀).overBit w = D.overBit w := by
  by_cases h : w.2.val = D.overStrand w.1
  · have e1 : (D.switch x₀).overBit w = true :=
      decide_eq_true (h.trans (switch_overStrand_of_ne D hw).symm)
    have e2 : D.overBit w = true := decide_eq_true h
    rw [e1, e2]
  · have e1 : (D.switch x₀).overBit w = false :=
      decide_eq_false fun heq => h (heq.trans (switch_overStrand_of_ne D hw))
    have e2 : D.overBit w = false := decide_eq_false h
    rw [e1, e2]

/-- The bit clause of the switch bridge, on occurrences of `D`. -/
theorem switch_record_bit (v : D.Γ.Visit) (hv : v.1 = x₀) (w : D.Γ.Visit) :
    (D.record.switch v).isOver w = (D.switch x₀).overBit w := by
  have h1 := Record.switch_isOver D.record v w
  rw [h1]
  split_ifs with hmem
  · have hw : w.1 = x₀ := by
      rw [← hv]
      exact ((D.mem_pair_twin_iff v w).mp hmem)
    have e := D.switch_overBit_self x₀ w hw
    rw [e]
  · have hw : w.1 ≠ x₀ := fun h => hmem ((D.mem_pair_twin_iff v w).mpr (h.trans hv.symm))
    have e := D.switch_overBit_of_ne x₀ w hw
    rw [e]

/-- The sign clause of the switch bridge, on occurrences of `D`. -/
theorem switch_record_sgn (v : D.Γ.Visit) (hv : v.1 = x₀) (w : D.Γ.Visit) :
    (D.record.switch v).sgn w = (D.switch x₀).sign w.1 := by
  have h1 := Record.switch_sgn D.record v w
  rw [h1]
  split_ifs with hmem
  · have hw : w.1 = x₀ := by
      rw [← hv]
      exact ((D.mem_pair_twin_iff v w).mp hmem)
    have e := D.switch_sign_self x₀
    rw [hw, e]
    show -D.sign w.1 = -D.sign x₀
    rw [hw]
  · have hw : w.1 ≠ x₀ := fun h => hmem ((D.mem_pair_twin_iff v w).mpr (h.trans hv.symm))
    have e := switch_sign_of_ne D hw
    rw [e]

/-- The record bridge for switching (rp:record-polynomial, lp:core; lp:lm sm-3:939-940 "order of
required crossing switches", sm-3:1085-1086 "A switch at the first bad crossing keeps the parameter
circles and their traversal order"): the record of `D^{sw}` at `x₀` is the record of `D` switched
at any occurrence `v` of `x₀`, by the identity of occurrences and components. -/
def switchRecordIso (v : D.Γ.Visit) (hv : v.1 = x₀) :
    RecordIso (D.switch x₀).record (D.record.switch v) where
  e := Equiv.refl _
  Φ := Equiv.refl _
  comp_eq _ := rfl
  succ_eq _ := rfl
  pair_eq _ := rfl
  bit_eq w := D.switch_record_bit x₀ v hv w
  sgn_eq w := D.switch_record_sgn x₀ v hv w

/-- `record (switch D x₀) ≅ (record D).switch v` for every occurrence `v` of `x₀`. -/
theorem switch_record (v : D.Γ.Visit) (hv : v.1 = x₀) :
    Nonempty (RecordIso (D.switch x₀).record (D.record.switch v)) :=
  ⟨D.switchRecordIso x₀ v hv⟩

/-- The two occurrences of `x₀` name the same switch (sanity, from `Record.switch_pair_eq`). -/
theorem switch_record_overVisit :
    Nonempty (RecordIso (D.switch x₀).record (D.record.switch (D.overVisit x₀))) :=
  D.switch_record x₀ (D.overVisit x₀) rfl

end Diagram

/-! ## E. Realizable records (graft (d))

A theorem-side predicate for mp:blocks' realization clause and cb:products: a record is
*realizable* when it is the record of some actual diagram up to named isomorphism.  It is never
part of the diagram type (CV:ax:gausscode guard: nothing concludes link equivalence from a record
isomorphism). -/

/-- `IsRealizable ρ`: some actual polygonal diagram has record isomorphic to `ρ` — the "full
record" that "a finite succession of clean marked joins of these actual diagrams realizes"
(mp:blocks, sm-3:1629-1630), as a predicate on abstract records. -/
def IsRealizable (ρ : Record) : Prop := ∃ D : Diagram, Nonempty (RecordIso D.record ρ)

theorem isRealizable_record (D : Diagram) : IsRealizable D.record := ⟨D, ⟨RecordIso.refl _⟩⟩

theorem IsRealizable.of_iso {ρ ρ' : Record} (h : IsRealizable ρ) (i : RecordIso ρ ρ') :
    IsRealizable ρ' := by
  obtain ⟨D, ⟨j⟩⟩ := h
  exact ⟨D, ⟨j.trans i⟩⟩

theorem isRealizable_iff_of_iso {ρ ρ' : Record} (i : RecordIso ρ ρ') :
    IsRealizable ρ ↔ IsRealizable ρ' :=
  ⟨fun h => h.of_iso i, fun h => h.of_iso i.symm⟩

/-- Switching preserves realizability (by the switch bridge). -/
theorem isRealizable_switch (D : Diagram) (v : D.Γ.Visit) : IsRealizable (D.record.switch v) :=
  ⟨D.switch v.1, D.switch_record v.1 v rfl⟩

/-! ## F. The case `c = 1`: agreement with the accepted Gauss-word data (graft (c))

def:gauss-record is stated "for an oriented circle" (sm-3:353-354).  For the one-component
shadow of an accepted generic polygon `P` (def:generic, `SM.Generic P`) the record's successor is
the accepted `nextGaussVisit` (the cyclic successor in `gaussList`, def:gauss) and its pairing is
the accepted `Carrier.visitTwin`, under the phase-1 identifications `singleCrossingEquiv` /
`singleVisitEquiv`.  This is the definitional-equality check adopted by the design panel. -/

/-- The one-component diagrams on the accepted generic polygon `C.P`: the shadow `Shadow.single C`,
genericity from `single_generic_of_generic`, and an arbitrary over-strand choice. -/
abbrev singleDiagram (C : PolyComp) (hP : SM.Generic C.P)
    (ov : (Shadow.single C).Crossing → (Shadow.single C).Strand) (hov : ∀ x, ov x ∈ x.val) :
    Diagram :=
  ⟨Shadow.single C, Shadow.single_generic_of_generic hP, ov, hov⟩

section SinglePolygon

variable (C : PolyComp) (hP : SM.Generic C.P)
  (ov : (Shadow.single C).Crossing → (Shadow.single C).Strand) (hov : ∀ x, ov x ∈ x.val)

/-- Every occurrence of a one-component diagram lies on the component `0`. -/
theorem singleDiagram_compOf (v : (singleDiagram C hP ov hov).Γ.Visit) :
    (singleDiagram C hP ov hov).compOf v = 0 := Subsingleton.elim _ _

theorem singleDiagram_compOf_eq (v w : (singleDiagram C hP ov hov).Γ.Visit) :
    (singleDiagram C hP ov hov).compOf v = (singleDiagram C hP ov hov).compOf w :=
  Subsingleton.elim _ _

/-- The crossing parameter of an occurrence is the accepted `visitParameter` of the corresponding
one-polygon visit (both parametrize the same crossing point on the same nondegenerate edge). -/
theorem singleDiagram_crossingParam (w : (singleDiagram C hP ov hov).Γ.Visit) :
    (singleDiagram C hP ov hov).crossingParam w.1 w.2.2 =
      visitParameter (Shadow.singleVisitEquiv C w) := by
  apply edgePoint_injective (g1_edge_ne_zero C.hk hP.1 w.2.val.2)
  have h1 := ((singleDiagram C hP ov hov).crossingParam_spec w.1 w.2.2).2.2
  have h2 := (crossingParameter_spec (Shadow.singleVisitEquiv C w).1
    (Shadow.singleVisitEquiv C w).2.val (Shadow.singleVisitEquiv C w).2.property).2.2
  have h3 := Shadow.single_crossingPoint C (singleDiagram C hP ov hov).generic w.1
  exact h1.symm.trans (h3.trans h2)

/-- The traversal key of an occurrence is the accepted `visitCoord` of the corresponding visit. -/
theorem singleDiagram_visitCoord (w : (singleDiagram C hP ov hov).Γ.Visit) :
    (singleDiagram C hP ov hov).visitCoord w = SM.visitKey C.hk hP.1 (Shadow.singleVisitEquiv C w) := by
  unfold Diagram.visitCoord SM.visitKey
  unfold traversalKey
  show ((w.2.val.2 : ZMod C.k).val : ℝ) + (singleDiagram C hP ov hov).crossingParam w.1 w.2.2 =
    ((w.2.val.2 : ZMod C.k).val : ℝ) + visitParameter (Shadow.singleVisitEquiv C w)
  rw [singleDiagram_crossingParam]

/-- The record's pairing is the accepted `Carrier.visitTwin`. -/
theorem singleDiagram_twin (w : (singleDiagram C hP ov hov).Γ.Visit) :
    Shadow.singleVisitEquiv C ((singleDiagram C hP ov hov).twin w) =
      Carrier.visitTwin (Shadow.singleVisitEquiv C w) := by
  apply Carrier.visitTwin_unique
  · rfl
  · intro h
    exact (singleDiagram C hP ov hov).twin_ne w ((Shadow.singleVisitEquiv C).injective h)

/-- The accepted cyclic successor moves (there are at least two visits once there is one). -/
theorem nextGaussVisit_ne_self (v : SM.Visit C.P) : nextGaussVisit C.hk hP v ≠ v := by
  classical
  rw [nextGaussVisit_eq_list_next]
  apply list_next_ne_self _ (gaussList_nodup C.hk hP)
  have hpos := List.length_pos_of_mem (mem_gaussList C.hk hP v)
  rw [gaussList_length] at hpos ⊢
  omega

/-- The record's successor is the accepted `nextGaussVisit` (def:gauss): both are the unique
occurrence after `v` with no occurrence strictly between, in the cyclic order of traversal keys. -/
theorem singleDiagram_nextVisit (v : (singleDiagram C hP ov hov).Γ.Visit) :
    Shadow.singleVisitEquiv C ((singleDiagram C hP ov hov).nextVisit v) =
      nextGaussVisit C.hk hP (Shadow.singleVisitEquiv C v) := by
  apply cycNext_unique (visitKey_injective C.hk hP) (v := Shadow.singleVisitEquiv C v)
  · intro h
    exact (singleDiagram C hP ov hov).nextVisit_ne_self v ((singleDiagram C hP ov hov).twin v)
      (singleDiagram_compOf_eq C hP ov hov _ _) ((singleDiagram C hP ov hov).twin_ne v)
      ((Shadow.singleVisitEquiv C).injective h)
  · exact nextGaussVisit_ne_self C hP _
  · intro u
    rw [← singleDiagram_visitCoord, ← singleDiagram_visitCoord]
    have h := (singleDiagram C hP ov hov).nextVisit_no_between v
      ((Shadow.singleVisitEquiv C).symm u) (singleDiagram_compOf_eq C hP ov hov _ _)
    rw [singleDiagram_visitCoord C hP ov hov ((Shadow.singleVisitEquiv C).symm u),
      Equiv.apply_symm_apply] at h
    exact h
  · intro u
    exact gauss_next_no_visit_between C.hk hP rfl u

/-- graft (c), `record_of_single_polygon`: for the one-component diagram on an accepted generic
polygon the record's data agree with the accepted one-polygon Gauss-word data — the successor is
`nextGaussVisit` (def:gauss's cyclic visit sequence), the pairing is `Carrier.visitTwin`, every
occurrence lies on the single component, the record has one component and `2·|X(P)|` occurrences
(the accepted `card_visit`), and the stored sign is the accepted `crossingSign` of the over and
under edges (eq:gauss-cross-sign, sm-3:358-359). -/
theorem record_of_single_polygon :
    (∀ v, Shadow.singleVisitEquiv C ((singleDiagram C hP ov hov).record.succ v) =
        nextGaussVisit C.hk hP (Shadow.singleVisitEquiv C v)) ∧
    (∀ v, Shadow.singleVisitEquiv C ((singleDiagram C hP ov hov).record.pair v) =
        Carrier.visitTwin (Shadow.singleVisitEquiv C v)) ∧
    (∀ v, (singleDiagram C hP ov hov).record.comp v = 0) ∧
    (singleDiagram C hP ov hov).record.componentCount = 1 ∧
    Fintype.card (singleDiagram C hP ov hov).record.M = 2 * (crossingSet C.P).card ∧
    (∀ v, (singleDiagram C hP ov hov).record.sgn v =
        crossingSign C.P (Shadow.singleStrandEquiv C ((singleDiagram C hP ov hov).overStrand v.1))
          (Shadow.singleStrandEquiv C ((singleDiagram C hP ov hov).underStrand v.1))) :=
  ⟨singleDiagram_nextVisit C hP ov hov, singleDiagram_twin C hP ov hov,
    singleDiagram_compOf C hP ov hov, Fintype.card_fin 1, Shadow.card_single_visit C,
    fun _ => rfl⟩

end SinglePolygon

/-! ## G. Successor preservation is cyclic-order preservation (def:gauss-record, sm-3:361-365)

"The parametrizing circles are oriented; the finite bijection must preserve their cyclic orders.
It does not prescribe a map at every unmarked parameter and does not permit traversal reversal."
The `succ_eq` clause of `RecordIso` renders this: on each oriented component the forward successor
determines the oriented cyclic order of the occurrences (their order of traversal keys), and
conversely a component-respecting bijection preserving the oriented cyclic order preserves the
successor; a reversal-preserving map would reverse `succ` and is excluded.  This section proves
the equivalence for every component size (with fewer than three occurrences on a component both
conditions are automatic). -/

/-- Cyclic index arithmetic: on a circle of `m` positions, the position `j` steps after `A` lies
strictly between `A` and the position `j'` steps after `A` exactly when `j < j'`
(`0 < j, j' < m`). -/
theorem cycIdx_iff (m j j' A B C : ℕ) (hi : 0 < m) (hB : B < m) (hC : C < m) (hj0 : 0 < j)
    (hj0' : 0 < j') (hjm : j < m) (hj'm : j' < m) (hb : B = A + j ∨ B + m = A + j)
    (hc : C = A + j' ∨ C + m = A + j') :
    ((A < B ∧ B < C) ∨ (B < C ∧ C < A) ∨ (C < A ∧ A < B)) ↔ j < j' := by
  omega

/-- `(A + j) % m` is `A + j` or `A + j - m` when `A, j < m`. -/
theorem add_mod_cases (m A j : ℕ) (hA : A < m) (hj : j < m) :
    (A + j) % m = A + j ∨ (A + j) % m + m = A + j := by
  rcases Nat.lt_or_ge (A + j) m with h | h
  · exact Or.inl (Nat.mod_eq_of_lt h)
  · right
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega

namespace Diagram

variable (D : Diagram)

/-- The oriented cyclic order of three occurrences of one component: strict oriented betweenness
of their traversal keys on the component's parameter circle (the accepted `traversalBetween` of
their traversal points). -/
def VisitBetween (v w u : D.Γ.Visit) : Prop :=
  cycBetween (D.visitCoord v) (D.visitCoord w) (D.visitCoord u)

theorem visitBetween_iff (v w u : D.Γ.Visit) :
    D.VisitBetween v w u ↔ cycBetween (traversalKey (D.visitPt v).2) (traversalKey (D.visitPt w).2)
      (traversalKey (D.visitPt u).2) := Iff.rfl

theorem not_visitBetween_left (v u : D.Γ.Visit) : ¬ D.VisitBetween v v u :=
  not_cycBetween_self_left _ _

theorem not_visitBetween_right (v w : D.Γ.Visit) : ¬ D.VisitBetween v w v :=
  not_cycBetween_self_right _ _

theorem not_visitBetween_mid (v w : D.Γ.Visit) : ¬ D.VisitBetween v w w :=
  not_cycBetween_self_mid _ _

/-- No occurrence of the component lies strictly between an occurrence and its successor. -/
theorem not_visitBetween_nextVisit (v u : D.Γ.Visit) (hu : D.compOf u = D.compOf v) :
    ¬ D.VisitBetween v u (D.nextVisit v) :=
  D.nextVisit_no_between v u hu

/-! ### The cyclic enumeration of a component's occurrences -/

section Enumeration

variable (i : Fin D.Γ.c) (hi : 0 < (D.compList i).length)

/-- The occurrences of component `i` enumerated cyclically along the oriented circle: the `n`-th
entry of the sorted component list, indices taken modulo the component's occurrence count
(auxiliary to the cyclic-order clause of def:gauss-record, sm-3:361-362). -/
def ent (n : ℕ) : D.Γ.Visit :=
  (D.compList i)[n % (D.compList i).length]'(Nat.mod_lt _ hi)

theorem ent_of_lt (n : ℕ) (hn : n < (D.compList i).length) : D.ent i hi n = (D.compList i)[n]'hn := by
  simp only [ent, Nat.mod_eq_of_lt hn]

theorem compOf_ent (n : ℕ) : D.compOf (D.ent i hi n) = i :=
  (D.mem_compList i _).mp (List.getElem_mem _)

theorem ent_inj_iff (a b : ℕ) :
    D.ent i hi a = D.ent i hi b ↔ a % (D.compList i).length = b % (D.compList i).length := by
  unfold ent
  exact (D.compList_nodup i).getElem_inj_iff

theorem exists_ent (w : D.Γ.Visit) (hw : D.compOf w = i) :
    ∃ a, a < (D.compList i).length ∧ D.ent i hi a = w := by
  obtain ⟨a, ha, hw'⟩ := List.getElem_of_mem ((D.mem_compList i w).mpr hw)
  exact ⟨a, ha, by rw [D.ent_of_lt i hi a ha, hw']⟩

/-- The successor advances the enumeration by one. -/
theorem nextVisit_ent (n : ℕ) : D.nextVisit (D.ent i hi n) = D.ent i hi (n + 1) := by
  unfold ent
  rw [D.nextVisit_getElem i]
  simp only [Nat.mod_add_mod]

theorem visitSucc_pow_ent (j n : ℕ) : (D.visitSucc ^ j) (D.ent i hi n) = D.ent i hi (n + j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', Perm.mul_apply, ih, visitSucc_apply, nextVisit_ent, Nat.add_assoc]

/-- Traversal keys along the enumeration compare as the indices modulo the count (the component
list is strictly sorted by key). -/
theorem visitCoord_ent_lt_iff (a b : ℕ) :
    D.visitCoord (D.ent i hi a) < D.visitCoord (D.ent i hi b) ↔
      a % (D.compList i).length < b % (D.compList i).length := by
  let _ := D.visitOrder
  have hs : (D.compList i).SortedLT := Finset.sortedLT_sort (D.compVisits i)
  have h := hs.getElem_lt_getElem_iff (hi := Nat.mod_lt a hi) (hj := Nat.mod_lt b hi)
  rw [← D.visitOrder_lt_iff ((D.compOf_ent i hi a).trans (D.compOf_ent i hi b).symm)]
  exact h

theorem ent_add_sub (a b : ℕ) (ha : a < (D.compList i).length) (_hb : b < (D.compList i).length) :
    D.ent i hi (a + (b + (D.compList i).length - a) % (D.compList i).length) = D.ent i hi b := by
  rw [ent_inj_iff, Nat.add_mod_mod, show a + (b + (D.compList i).length - a) = b + (D.compList i).length
    by omega, Nat.add_mod_right]

/-- Betweenness along the enumeration: `ent (a + j)` lies strictly between `ent a` and
`ent (a + j')` exactly when `j < j'` (for `0 < j, j' <` the count, `j ≠ j'`). -/
theorem visitBetween_ent_iff (a j j' : ℕ) (hj0 : 0 < j) (hj0' : 0 < j')
    (hjm : j < (D.compList i).length) (hj'm : j' < (D.compList i).length) :
    D.VisitBetween (D.ent i hi a) (D.ent i hi (a + j)) (D.ent i hi (a + j')) ↔ j < j' := by
  unfold VisitBetween cycBetween
  rw [visitCoord_ent_lt_iff, visitCoord_ent_lt_iff, visitCoord_ent_lt_iff]
  have e1 : (a + j) % (D.compList i).length = (a % (D.compList i).length + j) % (D.compList i).length :=
    (Nat.mod_add_mod a _ j).symm
  have e2 : (a + j') % (D.compList i).length =
      (a % (D.compList i).length + j') % (D.compList i).length :=
    (Nat.mod_add_mod a _ j').symm
  rw [e1, e2]
  exact cycIdx_iff (D.compList i).length j j' _ _ _ hi (Nat.mod_lt _ hi) (Nat.mod_lt _ hi) hj0 hj0'
    hjm hj'm (add_mod_cases _ _ _ (Nat.mod_lt _ hi) hjm) (add_mod_cases _ _ _ (Nat.mod_lt _ hi) hj'm)

end Enumeration

/-! ### Component-respecting bijections -/

section Bijection

variable {D' : Diagram} (Φ : D.Γ.Visit ≃ D'.Γ.Visit)

/-- A component-respecting bijection carries the occurrence set of a component onto the
occurrence set of the image component. -/
theorem compVisits_map_of_comp_iff
    (hcomp : ∀ v w, D'.compOf (Φ v) = D'.compOf (Φ w) ↔ D.compOf v = D.compOf w) (v : D.Γ.Visit) :
    D'.compVisits (D'.compOf (Φ v)) = (D.compVisits (D.compOf v)).map Φ.toEmbedding := by
  ext v'
  rw [Finset.mem_map_equiv, mem_compVisits, mem_compVisits]
  have h := hcomp (Φ.symm v') v
  rw [Equiv.apply_symm_apply] at h
  exact h

theorem compList_length_map
    (hcomp : ∀ v w, D'.compOf (Φ v) = D'.compOf (Φ w) ↔ D.compOf v = D.compOf w) (v : D.Γ.Visit) :
    (D'.compList (D'.compOf (Φ v))).length = (D.compList (D.compOf v)).length := by
  rw [compList_length, compList_length, compVisits_map_of_comp_iff D Φ hcomp, Finset.card_map]

/-- A bijection commuting with the successor commutes with its powers. -/
theorem visitSucc_pow_comm (hsucc : ∀ v, Φ (D.nextVisit v) = D'.nextVisit (Φ v)) (j : ℕ)
    (x : D.Γ.Visit) : Φ ((D.visitSucc ^ j) x) = (D'.visitSucc ^ j) (Φ x) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Perm.mul_apply, visitSucc_apply, hsucc, ih, pow_succ', Perm.mul_apply,
      visitSucc_apply]

/-- Successor preservation implies preservation of the oriented cyclic order on each component
("must preserve their cyclic orders"). -/
theorem visitBetween_iff_of_nextVisit_comm
    (hcomp : ∀ v w, D'.compOf (Φ v) = D'.compOf (Φ w) ↔ D.compOf v = D.compOf w)
    (hsucc : ∀ v, Φ (D.nextVisit v) = D'.nextVisit (Φ v))
    (v w u : D.Γ.Visit) (hw : D.compOf w = D.compOf v) (hu : D.compOf u = D.compOf v) :
    D'.VisitBetween (Φ v) (Φ w) (Φ u) ↔ D.VisitBetween v w u := by
  by_cases hvw : v = w
  · subst hvw
    exact iff_of_false (D'.not_visitBetween_left _ _) (D.not_visitBetween_left _ _)
  by_cases hvu : v = u
  · subst hvu
    exact iff_of_false (D'.not_visitBetween_right _ _) (D.not_visitBetween_right _ _)
  by_cases hwu : w = u
  · subst hwu
    exact iff_of_false (D'.not_visitBetween_mid _ _) (D.not_visitBetween_mid _ _)
  -- the enumeration of the component of `v`
  have hi : 0 < (D.compList (D.compOf v)).length := List.length_pos_of_mem (D.self_mem_compList v)
  obtain ⟨a, ha, hav⟩ := D.exists_ent _ hi v rfl
  obtain ⟨b, hb, hbw⟩ := D.exists_ent _ hi w hw
  obtain ⟨c, hc, hcu⟩ := D.exists_ent _ hi u hu
  have hjw : D.ent _ hi (a + (b + (D.compList (D.compOf v)).length - a) %
      (D.compList (D.compOf v)).length) = w := by
    rw [D.ent_add_sub _ hi a b ha hb, hbw]
  have hju : D.ent _ hi (a + (c + (D.compList (D.compOf v)).length - a) %
      (D.compList (D.compOf v)).length) = u := by
    rw [D.ent_add_sub _ hi a c ha hc, hcu]
  have hjm := Nat.mod_lt (b + (D.compList (D.compOf v)).length - a) hi
  have hj'm := Nat.mod_lt (c + (D.compList (D.compOf v)).length - a) hi
  have hj0 : 0 < (b + (D.compList (D.compOf v)).length - a) % (D.compList (D.compOf v)).length := by
    by_contra h0
    have h0' : (b + (D.compList (D.compOf v)).length - a) % (D.compList (D.compOf v)).length = 0 := by
      omega
    rw [h0', Nat.add_zero, hav] at hjw
    exact hvw hjw
  have hj0' : 0 < (c + (D.compList (D.compOf v)).length - a) % (D.compList (D.compOf v)).length := by
    by_contra h0
    have h0' : (c + (D.compList (D.compOf v)).length - a) % (D.compList (D.compOf v)).length = 0 := by
      omega
    rw [h0', Nat.add_zero, hav] at hju
    exact hvu hju
  have hD := D.visitBetween_ent_iff _ hi a _ _ hj0 hj0' hjm hj'm
  rw [hav, hjw, hju] at hD
  -- transport to `D'`
  have hi' : 0 < (D'.compList (D'.compOf (Φ v))).length :=
    List.length_pos_of_mem (D'.self_mem_compList (Φ v))
  have hm' : (D'.compList (D'.compOf (Φ v))).length = (D.compList (D.compOf v)).length :=
    compList_length_map D Φ hcomp v
  obtain ⟨a', ha', hav'⟩ := D'.exists_ent _ hi' (Φ v) rfl
  have hw' : Φ w = D'.ent _ hi' (a' + (b + (D.compList (D.compOf v)).length - a) %
      (D.compList (D.compOf v)).length) := by
    calc Φ w = Φ ((D.visitSucc ^ ((b + (D.compList (D.compOf v)).length - a) %
          (D.compList (D.compOf v)).length)) (D.ent _ hi a)) := by
          rw [D.visitSucc_pow_ent, hjw]
      _ = (D'.visitSucc ^ ((b + (D.compList (D.compOf v)).length - a) %
          (D.compList (D.compOf v)).length)) (Φ (D.ent _ hi a)) :=
          visitSucc_pow_comm D Φ hsucc _ _
      _ = (D'.visitSucc ^ ((b + (D.compList (D.compOf v)).length - a) %
          (D.compList (D.compOf v)).length)) (D'.ent _ hi' a') := by rw [hav, hav']
      _ = _ := D'.visitSucc_pow_ent _ hi' _ a'
  have hu' : Φ u = D'.ent _ hi' (a' + (c + (D.compList (D.compOf v)).length - a) %
      (D.compList (D.compOf v)).length) := by
    calc Φ u = Φ ((D.visitSucc ^ ((c + (D.compList (D.compOf v)).length - a) %
          (D.compList (D.compOf v)).length)) (D.ent _ hi a)) := by
          rw [D.visitSucc_pow_ent, hju]
      _ = (D'.visitSucc ^ ((c + (D.compList (D.compOf v)).length - a) %
          (D.compList (D.compOf v)).length)) (Φ (D.ent _ hi a)) :=
          visitSucc_pow_comm D Φ hsucc _ _
      _ = (D'.visitSucc ^ ((c + (D.compList (D.compOf v)).length - a) %
          (D.compList (D.compOf v)).length)) (D'.ent _ hi' a') := by rw [hav, hav']
      _ = _ := D'.visitSucc_pow_ent _ hi' _ a'
  have hD' := D'.visitBetween_ent_iff _ hi' a' _ _ hj0 hj0' (lt_of_lt_of_eq hjm hm'.symm)
    (lt_of_lt_of_eq hj'm hm'.symm)
  rw [hav', ← hw', ← hu'] at hD'
  exact hD'.trans hD.symm

/-- Preservation of the oriented cyclic order on each component implies successor preservation
(the cyclic successor is the unique occurrence with nothing strictly between; a component with one
occurrence is fixed). -/
theorem nextVisit_comm_of_visitBetween_iff
    (hcomp : ∀ v w, D'.compOf (Φ v) = D'.compOf (Φ w) ↔ D.compOf v = D.compOf w)
    (hbetw : ∀ v w u, D.compOf w = D.compOf v → D.compOf u = D.compOf v →
      (D'.VisitBetween (Φ v) (Φ w) (Φ u) ↔ D.VisitBetween v w u))
    (v : D.Γ.Visit) : Φ (D.nextVisit v) = D'.nextVisit (Φ v) := by
  by_cases hsingle : ∀ w, D.compOf w = D.compOf v → w = v
  · rw [D.nextVisit_eq_self v hsingle, D'.nextVisit_eq_self (Φ v)]
    intro w' hw'
    have h := hsingle (Φ.symm w') ((hcomp (Φ.symm w') v).mp (by rwa [Equiv.apply_symm_apply]))
    rw [← Equiv.apply_symm_apply Φ w', h]
  · push Not at hsingle
    obtain ⟨w, hw, hwv⟩ := hsingle
    apply cycNext_unique_on (p := fun u' => D'.compOf u' = D'.compOf (Φ v)) (k := D'.visitCoord)
      (fun a b ha hb hk => D'.visitCoord_injOn (ha.trans hb.symm) hk) rfl
    · exact (hcomp _ _).mpr (D.compOf_nextVisit v)
    · exact D'.compOf_nextVisit (Φ v)
    · intro h
      exact D.nextVisit_ne_self v w hw hwv (Φ.injective h)
    · exact D'.nextVisit_ne_self (Φ v) (Φ w) ((hcomp w v).mpr hw) (fun h => hwv (Φ.injective h))
    · intro u' hu'
      have hu : D.compOf (Φ.symm u') = D.compOf v :=
        (hcomp (Φ.symm u') v).mp (by rwa [Equiv.apply_symm_apply])
      have h : ¬ D.VisitBetween v (Φ.symm u') (D.nextVisit v) :=
        D.not_visitBetween_nextVisit v (Φ.symm u') hu
      rw [← hbetw v (Φ.symm u') (D.nextVisit v) hu (D.compOf_nextVisit v),
        Equiv.apply_symm_apply] at h
      exact h
    · intro u' hu'
      exact D'.not_visitBetween_nextVisit (Φ v) u' hu'

/-- def:gauss-record (sm-3:361-365), the cyclic-order clause: for a bijection of occurrences
respecting components, preserving the successor (the `succ_eq` clause of `RecordIso`) is
equivalent to preserving the oriented cyclic order of the occurrences on every component. -/
theorem nextVisit_comm_iff_visitBetween_iff
    (hcomp : ∀ v w, D'.compOf (Φ v) = D'.compOf (Φ w) ↔ D.compOf v = D.compOf w) :
    (∀ v, Φ (D.nextVisit v) = D'.nextVisit (Φ v)) ↔
      ∀ v w u, D.compOf w = D.compOf v → D.compOf u = D.compOf v →
        (D'.VisitBetween (Φ v) (Φ w) (Φ u) ↔ D.VisitBetween v w u) :=
  ⟨fun hsucc v w u hw hu => visitBetween_iff_of_nextVisit_comm D Φ hcomp hsucc v w u hw hu,
    fun hbetw v => nextVisit_comm_of_visitBetween_iff D Φ hcomp hbetw v⟩

end Bijection

end Diagram

namespace RecordIso

variable {D D' : Diagram} (ι : RecordIso D.record D'.record)

/-- A named record isomorphism respects components (its component bijection `e`). -/
theorem compOf_iff (v w : D.Γ.Visit) :
    D'.compOf (ι.Φ v) = D'.compOf (ι.Φ w) ↔ D.compOf v = D.compOf w := by
  have h1 : D'.compOf (ι.Φ v) = ι.e (D.compOf v) := ι.comp_eq v
  have h2 : D'.compOf (ι.Φ w) = ι.e (D.compOf w) := ι.comp_eq w
  rw [h1, h2]
  exact ι.e.injective.eq_iff

/-- "the finite bijection must preserve their cyclic orders": a named record isomorphism of the
records of two diagrams preserves the oriented cyclic order of the occurrences on each component
(and, being successor-preserving, never reverses a traversal). -/
theorem visitBetween_iff (v w u : D.Γ.Visit) (hw : D.compOf w = D.compOf v)
    (hu : D.compOf u = D.compOf v) :
    D'.VisitBetween (ι.Φ v) (ι.Φ w) (ι.Φ u) ↔ D.VisitBetween v w u :=
  Diagram.visitBetween_iff_of_nextVisit_comm D ι.Φ ι.compOf_iff (fun v => ι.succ_eq v) v w u hw hu

end RecordIso

/-! ## H. The piecewise-linear extension Φ̄ (def:gauss-record, sm-3:365-369): statement

"After a finite subdivision we choose an orientation-preserving piecewise-linear circle map
Φ̄ : C → C' extending Φ: on each interval between successive marked points use the positive affine
map in oriented interval coordinates. If M is empty, choose any positive circle parametrization."
Per decision 6 of the design record this is a construction on top of the finite data, not part of
the record or of the isomorphism; the statement below fixes its content for the theorem
`RecordIso.extend`, whose proof (the affine interpolation) is not part of this module. -/

namespace RecordIso

variable {D D' : Diagram} (ι : RecordIso D.record D'.record)

/-- `ι.ExtendsToCircleMaps`: there are bijections `φ i` of the parameter circle of component `i`
of `D` onto the parameter circle of component `ι.e i` of `D'` which preserve the oriented cyclic
order (`traversalBetween`, i.e. "orientation-preserving ... circle map" — for a bijection the
one-directional clause is equivalent to the two-directional one) and extend `Φ`: the traversal
point of every occurrence is carried to the traversal point of its image ("extending Φ").  The
printed construction ("on each interval between successive marked points use the positive affine
map in oriented interval coordinates. If M is empty, choose any positive circle parametrization",
sm-3:366-369) is the intended witness. -/
def ExtendsToCircleMaps : Prop :=
  ∃ φ : ∀ i : Fin D.Γ.c, TraversalPoint (D.Γ.comp i).k ≃ TraversalPoint (D'.Γ.comp (ι.e i)).k,
    (∀ i p q r, traversalBetween p q r → traversalBetween (φ i p) (φ i q) (φ i r)) ∧
    ∀ v : D.Γ.Visit, (⟨ι.e (D.visitPt v).1, φ _ (D.visitPt v).2⟩ : D'.Γ.Pt) = D'.visitPt (ι.Φ v)

/-- Sanity: the identity isomorphism extends by the identity circle maps. -/
theorem extendsToCircleMaps_refl (D : Diagram) : (RecordIso.refl D.record).ExtendsToCircleMaps :=
  ⟨fun _ => Equiv.refl _, fun _ _ _ _ h => h, fun _ => rfl⟩

end RecordIso

/-- The extension theorem of def:gauss-record (design decision 6, `RecordIso.extend`): every
named record isomorphism between the records of two diagrams extends to orientation-preserving
circle maps of the parameter circles carrying occurrences to occurrences.  Stated here as a
proposition; its proof (subdivide, then interpolate affinely between successive marks; any
positive parametrization on a mark-free circle) is listed as an open item of this module. -/
def recordIso_extend_statement : Prop :=
  ∀ (D D' : Diagram) (ι : RecordIso D.record D'.record), ι.ExtendsToCircleMaps

/-! ## I. The block-restriction bridge (mp:stack, sm-3:1495-1500): statement

"Let D_i be the actual restriction retaining all components in block i and all crossings internal
to it."  Diagram side: `Diagram.restrict B hB` (LinkDiagram); record side: `Record.restrict B`
(LinkRecord: circles of `B`, occurrences of internal crossings, first-return successor). -/

/-- `restrict_record`: the record of the block restriction `D|_B` is isomorphic to the record-level
restriction of `D.record` to `B`.  Stated here as a proposition and proved in section J
(`Diagram.restrictRecordIso`, `Diagram.restrict_record`): the first return of the sorted cyclic
successor to the internal occurrences of a component is the sorted cyclic successor of those
occurrences, and pairing, bits and signs transport along `restrictMap`. -/
def restrict_record_statement : Prop :=
  ∀ (D : Diagram) (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty),
    Nonempty (RecordIso (D.restrict B hB).record (D.record.restrict B))

/-! ## J. The block-restriction bridge: proof

The occurrences of `D|_B` are the occurrences of `D` at the internal crossings of the block
(`Record.RestrictKeep`), and the successor of `D|_B` on a component is the first return of the
successor of `D` to the retained occurrences of that component: both are the next retained
occurrence in the oriented cyclic order of traversal coordinates. -/

namespace Diagram

variable (D : Diagram) (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty)

/-- The occurrence of `D` at which an occurrence of the restriction `D|_B` sits (mp:stack,
sm-3:1499-1500 "all crossings internal to it"): the corresponding crossing
(`StrandMap.mapCrossing`) with the corresponding strand. -/
def restrictVisit (v : (D.Γ.restrictShadow B hB).Visit) : D.Γ.Visit :=
  ⟨(D.Γ.restrictMap B hB).mapCrossing v.1,
    ⟨(D.Γ.restrictMap B hB).toFun v.2.val, (D.Γ.restrictMap B hB).toFun_mem_of_mem v.2.2⟩⟩

theorem restrictVisit_fst (v : (D.Γ.restrictShadow B hB).Visit) :
    (D.restrictVisit B hB v).1 = (D.Γ.restrictMap B hB).mapCrossing v.1 := rfl

theorem restrictVisit_strand (v : (D.Γ.restrictShadow B hB).Visit) :
    (D.restrictVisit B hB v).2.val = (D.Γ.restrictMap B hB).toFun v.2.val := rfl

theorem compOf_restrictVisit (v : (D.Γ.restrictShadow B hB).Visit) :
    D.compOf (D.restrictVisit B hB v) = B.orderEmbOfFin rfl ((D.restrict B hB).compOf v) := rfl

theorem compOf_restrictVisit_iff (v w : (D.Γ.restrictShadow B hB).Visit) :
    D.compOf (D.restrictVisit B hB v) = D.compOf (D.restrictVisit B hB w) ↔
      (D.restrict B hB).compOf v = (D.restrict B hB).compOf w :=
  (B.orderEmbOfFin rfl).injective.eq_iff

theorem restrictVisit_injective : Function.Injective (D.restrictVisit B hB) := by
  intro v w h
  obtain ⟨x, s, hs⟩ := v
  obtain ⟨y, t, ht⟩ := w
  have h1 : (D.Γ.restrictMap B hB).mapCrossing x = (D.Γ.restrictMap B hB).mapCrossing y :=
    congrArg Sigma.fst h
  have hxy := (D.Γ.restrictMap B hB).mapCrossing_injective h1
  subst hxy
  have h2 : (D.Γ.restrictMap B hB).toFun s = (D.Γ.restrictMap B hB).toFun t :=
    congrArg (fun u : D.Γ.Visit => u.2.val) h
  have hst := (D.Γ.restrictMap B hB).inj h2
  subst hst
  rfl

/-- The pairing transports along the restriction (`StrandMap.other_mapCrossing`). -/
theorem twin_restrictVisit (v : (D.Γ.restrictShadow B hB).Visit) :
    D.twin (D.restrictVisit B hB v) = D.restrictVisit B hB ((D.restrict B hB).twin v) :=
  congrArg (fun t : {s // s ∈ ((D.Γ.restrictMap B hB).mapCrossing v.1).val} =>
      (⟨(D.Γ.restrictMap B hB).mapCrossing v.1, t⟩ : D.Γ.Visit))
    (Subtype.ext ((D.Γ.restrictMap B hB).other_mapCrossing v.2.2))

/-- Occurrences of the restriction sit at internal crossings. -/
theorem restrictKeep_restrictVisit (v : (D.Γ.restrictShadow B hB).Visit) :
    D.record.RestrictKeep B (D.restrictVisit B hB v) := by
  refine ⟨Finset.orderEmbOfFin_mem B rfl _, ?_⟩
  show D.compOf (D.twin (D.restrictVisit B hB v)) ∈ B
  rw [twin_restrictVisit]
  exact Finset.orderEmbOfFin_mem B rfl _

/-- Every occurrence of `D` at an internal crossing comes from the restriction. -/
theorem exists_restrictVisit (u : D.Γ.Visit) (hu : D.record.RestrictKeep B u) :
    ∃ v, D.restrictVisit B hB v = u := by
  obtain ⟨x, t, ht⟩ := u
  have hint : ∀ s ∈ x.val, s.1 ∈ B := by
    intro s hs
    rcases (D.Γ.mem_iff_eq_or_other x ht s).mp hs with rfl | rfl
    · exact hu.1
    · exact hu.2
  obtain ⟨y, hy⟩ := (D.Γ.restrict_mapCrossing_range_iff B hB x).mpr hint
  subst hy
  obtain ⟨s, hs, hst⟩ := (D.Γ.restrictMap B hB).exists_preimage_of_mem ht
  subst hst
  exact ⟨⟨y, ⟨s, hs⟩⟩, rfl⟩

/-- The occurrences of `D|_B` are exactly the retained occurrences of `D`. -/
def restrictVisitEquiv : (D.Γ.restrictShadow B hB).Visit ≃ {u : D.Γ.Visit // D.record.RestrictKeep B u} :=
  Equiv.ofBijective (fun v => ⟨D.restrictVisit B hB v, D.restrictKeep_restrictVisit B hB v⟩)
    ⟨fun v w h => D.restrictVisit_injective B hB (congrArg Subtype.val h),
     fun u => by
      obtain ⟨v, hv⟩ := D.exists_restrictVisit B hB u.1 u.2
      exact ⟨v, Subtype.ext hv⟩⟩

@[simp] theorem restrictVisitEquiv_apply_val (v : (D.Γ.restrictShadow B hB).Visit) :
    (D.restrictVisitEquiv B hB v).1 = D.restrictVisit B hB v := rfl

/-- The crossing parameter is the same on both sides (same edge, same crossing point). -/
theorem restrict_crossingParam (v : (D.Γ.restrictShadow B hB).Visit) :
    D.crossingParam (D.restrictVisit B hB v).1 (D.restrictVisit B hB v).2.2 =
      (D.restrict B hB).crossingParam v.1 v.2.2 := by
  have hedge : edge (D.Γ.comp ((D.Γ.restrictMap B hB).toFun v.2.val).1).P
      ((D.Γ.restrictMap B hB).toFun v.2.val).2 ≠ 0 :=
    ((regular_iff_edges _).mp (D.generic.regular _) _).1
  apply edgePoint_injective hedge
  have h1 := (D.crossingParam_spec (D.restrictVisit B hB v).1 (D.restrictVisit B hB v).2.2).2.2
  have h2 := ((D.restrict B hB).crossingParam_spec v.1 v.2.2).2.2
  have h3 := (D.Γ.restrictMap B hB).crossingPoint_mapCrossing D.generic v.1
  exact h1.symm.trans (h3.trans h2)

/-- The traversal coordinate is the same on both sides. -/
theorem visitCoord_restrictVisit (v : (D.Γ.restrictShadow B hB).Visit) :
    D.visitCoord (D.restrictVisit B hB v) = (D.restrict B hB).visitCoord v := by
  show (((D.restrictVisit B hB v).2.val.2).val : ℝ) +
      D.crossingParam (D.restrictVisit B hB v).1 (D.restrictVisit B hB v).2.2 =
    ((v.2.val.2).val : ℝ) + (D.restrict B hB).crossingParam v.1 v.2.2
  exact congrArg (fun t : ℝ => (((D.restrictVisit B hB v).2.val.2).val : ℝ) + t)
    (D.restrict_crossingParam B hB v)

/-- The over bit is the same on both sides (`toFun_pullback_overStrand`). -/
theorem overBit_restrictVisit (v : (D.Γ.restrictShadow B hB).Visit) :
    D.overBit (D.restrictVisit B hB v) = (D.restrict B hB).overBit v := by
  have hov : (D.Γ.restrictMap B hB).toFun ((D.restrict B hB).overStrand v.1) =
      D.overStrand ((D.Γ.restrictMap B hB).mapCrossing v.1) :=
    toFun_pullback_overStrand D (D.Γ.restrictMap B hB)
      (fun j => D.generic.regular (B.orderEmbOfFin rfl j)) v.1
  by_cases h : v.2.val = (D.restrict B hB).overStrand v.1
  · have e1 : D.overBit (D.restrictVisit B hB v) = true := by
      apply decide_eq_true
      show (D.Γ.restrictMap B hB).toFun v.2.val = D.overStrand ((D.Γ.restrictMap B hB).mapCrossing v.1)
      rw [h]
      exact hov
    have e2 : (D.restrict B hB).overBit v = true := decide_eq_true h
    rw [e1, e2]
  · have e1 : D.overBit (D.restrictVisit B hB v) = false :=
      decide_eq_false fun heq => h ((D.Γ.restrictMap B hB).inj (heq.trans hov.symm))
    have e2 : (D.restrict B hB).overBit v = false := decide_eq_false h
    rw [e1, e2]

theorem ent_add_length (i : Fin D.Γ.c) (hi : 0 < (D.compList i).length) (n : ℕ) :
    D.ent i hi (n + (D.compList i).length) = D.ent i hi n := by
  rw [ent_inj_iff, Nat.add_mod_right]

/-- The successor of `D|_B` is the first return of the successor of `D` to the retained
occurrences (both are the next retained occurrence in the cyclic order of traversal
coordinates). -/
theorem restrictVisit_nextVisit (v : (D.Γ.restrictShadow B hB).Visit) :
    D.restrictVisit B hB ((D.restrict B hB).nextVisit v) =
      ((D.record.restrict B).succ ⟨D.restrictVisit B hB v, D.restrictKeep_restrictVisit B hB v⟩).1 := by
  have hT : ∀ u', D.record.RestrictKeep B u' → D.compOf u' = D.compOf (D.restrictVisit B hB v) →
      ∃ w : (D.Γ.restrictShadow B hB).Visit,
        (D.restrict B hB).compOf w = (D.restrict B hB).compOf v ∧ D.restrictVisit B hB w = u' := by
    intro u' hu' hc
    obtain ⟨w, rfl⟩ := D.exists_restrictVisit B hB u' hu'
    exact ⟨w, (D.compOf_restrictVisit_iff B hB w v).mp hc, rfl⟩
  set k := returnTime D.record.succ (D.record.RestrictKeep B) (D.restrictVisit B hB v)
    (D.restrictKeep_restrictVisit B hB v) with hk
  have hsucc : ((D.record.restrict B).succ
      ⟨D.restrictVisit B hB v, D.restrictKeep_restrictVisit B hB v⟩).1 =
      (D.visitSucc ^ k) (D.restrictVisit B hB v) :=
    firstReturn_apply _ _ _
  rw [hsucc]
  have hk_pos : 0 < k := returnTime_pos _ _ _ _
  have hk_spec : D.record.RestrictKeep B ((D.visitSucc ^ k) (D.restrictVisit B hB v)) :=
    returnTime_spec _ _ _ _
  have hk_min : ∀ j, 0 < j → j < k →
      ¬ D.record.RestrictKeep B ((D.visitSucc ^ j) (D.restrictVisit B hB v)) :=
    fun j hj0 hjk => returnTime_min _ _ _ _ hj0 hjk
  have hk_comp : D.compOf ((D.visitSucc ^ k) (D.restrictVisit B hB v)) =
      D.compOf (D.restrictVisit B hB v) := D.record.comp_pow _ _
  by_cases hsingle : ∀ w : (D.Γ.restrictShadow B hB).Visit,
      (D.restrict B hB).compOf w = (D.restrict B hB).compOf v → w = v
  · rw [(D.restrict B hB).nextVisit_eq_self v hsingle]
    obtain ⟨w, hw, hwu⟩ := hT _ hk_spec hk_comp
    rw [hsingle w hw] at hwu
    exact hwu
  · push Not at hsingle
    obtain ⟨w, hw, hwv⟩ := hsingle
    -- the enumeration of the component of `u := restrictVisit v` in `D`
    have hi : 0 < (D.compList (D.compOf (D.restrictVisit B hB v))).length :=
      List.length_pos_of_mem (D.self_mem_compList _)
    obtain ⟨a, ha, hau⟩ := D.exists_ent _ hi (D.restrictVisit B hB v) rfl
    have hpow : ∀ j, (D.visitSucc ^ j) (D.restrictVisit B hB v) = D.ent _ hi (a + j) := fun j =>
      (congrArg (D.visitSucc ^ j) hau.symm).trans (D.visitSucc_pow_ent _ hi j a)
    -- the retained occurrence `restrictVisit w ≠ u` bounds the return time below the count
    obtain ⟨b, hb, hbw⟩ := D.exists_ent _ hi (D.restrictVisit B hB w)
      ((D.compOf_restrictVisit_iff B hB w v).mpr hw)
    have hjw : D.ent _ hi (a + (b + (D.compList (D.compOf (D.restrictVisit B hB v))).length - a) %
        (D.compList (D.compOf (D.restrictVisit B hB v))).length) = D.restrictVisit B hB w := by
      rw [D.ent_add_sub _ hi a b ha hb, hbw]
    have hj0 : 0 < (b + (D.compList (D.compOf (D.restrictVisit B hB v))).length - a) %
        (D.compList (D.compOf (D.restrictVisit B hB v))).length := by
      by_contra h0
      have h0' : (b + (D.compList (D.compOf (D.restrictVisit B hB v))).length - a) %
          (D.compList (D.compOf (D.restrictVisit B hB v))).length = 0 := by omega
      rw [h0', Nat.add_zero, hau] at hjw
      exact hwv (D.restrictVisit_injective B hB hjw.symm)
    have hjm := Nat.mod_lt (b + (D.compList (D.compOf (D.restrictVisit B hB v))).length - a) hi
    have hkm : k < (D.compList (D.compOf (D.restrictVisit B hB v))).length := by
      by_contra hge
      push Not at hge
      apply hk_min _ hj0 (lt_of_lt_of_le hjm hge)
      rw [hpow, hjw]
      exact D.restrictKeep_restrictVisit B hB w
    -- the first return differs from `u`
    have hr_ne : (D.visitSucc ^ k) (D.restrictVisit B hB v) ≠ D.restrictVisit B hB v := by
      intro h
      have h' : D.ent _ hi (a + k) = D.ent _ hi a := (hpow k).symm.trans (h.trans hau.symm)
      rw [D.ent_inj_iff] at h'
      have h2 : a + k ≡ a + 0 [MOD (D.compList (D.compOf (D.restrictVisit B hB v))).length] := by
        rw [Nat.add_zero]; exact h'
      have h3 := Nat.ModEq.add_left_cancel' a h2
      unfold Nat.ModEq at h3
      rw [Nat.mod_eq_of_lt hkm, Nat.zero_mod] at h3
      omega
    -- uniqueness of the cyclic successor among the retained occurrences of the component
    apply cycNext_unique_on
      (p := fun u' => D.record.RestrictKeep B u' ∧ D.compOf u' = D.compOf (D.restrictVisit B hB v))
      (k := D.visitCoord) (fun a b ha hb hk => D.visitCoord_injOn (ha.2.trans hb.2.symm) hk)
      ⟨D.restrictKeep_restrictVisit B hB v, rfl⟩
    · exact ⟨D.restrictKeep_restrictVisit B hB _,
        (D.compOf_restrictVisit_iff B hB _ v).mpr ((D.restrict B hB).compOf_nextVisit v)⟩
    · exact ⟨hk_spec, hk_comp⟩
    · intro h
      exact (D.restrict B hB).nextVisit_ne_self v w hw hwv (D.restrictVisit_injective B hB h)
    · exact hr_ne
    · intro u' hu'
      obtain ⟨w', hw', rfl⟩ := hT u' hu'.1 hu'.2
      rw [D.visitCoord_restrictVisit B hB v, D.visitCoord_restrictVisit B hB w',
        D.visitCoord_restrictVisit B hB ((D.restrict B hB).nextVisit v)]
      exact (D.restrict B hB).not_visitBetween_nextVisit v w' hw'
    · intro u' hu' hbetw
      by_cases huu : u' = D.restrictVisit B hB v
      · rw [huu] at hbetw
        exact not_cycBetween_self_left _ _ hbetw
      obtain ⟨b', hb', hb'u⟩ := D.exists_ent _ hi u' hu'.2
      have hj'u : D.ent _ hi (a + (b' + (D.compList (D.compOf (D.restrictVisit B hB v))).length - a) %
          (D.compList (D.compOf (D.restrictVisit B hB v))).length) = u' := by
        rw [D.ent_add_sub _ hi a b' ha hb', hb'u]
      have hj'0 : 0 < (b' + (D.compList (D.compOf (D.restrictVisit B hB v))).length - a) %
          (D.compList (D.compOf (D.restrictVisit B hB v))).length := by
        by_contra h0
        have h0' : (b' + (D.compList (D.compOf (D.restrictVisit B hB v))).length - a) %
            (D.compList (D.compOf (D.restrictVisit B hB v))).length = 0 := by omega
        rw [h0', Nat.add_zero, hau] at hj'u
        exact huu hj'u.symm
      have hj'm := Nat.mod_lt (b' + (D.compList (D.compOf (D.restrictVisit B hB v))).length - a) hi
      have key := D.visitBetween_ent_iff _ hi a _ k hj'0 hk_pos hj'm hkm
      rw [hj'u, ← hpow k, hau] at key
      apply hk_min _ hj'0 (key.mp hbetw)
      rw [hpow, hj'u]
      exact hu'.1

/-- The block-restriction bridge `restrict_record` (mp:stack): the record of `D|_B` is isomorphic
to the record-level restriction of `D.record` to `B`, by the correspondence of internal
occurrences. -/
def restrictRecordIso : RecordIso (D.restrict B hB).record (D.record.restrict B) where
  e := (B.orderIsoOfFin rfl).toEquiv
  Φ := D.restrictVisitEquiv B hB
  comp_eq v := Subtype.ext
    ((D.compOf_restrictVisit B hB v).trans (Finset.coe_orderIsoOfFin_apply B rfl _).symm)
  succ_eq v := Subtype.ext (D.restrictVisit_nextVisit B hB v)
  pair_eq v := Subtype.ext (D.twin_restrictVisit B hB v).symm
  bit_eq v := D.overBit_restrictVisit B hB v
  sgn_eq v := (D.restrict_sign B hB v.1).symm

/-- `restrict_record`: the statement of section I holds. -/
theorem restrict_record : restrict_record_statement :=
  fun D B hB => ⟨D.restrictRecordIso B hB⟩

/-- Restriction preserves realizability. -/
theorem isRealizable_restrict (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty) :
    IsRealizable (D.record.restrict B) :=
  ⟨D.restrict B hB, ⟨D.restrictRecordIso B hB⟩⟩

end Diagram

end

end SM.Link

/-! ## Axiom audit (must show only `propext`, `Classical.choice`, `Quot.sound`) -/

