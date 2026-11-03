import DirectGLSSW.OrderedEventSuccessor
import DirectGLSSW.PermutationOrbits
import DirectGLSSW.FiniteFirstReturn
import Mathlib.Data.Real.Basic

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc

variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)

/-- Physical edges only: the terminal-to-initial segment has no label. -/
def edgeInterior (e : Fin (n+1)) (x : PlanarPoint ℝ) : Prop :=
  ∃ t : ℝ, 0<t ∧ t<1 ∧ x = affinePoint (q e.castSucc) (q e.succ) t

def Crossing := {p : Fin (n+1) × Fin (n+1) // p.1<p.2 ∧
  ∃ x : PlanarPoint ℝ, edgeInterior q p.1 x ∧ edgeInterior q p.2 x}

instance crossingFintype : Fintype (Crossing q) := by
  classical
  unfold Crossing
  exact Fintype.ofFinite _

def NoTriple : Prop := ∀ e f g : Fin (n+1), ∀ x : PlanarPoint ℝ,
  e≠f → f≠g → g≠e → ¬ (edgeInterior q e x ∧ edgeInterior q f x ∧ edgeInterior q g x)

/-- Regularity refers exclusively to physical edges and actual vertices. -/
structure Regular : Prop where
  edge_nonzero : ∀ e : Fin (n+1), q e.succ-q e.castSucc ≠ 0
  transverse : ∀ e f : Fin (n+1), e≠f → ∀ x : PlanarPoint ℝ,
    edgeInterior q e x → edgeInterior q f x →
    planarDet (q e.succ-q e.castSucc) (q f.succ-q f.castSucc) ≠ 0
  noTriple : NoTriple q
  anchor_avoid : ∀ e : Fin (n+1), ∀ i : Fin (n+2),
    i≠e.castSucc → i≠e.succ → ¬ edgeInterior q e (q i)

def crossingPoint (c : Crossing q) : PlanarPoint ℝ := Classical.choose c.property.2

theorem crossingPoint_mem (c : Crossing q) :
    edgeInterior q c.val.1 (crossingPoint q c) ∧
    edgeInterior q c.val.2 (crossingPoint q c) := Classical.choose_spec c.property.2

def leftParameter (c : Crossing q) : ℝ := Classical.choose (crossingPoint_mem q c).1
def rightParameter (c : Crossing q) : ℝ := Classical.choose (crossingPoint_mem q c).2

theorem leftParameter_spec (c : Crossing q) :
    0<leftParameter q c ∧ leftParameter q c<1 ∧
    crossingPoint q c = affinePoint (q c.val.1.castSucc) (q c.val.1.succ) (leftParameter q c) :=
  Classical.choose_spec (crossingPoint_mem q c).1

theorem rightParameter_spec (c : Crossing q) :
    0<rightParameter q c ∧ rightParameter q c<1 ∧
    crossingPoint q c = affinePoint (q c.val.2.castSucc) (q c.val.2.succ) (rightParameter q c) :=
  Classical.choose_spec (crossingPoint_mem q c).2

theorem crossingPoint_injective (h : NoTriple q) : Function.Injective (crossingPoint q) := by
  intro c d hp
  have hc := crossingPoint_mem q c
  have hd := crossingPoint_mem q d
  rw [← hp] at hd
  have hl : d.val.1=c.val.1 ∨ d.val.1=c.val.2 := by
    by_contra hh
    push_neg at hh
    exact h c.val.1 c.val.2 d.val.1 (crossingPoint q c)
      (ne_of_lt c.property.1) (Ne.symm hh.2) hh.1 ⟨hc.1,hc.2,hd.1⟩
  have hr : d.val.2=c.val.1 ∨ d.val.2=c.val.2 := by
    by_contra hh
    push_neg at hh
    exact h c.val.1 c.val.2 d.val.2 (crossingPoint q c)
      (ne_of_lt c.property.1) (Ne.symm hh.2) hh.1 ⟨hc.1,hc.2,hd.2⟩
  apply Subtype.ext
  rcases hl with hl|hl <;> rcases hr with hr|hr
  · exact False.elim ((ne_of_lt d.property.1) (hl.trans hr.symm))
  · exact Prod.ext hl.symm hr.symm
  · have hh : c.val.2<c.val.1 := by simpa [hl,hr] using d.property.1
    exact False.elim (lt_asymm c.property.1 hh)
  · exact False.elim ((ne_of_lt d.property.1) (hl.trans hr.symm))

abbrev Visit := Crossing q × Bool
def visitEdge (v : Visit q) : Fin (n+1) := if v.2 then v.1.val.2 else v.1.val.1
def visitParameter (v : Visit q) : ℝ := if v.2 then rightParameter q v.1 else leftParameter q v.1

theorem visitParameter_spec (v : Visit q) :
    0<visitParameter q v ∧ visitParameter q v<1 ∧
    crossingPoint q v.1 = affinePoint (q (visitEdge q v).castSucc)
      (q (visitEdge q v).succ) (visitParameter q v) := by
  rcases v with ⟨c,b⟩
  cases b
  · exact leftParameter_spec q c
  · exact rightParameter_spec q c

/-- Every anchor is retained as an event, including both endpoints. -/
def Event := Fin (n+2) ⊕ Visit q
instance eventFintype : Fintype (Event q) := by unfold Event Visit;infer_instance

def eventPoint : Event q → PlanarPoint ℝ
  | .inl i => q i
  | .inr v => crossingPoint q v.1

def edgeTag : Event q → ℕ
  | .inl i => i.val
  | .inr v => (visitEdge q v).val

def parameter : Event q → ℝ
  | .inl _ => 0
  | .inr v => visitParameter q v

def key (x : Event q) : ℕ × ℝ := (edgeTag q x,parameter q x)

theorem key_injective (h : NoTriple q) : Function.Injective (key q) := by
  intro x y hh
  have he := congrArg Prod.fst hh
  have ht := congrArg Prod.snd hh
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl (Fin.ext he)
    | inr v => exact False.elim ((ne_of_gt (visitParameter_spec q v).1) ht.symm)
  | inr v =>
    cases y with
    | inl i => exact False.elim ((ne_of_gt (visitParameter_spec q v).1) ht)
    | inr w =>
      have hev : visitEdge q v=visitEdge q w := Fin.ext he
      have hp : crossingPoint q v.1=crossingPoint q w.1 := by
        rw [(visitParameter_spec q v).2.2,(visitParameter_spec q w).2.2,hev]
        change affinePoint _ _ (visitParameter q v)=affinePoint _ _ (visitParameter q w)
        rw [show visitParameter q v=visitParameter q w from ht]
      have hc := crossingPoint_injective q h hp
      rcases v with ⟨c,b⟩;rcases w with ⟨d,a⟩
      dsimp at hc
      subst d
      cases b <;> cases a
      · rfl
      · exact False.elim ((ne_of_lt c.property.1) hev)
      · exact False.elim ((ne_of_lt c.property.1) hev.symm)
      · rfl

def eventOrder (h : NoTriple q) : LinearOrder (Event q) :=
  LinearOrder.lift' (fun x => toLex (key q x))
    (fun _ _ hh => key_injective q h (congrArg ofLex hh))

theorem event_lt_iff (h : NoTriple q) (x y : Event q) :
    (letI := eventOrder q h; x<y) ↔
    edgeTag q x<edgeTag q y ∨ edgeTag q x=edgeTag q y ∧ parameter q x<parameter q y := by
  change toLex (key q x)<toLex (key q y) ↔ _
  exact Prod.Lex.toLex_lt_toLex

def start : Event q := Sum.inl ⟨0,by omega⟩
def terminal : Event q := Sum.inl ⟨n+1,by omega⟩

theorem start_ne_terminal : start q ≠ terminal q := by
  intro hh
  have hv := congrArg Fin.val (Sum.inl.inj hh)
  dsimp [start,terminal] at hv
  omega

theorem start_le (h : NoTriple q) (x : Event q) :
    letI := eventOrder q h; start q ≤ x := by
  letI := eventOrder q h
  apply le_of_not_gt
  intro hh
  have hx := (event_lt_iff q h x (start q)).mp hh
  cases x with
  | inl i => simp [edgeTag,parameter,start] at hx
  | inr v =>
    rcases hx with hx|⟨_,hx⟩
    · change (visitEdge q v).val<0 at hx;omega
    · exact (not_lt_of_ge (le_of_lt (visitParameter_spec q v).1)) hx

theorem le_terminal (h : NoTriple q) (x : Event q) :
    letI := eventOrder q h; x ≤ terminal q := by
  letI := eventOrder q h
  apply le_of_not_gt
  intro hh
  have hx := (event_lt_iff q h (terminal q) x).mp hh
  cases x with
  | inl i =>
    simp only [edgeTag,parameter,terminal,lt_self_iff_false,and_false,or_false] at hx
    have := i.isLt;omega
  | inr v =>
    have hv := (visitEdge q v).isLt
    rcases hx with hx|⟨hx,_⟩ <;> simp only [edgeTag,terminal] at hx <;> omega

/-- Combinatorial cyclic successor of the LINE event order. Its wrap is not an edge. -/
def successor (h : NoTriple q) : Equiv.Perm (Event q) :=
  letI := eventOrder q h
  orderedCyclicSuccessor (Event q)

theorem successor_terminal (h : NoTriple q) : successor q h (terminal q)=start q := by
  letI := eventOrder q h
  apply orderedCyclicSuccessor_eq_of_order_spec
  exact Or.inr ⟨le_terminal q h,start_le q h⟩

def pairingMap (S : Finset (Crossing q)) : Event q → Event q := by
  classical
  exact fun x => match x with
  | .inl i => .inl i
  | .inr v => if v.1∈S then .inr (v.1,!v.2) else .inr v

theorem pairingMap_involutive (S : Finset (Crossing q)) : Function.Involutive (pairingMap q S) := by
  classical
  intro x
  cases x with
  | inl i => rfl
  | inr v =>
    rcases v with ⟨c,b⟩
    by_cases hc : c∈S <;> cases b <;> simp [pairingMap,hc]

def pairing (S : Finset (Crossing q)) : Equiv.Perm (Event q) where
  toFun := pairingMap q S
  invFun := pairingMap q S
  left_inv := pairingMap_involutive q S
  right_inv := pairingMap_involutive q S

/-- Incoming-event convention: take the paired outgoing branch, then its successor. -/
def incoming (h : NoTriple q) (S : Finset (Crossing q)) : Equiv.Perm (Event q) :=
  successor q h * pairing q S

theorem incoming_terminal_eq_start (h : NoTriple q) (S : Finset (Crossing q)) :
    incoming q h S (terminal q)=start q := successor_terminal q h

open PermutationOrbits

def openComponent (h : NoTriple q) (S : Finset (Crossing q)) : Component (incoming q h S) :=
  componentOf (incoming q h S) (start q)

theorem component_endpoints_eq (h : NoTriple q) (S : Finset (Crossing q)) :
    componentOf (incoming q h S) (terminal q)=openComponent q h S := by
  rw [← componentOf_apply (incoming q h S) (terminal q),incoming_terminal_eq_start]
  rfl

theorem closedComponent_avoids_endpoints (h : NoTriple q) (S : Finset (Crossing q))
    (C : Component (incoming q h S)) (hc : C≠openComponent q h S)
    (x : Fibre (incoming q h S) C) : x.val≠start q ∧ x.val≠terminal q := by
  constructor
  · intro hh;apply hc
    rw [← x.property,hh];rfl
  · intro hh;apply hc
    rw [← x.property,hh,component_endpoints_eq]

theorem unique_seam_predecessor (h : NoTriple q) (S : Finset (Crossing q)) (x : Event q) :
    incoming q h S x=start q ↔ x=terminal q := by
  rw [← incoming_terminal_eq_start q h S]
  exact (incoming q h S).injective.eq_iff

/-- All anchors survive, especially the initial and terminal endpoints. -/
def retained (S : Finset (Crossing q)) : Event q → Prop
  | .inl _ => True
  | .inr v => v.1∈S

theorem endpoints_retained (S : Finset (Crossing q)) : retained q S (start q) ∧ retained q S (terminal q) :=
  ⟨True.intro,True.intro⟩

end DirectGLSSW.ActiveArc
