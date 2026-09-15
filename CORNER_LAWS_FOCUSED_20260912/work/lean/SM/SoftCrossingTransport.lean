import Mathlib.Data.List.Nodup
import SM.CrossingTransport
import SM.FiniteChiStability
import Mathlib.Topology.Order.LeftRightNhds
import SM.WeakTopology
import SM.WallSegmentStability
import SM.CuspParameters
import Mathlib.Data.Fin.Tuple.Basic
import SM.SinglePointTriple
import SM.CriticalSourceResponse
import Mathlib.Tactic
import SM.SegmentStability
import SM.G1Consequences
import SM.CrossingCriterion
import SM.ContinuousGeometry
import Mathlib.Topology.Instances.Sign
import SM.GenericTopology
import SM.CyclicChambers
import SM.PairVisits
import SM.Traversal
import SM.GaussCyclicGap
import Mathlib.Tactic.NormNum
import SM.BoundaryTripleSupports
import SM.CanonicalTripleSigns
import SM.SoftInsertionIndices
import SM.SoftInsertionSuccessors
import SM.SoftInsertionTuple
import SM.SoftParentEdges
import SM.SoftInheritedParameters
import SM.SoftParentPairStability
import SM.SoftLocalDeterminants
import SM.SoftFamilyG1
import SM.SoftFamilyLocalCrossing
import SM.SoftEdgeAvoidance
import SM.SoftCrossingClassification
import SM.SoftFamilyG2

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftCrossingTransport.body.lean (prototype SoftFamilyAssembly, kernel session 44274, receipt
SoftFamilyAssembly-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- Pointwise persistence of every actual parent crossing pair. This helper
premise is derived on a common interval below. -/
def SoftCrossingPersistence (P : LabelledTuple n) (j : ZMod n) (q : Plane) (ε : ℝ) : Prop :=
  ∀ k l : ZMod n, IsCrossing P {k, l} →
    IsCrossing (softInsertion P j q ε) {softParentEdge j k, softParentEdge j l}

/-- The exact frozen support classification at a fixed parameter, with no
chosen crossing correspondence hidden in the definition. -/
def SoftCrossingClassificationAt (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (ε : ℝ) : Prop :=
  ∀ s : Finset (ZMod (n + 1)), IsCrossing (softInsertion P j q ε) s ↔
    (∃ k l : ZMod n, IsCrossing P {k, l} ∧ s = {softParentEdge j k, softParentEdge j l}) ∨
    (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) ∧
      s = {softOldIndex j (j - 1), softNewIndex j}

/-- All helper premises, including child Generic, are derived on one positive
interval from the actual source hypotheses. Zero is not a Generic basepoint. -/
theorem soft_small_crossing_transport_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      Generic (softInsertion P j q ε) ∧ SoftCrossingPersistence P j q ε ∧
        SoftCrossingClassificationAt P j q ε := by
  obtain ⟨δp, hδp, hpair⟩ := soft_small_remote_pairs hn hP.1 j q
  obtain ⟨δc, hδc, hclass⟩ := soft_crossing_support_classification hn hP.1 j q hq
  obtain ⟨δg, hδg, hgen⟩ := softInsertion_small_Generic hn hP j q hq
  refine ⟨min δp (min δc δg), lt_min hδp (lt_min hδc hδg), ?_⟩
  intro ε hε hεδ
  have hεp : |ε| < δp := by
    simpa only [abs_of_pos hε] using lt_of_lt_of_le hεδ (min_le_left δp (min δc δg))
  have hεc : ε < δc := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δp (min δc δg)) (min_le_left δc δg))
  have hεg : ε < δg := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δp (min δc δg)) (min_le_right δc δg))
  refine ⟨hgen ε hε hεg, ?_, hclass ε hε hεc⟩
  intro k l hc
  exact (hpair ε hεp k l (crossing_pair_remote hc)).mpr hc

variable {P : LabelledTuple n} {j : ZMod n} {q : Plane} {ε : ℝ}

/-- The inherited crossing is the actual image of its unordered support. -/
def softInheritedCrossing (hp : SoftCrossingPersistence P j q ε) (c : Crossing P) :
    Crossing (softInsertion P j q ε) :=
  ⟨c.val.image (softParentEdge j), by
    obtain ⟨k, l, hs, _, _⟩ := c.property
    have hc : IsCrossing P {k, l} := hs ▸ c.property
    simpa only [hs, Finset.image_insert, Finset.image_singleton] using hp k l hc⟩

theorem softInheritedCrossing_support (hp : SoftCrossingPersistence P j q ε)
    (c : Crossing P) :
    (softInheritedCrossing hp c).val = c.val.image (softParentEdge j) := rfl

theorem softInheritedCrossing_injective (hp : SoftCrossingPersistence P j q ε) :
    Function.Injective (softInheritedCrossing hp) := by
  intro c d he
  apply Subtype.ext
  exact Finset.image_injective (softParentEdge_injective j) (congrArg Subtype.val he)

/-- The incoming/return support is never an inherited actual parent crossing. -/
theorem softInheritedCrossing_ne_newborn (hn : 3 ≤ n)
    (hp : SoftCrossingPersistence P j q ε) (c : Crossing P) :
    (softInheritedCrossing hp c).val ≠ {softOldIndex j (j - 1), softNewIndex j} := by
  obtain ⟨k, l, hs, _, _⟩ := c.property
  have hc : IsCrossing P {k, l} := hs ▸ c.property
  simpa only [softInheritedCrossing_support, hs, Finset.image_insert, Finset.image_singleton]
    using soft_newborn_support_not_inherited hn P j k l hc

/-- Exact range, in every sector: all child crossings except the possible
newborn support, rather than a freely supplied image predicate. -/
theorem softInheritedCrossing_range_iff (hn : 3 ≤ n)
    (hp : SoftCrossingPersistence P j q ε) (hclass : SoftCrossingClassificationAt P j q ε)
    (d : Crossing (softInsertion P j q ε)) :
    (∃ c : Crossing P, softInheritedCrossing hp c = d) ↔
      d.val ≠ {softOldIndex j (j - 1), softNewIndex j} := by
  constructor
  · rintro ⟨c, rfl⟩
    exact softInheritedCrossing_ne_newborn hn hp c
  · intro hne
    rcases (hclass d.val).mp d.property with ⟨k, l, hc, hs⟩ | ⟨_, hs⟩
    · refine ⟨⟨{k, l}, hc⟩, Subtype.ext ?_⟩
      change ({k, l} : Finset (ZMod n)).image (softParentEdge j) = d.val
      simpa only [Finset.image_insert, Finset.image_singleton] using hs.symm
    · exact (hne hs).elim

/-- An equivalence onto precisely the inherited child-crossing subtype. -/
def softInheritedCrossingEquiv (hn : 3 ≤ n) (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε) :
    Crossing P ≃ {d : Crossing (softInsertion P j q ε) //
      d.val ≠ {softOldIndex j (j - 1), softNewIndex j}} := by
  let f : Crossing P → {d : Crossing (softInsertion P j q ε) //
      d.val ≠ {softOldIndex j (j - 1), softNewIndex j}} := fun c =>
    ⟨softInheritedCrossing hp c, softInheritedCrossing_ne_newborn hn hp c⟩
  apply Equiv.ofBijective f
  constructor
  · intro c d he
    exact softInheritedCrossing_injective hp (congrArg Subtype.val he)
  · intro d
    obtain ⟨c, hc⟩ := (softInheritedCrossing_range_iff hn hp hclass d.val).mpr d.property
    exact ⟨c, Subtype.ext hc⟩

theorem softInheritedCrossing_surjective_nonloop (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)) :
    Function.Surjective (softInheritedCrossing hp) := by
  intro d
  rcases (hclass d.val).mp d.property with ⟨k, l, hc, hs⟩ | ⟨hloop, _⟩
  · refine ⟨⟨{k, l}, hc⟩, Subtype.ext ?_⟩
    change ({k, l} : Finset (ZMod n)).image (softParentEdge j) = d.val
    simpa only [Finset.image_insert, Finset.image_singleton] using hs.symm
  · exact (hnot hloop).elim

/-- In every non-loop sector the actual inherited crossing map is a bijection. -/
def softCrossingEquivNonloop (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)) :
    Crossing P ≃ Crossing (softInsertion P j q ε) :=
  Equiv.ofBijective (softInheritedCrossing hp)
    ⟨softInheritedCrossing_injective hp, softInheritedCrossing_surjective_nonloop hp hclass hnot⟩

/-- The actual newborn crossing selected by the proved loop-sector support. -/
def softNewbornCrossing (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    Crossing (softInsertion P j q ε) :=
  ⟨{softOldIndex j (j - 1), softNewIndex j},
    (hclass _).mpr (Or.inr ⟨hloop, rfl⟩)⟩

theorem softNewbornCrossing_support (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    (softNewbornCrossing hclass hloop).val =
      {softOldIndex j (j - 1), softNewIndex j} := rfl

theorem softInheritedCrossing_range_loop (hn : 3 ≤ n)
    (hp : SoftCrossingPersistence P j q ε) (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
    (d : Crossing (softInsertion P j q ε)) :
    (∃ c : Crossing P, softInheritedCrossing hp c = d) ↔ d ≠ softNewbornCrossing hclass hloop := by
  rw [softInheritedCrossing_range_iff hn hp hclass]
  constructor
  · intro hne he
    exact hne (congrArg Subtype.val he)
  · intro hne he
    exact hne (Subtype.ext he)

/-- A visit is transported by its crossing image and the image of its actual
member edge; no independently chosen edge or visit correspondence is supplied. -/
def softInheritedVisit (hp : SoftCrossingPersistence P j q ε) (v : Visit P) :
    Visit (softInsertion P j q ε) :=
  ⟨softInheritedCrossing hp v.1, softParentEdge j v.2.val,
    Finset.mem_image.mpr ⟨v.2.val, v.2.property, rfl⟩⟩

theorem softInheritedVisit_crossing (hp : SoftCrossingPersistence P j q ε) (v : Visit P) :
    (softInheritedVisit hp v).1 = softInheritedCrossing hp v.1 := rfl

theorem softInheritedVisit_edge (hp : SoftCrossingPersistence P j q ε) (v : Visit P) :
    (softInheritedVisit hp v).2.val = softParentEdge j v.2.val := rfl

theorem softInheritedVisit_injective (hp : SoftCrossingPersistence P j q ε) :
    Function.Injective (softInheritedVisit hp) := by
  intro v w he
  apply visit_ext
  · exact congrArg Subtype.val (softInheritedCrossing_injective hp (congrArg Sigma.fst he))
  · exact softParentEdge_injective j
      (congrArg (fun u : Visit (softInsertion P j q ε) => u.2.val) he)

/-- The two visits of each inherited crossing keep exactly their pairing. -/
theorem softInheritedVisit_pairing (hp : SoftCrossingPersistence P j q ε) (v w : Visit P) :
    (softInheritedVisit hp v).1 = (softInheritedVisit hp w).1 ↔ v.1 = w.1 :=
  (softInheritedCrossing_injective hp).eq_iff

/-- Every member-edge visit of an inherited crossing is inherited. -/
theorem softInheritedVisit_range_crossing_iff (hp : SoftCrossingPersistence P j q ε)
    (w : Visit (softInsertion P j q ε)) :
    (∃ v : Visit P, softInheritedVisit hp v = w) ↔
      ∃ c : Crossing P, softInheritedCrossing hp c = w.1 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v.1, rfl⟩
  · rintro ⟨c, hc⟩
    have hm : w.2.val ∈ (softInheritedCrossing hp c).val := by
      rw [hc]
      exact w.2.property
    change w.2.val ∈ c.val.image (softParentEdge j) at hm
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
    exact ⟨⟨c, i, hi⟩, visit_ext (congrArg Subtype.val hc) he⟩

theorem softInheritedVisit_range_iff (hn : 3 ≤ n)
    (hp : SoftCrossingPersistence P j q ε) (hclass : SoftCrossingClassificationAt P j q ε)
    (w : Visit (softInsertion P j q ε)) :
    (∃ v : Visit P, softInheritedVisit hp v = w) ↔
      w.1.val ≠ {softOldIndex j (j - 1), softNewIndex j} :=
  (softInheritedVisit_range_crossing_iff hp w).trans
    (softInheritedCrossing_range_iff hn hp hclass w.1)

/-- The visit equivalence onto the exact inherited subtype is suitable for
filtering child Gauss lists before proving their order. -/
def softInheritedVisitEquiv (hn : 3 ≤ n) (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε) :
    Visit P ≃ {w : Visit (softInsertion P j q ε) //
      w.1.val ≠ {softOldIndex j (j - 1), softNewIndex j}} := by
  let f : Visit P → {w : Visit (softInsertion P j q ε) //
      w.1.val ≠ {softOldIndex j (j - 1), softNewIndex j}} := fun v =>
    ⟨softInheritedVisit hp v, softInheritedCrossing_ne_newborn hn hp v.1⟩
  apply Equiv.ofBijective f
  constructor
  · intro v w he
    exact softInheritedVisit_injective hp (congrArg Subtype.val he)
  · intro w
    obtain ⟨v, hv⟩ := (softInheritedVisit_range_iff hn hp hclass w.val).mpr w.property
    exact ⟨v, Subtype.ext hv⟩

theorem softInheritedVisit_surjective_nonloop (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)) :
    Function.Surjective (softInheritedVisit hp) := by
  intro w
  exact (softInheritedVisit_range_crossing_iff hp w).mpr
    (softInheritedCrossing_surjective_nonloop hp hclass hnot w.1)

def softVisitEquivNonloop (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)) :
    Visit P ≃ Visit (softInsertion P j q ε) :=
  Equiv.ofBijective (softInheritedVisit hp)
    ⟨softInheritedVisit_injective hp, softInheritedVisit_surjective_nonloop hp hclass hnot⟩

theorem softInheritedVisit_range_loop (hn : 3 ≤ n)
    (hp : SoftCrossingPersistence P j q ε) (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
    (w : Visit (softInsertion P j q ε)) :
    (∃ v : Visit P, softInheritedVisit hp v = w) ↔ w.1 ≠ softNewbornCrossing hclass hloop :=
  (softInheritedVisit_range_crossing_iff hp w).trans
    (softInheritedCrossing_range_loop hn hp hclass hloop w.1)

/-- Canonical actual visitParameter equals the transported edgeParameter,
for any representation of that visit's two-element parent support. -/
theorem softInheritedVisit_parameter (hn : 3 ≤ n) (hp : SoftCrossingPersistence P j q ε)
    (hQ : G1 (softInsertion P j q ε)) (v : Visit P) (l : ZMod n)
    (hs : v.1.val = {v.2.val, l}) :
    visitParameter (softInheritedVisit hp v) =
      edgeParameter (softInsertion P j q ε) (softParentEdge j v.2.val) (softParentEdge j l) := by
  have hpair : (softInheritedVisit hp v).1.val =
      {softParentEdge j v.2.val, softParentEdge j l} := by
    change v.1.val.image (softParentEdge j) = _
    have himage := congrArg (fun s : Finset (ZMod n) => s.image (softParentEdge j)) hs
    simpa only [Finset.image_insert, Finset.image_singleton] using himage
  have hc : IsCrossing (softInsertion P j q ε)
      {softParentEdge j v.2.val, softParentEdge j l} := hpair ▸ (softInheritedVisit hp v).1.property
  have he : softInheritedVisit hp v = pairVisit hc := visit_ext hpair rfl
  rw [he]
  exact pairVisit_parameter (by omega : 3 ≤ n + 1) hQ hc

/-- Every source visit has such a partner label; no partner-selection oracle
is required to use the preceding parameter formula. -/
theorem softInheritedVisit_parameter_exists (hn : 3 ≤ n)
    (hp : SoftCrossingPersistence P j q ε) (hQ : G1 (softInsertion P j q ε)) (v : Visit P) :
    ∃ l : ZMod n, l ≠ v.2.val ∧ v.1.val = {v.2.val, l} ∧
      visitParameter (softInheritedVisit hp v) =
        edgeParameter (softInsertion P j q ε) (softParentEdge j v.2.val) (softParentEdge j l) := by
  obtain ⟨l, hl, hs⟩ := crossing_pair_of_mem v.1 v.2.val v.2.property
  exact ⟨l, hl, hs, softInheritedVisit_parameter hn hp hQ v l hs⟩

end
end SM
