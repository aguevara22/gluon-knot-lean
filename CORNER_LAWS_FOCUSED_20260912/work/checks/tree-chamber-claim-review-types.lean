import SM.Gates
import SM.FiniteCompositions
import SM.CyclicChambers
import Mathlib.Tactic
set_option pp.fullNames true
set_option pp.universes false
namespace SM

noncomputable section

universe u

variable {n : ℕ} [NeZero n] {R : Type u} [CommRing R]

/-- The open source recursion with arbitrary independent ordinary weights.
The complete raw composition type is finite by the proved encoding; every
recursive call has strictly fewer leaves by the proved child-size theorem. -/
def openTreeRec (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) : R :=
  if I.leaves = 1 then 1 else
    -∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
      ordinary I π.val * ∏ k : Fin π.val.parts, openTreeRec ordinary (π.val.part k)
termination_by I.leaves
decreasing_by exact π.val.part_leaves_lt π.property k

/-- The distinguished root may have one child and carries no extra minus sign. -/
def rootedTreeRec (ordinary rootWeight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) : R :=
  ∑ π : IntervalComposition I,
    rootWeight I π * ∏ k : Fin π.parts, openTreeRec ordinary (π.part k)

theorem openTreeRec_one (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) (hI : I.leaves = 1) : openTreeRec ordinary I = 1 := by
  rw [openTreeRec]
  simp [hI]

theorem openTreeRec_many (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) (hI : 2 ≤ I.leaves) :
    openTreeRec ordinary I =
      -∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        ordinary I π.val * ∏ k : Fin π.val.parts, openTreeRec ordinary (π.val.part k) := by
  rw [openTreeRec]
  simp [show I.leaves ≠ 1 by omega]

def fullBoundaryInterval (hn : 3 ≤ n) : BoundaryInterval n where
  left := ⟨0, by omega⟩
  right := ⟨n - 1, by omega⟩
  increasing := by change 0 < n - 1; omega

def openTreeSum (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (I : BoundaryInterval n) : ℤ :=
  openTreeRec (fun _ π => π.ordinaryWeight P hP g) I

def treeCoefficient (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) (hn : 3 ≤ n) : ℤ :=
  rootedTreeRec (fun _ π => π.ordinaryWeight P hP g)
    (fun _ π => π.rootWeight P hP g) (fullBoundaryInterval hn)

/-- The main text's last-edge root n is residue zero in the source label convention. -/
def mainTreeCoefficient (P : LabelledTuple n) (hP : G1 P) (hn : 3 ≤ n) : ℤ :=
  treeCoefficient P hP 0 hn

theorem openTreeSum_one (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (I : BoundaryInterval n) (hI : I.leaves = 1) : openTreeSum P hP g I = 1 :=
  openTreeRec_one _ I hI

theorem openTreeSum_many (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (I : BoundaryInterval n) (hI : 2 ≤ I.leaves) :
    openTreeSum P hP g I =
      -∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        π.val.ordinaryWeight P hP g * ∏ k : Fin π.val.parts, openTreeSum P hP g (π.val.part k) :=
  openTreeRec_many _ I hI

theorem treeCoefficient_eq (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient P hP g hn =
      ∑ π : IntervalComposition (fullBoundaryInterval hn),
        π.rootWeight P hP g * ∏ k : Fin π.parts, openTreeSum P hP g (π.part k) := rfl

/-- Source def:treesum, including all open interval sums and the rooted output. -/
def treesumData (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) (hn : 3 ≤ n) :=
  (openTreeSum P hP g, treeCoefficient P hP g hn, mainTreeCoefficient P hP hn)

end

end SM

namespace SM

noncomputable section

variable {n : ℕ} [NeZero n]

namespace IntervalComposition

variable {I : BoundaryInterval n} (π : IntervalComposition I)

theorem nearSign_eq_of_chi {P Q : LabelledTuple n}
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (k : Fin (π.parts - 1)) :
    π.nearSign P g k = π.nearSign Q g k := hchi _ _ _

theorem farSign_eq_of_chi {P Q : LabelledTuple n}
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (k : Fin (π.parts - 1)) :
    π.farSign P g k = π.farSign Q g k := hchi _ _ _

theorem ordinaryWeight_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) :
    π.ordinaryWeight P hP g = π.ordinaryWeight Q hQ g :=
  π.ordinaryWeight_eq_of_signs _ _ _ _ _ _ (π.nearSign_eq_of_chi hchi g)
    (π.farSign_eq_of_chi hchi g)

theorem rootWeight_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) :
    π.rootWeight P hP g = π.rootWeight Q hQ g :=
  π.rootWeight_eq_of_signs _ _ _ _ _ _ (π.nearSign_eq_of_chi hchi g)
    (π.farSign_eq_of_chi hchi g)

end IntervalComposition

theorem openTreeSum_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (I : BoundaryInterval n) :
    openTreeSum P hP g I = openTreeSum Q hQ g I := by
  unfold openTreeSum
  congr 1
  funext J π
  exact π.ordinaryWeight_eq_of_chi hP hQ hchi g

theorem treeCoefficient_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient P hP g hn = treeCoefficient Q hQ g hn := by
  unfold treeCoefficient
  congr 1
  · funext J π
    exact π.ordinaryWeight_eq_of_chi hP hQ hchi g
  · funext J π
    exact π.rootWeight_eq_of_chi hP hQ hchi g

theorem openTreeSum_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n)
    (I : BoundaryInterval n) :
    openTreeSum (shift a P) (g1_shift_forward a hP) (g - a) I = openTreeSum P hP g I := by
  unfold openTreeSum
  congr 1
  funext J π
  exact π.ordinaryWeight_shift P hP g a

theorem treeCoefficient_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient (shift a P) (g1_shift_forward a hP) (g - a) hn =
      treeCoefficient P hP g hn := by
  unfold treeCoefficient
  congr 1
  · funext J π
    exact π.ordinaryWeight_shift P hP g a
  · funext J π
    exact π.rootWeight_shift P hP g a

/-- Fixed label zero on the shifted representative corresponds to label a on
the original representative. No independence of different physical roots is assumed. -/
theorem mainTreeCoefficient_shift (P : LabelledTuple n) (hP : G1 P) (a : ZMod n) (hn : 3 ≤ n) :
    mainTreeCoefficient (shift a P) (g1_shift_forward a hP) hn = treeCoefficient P hP a hn := by
  simpa only [mainTreeCoefficient, sub_self] using treeCoefficient_shift P hP a a hn

theorem treesumData_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n) (hn : 3 ≤ n) :
    treesumData (shift a P) (g1_shift_forward a hP) (g - a) hn =
      (openTreeSum P hP g, treeCoefficient P hP g hn, treeCoefficient P hP a hn) := by
  unfold treesumData
  rw [funext (openTreeSum_shift P hP g a), treeCoefficient_shift P hP g a hn,
    mainTreeCoefficient_shift P hP a hn]

end

end SM

namespace SM

noncomputable section

variable {n : ℕ} [NeZero n]

/-- All quantities in the source chirotope-constancy clause, on G1 alone. -/
theorem tree_data_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (hn : 3 ≤ n) :
    (∀ (I : BoundaryInterval n) (π : IntervalComposition I),
      π.ordinaryWeight P hP g = π.ordinaryWeight Q hQ g ∧
      π.rootWeight P hP g = π.rootWeight Q hQ g) ∧
    (∀ I, openTreeSum P hP g I = openTreeSum Q hQ g I) ∧
    treeCoefficient P hP g hn = treeCoefficient Q hQ g hn :=
  ⟨fun _ π => ⟨π.ordinaryWeight_eq_of_chi hP hQ hchi g,
    π.rootWeight_eq_of_chi hP hQ hchi g⟩,
    openTreeSum_eq_of_chi hP hQ hchi g, treeCoefficient_eq_of_chi hP hQ hchi g hn⟩

/-- The labelled chamber is the actual connected component of the generic locus.
Its continuous sign maps have discrete target, so they are constant on it. -/
theorem labelled_chamber_chi_constant (P Q : GenericTuple n) (hQ : Q ∈ labelledChamber P)
    (i j k : ZMod n) : chi P.val i j k = chi Q.val i j k := by
  exact isPreconnected_connectedComponent.constant
    (continuous_generic_chi i j k).continuousOn mem_connectedComponent hQ

theorem tree_data_labelled_chamber_constant (P Q : GenericTuple n)
    (hQ : Q ∈ labelledChamber P) (g : ZMod n) (hn : 3 ≤ n) :
    (∀ (I : BoundaryInterval n) (π : IntervalComposition I),
      π.ordinaryWeight P.val P.property.1 g = π.ordinaryWeight Q.val Q.property.1 g ∧
      π.rootWeight P.val P.property.1 g = π.rootWeight Q.val Q.property.1 g) ∧
    (∀ I, openTreeSum P.val P.property.1 g I = openTreeSum Q.val Q.property.1 g I) ∧
    treeCoefficient P.val P.property.1 g hn = treeCoefficient Q.val Q.property.1 g hn :=
  tree_data_eq_of_chi P.property.1 Q.property.1 (labelled_chamber_chi_constant P Q hQ) g hn

/-- The path clause retains G1 only. Its asserted constant chirotope already
forces all values to agree; no further geometric condition is needed. -/
theorem tree_data_G1_path_constant {P Q : {P : LabelledTuple n // G1 P}}
    (γ : Path P Q)
    (hchi : ∀ s t : unitInterval, ∀ i j k, chi (γ s).val i j k = chi (γ t).val i j k)
    (g : ZMod n) (hn : 3 ≤ n) (s t : unitInterval) :
    (∀ (I : BoundaryInterval n) (π : IntervalComposition I),
      π.ordinaryWeight (γ s).val (γ s).property g =
        π.ordinaryWeight (γ t).val (γ t).property g ∧
      π.rootWeight (γ s).val (γ s).property g = π.rootWeight (γ t).val (γ t).property g) ∧
    (∀ I, openTreeSum (γ s).val (γ s).property g I =
      openTreeSum (γ t).val (γ t).property g I) ∧
    treeCoefficient (γ s).val (γ s).property g hn =
      treeCoefficient (γ t).val (γ t).property g hn :=
  tree_data_eq_of_chi (γ s).property (γ t).property (hchi s t) g hn

/-- On the actual unlabelled chamber, a label change must carry the root with it.
The proved chamber preimage theorem supplies the shift; this does not assume
independence of different physical roots. -/
theorem treeCoefficient_quotient_chamber_transport (P Q : GenericTuple n)
    (hn : 3 ≤ n) (hQ : polygonProjection Q ∈ chamber (polygonProjection P)) :
    ∃ a : ZMod n, Q ∈ labelledChamber (genericShift a P) ∧
      ∀ g : ZMod n, treeCoefficient Q.val Q.property.1 (g - a) hn =
        treeCoefficient P.val P.property.1 g hn := by
  have hm : Q ∈ ⋃ a : ZMod n, labelledChamber (genericShift a P) := by
    rw [← chamber_preimage_eq_cyclic_union hn P]
    exact hQ
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hm
  refine ⟨a, ha, ?_⟩
  intro g
  have he := (tree_data_labelled_chamber_constant (genericShift a P) Q ha (g - a) hn).2.2
  exact he.symm.trans (treeCoefficient_shift P.val P.property.1 g a hn)

end

end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The exact quantities named in the chirotope-constancy proposition. -/
def TreeDataEqual (P Q : LabelledTuple n) (hP : G1 P) (hQ : G1 Q)
    (g : ZMod n) (hn : 3 ≤ n) : Prop :=
  (∀ (I : BoundaryInterval n) (π : IntervalComposition I),
    π.ordinaryWeight P hP g = π.ordinaryWeight Q hQ g ∧
    π.rootWeight P hP g = π.rootWeight Q hQ g) ∧
  (∀ I, openTreeSum P hP g I = openTreeSum Q hQ g I) ∧
  treeCoefficient P hP g hn = treeCoefficient Q hQ g hn

/-- Source prop:A-chamber, with actual connected-component chambers and actual
G1 paths. Label changes in the unlabelled chamber carry the physical root,
as required by the source representative convention. -/
theorem A_chamber (hn : 3 ≤ n) :
    (∀ (P Q : LabelledTuple n) (hP : G1 P) (hQ : G1 Q),
      (∀ i j k, chi P i j k = chi Q i j k) →
      ∀ g, TreeDataEqual P Q hP hQ g hn) ∧
    (∀ (P Q : GenericTuple n), Q ∈ labelledChamber P →
      ∀ g, TreeDataEqual P.val Q.val P.property.1 Q.property.1 g hn) ∧
    (∀ (P Q : GenericTuple n), polygonProjection Q ∈ chamber (polygonProjection P) →
      ∃ a : ZMod n, Q ∈ labelledChamber (genericShift a P) ∧
        ∀ g : ZMod n, treeCoefficient Q.val Q.property.1 (g - a) hn =
          treeCoefficient P.val P.property.1 g hn) ∧
    (∀ (P Q : {P : LabelledTuple n // G1 P}) (γ : Path P Q),
      (∀ s t : unitInterval, ∀ i j k, chi (γ s).val i j k = chi (γ t).val i j k) →
      ∀ g (s t : unitInterval),
        TreeDataEqual (γ s).val (γ t).val (γ s).property (γ t).property g hn) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P Q hP hQ hchi g
    exact tree_data_eq_of_chi hP hQ hchi g hn
  · intro P Q hQ g
    exact tree_data_labelled_chamber_constant P Q hQ g hn
  · intro P Q hQ
    exact treeCoefficient_quotient_chamber_transport P Q hn hQ
  · intro P Q γ hchi g s t
    exact tree_data_G1_path_constant γ hchi g hn s t

end

end SM

#check SM.openTreeRec
#print axioms SM.openTreeRec
#check SM.rootedTreeRec
#print axioms SM.rootedTreeRec
#check SM.openTreeRec_one
#print axioms SM.openTreeRec_one
#check SM.openTreeRec_many
#print axioms SM.openTreeRec_many
#check SM.fullBoundaryInterval
#print axioms SM.fullBoundaryInterval
#check SM.openTreeSum
#print axioms SM.openTreeSum
#check SM.treeCoefficient
#print axioms SM.treeCoefficient
#check SM.mainTreeCoefficient
#print axioms SM.mainTreeCoefficient
#check SM.openTreeSum_one
#print axioms SM.openTreeSum_one
#check SM.openTreeSum_many
#print axioms SM.openTreeSum_many
#check SM.treeCoefficient_eq
#print axioms SM.treeCoefficient_eq
#check SM.treesumData
#print axioms SM.treesumData
#check SM.IntervalComposition.nearSign_eq_of_chi
#print axioms SM.IntervalComposition.nearSign_eq_of_chi
#check SM.IntervalComposition.farSign_eq_of_chi
#print axioms SM.IntervalComposition.farSign_eq_of_chi
#check SM.IntervalComposition.ordinaryWeight_eq_of_chi
#print axioms SM.IntervalComposition.ordinaryWeight_eq_of_chi
#check SM.IntervalComposition.rootWeight_eq_of_chi
#print axioms SM.IntervalComposition.rootWeight_eq_of_chi
#check SM.openTreeSum_eq_of_chi
#print axioms SM.openTreeSum_eq_of_chi
#check SM.treeCoefficient_eq_of_chi
#print axioms SM.treeCoefficient_eq_of_chi
#check SM.openTreeSum_shift
#print axioms SM.openTreeSum_shift
#check SM.treeCoefficient_shift
#print axioms SM.treeCoefficient_shift
#check SM.mainTreeCoefficient_shift
#print axioms SM.mainTreeCoefficient_shift
#check SM.treesumData_shift
#print axioms SM.treesumData_shift
#check SM.tree_data_eq_of_chi
#print axioms SM.tree_data_eq_of_chi
#check SM.labelled_chamber_chi_constant
#print axioms SM.labelled_chamber_chi_constant
#check SM.tree_data_labelled_chamber_constant
#print axioms SM.tree_data_labelled_chamber_constant
#check SM.tree_data_G1_path_constant
#print axioms SM.tree_data_G1_path_constant
#check SM.treeCoefficient_quotient_chamber_transport
#print axioms SM.treeCoefficient_quotient_chamber_transport
#check SM.TreeDataEqual
#print axioms SM.TreeDataEqual
#check SM.A_chamber
#print axioms SM.A_chamber
#print SM.TreeDataEqual
namespace TreeChamberClaimIndependentReview
open SM
variable {n : ℕ} [NeZero n]

theorem complete_G1_quantities (hn : 3 ≤ n) (P Q : LabelledTuple n)
    (hP : G1 P) (hQ : G1 Q) (hc : ∀ i j k, chi P i j k = chi Q i j k)
    (g : ZMod n) :
    (∀ I (π : IntervalComposition I),
      π.ordinaryWeight P hP g = π.ordinaryWeight Q hQ g ∧
      π.rootWeight P hP g = π.rootWeight Q hQ g) ∧
    (∀ I, openTreeSum P hP g I = openTreeSum Q hQ g I) ∧
    treeCoefficient P hP g hn = treeCoefficient Q hQ g hn :=
  (A_chamber hn).1 P Q hP hQ hc g

theorem actual_connected_component (hn : 3 ≤ n) (P Q : GenericTuple n)
    (hQ : Q ∈ connectedComponent P) (g : ZMod n) :
    TreeDataEqual P.val Q.val P.property.1 Q.property.1 g hn :=
  (A_chamber hn).2.1 P Q hQ g

theorem actual_G1_path (hn : 3 ≤ n) (P Q : {P : LabelledTuple n // G1 P})
    (γ : Path P Q)
    (hc : ∀ s t : unitInterval, ∀ i j k, chi (γ s).val i j k = chi (γ t).val i j k)
    (g : ZMod n) (s t : unitInterval) :
    TreeDataEqual (γ s).val (γ t).val (γ s).property (γ t).property g hn :=
  (A_chamber hn).2.2.2 P Q γ hc g s t

-- The quotient statement exposes an actual labelled component and a single
-- coherent cyclic relabelling of every physical root. All weights and open
-- sums transport as well; this does not choose a new arbitrary fixed root.
theorem all_quantities_under_quotient_transport (hn : 3 ≤ n) (P Q : GenericTuple n)
    (hQ : polygonProjection Q ∈ chamber (polygonProjection P)) :
    ∃ a : ZMod n, Q ∈ connectedComponent (genericShift a P) ∧
      ∀ g : ZMod n,
        (∀ I (π : IntervalComposition I),
          π.ordinaryWeight Q.val Q.property.1 (g - a) = π.ordinaryWeight P.val P.property.1 g ∧
          π.rootWeight Q.val Q.property.1 (g - a) = π.rootWeight P.val P.property.1 g) ∧
        (∀ I, openTreeSum Q.val Q.property.1 (g - a) I = openTreeSum P.val P.property.1 g I) ∧
        treeCoefficient Q.val Q.property.1 (g - a) hn = treeCoefficient P.val P.property.1 g hn := by
  obtain ⟨a, ha, hcoef⟩ := (A_chamber hn).2.2.1 P Q hQ
  refine ⟨a, ha, ?_⟩
  intro g
  have he := (A_chamber hn).2.1 (genericShift a P) Q ha (g - a)
  refine ⟨?_, ?_, hcoef g⟩
  · intro I π
    exact ⟨(he.1 I π).1.symm.trans (π.ordinaryWeight_shift P.val P.property.1 g a),
      (he.1 I π).2.symm.trans (π.rootWeight_shift P.val P.property.1 g a)⟩
  · intro I
    exact (he.2.1 I).symm.trans (openTreeSum_shift P.val P.property.1 g a I)

end TreeChamberClaimIndependentReview

#print axioms TreeChamberClaimIndependentReview.complete_G1_quantities
#print axioms TreeChamberClaimIndependentReview.actual_connected_component
#print axioms TreeChamberClaimIndependentReview.actual_G1_path
#print axioms TreeChamberClaimIndependentReview.all_quantities_under_quotient_transport
