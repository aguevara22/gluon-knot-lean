import DirectGLSSW.ShortEdgeSpanning
import DirectGLSSW.ShortEdgeSpanningPullback
import DirectGLSSW.ShortEdgeSpliceProducts
import DirectGLSSW.ShortEdgeSpanningBranches

namespace DirectGLSSW.ShortEdgeWeighted.SpanningBothImpl
open DirectGLSSW.ShortEdgeWeighted
open DirectGLSSW.ShortEdgeWeighted.SpliceProductsImpl
open DirectGLSSW.ShortEdgeWeighted.SpanningPullbackImpl
open DirectGLSSW.ShortEdgeWeighted.SpanningBranchesImpl
open scoped BigOperators

private theorem pairwise_rel_append {α : Type} {R : α → α → Prop} :
    ∀ (xs ys : List α), (xs ++ ys).Pairwise R →
      ∀ x ∈ xs, ∀ y ∈ ys, R x y
  | [], _, _, _, hx, _, _ => by simp at hx
  | z :: xs, ys, hp, x, hx, y, hy => by
      change (z :: (xs ++ ys)).Pairwise R at hp
      simp only [List.pairwise_cons] at hp
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hp.1 y (List.mem_append.mpr (Or.inr hy))
      · exact pairwise_rel_append xs ys hp.2 x hx y hy

set_option maxHeartbeats 1000000 in
theorem spanCandidate_cutAtBoth_contribution_factor
    (a i j : ℕ) (ha : 0 < a) (hiA : i < a) (hBj : a + 1 < j)
    (t : ℕ → Sign) (U : IntervalArray) (η : Sign) (D : TripleArray)
    (H : ℕ → ℕ → ℕ → Sign) (S : Finset ℕ) (haS : a ∈ S)
    (hS : S ⊆ Finset.Ioo i (ShortEdgeCutFibers.collapseAfter a j)) :
    ∃ pre L R post,
      cutVertices (ShortEdgeCutFibers.collapseAfter a i)
        (ShortEdgeCutFibers.collapseAfter a j) S = pre ++ [L, a, R] ++ post ∧
      L < a ∧ a < R ∧
      cutVertices i j (ShortEdgeCutFibers.spanCandidate a S
        ShortEdgeCutFibers.SpanLiftMode.cutAtBoth) =
        pre.map (ShortEdgeCutFibers.liftAfter a) ++ [L, a, a + 1, R + 1] ++
          post.map (ShortEdgeCutFibers.liftAfter a) ∧
      cutContribution (D1 a t D)
          (fun x k y => -η.value * H1 a t H x k y)
          (parentTable a ha t U) i j
          (ShortEdgeCutFibers.spanCandidate a S
            ShortEdgeCutFibers.SpanLiftMode.cutAtBoth) =
        ((t R).value +
            η.value * (H i a (ShortEdgeCutFibers.collapseAfter a j)).value) / 2 *
          cutContribution (D0 a t D)
            (fun x k y => -η.value * H0 H x k y) U
            (ShortEdgeCutFibers.collapseAfter a i)
            (ShortEdgeCutFibers.collapseAfter a j) S := by
  classical
  let c := ShortEdgeCutFibers.collapseAfter a j
  let ci := ShortEdgeCutFibers.collapseAfter a i
  let core := cutVertices ci c S
  obtain ⟨pre, L, R, post, hword, hLa, haR, hparentWord⟩ :=
    spanCandidate_cutAtBoth_word a i j hiA hBj S haS hS
  have hci : ci = i := by dsimp [ci]; exact ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega)
  have hc : c = j - 1 := by dsimp [c]; exact ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)
  have hjcore : a < c := by rw [hc]; omega
  have hiCore : ci < c := by rw [hci]; exact lt_trans hiA hjcore
  have hCorePair : core.Pairwise (· < ·) := by
    apply cutVertices_pairwise hiCore
    simpa [core, ci, hci] using hS
  have hCoreWord : core = pre ++ [L, a, R] ++ post := by
    simpa [core, ci, c] using hword
  have hCorePairWord : (pre ++ [L, a, R] ++ post).Pairwise (· < ·) := by
    simpa [hCoreWord] using hCorePair
  have hCorePairAssoc : (pre ++ ([L, a, R] ++ post)).Pairwise (· < ·) := by
    simpa [List.append_assoc] using hCorePairWord
  have hPreSide : ∀ x ∈ pre ++ [L, a], x ≤ a := by
    intro x hx
    rcases List.mem_append.mp hx with hxpre | hxlast
    · exact Nat.le_of_lt (pairwise_rel_append pre ([L, a, R] ++ post)
        hCorePairAssoc x hxpre a (by simp))
    · simp only [List.mem_cons, List.mem_singleton] at hxlast
      rcases hxlast with hL | htail
      · rw [hL]
        exact Nat.le_of_lt hLa
      · rcases htail with hEq | hFalse
        · rw [hEq]
        · simp at hFalse
  have hTailSide : ∀ x ∈ a :: R :: post, a ≤ x := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_rfl
    · rcases List.mem_cons.mp hx with rfl | hxpost
      · exact Nat.le_of_lt haR
      · exact Nat.le_of_lt (pairwise_rel_append (pre ++ [L, a, R]) post
          hCorePairWord a (by simp) x hxpost)
  have hPreMap : (pre ++ [L, a]).map (ShortEdgeCutFibers.liftAfter a) =
      pre.map (ShortEdgeCutFibers.liftAfter a) ++ [L, a] := by
    simp [ShortEdgeCutFibers.liftAfter, Nat.le_of_lt hLa]
  have hTailMap : (a :: R :: post).map (liftAt a) =
      (a + 1) :: (R + 1) :: post.map (ShortEdgeCutFibers.liftAfter a) := by
    have hA : liftAt a a = a + 1 := by simp [liftAt]
    have hR : liftAt a R = R + 1 := by simp [liftAt, Nat.not_lt_of_ge (Nat.le_of_lt haR)]
    have hpost : ∀ x ∈ post, liftAt a x = ShortEdgeCutFibers.liftAfter a x := by
      intro x hx
      have hax : a < x := by
        have hpair := pairwise_rel_append (pre ++ [L, a, R]) post
          hCorePairWord R (by simp) x hx
        exact lt_trans haR hpair
      rw [liftAt, ShortEdgeCutFibers.liftAfter]
      rw [if_neg (by omega), if_neg (by omega)]
    have hpostMap : List.map (liftAt a) post =
        List.map (ShortEdgeCutFibers.liftAfter a) post := List.map_congr_left hpost
    simp only [List.map_cons, hA, hR, hpostMap]
  have hPrefixPair : (pre ++ [L, a]).Pairwise (· < ·) := by
    apply List.Pairwise.sublist _ hCorePairWord
    simpa [List.append_assoc] using
      (List.sublist_append_left (pre ++ [L, a]) ([R] ++ post))
  have hTailPair : (a :: R :: post).Pairwise (· < ·) := by
    apply List.Pairwise.sublist _ hCorePairWord
    simpa [List.append_assoc] using
      (List.sublist_append_right (pre ++ [L]) (a :: R :: post))
  have hBranchPrefix := branchProduct_liftAfter_on_side a ha t U
    (pre ++ [L, a]) hPrefixPair hPreSide
  have hBranchTail := branchProduct_liftAt_on_side a ha t U
    (a :: R :: post) hTailPair hTailSide
  have hBranch : branchProduct (parentTable a ha t U)
      (pre.map (ShortEdgeCutFibers.liftAfter a) ++ [L, a, a + 1, R + 1] ++
        post.map (ShortEdgeCutFibers.liftAfter a)) = branchProduct U core := by
    rw [hCoreWord]
    have hParentAssoc : (pre.map (ShortEdgeCutFibers.liftAfter a) ++
        [L, a, a + 1, R + 1] ++ post.map (ShortEdgeCutFibers.liftAfter a)) =
        (pre.map (ShortEdgeCutFibers.liftAfter a) ++ [L]) ++
          a :: ((a + 1) :: (R + 1) :: post.map (ShortEdgeCutFibers.liftAfter a)) := by
      simp [List.append_assoc]
    have hCoreAssoc : pre ++ [L, a, R] ++ post =
        (pre ++ [L]) ++ a :: (R :: post) := by simp [List.append_assoc]
    rw [hParentAssoc, hCoreAssoc]
    rw [branchProduct_splice _ (pre.map (ShortEdgeCutFibers.liftAfter a) ++ [L])
      ((a + 1) :: (R + 1) :: post.map (ShortEdgeCutFibers.liftAfter a)) a]
    rw [branchProduct_splice U (pre ++ [L]) (R :: post) a]
    rw [hPreMap] at hBranchPrefix
    have hEdge : parentTable a ha t U a (a + 1) = 1 := by
      simp [parentTable]
    have hBranchTailEq : branchProduct (parentTable a ha t U)
        ((a + 1) :: (R + 1) :: post.map (ShortEdgeCutFibers.liftAfter a)) =
        branchProduct U (a :: R :: post) := by
      rw [← hTailMap]
      exact hBranchTail
    have hBranchTailEq' : branchProduct (parentTable a ha t U)
        (a :: ((a + 1) :: (R + 1) :: post.map (ShortEdgeCutFibers.liftAfter a))) =
        branchProduct U (a :: R :: post) := by
      simpa [branchProduct, hEdge] using hBranchTailEq
    have hBranchPrefix' : branchProduct (parentTable a ha t U)
        (pre.map (ShortEdgeCutFibers.liftAfter a) ++ [L] ++ [a]) =
        branchProduct U (pre ++ [L] ++ [a]) := by
      simpa [List.append_assoc] using hBranchPrefix
    rw [hBranchPrefix']
    rw [hBranchTailEq']
  let G1 : TripleArray := fun x k y => -η.value * H1 a t H x k y
  let G0 : TripleArray := fun x k y => -η.value * H0 H x k y
  have hPrefGate : gateProduct (D1 a t D) G1 i j
      (pre.map (ShortEdgeCutFibers.liftAfter a) ++ [L, a]) =
      gateProduct (D0 a t D) G0 ci c (pre ++ [L, a]) := by
    have h := gateProduct_liftAfter_pullback a t D H η ci c (pre ++ [L, a])
    have hleft : ShortEdgeCutFibers.liftAfter a ci = i := by
      rw [hci]
      simp [ShortEdgeCutFibers.liftAfter, Nat.le_of_lt hiA]
    have hright : ShortEdgeCutFibers.liftAfter a c = j := by
      rw [hc]
      change (if j - 1 ≤ a then j - 1 else j - 1 + 1) = j
      rw [if_neg (by omega)]
      exact Nat.sub_add_cancel (by omega)
    rw [hleft, hright] at h
    simpa [G1, G0, hPreMap] using h
  have hTailGate : gateProduct (D1 a t D) G1 i j
      ((a + 1) :: (R + 1) :: post.map (ShortEdgeCutFibers.liftAfter a)) =
      gateProduct (D0 a t D) G0 ci c (a :: R :: post) := by
    have h := gateProduct_liftAt_pullback a t D H η ci c (a :: R :: post)
    have hleft : liftAt a ci = i := by rw [hci]; simp [liftAt, hiA]
    have hright : liftAt a c = j := by
      rw [hc]
      change (if j - 1 < a then j - 1 else j - 1 + 1) = j
      rw [if_neg (by omega)]
      exact Nat.sub_add_cancel (by omega)
    rw [hleft, hright] at h
    simpa [G1, G0, hTailMap] using h
  have hCoreGate : gateProduct (D0 a t D) G0 ci c [L, a, R] =
      ((t L).value + η.value * (H i a c).value) / 2 := by
    have hL : ShortEdgeCutFibers.collapseAfter a L = L :=
      ShortEdgeCutFibers.collapseAfter_eq_of_le a L (by omega)
    simpa [gateProduct, D0, H0, G0, c, ci, hci, hL,
      ShortEdgeCutFibers.collapseAfter_eq_of_le a a le_rfl]
  have hFirstGate : gateProduct (D1 a t D) G1 i j [L, a, a + 1] =
      ((t L).value + η.value * (H i a c).value) / 2 := by
    have hL : ShortEdgeCutFibers.collapseAfter a L = L :=
      ShortEdgeCutFibers.collapseAfter_eq_of_le a L (by omega)
    have hjneq : j ≠ a + 1 := by omega
    have hine : i ≠ a := by omega
    simpa [gateProduct, D1, H1, D0, H0, G1, c, ci, hci, hc, hL, hjneq, hine,
      ShortEdgeCutFibers.collapseAfter_eq_of_le a a le_rfl]
  have hSecondGate : gateProduct (D1 a t D) G1 i j [a, a + 1, R + 1] =
      ((t R).value + η.value * (H i a c).value) / 2 := by
    have hRcollapse : ShortEdgeCutFibers.collapseAfter a (R + 1) = R := by
      rw [ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a (R + 1) (by omega)]
      omega
    have hine : i ≠ a := by omega
    have hjneq : j ≠ a + 1 := by omega
    have hcollapseA : ShortEdgeCutFibers.collapseAfter a a = a :=
      ShortEdgeCutFibers.collapseAfter_eq_of_le a a le_rfl
    have hcollapseI : ShortEdgeCutFibers.collapseAfter a i = i :=
      ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega)
    simpa [gateProduct, D1, H1, D0, H0, G1, c, ci, hc, hRcollapse, hine, hjneq,
      hcollapseA, hcollapseI,
      ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a (a + 1) (by omega)]
  have hGate : gateProduct (D1 a t D) G1 i j
      (pre.map (ShortEdgeCutFibers.liftAfter a) ++ [L, a, a + 1, R + 1] ++
        post.map (ShortEdgeCutFibers.liftAfter a)) =
      ((t R).value + η.value * (H i a c).value) / 2 *
        gateProduct (D0 a t D) G0 ci c core := by
    rw [hCoreWord]
    have hParentAssoc : (pre.map (ShortEdgeCutFibers.liftAfter a) ++
        [L, a, a + 1, R + 1] ++ post.map (ShortEdgeCutFibers.liftAfter a)) =
        pre.map (ShortEdgeCutFibers.liftAfter a) ++
          (L :: a :: (a + 1) :: (R + 1) :: post.map (ShortEdgeCutFibers.liftAfter a)) := by
      simp [List.append_assoc]
    have hCoreAssoc : pre ++ [L, a, R] ++ post = pre ++ (L :: a :: R :: post) := by
      simp [List.append_assoc]
    rw [hParentAssoc, hCoreAssoc]
    rw [gateProduct_splice (D1 a t D) G1 i j
      (pre.map (ShortEdgeCutFibers.liftAfter a))
      ((a + 1) :: (R + 1) :: post.map (ShortEdgeCutFibers.liftAfter a)) L a]
    rw [gateProduct_splice (D0 a t D) G0 ci c pre (R :: post) L a]
    have hParentInner := gateProduct_splice (D1 a t D) G1 i j [L]
      ((R + 1) :: post.map (ShortEdgeCutFibers.liftAfter a)) a (a + 1)
    rw [show gateProduct (D1 a t D) G1 i j
        (L :: a :: (a + 1) :: (R + 1) :: post.map (ShortEdgeCutFibers.liftAfter a)) =
          gateProduct (D1 a t D) G1 i j [L, a, a + 1] *
            gateProduct (D1 a t D) G1 i j (a :: ((a + 1) :: (R + 1) :: post.map (ShortEdgeCutFibers.liftAfter a))) by
          simpa only [List.cons_append, List.nil_append] using hParentInner]
    have hCoreInner := gateProduct_splice (D0 a t D) G0 ci c [L] post a R
    rw [show gateProduct (D0 a t D) G0 ci c (L :: a :: R :: post) =
          gateProduct (D0 a t D) G0 ci c [L, a, R] *
            gateProduct (D0 a t D) G0 ci c (a :: R :: post) by
          simpa only [List.cons_append, List.nil_append] using hCoreInner]
    have hParentTail := gateProduct_splice (D1 a t D) G1 i j [a]
      (post.map (ShortEdgeCutFibers.liftAfter a)) (a + 1) (R + 1)
    rw [show gateProduct (D1 a t D) G1 i j
        (a :: (a + 1) :: (R + 1) :: post.map (ShortEdgeCutFibers.liftAfter a)) =
          gateProduct (D1 a t D) G1 i j [a, a + 1, R + 1] *
            gateProduct (D1 a t D) G1 i j
              ((a + 1) :: (R + 1) :: post.map (ShortEdgeCutFibers.liftAfter a)) by
          simpa only [List.cons_append, List.nil_append] using hParentTail]
    rw [hPrefGate, hTailGate, hCoreGate, hFirstGate, hSecondGate]
    ring
  refine ⟨pre, L, R, post, hword, hLa, haR, hparentWord, ?_⟩
  unfold cutContribution
  rw [hparentWord]
  rw [hGate, hBranch]
  dsimp [c, ci, core, hci, G0]
  simp only [neg_mul]
  ring

end DirectGLSSW.ShortEdgeWeighted.SpanningBothImpl
