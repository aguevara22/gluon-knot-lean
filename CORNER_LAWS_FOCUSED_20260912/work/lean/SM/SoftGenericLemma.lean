import SM.SoftFamilyAssembly

/-! Source lem:soft-generic (reference/SM/sm-2-amplitude.tex:1017, frame SM15): the soft family is
generic. Main declaration: `SM.soft_family_generic`.

Notation. `P` generic (def:generic), `j` a vertex, `q` admissible (`SoftAdmissible`, def:soft);
`softInsertion P j q ε = P_ε = P^{(j,q)}_ε` with the old vertex `μ_k` at the label
`softOldIndex j k` and the new vertex `M_ε = μ_j + ε q` at `softNewIndex j`; the soft edge is the
edge `softOldIndex j j`, the return edge (`D_ε = v - ε q`) is the edge `softNewIndex j`, and
`softParentEdge j k` identifies each unchanged edge with its parent edge and the return edge with
the parent edge `E_j` (clause (iii)); `softAttachmentMinus/Plus = χ_-, χ_+`; `turn P j = τ`;
`u = edge P (j-1)`, `v = edge P j`. `labelledChamber`/`chamber` are the chambers of def:chamber;
`IsCrossing`, `Crossing`, `crossingPoint`, `edgeParameter`, `visitParameter`, `pairVisit` are the
crossing data of def:crossings; `softInheritedCrossing hp c` / `softInheritedVisit hp v` are the
crossing / visit of `P_ε` inherited from the parent crossing `c` / visit `v` under the identification
of edges (clause (iii)); `gaussWord`/`gaussCycle` are the Gauss word and its visit cycle
(def:gauss), `nextGaussVisit` the cyclic successor visit; in the loop sector
`softNewbornCrossing` is the additional crossing `y` between the return edge and `E_{j-1}`, with
its incoming-edge visit `a` and return-edge visit `b`, `softNewbornPoint` its point, and
`traversalBetween x y z` says that the traversal position `y` lies on the oriented traversal arc
from `x` to `z` (the arc "from `a` through `M, M_ε` to `b`"). The limits (`Tendsto … (𝓝 0) …`) are
two-sided limits at `0` of functions defined for every real `ε` (the soft family and its crossing
data are defined by the same formulas for all `ε`); they are stronger than, and imply, the printed
one-sided limits `ε → 0⁺` ("converge to the parent values", "tends to `M`"). `ε₀` is the `δ` of
the statement.
The proof is the previous executor's kernel-checked candidate lane (prototype
SoftFamilyAssembly), ported verbatim. -/

namespace SM

noncomputable section
open Filter Topology
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- lem:soft-generic (the soft family is generic), clauses (i)–(iv) as printed on SM15. -/
theorem soft_family_generic (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    Tendsto (fun ε : ℝ => edge (softInsertion P j q ε) (softNewIndex j))
      (𝓝 (0 : ℝ)) (𝓝 (edge P j)) ∧
    (∀ k l : ZMod n, ∀ hc : IsCrossing P {k, l},
      Tendsto (softInheritedPoint P j k l q) (𝓝 (0 : ℝ))
        (𝓝 (crossingPoint (⟨{k, l}, hc⟩ : Crossing P))) ∧
      Tendsto (fun ε : ℝ => edgeParameter (softInsertion P j q ε)
        (softParentEdge j k) (softParentEdge j l)) (𝓝 (0 : ℝ))
        (𝓝 (visitParameter (pairVisit hc))) ∧
      Tendsto (fun ε : ℝ => edgeParameter (softInsertion P j q ε)
        (softParentEdge j l) (softParentEdge j k)) (𝓝 (0 : ℝ))
        (𝓝 (visitParameter
          (pairVisit (by simpa only [Finset.pair_comm] using hc : IsCrossing P {l, k}))))) ∧
    Tendsto (softNewbornIncomingParameter P j q) (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ)) ∧
    Tendsto (softNewbornReturnParameter P j q) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
    Tendsto (softNewbornPoint P j q) (𝓝 (0 : ℝ)) (𝓝 (P j)) ∧
    ∃ δ > 0, ∃ B : GenericTuple (n + 1),
      ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ hQ : Generic (softInsertion P j q ε),
      ∃ hp : SoftCrossingPersistence P j q ε,
      ∃ hclass : SoftCrossingClassificationAt P j q ε,
        /- Clause (i): actual Generic, one chamber and all soft-edge contacts. -/
        ((⟨softInsertion P j q ε, hQ⟩ : GenericTuple (n + 1)) ∈ labelledChamber B ∧
          polygonProjection (⟨softInsertion P j q ε, hQ⟩ : GenericTuple (n + 1)) ∈
            chamber (polygonProjection B) ∧
          edgeSegment (softInsertion P j q ε) (softOldIndex j j) ∩
            edgeSegment (softInsertion P j q ε) (softOldIndex j (j - 1)) = {P j} ∧
          edgeSegment (softInsertion P j q ε) (softOldIndex j j) ∩
            edgeSegment (softInsertion P j q ε) (softNewIndex j) = {P j + ε • q} ∧
          (∀ a : ZMod (n + 1), a ≠ softOldIndex j j → a ≠ softOldIndex j (j - 1) →
            a ≠ softNewIndex j →
            Disjoint (edgeSegment (softInsertion P j q ε) (softOldIndex j j))
              (edgeSegment (softInsertion P j q ε) a))) ∧
        /- Clause (ii): unchanged directions, both new directions and all turns/signs. -/
        ((∀ k : ZMod n, k ≠ j → edge (softInsertion P j q ε) (softOldIndex j k) = edge P k) ∧
          edge (softInsertion P j q ε) (softOldIndex j j) = ε • q ∧
          edge (softInsertion P j q ε) (softNewIndex j) = edge P j - ε • q ∧
          (∀ k : ZMod n, k ≠ j → turn (softInsertion P j q ε) (softOldIndex j k) = turn P k) ∧
          turn (softInsertion P j q ε) (softOldIndex j j) = -softAttachmentMinus P j q ∧
          turn (softInsertion P j q ε) (softNewIndex j) = -softAttachmentPlus P j q ∧
          SignType.sign (det (edge P (j - 1)) (edge (softInsertion P j q ε) (softNewIndex j))) =
            turn P j ∧
          SignType.sign (det (edge (softInsertion P j q ε) (softNewIndex j)) (edge P (j - 1))) =
            -turn P j) ∧
        /- Clause (iii): persistence is hp; limits above refer to these exact data. -/
        (∀ k l : ZMod n, ∀ hc : IsCrossing P {k, l},
          (0 < edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) ∧
            edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) < 1) ∧
          (0 < edgeParameter (softInsertion P j q ε) (softParentEdge j l) (softParentEdge j k) ∧
            edgeParameter (softInsertion P j q ε) (softParentEdge j l) (softParentEdge j k) < 1) ∧
          det (edge (softInsertion P j q ε) (softParentEdge j k))
            (edge (softInsertion P j q ε) (softParentEdge j l)) ≠ 0 ∧
          SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
            (edge (softInsertion P j q ε) (softParentEdge j l))) =
              SignType.sign (det (edge P k) (edge P l)) ∧
          crossingPoint (softInheritedCrossing hp (⟨{k, l}, hc⟩ : Crossing P)) =
            softInheritedPoint P j k l q ε ∧
          visitParameter (softInheritedVisit hp (pairVisit hc)) =
            edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) ∧
          visitParameter (softInheritedVisit hp
            (pairVisit (by simpa only [Finset.pair_comm] using hc : IsCrossing P {l, k}))) =
            edgeParameter (softInsertion P j q ε) (softParentEdge j l) (softParentEdge j k)) ∧
        (∀ v w : Visit P, v.2.val = w.2.val →
          (visitParameter (softInheritedVisit hp v) < visitParameter (softInheritedVisit hp w) ↔
            visitParameter v < visitParameter w)) ∧
        /- Clause (iv), the printed same-sign and mixed sectors. -/
        (((softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) ∨
          softAttachmentMinus P j q ≠ softAttachmentPlus P j q) →
          Function.Bijective (softInheritedCrossing hp) ∧
          (gaussWord hn hP).map (softInheritedCrossing hp) = gaussWord (by omega : 3 ≤ n + 1) hQ) ∧
        /- Clause (iv), the loop sector, with exact uniqueness and the oriented arc. -/
        (∀ hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j,
          (∀ d : Crossing (softInsertion P j q ε),
            (∃ c : Crossing P, softInheritedCrossing hp c = d) ↔ d ≠ softNewbornCrossing hclass hloop) ∧
          (softNewbornCrossing hclass hloop).val = {softOldIndex j (j - 1), softNewIndex j} ∧
          crossingPoint (softNewbornCrossing hclass hloop) = softNewbornPoint P j q ε ∧
          visitParameter (softNewbornIncomingVisit hclass hloop) = softNewbornIncomingParameter P j q ε ∧
          visitParameter (softNewbornReturnVisit hclass hloop) = softNewbornReturnParameter P j q ε ∧
          (0 < visitParameter (softNewbornIncomingVisit hclass hloop) ∧
            visitParameter (softNewbornIncomingVisit hclass hloop) < 1) ∧
          (0 < visitParameter (softNewbornReturnVisit hclass hloop) ∧
            visitParameter (softNewbornReturnVisit hclass hloop) < 1) ∧
          traversalEvaluation (softInsertion P j q ε) (softAttachmentVertexPosition j) = P j ∧
          traversalEvaluation (softInsertion P j q ε) (softInsertedVertexPosition j) = P j + ε • q ∧
          traversalBetween
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornIncomingVisit hclass hloop))
            (softAttachmentVertexPosition j)
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornReturnVisit hclass hloop)) ∧
          traversalBetween
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornIncomingVisit hclass hloop))
            (softInsertedVertexPosition j)
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornReturnVisit hclass hloop)) ∧
          traversalBetween
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornIncomingVisit hclass hloop))
            (softAttachmentVertexPosition j) (softInsertedVertexPosition j) ∧
          traversalBetween (softAttachmentVertexPosition j) (softInsertedVertexPosition j)
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornReturnVisit hclass hloop)) ∧
          (∀ w : Visit (softInsertion P j q ε),
            ¬ traversalBetween
              (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornIncomingVisit hclass hloop))
              (visitPosition (by omega : 3 ≤ n + 1) hQ.1 w)
              (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornReturnVisit hclass hloop))) ∧
          nextGaussVisit (by omega : 3 ≤ n + 1) hQ (softNewbornIncomingVisit hclass hloop) =
            softNewbornReturnVisit hclass hloop ∧
          (gaussCycle hn hP).map (softInheritedVisit hp) =
            (gaussCycle (by omega : 3 ≤ n + 1) hQ).filter
              (fun w => decide (w.1 ≠ softNewbornCrossing hclass hloop)) ∧
          (gaussWord hn hP).map (softInheritedCrossing hp) =
            (gaussWord (by omega : 3 ≤ n + 1) hQ).filter
              (fun c => decide (c ≠ softNewbornCrossing hclass hloop))) :=
  soft_family_generic_source hn hP j q hq

end
end SM
