import SM.LocalPolynomial
import SM.LinkDiagramRecord

/-! Source lc:presentations (reference/SM/sm-3-statesum.tex:1306-1320, frame SM15): presentations of the same
decorated record. Main declaration: `SM.presentations`.

Notation (namespace `SM.Link`): "two actual finite nonempty decorated diagrams" are `D D' : Diagram`; "a
specified bijection of their oriented parameter circles and crossing occurrences, preserving cyclic
successor, pairing, over/under designations and signs; all crossing-free circles must be included in the
component bijection" is `RecordIso D.record D'.record` (def:gauss-record); "their evaluations by the same
local LM construction" are `P D`, `P D'` (`SM.P`, the Gaussian evaluation of the source value of lp:lm).
The sentence listing instances (positive page-chart changes, clean crossing-free replacements, compatible
height choices, within the finite-page domain) and the closing sentence (no ambient isotopy hypothesis or
conclusion) are illustrative/non-definitional: the theorem is stated for every named record bijection of
two actual diagrams, which is exactly what those instances supply. -/

namespace SM

open SM.Link

/-- lc:presentations as printed: "Their evaluations by the same local LM construction agree." -/
theorem presentations (D D' : Diagram) (h : Nonempty (RecordIso D.record D'.record)) : P D = P D' := by
  sorry

end SM
