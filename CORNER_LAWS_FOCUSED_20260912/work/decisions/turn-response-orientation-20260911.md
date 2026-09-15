# Right-minus-left orientation candidate

2026-09-11. **UNCHECKED LEAN CANDIDATE** written by another agent of the same currently available model. No Lean kernel or build was run. This is technical assistance, not stronger-model fidelity approval or original-source acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8.

Candidate: `work/checks/TurnResponseOrientation.body.lean`, containing two theorem declarations. Suggested prototype imports are `SM.GermTurnSigns` and `Mathlib.Tactic`; the former imports the actual wall-germ, side-time and side-turn APIs. No new axiom or replacement definition is used.

## Exact scope

`turn_right_left_opposite_time_sides` accepts arbitrary punctured `w.Parameter` values whose actual turns are -1 and +1. It proves that one is a negative-time parameter and the other a positive-time parameter, with both possible orientations retained. It does not assume `FlatAt`, turn sign change, or a preselected right side.

`turn_response_right_minus_left` accepts an arbitrary integer-valued function F on the original parameter interval, a fixed integer C, a fixed integer d = ±1, and one positive radius bounded by the germ radius. Its response premise is the complete signed pair of equalities for **every independent** negative/positive pair within that radius. For any two punctured parameters within the same radius having turns -1/+1, its conclusion is exactly F(right) - F(left) = C. It neither assumes F constant on chambers nor identifies positive time with right.

Puncturedness is explicit and necessary for this generic helper: a general wall germ need not have zero turn at its center, so a nonzero turn alone would not justify side-time coverage. The sign bound and radius conditions are retained from the checked response package. Once actual nearby parameters and their response are available, the pointwise algebra derives d's value directly; therefore those package conditions may be reported unused by the linter.

## Proof construction

1. Use `sideTime_surjective_punctured` on each input parameter. It yields Boolean side labels and positive-distance parameters, with actual equalities back to the original parameters. If the Boolean labels coincided, `side_turn_constant` would make their turns equal. Substituting the required -1/+1 values contradicts that equality. This uses connected generic-side constancy already proved for the actual curve.
2. Split the two Boolean labels. Their unequal cases give the two possible time placements by unfolding `sideTime`. The original parameter equalities are used explicitly, so the argument preserves the entire original parameter domain and does not restrict to symmetric distances.
3. If right is positive-time and left negative-time, apply the response to `(sMinus,sPlus) = (left,right)`. The turn-jump equation specializes to `2 = 2*d`; integer arithmetic gives d = 1. Substitution into the F-response gives the desired difference.
4. If right is negative-time and left positive-time, apply it to `(right,left)`. The turn-jump equation gives `-2 = 2*d`; hence d = -1. The F-response is then F(left) - F(right) = -C, whose negation yields the desired right-minus-left difference. No division in the integers is used.

These are the two orientations in `sm-1-polygons.tex` lines 714–718 and `sm-2-amplitude.tex` lines 395–427. The candidate normalizes a supplied signed response; it does not prove the response hypothesis or complete the missing nonincident geometric construction.

## Integration note

For a tree amplitude application, F may be defined on the whole `w.Parameter` by using the punctured G1 tree coefficient when the parameter is nonzero and an arbitrary value at zero. The candidate only evaluates F at explicitly nonzero parameters, so the center value has no mathematical effect. The signed theorem supplies its existing d and radius unchanged; its integer turn equation matches the premise literally.

The two declarations should be checked by root before being frozen. Possible elaboration-sensitive points are substitution of the Boolean side label and simplification of SignType-to-integer casts; neither tactic sequence has been executed here. No frozen body, canonical file, map, or acceptance status was edited.
