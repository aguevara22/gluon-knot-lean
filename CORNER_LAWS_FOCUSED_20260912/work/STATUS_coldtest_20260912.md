# Resume point — 2026-09-12T10:47Z (after the cold-start executor's first unit)

Claims verified 20/132 (15.2%). Checklist 40/192 accepted. Final targets 0/8.
Frame SM15. The library builds; `python3 tools/check_lean.py work/lean` passes
(40 mapped, 4271 audited; receipt work/checks/stage-development.json, log
work/coldstart-check2.log). No sorry in work/lean. Axioms used: propext,
Classical.choice, Quot.sound. The handover-time text of this file is preserved
as STATUS_handover_20260912.md; the previous executor's last status is
STATUS_origin_20260912T0720Z.md.

Done this session (executor-coldstart-claude-fable-5-1-20260912):

1. `bash setup.sh` on a bare Debian 12 VM (8 cores, 31 GB): SETUP COMPLETE in
   about 5 minutes with no stop (checker passed, 39 mapped, 4263 audited);
   log work/setup.log; details in AUTHOR_NOTES.md.
2. lem:shift proved exactly as printed in SM15 (four clauses):
   `SM.shift_reversal` in work/lean/SM/ShiftTheorem.lean; independent AI review
   work/reviews/lem-shift.json (verdict faithful); row accepted; task
   SM-shift-original-scope done. Nothing else in work/lean changed.

Next executable steps, in order:

1. `export PATH="$HOME/.elan/bin:$PATH"` in every new shell. Start
   `python3 tools/progress.py --watch` in a second terminal (or run `--once`
   at every checkpoint when no second terminal exists) and relay
   "claims verified X/132" every 15 minutes.
2. Re-review the 39 rows accepted before this session with an independent
   reviewer session (../STATE_OF_WORK.md section 4); countersign the three
   SM15 re-reads (lem:chi-basic, lem:g1, prop:A-chamber).
3. Continue claim by claim per `python3 tools/claims.py --pending-only` along
   PROOF_PLAN.md. Learned this session: the first "ready" rows of that list
   (CV:lem:carrierword, lem:gauss-two-discs, lem:carriers, lc:single-crossing,
   ce:rounding, ...) rest on Chapter 3 / CV definitions with no accepted row
   yet; read the source context before choosing. Rows whose source context is
   self-contained today: lem:transport-angle-interval and lem:transport-lengths
   (sm-5-transport.tex:132 and :75, real analysis), lem:star-generic (its listed
   dependency lem:shift is now accepted), and thm:A-soft through the
   candidate-lane body (../STATE_OF_WORK.md section 3).
4. Then the Chapter 3 definitions (independent supports, carriers, records,
   positive lifts, corner coefficients, def:C), the direct C laws, the
   full-cusp route, R and the bridge.

Keep this file current after each work unit: results, blockers, next step.
There is nobody to ask; record decisions in AUTHOR_NOTES.md.
