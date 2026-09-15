# Progress while executing

Report progress at startup, after every work-unit checkpoint, every **15 minutes
while execution is active**, and before stopping or handing over. Do not wait for
the author. The running agent must relay the percentage, accepted/total counts,
current task, and any local blocker in its own status channel. If a tool call
prevents an update at the deadline, report at the next available boundary.

The automatic wrapper prints a report every 900 seconds while the supplied
execution command runs, including during long builds:

```sh
python3 tools/run_with_progress.py -- YOUR_EXECUTION_COMMAND
```

`YOUR_EXECUTION_COMMAND` means the recipient's existing agent or proof-runner
command, with its ordinary arguments; it is not a supplied executable. Choose it
locally. For an agent already running in an app, start this in a separate terminal:

```sh
python3 tools/progress.py --watch
```

After each checkpoint, update the declaration map and task states, then run:

```sh
python3 tools/progress.py --once
```

Reports also appear in `work/PROGRESS.md`, `work/progress/latest.json`, and the
timestamped `work/progress/history.jsonl`. Use one reporter process per work
directory. Stop its watch when the execution session ends; resume it next session.
This is terminal/file reporting, not a scheduled notification service.

**Percentage = accepted checklist rows / tracked obligations.** Each definition,
literature interface, theorem, extra result, and required certificate counts once.
Rows count only after their status is `accepted` under the review policy. This
measures reported checklist completion, not elapsed effort, remaining time, or
verified mathematics. A long theorem and a short definition have equal weight.
Only the acceptance checker and independent fidelity review establish completion.
Current receipts are bound to the code, review evidence, supplied sources and
acceptance policy. Changes invalidate that status. A logging failure is reported
on the terminal and must not stop the proof command; repair logging locally.

The shipped scope is always in the denominator; missing rows remain pending.
New helper rows expand it and remain tracked across restarts even if deleted from
the map. A scope expansion may lower the percentage and is reported. Malformed
state reports “unavailable”, never fabricated progress. Keep completed proofs
awaiting review at `review`; a blocked obligation never counts as accepted.

**Claims verified / total claims** is the primary figure of every report. A claim
is a statement with a printed proof (action PROVE) or an R/bridge/final obligation;
definitions, literature inputs and hypotheses are not claims. A claim is verified
when its row is `accepted`: kernel-checked, independently reviewed, recorded in the
map. `python3 tools/claims.py` lists every claim in dependency order with its status;
prove them one at a time in that order so progress is visible claim by claim.
At handover the figure is 19/132.
