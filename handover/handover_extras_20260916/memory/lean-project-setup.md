---
name: lean-project-setup
description: Where the Lean 4 "Gluons and Knots" formalization lives on the pod, its env file, and how setup was done (2026-09-13)
metadata:
  type: project
---

The Lean side project (Mark's `lean_repo`, GitHub marikgoldstein/lean_repo) is a cold handoff:
a Lean 4 + Mathlib formalization of the Supplemental Material of "Gluons and Knots", 132 claims,
20 verified at handover. Working directory of the executing agent:
`/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912`
(unzipped 2026-09-13 from the 50 MB zip beside it; manifest verified, 3429 files OK).

Environment: `source /workspace/envs/lean/env.sh` in every shell. It puts a uv Python 3.11 venv
(`/workspace/envs/lean/py`, system python is 3.8 and the tools need 3.9+) and elan
(`ELAN_HOME=/root/.elan`, LOCAL disk; a copy sits at /workspace/envs/lean/elan for re-creation)
on PATH and sets `$LEAN_PROJ`. Toolchain pin leanprover/lean4:v4.34.0-rc2, Mathlib 85e3a25e.
The build tree `$LEAN_PROJ/work/lean/.lake` is a symlink to /root/lean-lake (LOCAL disk):
Mathlib's `cache get` uses io_uring and crawled at 100 KB/s on the FUSE volume, so Lean build
artifacts must not live on /workspace. If the pod is re-created, re-run `bash setup.sh` in
`$LEAN_PROJ` after re-creating the symlink and /root/.elan (~5-10 min).

**Why:** everything must stay on the volume (pod container disk is ephemeral); Mark asked for
autonomy and Anthropic-only API use (no OpenAI).
**How to apply:** start each session by sourcing env.sh, then `python3 tools/progress.py --once`
and `python3 tools/claims.py --next` in `$LEAN_PROJ`. Follow the package's CLAUDE.md /
ACCEPT_CYCLE.md. See [[lean-project-progress]] for the running state.
