# CLAUDE.md — lean (side project)

Written 2026-09-13 by the Claude session in tmux `main` on Mark's RunPod home pod. This
project is separate from `persona/`; do not read or edit anything under `/workspace/repos/persona`
unless Mark asks. Run everything on this pod, and you do not need to speak to anything else.

## Where you are

You are on Mark's always-on CPU pod (8 vCPU, no GPU) with a 10 TB network volume at
`/workspace`. This session is tmux `side` (shortcut `s`); the persona work runs in tmux `main`
(shortcut `t`) with its own Claude, a Discord poller and hooks. Nothing you print here is mirrored
anywhere, but do not touch session `main` (no `tmux send-keys` into it). Python venv for
persona lives at `/workspace/envs/persona`; make your own under `/workspace/envs/lean` with `uv`
(on PATH) rather than reusing it. Keep outputs on the volume (`/workspace/...`), not in `/root`.

## API keys

They are already in your environment: `/workspace/home/.keys.env` is sourced by every shell via
`/workspace/home/rc.sh`. Variables: `ANTHROPIC_API_KEY_LO_PRIO` (use this one), `ANTHROPIC_API_KEY_BATCH`
(Message Batches), `ANTHROPIC_API_KEY_HI_PRIO` (Mark's interactive key; leave it alone),
`OPENAI_API_KEY`, `GEMINI_API_KEY`, `OPENROUTER_API_KEY`, `HF_TOKEN`, `OVERLEAF_TOKEN`. Plain
`ANTHROPIC_API_KEY` is deliberately unset so Claude Code keeps its own login; if your code needs
it, set it from `ANTHROPIC_API_KEY_LO_PRIO` inside the process, never in the shared rc files.
Rules: never print, echo, cat or log a key; verify by length or by whether a call succeeds. Never
write keys into this repo or any file on the volume other than that one. If a variable is missing
in an old window, open a new tmux window.

OPENAI is expensive, dont use it. use basically just anthropic. can double check small things with gemini etc if needed.
but just anthropic subagents or separate api calls is fine/preferred.

## Shared things worth knowing

`HF_HOME=/workspace/hf` (models and datasets already there; Hugging Face downloads need
`hf download --max-workers 8`, one `--include` flag per pattern). GPU workers can be created from
this pod with `~/.claude/skills/runpod-control/scripts/gpu-pod.sh <name> [count] [gpuType]` and
terminated with `terminate-pod.sh <id>`; capacity in EUR-IS-1 comes and goes, and workers cost
money, so terminate them when done and say so. Times in messages to Mark: UTC and New York time
("14:05 UTC / 10:05am ET").


## for this lean project specifically

use ultracode if/when helpful! this is a tough project with effort and coordination required


# autonomy

focus on autonomy here, feel free to try stuff, observe results, wonder aobut something, and keep going with a new plan. 
you can set a timer to send a message to remind yourself to observe, plan, and keep excuting. 
