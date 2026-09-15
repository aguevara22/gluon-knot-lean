#!/usr/bin/env bash
# One-shot environment setup for this package. Assumes NOTHING is installed.
# Idempotent: re-run it after fixing any reported problem. Takes 15-90 minutes
# the first time (network download of the Lean libraries, then a build).
#   bash setup.sh            # everything
#   bash setup.sh --check    # only report what is installed / missing
set -uo pipefail
export DEBIAN_FRONTEND=noninteractive
HERE="$(cd "$(dirname "$0")" && pwd)"
log() { printf '\n== %s\n' "$*"; }
fail() { printf '\nSETUP STOPPED: %s\n' "$*"; exit 3; }
as_root() { if [ "$(id -u)" = 0 ]; then "$@"; elif command -v sudo >/dev/null 2>&1; then sudo "$@"; else fail "root is needed to run: $* . Install the missing packages yourself, then re-run setup.sh"; fi; }
export PATH="$HOME/.elan/bin:$PATH"

log "Checking prerequisites"
missing=()
for c in git curl unzip python3; do command -v "$c" >/dev/null 2>&1 || missing+=("$c"); done
for c in git curl unzip python3 elan lean lake; do printf '  %-8s %s\n' "$c" "$(command -v "$c" 2>/dev/null || echo MISSING)"; done
if [ "${1:-}" = "--check" ]; then exit 0; fi

if [ ${#missing[@]} -gt 0 ]; then
  log "Installing missing prerequisites: ${missing[*]}"
  if command -v apt-get >/dev/null 2>&1; then as_root apt-get update -qq && as_root apt-get install -y -qq "${missing[@]}"
  elif command -v dnf >/dev/null 2>&1; then as_root dnf install -y "${missing[@]}"
  elif command -v yum >/dev/null 2>&1; then as_root yum install -y "${missing[@]}"
  elif command -v apk >/dev/null 2>&1; then as_root apk add "${missing[@]}"
  elif command -v brew >/dev/null 2>&1; then brew install "${missing[@]}"
  elif [ "$(uname)" = Darwin ]; then fail "on macOS run: xcode-select --install   (installs git, python3, curl), then re-run setup.sh"
  else fail "no package manager found; install ${missing[*]} yourself, then re-run setup.sh"; fi
  for c in "${missing[@]}"; do command -v "$c" >/dev/null 2>&1 || fail "$c still missing"; done
fi
python3 -c 'import sys; raise SystemExit(0 if sys.version_info >= (3, 9) else 1)' || fail "python3 is $(python3 --version 2>&1); 3.9 or newer is required"

if ! command -v elan >/dev/null 2>&1; then
  log "Installing elan (the Lean toolchain manager) into $HOME/.elan"
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$HOME/elan-init.sh" || fail "cannot download the elan installer (network to raw.githubusercontent.com needed)"
  sh "$HOME/elan-init.sh" -y --default-toolchain none || fail "elan installer failed"
  rm -f "$HOME/elan-init.sh"
  export PATH="$HOME/.elan/bin:$PATH"
  command -v elan >/dev/null 2>&1 || fail "elan not on PATH after install; open a new shell and re-run"
fi

if [ ! -d "$HERE/work/lean" ]; then log "Initializing work/"; python3 "$HERE/tools/bootstrap.py" || fail "bootstrap failed"; fi
toolchain="$(tr -d '[:space:]' < "$HERE/work/lean/lean-toolchain")"
log "Installing the pinned Lean toolchain: $toolchain"
elan toolchain install "$toolchain" 2>&1 | tail -1
elan override set "$toolchain" >/dev/null 2>&1 || true

cd "$HERE/work/lean" || fail "work/lean missing"
if [ ! -d .lake/packages/mathlib ]; then
  log "Fetching the pinned dependencies (git clones from github.com; a few GB; 5-20 minutes)"
  cp lake-manifest.json "$HERE/work/lake-manifest.shipped.json"
  lake update 2>&1 | tail -3 || fail "lake update failed (network to github.com needed)"
  if ! cmp -s lake-manifest.json "$HERE/work/lake-manifest.shipped.json"; then
    echo "WARNING: lake-manifest.json changed during lake update; the shipped copy is work/lake-manifest.shipped.json. Record this in work/AUTHOR_NOTES.md."
  fi
fi
log "Downloading prebuilt Mathlib (network; 5-30 minutes)"
lake exe cache get 2>&1 | tail -3 || echo "WARNING: cache download failed; lake build will compile Mathlib from source (hours)"
log "Building the library (first time: 10-60 minutes on 8 cores)"
lake build 2>&1 | tail -3 || fail "lake build failed; read the errors above"
cd "$HERE"

log "Verifying the package and the library"
python3 verify_bundle.py | tail -1 || fail "verify_bundle.py failed"
python3 tools/check_lean.py work/lean > "$HERE/work/setup-check.json" 2>"$HERE/work/setup-check.err" || { tail -5 "$HERE/work/setup-check.err"; fail "tools/check_lean.py failed"; }
python3 -c "import json; d=json.load(open('$HERE/work/setup-check.json')); print('checker passed:', d['passed'], '| mapped', d['mapped_declarations'], '| audited', d['audited_declarations'])"
python3 tools/progress.py --once | head -1

log "SETUP COMPLETE"
echo "In every new shell run:  export PATH=\"\$HOME/.elan/bin:\$PATH\""
echo "Then: python3 tools/progress.py --watch   (15-minute reports) and python3 tools/claims.py --pending-only"
