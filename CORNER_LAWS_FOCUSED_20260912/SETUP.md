# Setup, for a machine and a person that never heard of Lean

Lean 4 is a programming language and proof checker. Mathlib is its standard
mathematics library. This package ships Lean source files (work/lean) that must
be compiled and checked on your machine. Nothing needs to be understood by the
person; the executing agent runs `bash setup.sh`, which installs everything.
Measured on a bare Debian 12 machine with 8 cores: 5 minutes end to end; on a
slow network or fewer cores expect up to an hour.

What setup.sh does, in order (all idempotent):
1. Checks git, curl, unzip, python3 (3.9 or newer); installs missing ones with the
   system package manager (apt, dnf, yum, apk, brew). Needs sudo for that step.
2. Installs elan, the Lean toolchain manager, into ~/.elan (about 1 GB).
3. Installs the pinned Lean toolchain named in work/lean/lean-toolchain.
4. Clones the pinned dependencies (Mathlib and 8 others) into work/lean/.lake
   and downloads prebuilt Mathlib from the Mathlib cache server (about 5 GB).
5. Builds the 327 shipped modules (10-60 minutes on 8 cores).
6. Runs the package verifier, the acceptance checker (expected: passed, 40
   mapped, 4271 audited) and prints the first "claims verified 20/132" line.

Machine: Linux or macOS (Windows: use WSL2), 8 cores recommended, 16 GB RAM
minimum and 32 GB recommended, 30 GB free disk, network access to github.com,
raw.githubusercontent.com and Mathlib's cache server.

If `unzip` is missing, extract with `python3 -m zipfile -e <file>.zip .` (that
extractor drops executable bits; always run `bash setup.sh`, not `./setup.sh`).
If a step fails, the message says what is missing. Fix it and re-run
`bash setup.sh`. Nothing is downloaded twice. To only see what is installed:
`bash setup.sh --check`.

After setup, every new shell needs: `export PATH="$HOME/.elan/bin:$PATH"`.
