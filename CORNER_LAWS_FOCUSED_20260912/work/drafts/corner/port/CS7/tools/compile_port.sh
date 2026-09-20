#!/bin/bash
# usage: compile_port.sh <portdir>   — module-semantics compile of SM/CS7Units, SM/CS7, SM/ComparisonRows in a scratch object tree
source /workspace/envs/lean/env.sh
S=/workspace/scratch/claude-0/-workspace-repos-lean/d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/w6asmA
P=$1
W=/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912/work/lean
rm -rf $S/ptree && mkdir -p $S/ptree/O/SM $S/ptree/T/SM
for f in $W/.lake/build/lib/lean/SM/*; do ln -s $f $S/ptree/O/SM/; done
cp $P/SM/CS7Units.lean $P/SM/CS7.lean $P/SM/ComparisonRows.lean $S/ptree/T/SM/
cd $W
LP=$(lake env printenv LEAN_PATH)
LEAN=/root/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean
for m in CS7Units CS7 ComparisonRows; do
  echo "=== $m"
  ( time LEAN_PATH="$S/ptree/O:$LP" $LEAN --root=$S/ptree/T -o $S/ptree/O/SM/$m.olean $S/ptree/T/SM/$m.lean ) 2>&1 | grep -v "declaration uses" 
  echo "exit ${PIPESTATUS[0]}"
done
cat > $S/ptree/axioms_port.lean <<'EOT'
import SM.ComparisonRows
#print axioms SM.thm_C_S7
#print axioms SM.thm_comparison
#print axioms SM.cor_C_inherits
#print axioms SM.s7_bigon_law_at
#print axioms SM.s7_sliding_law_at
EOT
echo "=== axioms"
LEAN_PATH="$S/ptree/O:$LP" $LEAN $S/ptree/axioms_port.lean 2>&1
