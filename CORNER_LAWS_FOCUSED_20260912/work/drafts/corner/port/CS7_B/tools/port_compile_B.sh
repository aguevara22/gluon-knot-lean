#!/usr/bin/env bash
# port_compile_B.sh — compile the CS7_B port modules with true module semantics WITHOUT touching work/lean (the scratch
# .olean recipe of work/drafts/cvtail/port/PORT_REPORT.md §8.5): copy the modules into a scratch tree T/SM/, symlink every
# accepted SM .olean/.ilean into O/SM/, then `lean --root=T -o O/SM/X.olean T/SM/X.lean` in import order with O first on
# LEAN_PATH; finally compile the scratch importer Axioms.lean (the `#print axioms` probe lives ONLY there).
# Usage: source /workspace/envs/lean/env.sh; bash port_compile_B.sh <scratchdir> <portdir> <module> [<module> ...]
set -u
S=${1:?scratch dir}; PORT=${2:?port dir}; shift 2; MODS="$@"
LEAN=$LEAN_PROJ/work/lean
T=$S/porttree/T; O=$S/porttree/O; LOGS=$S/logs; rm -rf "$T" "$O"; mkdir -p "$T/SM" "$O/SM" "$LOGS"
cp "$PORT"/SM/*.lean "$T/SM/"
for f in "$LEAN"/.lake/build/lib/lean/SM/*.olean "$LEAN"/.lake/build/lib/lean/SM/*.ilean; do ln -sf "$f" "$O/SM/"; done
cd "$LEAN"
for m in $MODS; do
  t0=$(date +%s)
  lake env sh -c "LEAN_PATH=\"$O:\$LEAN_PATH\" lean --root=$T -o $O/SM/$m.olean -i $O/SM/$m.ilean $T/SM/$m.lean" > "$LOGS/$m.log" 2>&1
  rc=$?; t1=$(date +%s)
  echo "$m exit=$rc $((t1-t0))s errors=$(grep -c ': error' "$LOGS/$m.log") warnings=$(grep -c ': warning' "$LOGS/$m.log")"
done
cat > "$T/Axioms.lean" <<'EOT'
import SM.ComparisonRows
#print axioms SM.thm_C_S7
#print axioms SM.thm_C_S7_of_floor
#print axioms SM.thm_C_S7_of
#print axioms SM.s7_bigon_law_at
#print axioms SM.s7_sliding_law_at
#print axioms SM.w4_box_returnedRows
#print axioms SM.thm_comparison
#print axioms SM.cor_C_inherits
#print axioms SM.thm_C_soft
EOT
t0=$(date +%s)
lake env sh -c "LEAN_PATH=\"$O:\$LEAN_PATH\" lean $T/Axioms.lean" > "$LOGS/axioms.log" 2>&1
echo "Axioms exit=$? $(( $(date +%s)-t0 ))s"; cat "$LOGS/axioms.log"
