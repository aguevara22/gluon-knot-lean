#!/usr/bin/env bash
# port_compile.sh — compile the comparison-lane port modules with true module semantics WITHOUT touching work/lean
# (the scratch .olean recipe of work/drafts/cvtail/port/PORT_REPORT.md §8.5): copy the modules into a scratch tree T/SM/,
# symlink every accepted SM .olean into O/SM/, then `lean --root=T -o O/SM/X.olean T/SM/X.lean` in dependency order with
# O first on LEAN_PATH; finally compile the scratch importer Axioms.lean (the `#print axioms` probe lives ONLY there).
# Usage: source /workspace/envs/lean/env.sh; bash port_compile.sh <scratchdir>
set -u
S=${1:?scratch dir}
HERE=$(cd "$(dirname "$0")" && pwd); PORT=$(dirname "$HERE"); LEAN=$LEAN_PROJ/work/lean
T=$S/porttree/T; O=$S/porttree/O; LOGS=$S/logs; rm -rf "$T" "$O"; mkdir -p "$T/SM" "$O/SM" "$LOGS"
cp "$PORT"/SM/*.lean "$T/SM/"
for f in "$LEAN"/.lake/build/lib/lean/SM/*.olean "$LEAN"/.lake/build/lib/lean/SM/*.ilean; do ln -sf "$f" "$O/SM/"; done
cd "$LEAN"
for m in CornerPolygon CuspDeletionGeneric AnchorValues AnchorValuesRow Comparison CInherits; do
  t0=$(date +%s)
  lake env sh -c "LEAN_PATH=\"$O:\$LEAN_PATH\" lean --root=$T -o $O/SM/$m.olean -i $O/SM/$m.ilean $T/SM/$m.lean" > "$LOGS/$m.log" 2>&1
  rc=$?; t1=$(date +%s)
  echo "$m exit=$rc $((t1-t0))s errors=$(grep -c ': error:' "$LOGS/$m.log") warnings=$(grep -c ': warning:' "$LOGS/$m.log")"
done
cat > "$T/Axioms.lean" <<'EOF'
import SM.AnchorValuesRow
import SM.CInherits
#print axioms SM.prop_anchor_values
#print axioms SM.anchor_values_of
#print axioms SM.thm_comparison_of
#print axioms SM.cor_C_inherits_of
#print axioms SM.trianglesC
#print axioms SM.cusp_deletion_generic
#print axioms SM.cu_cuspLawC_of
#print axioms SM.uniquenessHypotheses_C_of
#print axioms SM.thm_comparison_root_of
#print axioms SM.thm_comparison_polygon_of
#print axioms SM.cornerPolygon
#print axioms SM.cornerPolygon_chamber
#print axioms SM.cs3_flat_law_C
#print axioms SM.thm_C_soft
EOF
t0=$(date +%s)
lake env sh -c "LEAN_PATH=\"$O:\$LEAN_PATH\" lean $T/Axioms.lean" > "$LOGS/axioms.log" 2>&1
echo "Axioms exit=$? $(( $(date +%s)-t0 ))s"; cat "$LOGS/axioms.log"
