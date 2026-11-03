#!/usr/bin/env python3
"""Create release-root manifests from the finalized selected inventory and export list."""
from pathlib import Path
import argparse, hashlib, json, re

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("release", type=Path); ap.add_argument("selection", type=Path); ap.add_argument("exports", type=Path)
    a = ap.parse_args(); root = a.release.resolve()
    inv = json.loads(a.selection.read_text()); rows = inv["selected_modules"]
    sources=[]; seen=set(); seen_paths=set()
    for row in rows:
        mod, rel = row["module"], row.get("release_path", row.get("path"))
        if not isinstance(rel,str) or not rel or Path(rel).is_absolute() or "\\" in rel or any(x in ("", ".", "..") for x in rel.split("/")) or not rel.endswith(".lean"):
            raise SystemExit("unsafe source path: "+str(rel))
        parts=rel.split("/"); p=root.joinpath(*parts); resolved=p.resolve(strict=True)
        if not resolved.is_relative_to(root) or any(x.is_symlink() for x in [p, *p.parents[:len(parts)]]):
            raise SystemExit("source symlink or path escape: "+str(rel))
        expected_mod=".".join(parts)[:-5]
        if not isinstance(mod,str) or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.\u0080-\uffff']*",mod) or mod!=expected_mod:
            raise SystemExit("module/path mismatch: "+str(mod)+" / "+str(rel))
        if mod in seen or rel in seen_paths: raise SystemExit("duplicate module or path: "+str(mod)+" / "+str(rel))
        if not re.fullmatch(r"[0-9a-f]{64}",str(row.get("sha256",""))) or row["sha256"] != sha(resolved):
            raise SystemExit("selected source hash missing or mismatched: "+rel)
        seen.add(mod); seen_paths.add(rel); sources.append({"module":mod,"path":rel,"sha256":sha(resolved)})
    if len(sources)!=1589: raise SystemExit(f"expected exact 1589-module inventory, got {len(sources)}")
    export_input=json.loads(a.exports.read_text())
    exports=export_input["exports"]
    if not exports or len(exports)!=len(set(exports)) or any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.\u0080-\uffff']*",x) for x in exports):
        raise SystemExit("invalid or duplicate export")
    frozen=root/"ArmstrongFrozen/Frozen/JointNormalizedHomflyCornerIdentity.lean"
    manifest={"schema":1,"source_count":len(sources),"sources":sources,
      "selection_input_sha256":sha(a.selection),"export_input_sha256":sha(a.exports),
      "lean_toolchain_sha256":sha(root/"lean-toolchain"),"lakefile_sha256":sha(root/"lakefile.toml"),
      "lake_manifest_sha256":sha(root/"lake-manifest.json"),"frozen_theorem_sha256":sha(frozen)}
    (root/"SOURCE_MANIFEST.json").write_text(json.dumps(manifest,indent=2,sort_keys=True)+"\n")
    export_manifest={"schema":1,"exports":sorted(exports)}
    for category in ("graph_exports","moved_diagnostic_targets"):
        if category in export_input:
            names=export_input[category]
            if not isinstance(names,list) or len(set(names))!=len(names) or not set(names)<=set(exports):
                raise SystemExit("invalid export category: "+category)
            export_manifest[category]=sorted(names)
    (root/"EXPORTS.json").write_text(json.dumps(export_manifest,indent=2,sort_keys=True)+"\n")
    print(f"wrote SOURCE_MANIFEST.json ({len(sources)} modules) and EXPORTS.json ({len(exports)} exports)")
if __name__=="__main__": main()
