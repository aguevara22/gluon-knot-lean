#!/usr/bin/env python3
"""Portable source and export audit. Run after the documented Lake build."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import signal
import subprocess
import time
from datetime import datetime, timezone

FROZEN = "dc0f4aa9f655dc14352c1f30d3e0b59d4d874a44149803aeea173cc567da389d"
ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9.\u0080-\uffff']*")

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p, obj): p.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")

def source_inventory(root):
    paths = set()
    for base, dirs, files in os.walk(root, followlinks=False):
        if Path(base) == root:
            dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
        for name in files:
            if name.endswith(".lean"):
                paths.add((Path(base) / name).relative_to(root).as_posix())
    return paths

def code_only(s):
    """Blank Lean comments, strings, and character literals; reject unterminated syntax."""
    out = list(s); i = depth = 0; string = line = False
    while i < len(s):
        c = s[i]; pair = s[i:i+2]
        if c == "\n": line = False; i += 1; continue
        if line: out[i] = " "
        elif depth:
            out[i] = " "
            if pair == "/-": depth += 1; out[i+1] = " "; i += 1
            elif pair == "-/": depth -= 1; out[i+1] = " "; i += 1
        elif string:
            out[i] = " "
            if c == "\\" and i+1 < len(s):
                if s[i+1] != "\n": out[i+1] = " "
                i += 1
            elif c == '"': string = False
        elif pair == "--": line = True; out[i] = out[i+1] = " "; i += 1
        elif pair == "/-": depth = 1; out[i] = out[i+1] = " "; i += 1
        elif c == '"': string = True; out[i] = " "
        elif c == "'":
            # Lean identifiers may contain apostrophes; blank only valid quoted chars.
            j = i + 1
            if j < len(s) and s[j] == "\\":
                j += 1
                if j < len(s) and s[j] == "u" and j+1 < len(s) and s[j+1] == "{":
                    end = s.find("}", j+2)
                    j = len(s) if end < 0 else end+1
                elif j < len(s): j += 1
            elif j < len(s) and s[j] != "\n": j += 1
            if j < len(s) and s[j] == "'":
                for k in range(i, j+1):
                    if s[k] != "\n": out[k] = " "
                i = j
        i += 1
    if depth: raise ValueError("unterminated block comment")
    if string: raise ValueError("unterminated string literal")
    return "".join(out)

def safe_source(root, rel, mod):
    if not isinstance(rel, str) or not rel or Path(rel).is_absolute() or "\\" in rel:
        raise ValueError("source path must be relative POSIX path")
    parts = rel.split("/")
    if any(x in ("", ".", "..") for x in parts) or not rel.endswith(".lean"):
        raise ValueError("invalid source path: " + rel)
    if not isinstance(mod, str) or not NAME.fullmatch(mod) or mod != ".".join(parts)[:-5]:
        raise ValueError("module/path mismatch: " + str(mod) + " / " + rel)
    p = root.joinpath(*parts); resolved = p.resolve(strict=True)
    chain = [p]
    parent = p.parent
    while parent != root.parent:
        chain.append(parent); parent = parent.parent
    if not resolved.is_relative_to(root) or any(x.is_symlink() for x in chain):
        raise ValueError("source symlink or path escape: " + rel)
    return resolved

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("release", nargs="?", type=Path, default=Path(__file__).resolve().parent)
    ap.add_argument("--output", type=Path)
    a = ap.parse_args(); root = a.release.resolve()
    out = a.output.resolve() if a.output else root / ".lake" / "release-audit" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    out.mkdir(parents=True, exist_ok=False)
    source_path, export_path = root / "SOURCE_MANIFEST.json", root / "EXPORTS.json"
    result = {"status": "FAIL", "root": ".", "started_utc": datetime.now(timezone.utc).isoformat(),
              "checker_sha256": sha(Path(__file__).resolve())}
    failures = []
    try:
        result["source_manifest_sha256"] = sha(source_path); result["exports_manifest_sha256"] = sha(export_path)
        sm, em = json.loads(source_path.read_text()), json.loads(export_path.read_text())
    except Exception as e:
        result.update(status="FAIL_INPUT", failures=[f"cannot read release manifests: {type(e).__name__}: {e}"])
        dump(out / "RESULT.json", result); print(json.dumps(result)); return 1
    if sm.get("schema") != 1 or em.get("schema") != 1: failures.append("unsupported manifest schema")
    metadata = [("lean-toolchain", "lean_toolchain_sha256"), ("lakefile.toml", "lakefile_sha256"),
                ("lake-manifest.json", "lake_manifest_sha256")]
    metadata_hashes = {}
    for rel, key in metadata:
        try: metadata_hashes[rel] = sha(root / rel)
        except Exception as e: failures.append(f"missing metadata {rel}: {e}"); continue
        if metadata_hashes[rel] != sm.get(key): failures.append("pinned metadata mismatch: " + rel)
    rows = sm.get("sources", []); exports = em.get("exports", [])
    if len(rows) != sm.get("source_count") or len(rows) != 1589: failures.append("source count mismatch")
    if not isinstance(exports, list) or not exports or any(not isinstance(n, str) for n in exports) or len(set(exports)) != len(exports) or any(not NAME.fullmatch(n) for n in exports): failures.append("invalid or duplicate export name")
    source_hashes = {}; source_relpaths = {}; source_paths = set(); forbidden = []; heartbeats = []; diagnostics = []
    for row in rows:
        rel, mod = row.get("path", ""), row.get("module", "")
        try: p = safe_source(root, rel, mod)
        except Exception as e: failures.append(f"invalid source entry {rel!r}: {e}"); continue
        if rel in source_paths or mod in source_hashes: failures.append("duplicate source path or module: " + rel); continue
        source_paths.add(rel)
        source_relpaths[mod] = rel
        try: digest = sha(p)
        except Exception as e: failures.append(f"cannot hash source {rel}: {e}"); continue
        if digest != row.get("sha256"): failures.append("source hash mismatch: " + rel)
        source_hashes[mod] = digest
        try: code = code_only(p.read_text(encoding="utf-8"))
        except Exception as e: failures.append(f"source scan failed for {rel}: {e}"); continue
        for m in re.finditer(r"\b(?:sorry|admit|axiom|unsafe)\b", code):
            forbidden.append({"module": mod, "line": code.count("\n", 0, m.start())+1, "token": m.group()})
        for n, line in enumerate(code.splitlines(), 1):
            if re.search(r"\bset_option\s+max(?:Heartbeats|RecDepth)\b", line): heartbeats.append({"module": mod, "line": n})
            if re.match(r"\s*#(?:check|print|eval|reduce)\b", line): diagnostics.append({"module": mod, "line": n})
    frozen = root / "ArmstrongFrozen/Frozen/JointNormalizedHomflyCornerIdentity.lean"
    try: frozen_hash = sha(frozen)
    except Exception as e: frozen_hash = "MISSING"; failures.append(f"frozen theorem unavailable: {e}")
    if frozen_hash != FROZEN or sm.get("frozen_theorem_sha256") != FROZEN: failures.append("frozen theorem hash mismatch")
    audit = {"source_hashes": source_hashes, "forbidden": forbidden, "heartbeat_override_count": len(heartbeats),
             "heartbeat_overrides": heartbeats, "diagnostic_command_count": len(diagnostics), "diagnostic_commands": diagnostics,
             "frozen_theorem_sha256": frozen_hash}
    actual_sources = source_inventory(root)
    if actual_sources != source_paths:
        failures.append("source manifest does not match actual Lean files")
        audit["unlisted_sources"] = sorted(actual_sources - source_paths)
        audit["missing_sources"] = sorted(source_paths - actual_sources)
    dump(out / "SOURCE_AUDIT.json", audit)
    if forbidden: failures.append("forbidden source tokens found")
    if failures:
        result.update(failures=failures, status="FAIL_SOURCE_OR_MANIFEST")
        dump(out / "RESULT.json", result); print(json.dumps(result)); return 1
    probe = out / "ReleaseAxioms.lean"
    mods = sorted(source_hashes)
    probe.write_text("".join("import " + m + "\n" for m in mods) + '''import Lean
open Lean Elab Command
elab "#assert_batch_axioms " "[" decls:str,* "]" : command => do
  let env ← getEnv
  let requested := decls.getElems.toList.map (fun d => d.getString)
  let wanted := requested.foldl (fun (s : Std.HashSet String) n => s.insert n) {}
  let mut nameCandidates : Std.HashMap String (List Name) := {}
  for (n, _) in env.constants.toList do
    let spelling := n.toString
    if wanted.contains spelling then
      nameCandidates := nameCandidates.insert spelling (n :: nameCandidates.getD spelling [])
  let mut names : List Name := []
  for spelling in requested do
    match nameCandidates.getD spelling [] with
    | [n] => names := n :: names
    | [] => throwError m!"missing declaration spelling: {spelling}"
    | _ => throwError m!"ambiguous declaration spelling: {spelling}"
  for n in names do
    match env.checked.get.find? n with
    | none => throwError m!"missing checked declaration: {n}"
    | some _ => pure ()
  let action : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, collected) := (action.run env).run {}
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let extra := collected.axioms.toList.filter (fun n => !allowed.contains n)
  if !extra.isEmpty then throwError m!"unexpected axiom union: {extra}"
  logInfo m!"KERNEL_AXIOMS_BATCH_OK count={names.length} axioms={collected.axioms}"
''' + "#assert_batch_axioms [\n" + ",\n".join(json.dumps(n, ensure_ascii=False) for n in exports) + "\n]\n")
    env = os.environ.copy(); env.pop("LEAN_PATH", None)
    cmd = ["lake", "env", "lean", "-j", "2", str(probe.resolve())]
    started = time.monotonic()
    try:
        with (out / "axioms.log").open("w") as log:
            p = subprocess.Popen(cmd, cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT,
                                 stdin=subprocess.DEVNULL, start_new_session=True)
            try: p.wait(timeout=900)
            except subprocess.TimeoutExpired:
                os.killpg(p.pid, signal.SIGKILL); p.wait(); result["timed_out"] = True
    except Exception as e:
        result.update(status="FAIL_SUBPROCESS", failures=[f"audit invocation failed: {type(e).__name__}: {e}"])
        if not (out / "axioms.log").exists(): (out / "axioms.log").write_text("")
        dump(out / "RESULT.json", result); print(json.dumps(result)); return 1
    logtext = (out / "axioms.log").read_text(errors="replace")
    markers = re.findall(r"KERNEL_AXIOMS_BATCH_OK count=([0-9]+) axioms=([^\n]+)", logtext)
    audit_ok = len(markers) == 1 and int(markers[0][0]) == len(exports)
    # Recheck inputs after Lean finishes, so a concurrent tree change cannot inherit a pass.
    changed = []
    if source_inventory(root) != source_paths: changed.append("source inventory changed during audit")
    for mod, expected in source_hashes.items():
        rel = source_relpaths[mod]
        try:
            if sha(root / rel) != expected: changed.append("source changed during audit: " + rel)
        except Exception as e: changed.append(f"source unavailable after audit: {rel}: {e}")
    for rel, key in [("lean-toolchain", "lean_toolchain_sha256"), ("lakefile.toml", "lakefile_sha256"), ("lake-manifest.json", "lake_manifest_sha256")]:
        try:
            if sha(root / rel) != sm.get(key): changed.append("metadata changed during audit: " + rel)
        except Exception as e: changed.append(f"metadata unavailable after audit: {rel}: {e}")
    try:
        if sha(source_path) != result["source_manifest_sha256"] or sha(export_path) != result["exports_manifest_sha256"]:
            changed.append("release manifest changed during audit")
    except Exception as e: changed.append(f"release manifest unavailable after audit: {e}")
    try:
        if sha(frozen) != FROZEN: changed.append("frozen theorem changed during audit")
    except Exception as e: changed.append(f"frozen theorem unavailable after audit: {e}")
    result.update(status="PASS_SOURCE_AND_EXPORT_AXIOMS" if p.returncode == 0 and audit_ok and not changed else "FAIL_EXPORT_AXIOMS",
                  returncode=p.returncode, export_count=len(exports), success_marker_count=len(markers),
                  checked_export_count=int(markers[0][0]) if audit_ok else 0,
                  collected_axiom_union=markers[0][1] if audit_ok else None,
                  audit_method="Unique kernel-name spelling resolution, then Lean.CollectAxioms.collect with one shared visited set over all named checked declarations",
                  elapsed_seconds=round(time.monotonic()-started, 3), command=cmd,
                  source_count=len(rows), module_count=len(mods), probe_sha256=sha(probe), log_sha256=sha(out/"axioms.log"),
                  source_audit_sha256=sha(out/"SOURCE_AUDIT.json"), allowed_axioms=ALLOWED_AXIOMS, failures=changed)
    dump(out / "RESULT.json", result); print(json.dumps(result)); return 0 if result["status"].startswith("PASS_") else 1

if __name__ == "__main__": raise SystemExit(main())
