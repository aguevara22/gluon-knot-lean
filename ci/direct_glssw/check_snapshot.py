#!/usr/bin/env python3
"""Verify the relocated release against its archived build and audit receipts.

This checks bytes and inventory only; check_release.py performs the kernel audit.
"""
from pathlib import Path
import hashlib
import json


REPO = Path(__file__).resolve().parents[2]
ROOT = REPO / "DIRECT_GLSSW"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def main():
    manifest = read_json(ROOT / "SOURCE_MANIFEST.json")
    exports = read_json(ROOT / "EXPORTS.json")
    evidence = ROOT / "evidence/20261020"
    build = read_json(evidence / "build/RESULT.json")
    audit = read_json(evidence / "audit/portable/RESULT.json")
    consumption = read_json(evidence / "audit/PROOF_CONSUMPTION.json")

    require(build["status"] == "PASS_FRESH_PROJECT_BUILD", "build receipt is not a pass")
    require(audit["status"] == "PASS_SOURCE_AND_EXPORT_AXIOMS", "axiom receipt is not a pass")
    for name, key in [("SOURCE_MANIFEST.json", "source_manifest_sha256"),
                      ("EXPORTS.json", "exports_manifest_sha256"),
                      ("check_release.py", "checker_sha256")]:
        require(sha(ROOT / name) == audit[key], "audited input changed: " + name)

    for name, key in [("lean-toolchain", "lean_toolchain_sha256"),
                      ("lakefile.toml", "lakefile_sha256"),
                      ("lake-manifest.json", "lake_manifest_sha256")]:
        require(sha(ROOT / name) == manifest[key] == build["metadata_pins"][name],
                "pinned build metadata changed: " + name)

    expected_paths = set()
    hashes = {}
    for row in manifest["sources"]:
        relative = Path(row["path"])
        require(not relative.is_absolute() and ".." not in relative.parts,
                "invalid source path: " + str(relative))
        path = ROOT / relative
        require(path.resolve().is_relative_to(ROOT.resolve()) and not path.is_symlink(),
                "source path escapes package: " + str(relative))
        require(row["module"] == ".".join(relative.with_suffix("").parts),
                "module/path mismatch: " + str(relative))
        require(sha(path) == row["sha256"], "source changed: " + str(relative))
        require(row["path"] not in expected_paths and row["module"] not in hashes,
                "duplicate source entry: " + str(relative))
        expected_paths.add(row["path"])
        hashes[row["module"]] = row["sha256"]
    actual_paths = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*.lean")
                    if ".lake" not in p.relative_to(ROOT).parts}
    require(actual_paths == expected_paths, "Lean inventory differs from audited snapshot")
    require(len(expected_paths) == manifest["source_count"] == build["module_count"] == 1589,
            "unexpected source count")
    require(len(exports["exports"]) == len(set(exports["exports"])) == audit["checked_export_count"] == 3382,
            "unexpected export count")
    frozen = ROOT / "ArmstrongFrozen/Frozen/JointNormalizedHomflyCornerIdentity.lean"
    require(sha(frozen) == manifest["frozen_theorem_sha256"], "frozen theorem changed")

    recorded_source_audit = evidence / "audit/portable/SOURCE_AUDIT.json"
    require(sha(recorded_source_audit) == audit["source_audit_sha256"], "source receipt changed")
    source_audit = read_json(recorded_source_audit)
    require(source_audit["source_hashes"] == hashes and not source_audit["forbidden"],
            "source audit does not certify this snapshot")
    for path, expected in [
        (evidence / "build/build.log", build["build_log_sha256"]),
        (evidence / "audit/portable/axioms.log", audit["log_sha256"]),
        (evidence / "audit/proof-consumption.log", consumption["log_sha256"]),
        (REPO / "ci/direct_glssw/FrozenProofConsumption.lean", consumption["probe_sha256"]),
    ]:
        require(sha(path) == expected, "verification evidence changed: " + path.name)
    require(set(audit["allowed_axioms"]) == {"propext", "Classical.choice", "Quot.sound"},
            "unexpected axiom allowlist")
    print(json.dumps({"status": "PASS_SNAPSHOT_INTEGRITY", "sources": len(expected_paths),
                      "exports": len(exports["exports"]), "kernel_rerun": False}, indent=2))


if __name__ == "__main__":
    main()
