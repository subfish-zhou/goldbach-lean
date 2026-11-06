#!/usr/bin/env python3
"""Audit a completed shared-proof batch without compiling or installing anything.

This checks actual sources, objects, recursive receipt contexts and logs. It
deliberately rejects a running/partial build. Interface, axiom, retirement and
kernel gates are separate requirements; this audit never reports acceptance.
"""

import argparse
import hashlib
import json
from pathlib import Path


EXTENSIONS = [".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(payload):
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def audit(run, baseline):
    state = json.loads((run / "process.json").read_text())
    status = json.loads((run / "build/STATUS.json").read_text())
    if state.get("exit_code") != 0 or status.get("status") != "passed":
        raise ValueError("Build is not terminal and fully passed; no context acceptance")
    preflight = json.loads((run / "preflight.json").read_text())
    preflight_hash = sha(run / "preflight.json")
    assert preflight_hash == state.get("original_preflight_sha256", state.get("preflight_sha256"))
    cached_bundles = dict(preflight.get("cached_artifact_bundles", {}))
    if state.get("bundle_repair_sha256"):
        repair_path = run / "bundle-repair.json"
        assert sha(repair_path) == state["bundle_repair_sha256"]
        repair = json.loads(repair_path.read_text())
        assert repair["original_preflight_sha256"] == preflight_hash
        assert repair["source_and_manifest_changes"] is False
        assert repair["failure_process"]["exit_code"] == 1
        for row in repair["copied_auxiliary_artifacts"]:
            name = row["module"]
            assert name in preflight["unaffected_object_hashes"]
            assert row["extension"] in EXTENSIONS and row["extension"] != ".olean"
            bundle = cached_bundles.setdefault(name, {".olean": preflight["unaffected_object_hashes"][name]})
            assert row["extension"] not in bundle
            bundle[row["extension"]] = row["sha256"]
    manifest_path = run / "source-manifest.json"
    manifest_hash = sha(manifest_path)
    assert manifest_hash == preflight["candidate_manifest_sha256"]
    assert sha(baseline / "source-manifest.json") == preflight["baseline_manifest_sha256"]
    manifest = {r["module"]: r for r in json.loads(manifest_path.read_text())}
    original = {r["module"]: r for r in json.loads((baseline / "source-manifest.json").read_text())}
    plan = json.loads((run / "build/PLAN.json").read_text())
    order = plan["modules"]
    assert set(order) == set(manifest) == set(original) and len(order) == 4151
    assert len(set(order)) == len(order)
    assert status["verified"] == status["planned"] == 4151
    assert sha(run / "build.py") == preflight["builder_sha256"] == sha(baseline / "build.py")
    for name in ["lakefile.toml", "lake-manifest.json", "lean-toolchain"]:
        assert sha(run / name) == sha(baseline / name), name
    actual_sources = {str(p.relative_to(run / "src").with_suffix("")).replace("/", ".") for p in (run / "src").rglob("*.lean")}
    actual_objects = {str(p.relative_to(run / "build/lib").with_suffix("")).replace("/", ".") for p in (run / "build/lib").rglob("*.olean")}
    assert actual_sources == actual_objects == set(manifest)
    affected = set(preflight["affected_names"])
    assert len(affected) == 3297 and len(manifest) - len(affected) == 854
    assert set(preflight["changed_modules"]) == set(preflight["candidate_records"])
    assert len(preflight["changed_modules"]) == 3
    assert set(preflight["unaffected_object_hashes"]) == set(manifest) - affected
    facts = {}
    lean = None
    for name in order:
        relative = Path(*name.split("."))
        source = (run / "src" / relative).with_suffix(".lean")
        obj = (run / "build/lib" / relative).with_suffix(".olean")
        receipt_path = (run / "build/receipts" / relative).with_suffix(".json")
        r = json.loads(receipt_path.read_text())
        assert r["module"] == name, name
        assert type(r["exit_code"]) is int and r["exit_code"] == 0, name
        source_hash, object_hash = sha(source), sha(obj)
        assert source_hash == manifest[name]["source_sha256"] == r["source_sha256"], name
        assert object_hash == r["object_sha256"], name
        assert sha((baseline / "src" / relative).with_suffix(".lean")) == original[name]["source_sha256"], name
        if name in preflight["candidate_records"]:
            candidate = preflight["candidate_records"][name]
            assert source_hash == candidate["after_sha256"]
            assert original[name]["source_sha256"] == candidate["before_sha256"]
        else:
            assert source_hash == original[name]["source_sha256"], name
        dependencies = {d: facts[d]["object"] for d in manifest[name]["imports"] if d in manifest}
        contexts = {d: facts[d]["context"] for d in dependencies}
        assert dependencies == r["dependencies"] and contexts == r["dependency_contexts"], name
        context = digest({"source_sha256": source_hash, "object_sha256": object_hash, "dependency_contexts": contexts})
        assert context == r["context_sha256"], name
        if name in affected:
            command = r["command"]
            lean = lean or command[0]
            expected = [lean, "-j1", "-DwarningAsError=true", "-R", str(run / "src"), "-o", str(obj)]
            if name.startswith(("W", "R2")):
                expected.append("-DautoImplicit=false")
            expected.append(str(source))
            assert command == expected, name
            log = run / r["log"]
            assert json.loads(log.with_suffix(".json").read_text()) == r, name
        else:
            original_receipt = (baseline / "build/receipts" / relative).with_suffix(".json")
            assert sha(receipt_path) == sha(original_receipt), name
            assert object_hash == preflight["unaffected_object_hashes"][name], name
            log = baseline / r["log"]
        assert sha(log) == r["log_sha256"], name
        bundle = {extension: sha((run / "build/lib" / relative).with_suffix(extension)) for extension in EXTENSIONS if (run / "build/lib" / relative).with_suffix(extension).exists()}
        if name not in affected:
            original_bundle = {extension: sha((baseline / "build/lib" / relative).with_suffix(extension)) for extension in EXTENSIONS if (baseline / "build/lib" / relative).with_suffix(extension).exists()}
            expected_bundle = cached_bundles.get(name, {".olean": preflight["unaffected_object_hashes"][name]})
            assert bundle == original_bundle == expected_bundle, name
        facts[name] = {"source": source_hash, "object": object_hash, "context": context, "bundle": bundle, "receipt": sha(receipt_path), "log": r["log_sha256"]}
    # Only PanV3 gains an import. Every other import sequence stays unchanged.
    for name in manifest:
        imports = list(original[name]["imports"])
        if name == "AnalyticNumberTheory.Sieve.PanV3SquareMean":
            insertion = next(i for i, n in enumerate(imports) if n != "Init")
            imports.insert(insertion, "AnalyticNumberTheory.Sieve.PanV1SquareMean")
        assert manifest[name]["imports"] == imports, name
    assert sha(manifest_path) == manifest_hash
    assert sha(baseline / "source-manifest.json") == preflight["baseline_manifest_sha256"]
    assert state["log"] and Path(state["log"]).read_text().splitlines()[-1] == "BUILD_PASS 4151"
    return {
        "status": "COMPLETE_SOURCE_OBJECT_LOG_AND_RECURSIVE_CONTEXT_AUDIT_NOT_ACCEPTANCE",
        "modules": len(facts), "fresh_source_compilations": len(affected),
        "verified_unchanged": len(facts) - len(affected),
        "manifest_sha256": manifest_hash, "context_digest": digest(facts),
        "lean": lean, "package_paths": plan["package_paths"], "facts": facts,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    baseline = Path(__file__).resolve().parent.parent / "wu2008"
    result = audit(args.run.resolve(), baseline)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "facts"}))


if __name__ == "__main__":
    main()
