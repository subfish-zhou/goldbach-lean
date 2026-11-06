#!/usr/bin/env python3
"""Freeze the three reviewed proof candidates for an isolated incremental build.

This never installs candidates. It verifies baseline source/object/receipt
contexts, copies all source files, and reuses only unaffected accepted objects.
Affected objects are deliberately absent, so compilation cannot overwrite a
hard link to an accepted object. Run the copied build.py under the Lean lock.
"""

import argparse
import hashlib
import json
import os
import shutil
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    baseline = here.parent / "wu2008"
    output = args.output_dir.resolve()
    if output.exists():
        parser.error("output must be a new directory")
    rows = json.loads((baseline / "source-manifest.json").read_text())
    manifest = {row["module"]: row for row in rows}
    specs = [
        ("jurkat-cutoff.json", Path("/tmp/wu-jurkat-cutoff-v1/src")),
        ("pan-shared-square.json", Path("/tmp/wu-pan-shared-square-v1/src")),
        ("shared-singular-series.json", Path("/tmp/wu-shared-singular-series-v1/src")),
    ]
    changes = {}
    for record, source_root in specs:
        spec = json.loads((here / record).read_text())
        name = spec["module"]
        relative = Path(*name.split(".")).with_suffix(".lean")
        assert sha(source_root / relative) == spec["after_sha256"], name
        assert manifest[name]["source_sha256"] == spec["before_sha256"], name
        changes[name] = (source_root / relative, spec)
    affected = set(changes)
    while True:
        expanded = affected | {
            name for name, row in manifest.items()
            if affected.intersection(row["imports"])
        }
        if expanded == affected:
            break
        affected = expanded

    receipts, object_hashes = {}, {}
    cached_bundles = {}
    for name, row in manifest.items():
        rel = Path(*name.split("."))
        source = (baseline / "src" / rel).with_suffix(".lean")
        obj = (baseline / "build/lib" / rel).with_suffix(".olean")
        receipt = (baseline / "build/receipts" / rel).with_suffix(".json")
        assert sha(source) == row["source_sha256"], name
        r = json.loads(receipt.read_text())
        assert r["exit_code"] == 0 and r["source_sha256"] == sha(source), name
        object_hashes[name] = sha(obj)
        assert r["object_sha256"] == object_hashes[name], name
        receipts[name] = r
    for name, r in receipts.items():
        dependencies = {d: object_hashes[d] for d in manifest[name]["imports"] if d in manifest}
        contexts = {d: receipts[d]["context_sha256"] for d in dependencies}
        assert r["dependencies"] == dependencies, name
        assert r["dependency_contexts"] == contexts, name
        payload = {
            "source_sha256": r["source_sha256"],
            "object_sha256": r["object_sha256"],
            "dependency_contexts": contexts,
        }
        digest = hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        assert digest == r["context_sha256"], name

    needed = sum(
        (baseline / "build/lib" / Path(*n.split("."))).with_suffix(".olean").stat().st_size
        for n in affected
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    assert shutil.disk_usage(output.parent).free > needed + 1_000_000_000
    output.mkdir(parents=True)
    for name, row in manifest.items():
        rel = Path(*name.split("."))
        dst = (output / "src" / rel).with_suffix(".lean")
        dst.parent.mkdir(parents=True, exist_ok=True)
        source = changes[name][0] if name in changes else (baseline / "src" / rel).with_suffix(".lean")
        shutil.copyfile(source, dst)
        dst.chmod(0o444)
        if name in changes:
            row["source_sha256"] = sha(dst)
            row["source_binding"] = "isolated_shared_proof_candidate_not_accepted"
        if name not in affected:
            obj = (baseline / "build/lib" / rel).with_suffix(".olean")
            target = (output / "build/lib" / rel).with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            os.link(obj, target)
            bundle = {".olean": sha(obj)}
            for extension in [".olean.server", ".olean.private", ".ir", ".ir.sig"]:
                auxiliary = (baseline / "build/lib" / rel).with_suffix(extension)
                if auxiliary.exists():
                    destination = (output / "build/lib" / rel).with_suffix(extension)
                    os.link(auxiliary, destination)
                    bundle[extension] = sha(auxiliary)
            cached_bundles[name] = bundle
            receipt = (baseline / "build/receipts" / rel).with_suffix(".json")
            target_receipt = (output / "build/receipts" / rel).with_suffix(".json")
            target_receipt.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(receipt, target_receipt)
    # Keep the historical duplicate Init entries; add only the actual new import.
    pan = manifest["AnalyticNumberTheory.Sieve.PanV3SquareMean"]
    insertion = next(i for i, n in enumerate(pan["imports"]) if n != "Init")
    pan["imports"].insert(insertion, "AnalyticNumberTheory.Sieve.PanV1SquareMean")
    save(output / "source-manifest.json", rows)
    for filename in ["build.py", "lakefile.toml", "lake-manifest.json", "lean-toolchain", "roots.json"]:
        shutil.copyfile(baseline / filename, output / filename)
    # Share package links, while keeping this project's Lake metadata separate.
    (output / ".lake").mkdir()
    (output / ".lake/packages").symlink_to((baseline / ".lake/packages").resolve())
    save(output / "preflight.json", {
        "status": "FROZEN_INCREMENTAL_INPUTS_NOT_BUILT_OR_INSTALLED",
        "baseline_manifest_sha256": sha(baseline / "source-manifest.json"),
        "candidate_manifest_sha256": sha(output / "source-manifest.json"),
        "modules": len(manifest), "affected_modules": len(affected),
        "cached_modules": len(manifest) - len(affected),
        "changed_modules": sorted(changes), "affected_names": sorted(affected),
        "source_compilations_already_completed_in_this_run": 0,
        "unaffected_object_hashes": {n: h for n, h in object_hashes.items() if n not in affected},
        "cached_artifact_bundles": cached_bundles,
        "candidate_records": {n: spec for n, (_, spec) in changes.items()},
        "builder_sha256": sha(output / "build.py"),
        "required_estimated_object_bytes": needed,
    })
    print(json.dumps({"output": str(output), "affected": len(affected), "cached": len(manifest) - len(affected)}))


if __name__ == "__main__":
    main()
