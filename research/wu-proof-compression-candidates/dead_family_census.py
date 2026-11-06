#!/usr/bin/env python3
"""Prepare a private-inclusive census, or analyze its actual family edges.

No Lean process or source deletion is performed by either subcommand. Families
cover a source theorem and name-prefixed compiler auxiliaries in the same
module. Non-theorem members and ownership ambiguities are conservatively kept.
"""

import argparse
import collections
import hashlib
import json
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n")


def prepare(args):
    run, output, opportunities = args.run.resolve(), args.output_dir.resolve(), args.opportunities.resolve()
    assert not output.exists() and output != run and run not in output.parents
    model = json.loads(opportunities.read_text())
    assert model["status"] == "LEXICAL_ITERATED_OPPORTUNITIES_ONLY_NOT_REFERENCES_DELETION_OR_PROOF_ACCEPTANCE"
    assert sha(run / "source-manifest.json") == model["source_manifest_sha256"]
    names = [(r["written_name"].split(".")[-1], r["module"]) for r in model["candidates"]]
    assert len(names) == len({base for base, _ in names})
    manifest = {r["module"]: r for r in json.loads((run / "source-manifest.json").read_text())}
    for name, row in manifest.items():
        assert sha(run / "src" / Path(*name.split(".")).with_suffix(".lean")) == row["source_sha256"]
    here = Path(__file__).resolve().parent
    accepted = here.parent / "wu-unused-proof-audit/isolated/report.json"
    roots = [r["label"].removeprefix("kernel-") for r in json.loads(accepted.read_text())["steps"] if r["label"].startswith("kernel-")]
    covered, todo = set(), list(roots)
    while todo:
        name = todo.pop()
        if name not in manifest or name in covered:
            continue
        covered.add(name)
        todo.extend(manifest[name]["imports"])
    assert covered == set(manifest) and len(roots) == 21
    output.mkdir(parents=True)
    module_file, request_file = output / "modules.txt", output / "requested.tsv"
    module_file.write_text("\n".join(sorted(manifest)) + "\n")
    request_file.write_text("".join(base + "\t" + owner + "\n" for base, owner in sorted(names)))
    template_path = here / "DeadProofFamilies.lean.in"
    source = template_path.read_text()
    for marker, text in {
        "@@IMPORTS@@": "\n".join("import " + root for root in roots),
        "@@MODULE_FILE@@": json.dumps(str(module_file)),
        "@@REQUEST_FILE@@": json.dumps(str(request_file)),
        "@@OUTPUT_FILE@@": json.dumps(str(output / "census.json")),
    }.items():
        assert source.count(marker) == 1
        source = source.replace(marker, text)
    assert "@@" not in source
    (output / "Probe.lean").write_text(source)
    save(output / "plan.json", {
        "status": "PREPARED_UNCOMPILED_CENSUS_NOT_RETIREMENT_ACCEPTANCE",
        "run": str(run), "candidate_count": len(names), "research_modules": len(manifest),
        "roots": roots, "opportunities": str(opportunities),
        "bindings": {str(p): sha(p) for p in [Path(__file__).resolve(), template_path, accepted, opportunities, run / "source-manifest.json", module_file, request_file, output / "Probe.lean"]},
        "requires_before_execution": ["Terminal successful source build and completed validation", "Existing exclusive Lean lock", "Pinned tools/packages and exact library context", "Actual command, exit code, logs, source and payload hashes"],
        "requires_after_selection": ["Compiler source ranges and auxiliary-family ownership review", "Registration and current consumer review", "Downstream source compilation and retained-interface/value/precision checks", "Kernel replay before any installation"],
    })
    print(json.dumps({"status": "PREPARED_UNCOMPILED", "candidates": len(names), "modules": len(manifest), "directory": str(output)}))


def select_families(census):
    assert census["schema"] == "wu-dead-proof-family-census-v1"
    assert census["status"] == "ELABORATED_FAMILY_EDGES_NOT_RETIREMENT_OR_PROOF_ACCEPTANCE"
    targets = {r["name"]: r for r in census["candidates"]}
    assert len(targets) == len(census["candidates"]) == census["candidateCount"]
    assert len({r["basename"] for r in targets.values()}) == len(targets)
    reasons = collections.defaultdict(list)
    adjacency = collections.defaultdict(set)
    for row in census["ownershipIssues"]:
        assert row["family"] in targets
        reasons[row["family"]].append("ambiguous generated-family ownership")
    for row in census["members"]:
        assert row["family"] in targets
        assert row["module"] == targets[row["family"]]["module"]
        if row["kind"] != "theorem":
            reasons[row["family"]].append("non-theorem member requires separate source ownership review")
    for edge in census["edges"]:
        target, user = edge["target"], edge["userFamily"]
        assert target in targets and (user is None or user in targets)
        if user is None:
            reasons[target].append("incoming reference from a retained declaration")
        else:
            adjacency[user].add(target)
    retained = set(reasons)
    todo = list(retained)
    while todo:
        user = todo.pop()
        for target in adjacency[user] - retained:
            retained.add(target)
            reasons[target].append("required by another retained candidate family")
            todo.append(target)
    selected = set(targets) - retained
    # Independent boundary invariant: no selected family may receive an edge
    # from outside the selected set, including through a compiler auxiliary.
    for edge in census["edges"]:
        if edge["target"] in selected:
            assert edge["userFamily"] in selected
    return {"status": "FAMILY_REFERENCE_BOUNDARY_ONLY_NOT_SOURCE_RETIREMENT_OR_PROOF_ACCEPTANCE", "selected": [targets[n] for n in sorted(selected)], "retained": [{**targets[n], "reasons": sorted(set(reasons[n]))} for n in sorted(retained)], "census_modules": census["modules"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest="operation", required=True)
    pre = subs.add_parser("prepare")
    pre.add_argument("--run", type=Path, required=True)
    pre.add_argument("--opportunities", type=Path, required=True)
    pre.add_argument("--output-dir", type=Path, required=True)
    post = subs.add_parser("select")
    post.add_argument("--census", type=Path, required=True)
    post.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.operation == "prepare":
        prepare(args)
    else:
        result = select_families(json.loads(args.census.read_text()))
        result["census_sha256"] = sha(args.census)
        save(args.output, result)
        print(json.dumps({"selected": len(result["selected"]), "retained": len(result["retained"]), "status": result["status"]}))


if __name__ == "__main__":
    main()
