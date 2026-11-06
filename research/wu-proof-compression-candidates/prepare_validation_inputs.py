#!/usr/bin/env python3
"""Freeze validation queries for the shared-proof batch; execute no Lean gates."""

import argparse
import ast
import hashlib
import json
import re
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_name(name):
    result = "Name.anonymous"
    for part in name.split("."):
        result = f"(Name.num {result} {part})" if part.isdigit() else f"(Name.str {result} {json.dumps(part)})"
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    run, output = args.run.resolve(), args.output_dir.resolve()
    if output.exists() or output == run or run in output.parents:
        parser.error("output must be a new directory outside the frozen run")
    here = Path(__file__).resolve().parent
    baseline, accepted = here.parent / "wu2008", here.parent / "wu-unused-proof-audit"
    preflight = json.loads((run / "preflight.json").read_text())
    assert sha(baseline / "source-manifest.json") == preflight["baseline_manifest_sha256"]
    assert sha(run / "source-manifest.json") == preflight["candidate_manifest_sha256"]
    manifest = {r["module"]: r for r in json.loads((run / "source-manifest.json").read_text())}
    build_plan = json.loads((run / "build/PLAN.json").read_text())
    assert set(build_plan["modules"]) == set(manifest)
    output.mkdir(parents=True)
    bindings = {
        str(Path(__file__).resolve()): sha(Path(__file__).resolve()),
        str(run / "preflight.json"): sha(run / "preflight.json"),
        str(run / "source-manifest.json"): sha(run / "source-manifest.json"),
        str(baseline / "source-manifest.json"): sha(baseline / "source-manifest.json"),
    }
    steps, comparisons = [], []
    # The accepted compiler path is also checked against pinned toolchain hashes
    # by the executor; a query plan alone is not a toolchain or proof check.
    lean = json.loads((baseline / "build/receipts/AnalyticNumberTheory/Sieve/PanV3SquareMean.json").read_text())["command"][0]

    def write_query(label, source, library, payload=None, expected=0):
        destination = output / (label + ".lean")
        destination.write_text(source)
        bindings[str(destination)] = sha(destination)
        command = [lean, "-j1", "-DwarningAsError=true", "-DautoImplicit=false", "-DmaxRecDepth=16384", "-o", str(output / (label + ".olean")), str(destination)]
        steps.append({"label": label, "command": command, "library": str(library), "expected_exit_code": expected, "payload": str(payload) if payload else None})

    def retarget(source, payload):
        matches = re.findall(r'IO\.FS\.writeFile ("(?:\\.|[^"\\])*")', source)
        assert len(matches) == 1
        return source.replace(matches[0], json.dumps(str(payload)))

    for kind, count in [("types", 696), ("values", 183)]:
        template = accepted / "isolated" / ("after-" + kind + ".lean")
        reference = accepted / "isolated" / ("after-" + kind + ".json")
        bindings[str(template)] = sha(template)
        bindings[str(reference)] = sha(reference)
        assert len(json.loads(reference.read_text())["declarations"]) == count
        for phase, library in [("before", baseline / "build/lib"), ("after", run / "build/lib")]:
            label = phase + "-" + kind
            payload = output / (label + ".json")
            write_query(label, retarget(template.read_text(), payload), library, payload)
        comparisons.append({"before": "before-" + kind, "after": "after-" + kind, "count": count})

    names = []
    for stem in ["jurkat-cutoff", "pan-shared-square", "shared-singular-series"]:
        reference = here / (stem + "-evidence/before-types.json")
        bindings[str(reference)] = sha(reference)
        names.extend(row["name"] for row in json.loads(reference.read_text()))
    assert len(names) == len(set(names)) == 33
    template = (accepted / "isolated/after-types.lean").read_text()
    replacement = "  let requested : List Name := [" + ", ".join(lean_name(n) for n in names) + "]"
    template, replaced = re.subn(r"^  let requested : List Name := .*", lambda _: replacement, template, flags=re.M)
    assert replaced == 1
    for phase, library in [("before", baseline / "build/lib"), ("after", run / "build/lib")]:
        label = phase + "-changed-types"
        payload = output / (label + ".json")
        write_query(label, retarget(template, payload), library, payload)
    comparisons.append({"before": "before-changed-types", "after": "after-changed-types", "count": 33})

    classical = baseline / "check_classical.py"
    bindings[str(classical)] = sha(classical)
    tree = ast.parse(classical.read_text())
    literal = next(ast.literal_eval(n.value) for n in tree.body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "PROBE" for t in n.targets))
    write_query("literal-axioms", literal, run / "build/lib")

    def closure(root):
        seen, todo = set(), [root]
        while todo:
            name = todo.pop()
            if name in seen or name not in manifest:
                continue
            seen.add(name)
            todo.extend(manifest[name]["imports"])
        return seen

    final_modules = closure("WR2ClassicalCertificate")
    assert len(final_modules) == 3764
    module_file = output / "retirement-modules.txt"
    module_file.write_text("\n".join(sorted(final_modules)) + "\n")
    bindings[str(module_file)] = sha(module_file)
    targets = [
        ("_private.AnalyticNumberTheory.Sieve.PanV3SquareMean.0.AnalyticNumberTheory.Sieve.lcm_inv_eq_gcd_div", "AnalyticNumberTheory.Sieve.PanV3SquareMean"),
        ("MathlibNt.SieveTheory.SwitchingPrinciple.prod_one_sub_ge_one_sub_sum", "MathlibNt.SieveTheory.Switching.MainTerm"),
        ("MathlibNt.SieveTheory.SwitchingPrinciple.sum_sq_recip_primes_ge_three_le_half", "MathlibNt.SieveTheory.Switching.MainTerm"),
    ]
    template_path = accepted / "RetiredAbsentTemplate.lean"
    bindings[str(template_path)] = sha(template_path)
    template = template_path.read_text()
    original = "  let expectedModules : Array String := @@LOCAL_MODULES@@"
    assert template.count(original) == 1
    template = template.replace(original, "  let moduleText ← Lean.Elab.Command.liftIO <| IO.FS.readFile " + json.dumps(str(module_file)) + '\n  let expectedModules := ((moduleText.splitOn "\\n").filter (· != "")).toArray')
    for label, library, expected in [("retirement-before-negative", baseline / "build/lib", 1), ("retirement-after-absent", run / "build/lib", 0)]:
        payload = output / (label + ".json")
        source = template
        for marker, value in {
            "@@MODULE_IMPORTS@@": "import WR2ClassicalCertificate",
            "@@REQUESTED@@": "#[" + ", ".join("(" + json.dumps(n) + ", " + json.dumps(m) + ")" for n, m in targets) + "]",
            "@@OUTPUT_PATH@@": json.dumps(str(payload)),
        }.items():
            assert source.count(marker) == 1
            source = source.replace(marker, value)
        assert "@@" not in source
        write_query(label, source, library, payload, expected)

    report = accepted / "isolated/report.json"
    bindings[str(report)] = sha(report)
    roots = [s["label"].removeprefix("kernel-") for s in json.loads(report.read_text())["steps"] if s["label"].startswith("kernel-")]
    assert len(roots) == 21 and set().union(*(closure(r) for r in roots)) == set(manifest)
    for root in roots:
        steps.append({"label": "kernel-" + root, "command": [str(Path(lean).with_name("leanchecker")), "--verbose", root], "library": str(run / "build/lib"), "expected_exit_code": 0})
    # Default leanchecker replays only the target module's own constants.
    # A separate union root with --fresh replays its imported environment too.
    union_module = "WuBatchKernelUnion"
    write_query(union_module, "\n".join("import " + root for root in roots) + "\n", run / "build/lib")
    steps.append({"label": "fresh-kernel-union", "command": [str(Path(lean).with_name("leanchecker")), "--verbose", "--fresh", union_module], "library": str(output) + ":" + str(run / "build/lib"), "expected_exit_code": 0, "timeout_seconds": 14400})
    for label, script, arguments in [
        ("hf4-producer-check", baseline / "diagnostics/hf4_constructive/produce.py", ["--route", "constructive", "--output-dir", str(run / "src"), "--check"]),
        ("c-eighth-producer-check", baseline / "diagnostics/classical_c_eighth_certificates.py", ["--check", str(run / "src")]),
    ]:
        bindings[str(script)] = sha(script)
        steps.append({"label": label, "command": ["python3", str(script), *arguments], "library": str(run / "build/lib"), "expected_exit_code": 0})
    assert len(steps) == len({s["label"] for s in steps}) == 34
    plan = {
        "status": "PREPARED_NOT_EXECUTED_NOT_ACCEPTED", "run": str(run),
        "baseline": str(baseline), "lean": lean,
        "package_paths": build_plan["package_paths"], "steps": steps,
        "comparisons": comparisons, "retirement_targets": targets,
        "retirement_expected_modules": len(final_modules), "kernel_roots": roots,
        "fresh_kernel_module": union_module, "fresh_kernel_research_modules": len(manifest),
        "bindings": bindings,
        "required_executor_checks": [
            "Acquire the existing Lean lock only after a terminal successful build.",
            "Audit full source/object/log/receipt contexts before and after all gates.",
            "Verify toolchain hashes, package revisions and producer inputs against accepted pins.",
            "Check literal axiom output using scripts/check.py, not exit code alone.",
            "Require the expected old-control failure message and exact new absence payload.",
            "Require deep-equal exports with exact declaration counts and kernel replay output.",
            "Preserve the initial missing-bundle failure separately from expected retirement controls.",
        ],
    }
    (output / "validation-plan.json").write_text(json.dumps(plan, indent=2) + "\n")
    print(json.dumps({"status": plan["status"], "gates": len(steps), "directory": str(output)}))


if __name__ == "__main__":
    main()
