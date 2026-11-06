#!/usr/bin/env python3
"""Execute staged interface/kernel gates after a completed isolated build.

No installation is performed. Running builds are rejected before acquiring the
Lean lock. Each child has its own process group and is stopped on interruption.
"""

import argparse
import fcntl
import importlib.util
import json
import os
import signal
import subprocess
import time
from pathlib import Path

from audit_completed_batch import audit, sha


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def review_pins(plan):
    baseline = Path(plan["baseline"])
    repo = baseline.parents[1]
    accepted = baseline.parent / "wu-unused-proof-audit"
    validation = json.loads((accepted / "validation.json").read_text())
    mathematical = json.loads((baseline / "mathematical-status.json").read_text())
    assert mathematical["final_acceptance"]["validation_sha256"] == sha(accepted / "validation.json")
    pins_path = accepted / "isolated/toolchain-review.json"
    index_path = accepted / "historical-evidence-index.json"
    for path in [pins_path, index_path]:
        assert sha(path) == validation["bindings"][str(path.relative_to(accepted))]
    pins = json.loads(pins_path.read_text())
    sysroot = Path(plan["lean"]).parent.parent
    bindings = {str(pins_path): sha(pins_path), str(index_path): sha(index_path)}
    for relative in ["bin/lean", "bin/leanchecker", "lib/lean/Init.olean"]:
        hashes = [h for p, h in pins["bindings"].items() if p.endswith("/" + relative)]
        assert len(hashes) == 1 and sha(sysroot / relative) == hashes[0], relative
        bindings[str(sysroot / relative)] = hashes[0]
    revisions = {}
    for library in plan["package_paths"]:
        path = Path(library)
        roots = [p for p in [path, *path.parents] if p.parent.name == "packages" and p.parent.parent.name == ".lake"]
        assert len(roots) == 1
        root = roots[0]
        revision = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
        assert revision == pins["package_revisions"][root.name]
        revisions[root.name] = revision
    assert revisions == pins["package_revisions"]
    # Bind the complete accepted diagnostic inputs, including generator helper
    # code and frozen Lean inputs, rather than just the two entry-point files.
    prefix = "adoption/baseline-consumers/files/"
    selected = 0
    for name, row in json.loads(index_path.read_text()).items():
        if name.startswith(prefix + "research/wu2008/diagnostics/"):
            path = repo / name.removeprefix(prefix)
            assert sha(path) == row["sha256"], str(path)
            bindings[str(path)] = row["sha256"]
            selected += 1
    assert selected > 10
    return {"bindings": bindings, "package_revisions": revisions, "producer_input_files": selected}


def execute(plan_path):
    plan = json.loads(plan_path.read_text())
    assert plan["status"] == "PREPARED_NOT_EXECUTED_NOT_ACCEPTED"
    run, baseline, output = Path(plan["run"]), Path(plan["baseline"]), plan_path.parent
    # This is intentionally before the lock and before writing a report.
    state = json.loads((run / "process.json").read_text())
    status = json.loads((run / "build/STATUS.json").read_text())
    if state.get("exit_code") != 0 or status.get("status") != "passed":
        raise ValueError("Build is not terminal and fully passed; validation not started")
    assert not (output / "report.json").exists(), "use newly staged inputs for a new validation attempt"
    assert len(plan["steps"]) == len({s["label"] for s in plan["steps"]}) == 34
    assert plan["fresh_kernel_module"] == "WuBatchKernelUnion"
    assert plan["fresh_kernel_research_modules"] == 4151
    assert sorted(c["count"] for c in plan["comparisons"]) == [33, 183, 696]
    report = {"status": "VALIDATING_NOT_INSTALLED", "steps": [], "plan_sha256": sha(plan_path)}
    lease_path = Path("/tmp/wu-lean-exclusive.lock")
    with lease_path.open("a") as lease:
        fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
        pins = review_pins(plan)
        initial = audit(run, baseline)
        assert initial["lean"] == plan["lean"] and initial["package_paths"] == plan["package_paths"]
        save(output / "context-before.json", initial)
        save(output / "pin-review.json", pins)
        bindings = {**plan["bindings"], **pins["bindings"], str(plan_path): sha(plan_path)}
        for path in [Path(__file__).resolve(), Path(__file__).resolve().with_name("audit_completed_batch.py"), baseline.parents[1] / "scripts/check.py"]:
            bindings[str(path)] = sha(path)

        def check_bindings():
            for filename, expected in bindings.items():
                assert sha(Path(filename)) == expected, filename

        checker = load(baseline.parents[1] / "scripts/check.py", "shared_batch_axiom_checker")
        (output / "tmp").mkdir(exist_ok=True)
        report.update(context_digest=initial["context_digest"], fresh_source_compilations=3297, verified_unchanged=854, kernel_roots=plan["kernel_roots"], bindings=bindings)
        save(output / "report.json", report)
        old_handlers = {s: signal.getsignal(s) for s in [signal.SIGINT, signal.SIGTERM]}

        def interrupted(signum, frame):
            raise InterruptedError(f"validation interrupted by signal {signum}")

        for signum in old_handlers:
            signal.signal(signum, interrupted)
        try:
            for step in plan["steps"]:
                check_bindings()
                label = step["label"]
                payload = Path(step["payload"]) if step.get("payload") else None
                if payload:
                    assert not payload.exists(), f"stale payload: {payload}"
                env = os.environ.copy()
                for key in ["LEAN_PATH", "LEAN_SYSROOT", "LEAN_SRC_PATH"]:
                    env.pop(key, None)
                env.update(LEAN_PATH=":".join([step["library"], *plan["package_paths"]]), LEAN_SYSROOT=str(Path(plan["lean"]).parent.parent), TMPDIR=str(output / "tmp"))
                log, resource = output / (label + ".log"), output / (label + ".resources")
                measured = ["/usr/bin/time", "-v", "-o", str(resource), *step["command"]]
                invocation = {"command": step["command"], "execution_command": measured, "environment": {k: env[k] for k in ["LEAN_PATH", "LEAN_SYSROOT", "TMPDIR"]}, "expected_exit_code": step["expected_exit_code"]}
                invocation_path = output / (label + ".invocation.json")
                report["current"] = label
                save(output / "report.json", report)
                start = time.monotonic()
                with log.open("x") as stream:
                    child = subprocess.Popen(measured, cwd=output, env=env, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
                    invocation["pid"] = child.pid
                    save(invocation_path, invocation)
                    try:
                        rc = child.wait(timeout=step.get("timeout_seconds", 3600))
                    except BaseException:
                        if child.poll() is None:
                            try:
                                os.killpg(child.pid, signal.SIGKILL)
                            except ProcessLookupError:
                                pass
                        invocation["aborted_exit_code"] = child.wait()
                        save(invocation_path, invocation)
                        raise
                row = {"label": label, "exit_code": rc, "expected_exit_code": step["expected_exit_code"], "seconds": time.monotonic() - start, "log_sha256": sha(log), "resources_sha256": sha(resource), "invocation_sha256": sha(invocation_path)}
                report["steps"].append(row)
                save(output / "report.json", report)
                print(label, rc, round(row["seconds"], 2), flush=True)
                assert type(rc) is int and rc == step["expected_exit_code"], label
                text = log.read_text()
                if label == plan["fresh_kernel_module"]:
                    union_object = output / (plan["fresh_kernel_module"] + ".olean")
                    bindings[str(union_object)] = sha(union_object)
                elif label == "literal-axioms":
                    checker.check_axiom_output(text, {"WuPaper.ClassicalSlots.one8938", "WuPaper.ClassicalSlots.one894", "WuPaper.ClassicalSlots.classical_lower", "WuLiteralAcceptance", "WuLegacyLiteralAcceptance"})
                elif label == "retirement-before-negative":
                    assert "Retired declaration survived:" in text and not payload.exists()
                elif label == "retirement-after-absent":
                    absence = json.loads(payload.read_text())
                    assert absence["schema"] == "wu-retired-declaration-absence-v1"
                    assert absence["status"] == "RAW_PRIVATE_INCLUSIVE_RETIREMENT_ABSENCE_NOT_PROOF_ACCEPTANCE"
                    assert absence["requestedCount"] == absence["absentCount"] == len(plan["retirement_targets"]) == 3
                    assert absence["expectedResearchModules"] == plan["retirement_expected_modules"] == 3764
                elif label == "fresh-kernel-union":
                    assert step["command"] == [str(Path(plan["lean"]).with_name("leanchecker")), "--verbose", "--fresh", plan["fresh_kernel_module"]]
                    assert text.strip() == "replaying " + plan["fresh_kernel_module"] + " with --fresh"
                    report["fresh_kernel_union_object_sha256"] = sha(output / (plan["fresh_kernel_module"] + ".olean"))
                elif label.startswith("kernel-"):
                    assert text.strip() == "replaying " + label.removeprefix("kernel-")
                check_bindings()
            assert len(report["steps"]) == 34
            assert "fresh_kernel_union_object_sha256" in report
            for pair in plan["comparisons"]:
                before = json.loads((output / (pair["before"] + ".json")).read_text())
                after = json.loads((output / (pair["after"] + ".json")).read_text())
                assert before == after and len(before["declarations"]) == pair["count"], pair
            final = audit(run, baseline)
            assert final == initial and review_pins(plan) == pins
            save(output / "context-after.json", final)
            report.update(status="FULL_CONTEXT_EXPORTS_LITERALS_RETIREMENT_21_KERNELS_FRESH_UNION_PRODUCERS_PASS_NOT_INSTALLED", current=None, comparisons=plan["comparisons"])
            save(output / "report.json", report)
            print("VALIDATION_PASS_NOT_INSTALLED", str(output), flush=True)
        except BaseException as error:
            report.update(status="VALIDATION_FAILED_NOT_INSTALLED", error_type=type(error).__name__, error=str(error))
            save(output / "report.json", report)
            raise
        finally:
            for signum, handler in old_handlers.items():
                signal.signal(signum, handler)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", type=Path, required=True)
    args = parser.parse_args()
    execute(args.plan.resolve())


if __name__ == "__main__":
    main()
