#!/usr/bin/env python3
"""Wait for the existing build, then validate and census; never install or restart.

The existing build is observed by its recorded PID/start identity. Only this
pipeline's own later children are signalled on interruption. All Lean commands
remain serialized by the existing exclusive lock.
"""

import argparse
import fcntl
import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

from audit_completed_batch import audit, sha
from dead_family_census import select_families
from validate_completed_batch import review_pins


def save(path, value):
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def observe_build(run):
    """A partially written status file is an observation retry, not termination."""
    try:
        build = json.loads((run / "process.json").read_text())
        status = json.loads((run / "build/STATUS.json").read_text())
    except (OSError, json.JSONDecodeError):
        return None
    if not isinstance(build, dict) or not isinstance(status, dict):
        raise ValueError("unexpected build-state schema; no restart attempted")
    return build, status


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validation-plan", type=Path, required=True)
    parser.add_argument("--census-plan", type=Path, required=True)
    parser.add_argument("--state-dir", type=Path, required=True)
    args = parser.parse_args()
    validation_path, census_path = args.validation_plan.resolve(), args.census_plan.resolve()
    validation, census = json.loads(validation_path.read_text()), json.loads(census_path.read_text())
    run = Path(validation["run"])
    assert run == Path(census["run"])
    state_dir = args.state_dir.resolve()
    assert not state_dir.exists()
    state_dir.mkdir(parents=True)
    with (run.parent / "pipeline.lock").open("a") as queue_lease:
        fcntl.flock(queue_lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
        state = {"status": "WAITING_EXISTING_BUILD_NOT_ACCEPTED", "pid": os.getpid(), "start_ticks": Path(f"/proc/{os.getpid()}/stat").read_text().split()[21], "run": str(run), "validation_plan": str(validation_path), "census_plan": str(census_path), "started_unix": time.time(), "current_child": None}
        state_path = state_dir / "process.json"
        save(state_path, state)
        print("WAITING_EXISTING_BUILD", str(run), flush=True)
        child = None

        def interrupted(signum, frame):
            raise InterruptedError(f"pipeline interrupted by signal {signum}")

        old = {s: signal.getsignal(s) for s in [signal.SIGINT, signal.SIGTERM]}
        for s in old:
            signal.signal(s, interrupted)

        def command(label, cmd, environment=None, cwd=None):
            nonlocal child
            state.update(status=label, current_child=None)
            save(state_path, state)
            log = state_dir / (label + ".log")
            with log.open("x") as stream:
                child = subprocess.Popen(cmd, cwd=cwd, env=environment, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
                state["current_child"] = {"pid": child.pid, "command": cmd, "log": str(log)}
                save(state_path, state)
                try:
                    rc = child.wait()
                except BaseException:
                    # The validator forwards SIGTERM to its currently owned
                    # Lean process group before exiting.
                    if child.poll() is None:
                        os.killpg(child.pid, signal.SIGTERM)
                        try:
                            child.wait(timeout=10)
                        except subprocess.TimeoutExpired:
                            os.killpg(child.pid, signal.SIGKILL)
                            child.wait()
                    state["current_child"]["exit_code"] = child.returncode
                    save(state_path, state)
                    raise
                state["current_child"]["exit_code"] = rc
                state["current_child"]["log_sha256"] = sha(log)
                save(state_path, state)
                child = None
                if rc != 0:
                    raise RuntimeError(f"{label} failed with actual exit code {rc}")
            print(label, rc, flush=True)

        def verify_bindings(bindings):
            for filename, expected in bindings.items():
                assert sha(Path(filename)) == expected, filename

        try:
            missing_since = None
            while True:
                observation = observe_build(run)
                if observation is None:
                    state["last_observation_retry_unix"] = time.time()
                    save(state_path, state)
                    time.sleep(10)
                    continue
                build, status = observation
                if "exit_code" in build:
                    assert build["exit_code"] == 0 and status["status"] == "passed", "existing build terminated without full success"
                    break
                proc = Path("/proc") / str(build["pid"])
                try:
                    live = proc.joinpath("stat").read_text().split()[21] == build["start_ticks"]
                except FileNotFoundError:
                    live = False
                if live:
                    missing_since = None
                elif missing_since is None:
                    missing_since = time.monotonic()
                elif time.monotonic() - missing_since > 30:
                    raise RuntimeError("recorded build handle is missing without a terminal success record; no restart attempted")
                state["last_observation"] = {"unix": time.time(), "build_pid": build["pid"], "build_identity_live": live, "verified_modules": status.get("verified"), "planned_modules": status.get("planned")}
                save(state_path, state)
                time.sleep(10)
            here = Path(__file__).resolve().parent
            command("VALIDATING_EXISTING_BUILD", [sys.executable, str(here / "validate_completed_batch.py"), "--plan", str(validation_path)])
            report = json.loads((validation_path.parent / "report.json").read_text())
            assert report["status"] == "FULL_CONTEXT_EXPORTS_LITERALS_RETIREMENT_21_KERNELS_FRESH_UNION_PRODUCERS_PASS_NOT_INSTALLED"
            assert len(report["steps"]) == 34
            verify_bindings(report["bindings"])
            assert census["status"] == "PREPARED_UNCOMPILED_CENSUS_NOT_RETIREMENT_ACCEPTANCE"
            with Path("/tmp/wu-lean-exclusive.lock").open("a") as lease:
                fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
                verify_bindings(census["bindings"])
                before = audit(run, Path(validation["baseline"]))
                assert before["context_digest"] == report["context_digest"]
                pins = review_pins(validation)
                output = census_path.parent
                assert not (output / "census.json").exists()
                (output / "tmp").mkdir(exist_ok=True)
                env = os.environ.copy()
                for key in ["LEAN_PATH", "LEAN_SYSROOT", "LEAN_SRC_PATH"]:
                    env.pop(key, None)
                env.update(LEAN_PATH=":".join([str(run / "build/lib"), *validation["package_paths"]]), LEAN_SYSROOT=str(Path(validation["lean"]).parent.parent), TMPDIR=str(output / "tmp"))
                lean_command = [validation["lean"], "-j1", "-DwarningAsError=true", "-DautoImplicit=false", "-DmaxRecDepth=16384", "-o", str(output / "Probe.olean"), str(output / "Probe.lean")]
                measured = ["/usr/bin/time", "-v", "-o", str(output / "resources.txt"), *lean_command]
                save(output / "invocation.json", {"command": lean_command, "execution_command": measured, "environment": {k: env[k] for k in ["LEAN_PATH", "LEAN_SYSROOT", "TMPDIR"]}, "bindings": census["bindings"]})
                command("COMPILED_FAMILY_CENSUS", measured, env, output)
                payload = json.loads((output / "census.json").read_text())
                assert payload["modules"] == census["research_modules"] == 4151
                assert payload["candidateCount"] == census["candidate_count"] == 2975
                requested = {tuple(line.split("\t")) for line in (output / "requested.tsv").read_text().splitlines()}
                assert {(r["basename"], r["module"]) for r in payload["candidates"]} == requested
                selected = select_families(payload)
                selected["census_sha256"] = sha(output / "census.json")
                save(output / "family-selection.json", selected)
                verify_bindings(census["bindings"])
                verify_bindings(report["bindings"])
                assert audit(run, Path(validation["baseline"])) == before
                assert review_pins(validation) == pins
                save(output / "execution-result.json", {"status": "ACTUAL_FAMILY_CENSUS_PASS_NOT_SOURCE_RETIREMENT_OR_ACCEPTANCE", "payload_sha256": sha(output / "census.json"), "selection_sha256": sha(output / "family-selection.json"), "context_digest": before["context_digest"], "selected_families": len(selected["selected"]), "retained_families": len(selected["retained"])})
            state.update(status="VALIDATION_AND_FAMILY_CENSUS_PASS_NOT_INSTALLED", finished_unix=time.time(), current_child=None)
            save(state_path, state)
            print(state["status"], flush=True)
        except BaseException as error:
            state.update(status="PIPELINE_STOPPED_NOT_INSTALLED", error_type=type(error).__name__, error=str(error), finished_unix=time.time())
            save(state_path, state)
            raise
        finally:
            # Also cover interruption between Popen and its wait block.
            if child is not None and child.poll() is None:
                try:
                    os.killpg(child.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    child.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid, signal.SIGKILL)
                    child.wait()
            for s, handler in old.items():
                signal.signal(s, handler)


if __name__ == "__main__":
    main()
