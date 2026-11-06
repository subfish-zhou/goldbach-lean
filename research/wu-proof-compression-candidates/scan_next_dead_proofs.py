#!/usr/bin/env python3
"""Model successive lexical proof-leaf removal without editing any sources.

This is an opportunity scan, not a reference census or deletion authorization.
Historical source variants are recorded as exclusions because the Wu README
explicitly excludes history from the supported build. Other current consumers,
selected interfaces and generator-owned Hf4 modules remain protected.
"""

import argparse
import bisect
import collections
import hashlib
import importlib.util
import json
import re
import subprocess
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def words(text):
    return re.findall(r"[A-Za-z_][\w']*", text)


def incremental_rounds(texts, manifest, closure, generated, protected, counter, pattern, limit):
    """Maintain lexical token counts instead of rescanning every file per wave."""
    tokens, occurrences = collections.Counter(), collections.defaultdict(list)
    for name, text in texts.items():
        kept = counter.code_only(text, keep_strings=True)
        masked = counter.code_only(text)
        assert len(kept) == len(masked) == len(text)
        tokens.update(words(kept))
        if name not in closure or name in generated:
            continue
        starts = [m.start() for m in re.finditer(r"^\S", masked, re.M)]
        for match in pattern.finditer(masked):
            written, private = match["name"], bool(match["private"])
            basename = written.split(".")[-1]
            position = bisect.bisect_left(starts, match.start())
            previous = masked[starts[position - 1]:match.start()].lstrip() if position else ""
            end = starts[position + 1] if position + 1 < len(starts) else len(text)
            fragment = text[match.start():end]
            record = {
                "module": name, "written_name": written,
                "visibility": "private" if private else "public",
                "original_line": text.count("\n", 0, match.start()) + 1,
                "original_source_sha256": manifest[name]["source_sha256"],
                "provisional_effective_lines": counter.count_code_lines(fragment),
                "provisional_bytes": len(fragment.encode()),
                "preceding_scoped_directive": previous.strip() if previous.rstrip().endswith(" in") else None,
            }
            occurrences[basename].append((record, collections.Counter(words(kept[match.start():end])), previous.startswith("@[")))
    remaining = {name: entries[0] for name, entries in occurrences.items() if len(entries) == 1 and name not in protected and not entries[0][2]}
    frontier = {name for name in remaining if tokens[name] == 1}
    rounds, candidates = [], []
    for index in range(limit):
        selected, touched = [], set()
        for name in sorted(frontier):
            record, fragment_words, _ = remaining.pop(name)
            selected.append({**record, "round": index + 1})
            for word, count in fragment_words.items():
                assert tokens[word] >= count, (record["module"], name, word)
                tokens[word] -= count
                if word in remaining:
                    touched.add(word)
        row = {"round": index + 1, "candidates": len(selected), "modules": len({r["module"] for r in selected}), "provisional_effective_lines": sum(r["provisional_effective_lines"] for r in selected)}
        rounds.append(row)
        candidates.extend(selected)
        print(json.dumps(row), flush=True)
        if not selected:
            break
        frontier = {name for name in touched if tokens[name] == 1}
    fixed_point = not frontier
    if fixed_point:
        assert all(tokens[name] != 1 for name in remaining)
    return rounds, candidates, fixed_point


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--max-rounds", type=int, default=16)
    parser.add_argument("--incremental", action="store_true", help="Update token counts incrementally; identical conservative lexical criterion")
    args = parser.parse_args()
    run, output = args.run.resolve(), args.output_dir.resolve()
    if output.exists() or args.max_rounds < 1:
        parser.error("use a new output directory and a positive round limit")
    here = Path(__file__).resolve().parent
    repo, canonical = here.parents[1], here.parent / "wu2008"
    manifest_path = run / "source-manifest.json"
    manifest = {r["module"]: r for r in json.loads(manifest_path.read_text())}
    source_root = run / "src"
    graph = {n: [d for d in r["imports"] if d in manifest] for n, r in manifest.items()}
    closure, todo = set(), ["WR2ClassicalCertificate"]
    while todo:
        name = todo.pop()
        if name in closure:
            continue
        closure.add(name)
        todo.extend(graph[name])
    assert len(manifest) == 4151 and len(closure) == 3764
    spec = importlib.util.spec_from_file_location("published_counter", repo / "scripts/check.py")
    counter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(counter)
    protected, bindings = set(), {str(manifest_path): sha(manifest_path)}
    for kind in ["types", "values"]:
        source = repo / "research/wu-unused-proof-audit/isolated" / ("after-" + kind + ".json")
        bindings[str(source)] = sha(source)
        protected.update(n.split(".")[-1] for n in json.loads(source.read_text())["requested_names"])
    for stem in ["jurkat-cutoff", "pan-shared-square", "shared-singular-series"]:
        source = here / (stem + "-evidence/before-types.json")
        bindings[str(source)] = sha(source)
        protected.update(r["name"].split(".")[-1] for r in json.loads(source.read_text()))
    protected.update(["one8938", "one894", "classical_lower"])
    exclusions, consumers = [], []
    archival = [
        (canonical / "history", "Historical variants are outside the supported build; research/wu2008/README.md explicitly does not promise they compile."),
        (repo / "research/wu-hf4-constructive-wip", "Historical construction work, excluded by the previous accepted opportunity scan."),
        (repo / "research/wu-hf4-constructive-audit/isolated", "Historical validation probes, excluded by the previous accepted opportunity scan."),
    ]
    names = subprocess.check_output(["rg", "--files", "-g", "*.md", "-g", "*.py", "-g", "*.lean"], cwd=repo, text=True).splitlines()
    for relative in names:
        path = repo / relative
        if path.is_relative_to(canonical / "src"):
            continue
        reason = next((reason for root, reason in archival if path.is_relative_to(root)), None)
        if reason:
            exclusions.append({"path": relative, "sha256": sha(path), "reason": reason})
            continue
        bindings[str(path)] = sha(path)
        consumers.append(relative)
        protected.update(words(path.read_text()))
    golden = canonical / "diagnostics/hf4_constructive/frozen/golden.json"
    bindings[str(golden)] = sha(golden)
    generated = set(json.loads(golden.read_text())["routes"]["constructive"]["modules"])
    assert len(generated) == 17
    texts = {}
    for name, row in manifest.items():
        path = source_root / Path(*name.split(".")).with_suffix(".lean")
        assert sha(path) == row["source_sha256"], name
        texts[name] = path.read_text()
    originals = dict(texts)
    pattern = re.compile(r"^(?P<private>private\s+(?:noncomputable\s+)?)?(?:theorem|lemma)\s+(?P<name>[A-Za-z_][\w.']*)(?![\w.'])", re.M)
    rounds, all_candidates = [], []
    output.mkdir(parents=True)
    fixed_point = False
    if args.incremental:
        rounds, all_candidates, fixed_point = incremental_rounds(texts, manifest, closure, generated, protected, counter, pattern, args.max_rounds)
    for index in range(0 if args.incremental else args.max_rounds):
        tokens = collections.Counter()
        for text in texts.values():
            tokens.update(words(counter.code_only(text, keep_strings=True)))
        selected, removals = [], collections.defaultdict(list)
        for name in sorted(closure - generated):
            text = texts[name]
            masked = counter.code_only(text)
            starts = [m.start() for m in re.finditer(r"^\S", masked, re.M)]
            for match in pattern.finditer(masked):
                written, private = match["name"], bool(match["private"])
                basename = written.split(".")[-1]
                if tokens[basename] != 1 or basename in protected:
                    continue
                position = bisect.bisect_left(starts, match.start())
                previous = masked[starts[position - 1]:match.start()].lstrip() if position else ""
                if previous.startswith("@["):
                    continue
                end = starts[position + 1] if position + 1 < len(starts) else len(text)
                fragment = text[match.start():end]
                original_matches = [m for m in pattern.finditer(counter.code_only(originals[name])) if m["name"] == written]
                assert len(original_matches) == 1
                selected.append({
                    "round": index + 1, "module": name, "written_name": written,
                    "visibility": "private" if private else "public",
                    "original_line": originals[name].count("\n", 0, original_matches[0].start()) + 1,
                    "original_source_sha256": manifest[name]["source_sha256"],
                    "provisional_effective_lines": counter.count_code_lines(fragment),
                    "provisional_bytes": len(fragment.encode()),
                    "preceding_scoped_directive": previous.strip() if previous.rstrip().endswith(" in") else None,
                })
                removals[name].append((match.start(), end))
        row = {"round": index + 1, "candidates": len(selected), "modules": len(removals), "provisional_effective_lines": sum(r["provisional_effective_lines"] for r in selected)}
        rounds.append(row)
        print(json.dumps(row), flush=True)
        all_candidates.extend(selected)
        if not selected:
            fixed_point = True
            break
        for name, intervals in removals.items():
            for start, end in sorted(intervals, reverse=True):
                texts[name] = texts[name][:start] + texts[name][end:]
    assert sha(manifest_path) == bindings[str(manifest_path)]
    for name, row in manifest.items():
        assert sha(source_root / Path(*name.split(".")).with_suffix(".lean")) == row["source_sha256"]
    result = {
        "status": "LEXICAL_ITERATED_OPPORTUNITIES_ONLY_NOT_REFERENCES_DELETION_OR_PROOF_ACCEPTANCE",
        "source_manifest_sha256": sha(manifest_path), "source_modules": len(manifest),
        "final_closure_modules": len(closure), "rounds": rounds,
        "incremental_token_model": args.incremental, "lexical_fixed_point_reached": fixed_point,
        "candidates": all_candidates, "consumers": consumers,
        "archival_exclusions": exclusions, "bindings": bindings,
        "producer_owned_modules_excluded": sorted(generated),
        "limitations": [
            "All stripping occurred in memory; no source file was edited and no Lean process was started.",
            "Later rounds model calls removed with earlier candidates; they are not independently zero-incoming claims.",
            "Provisional spans are lexical, not compiler declaration/doc/directive ranges.",
            "A private-inclusive compiled census must reject any incoming reference from a retained declaration, including generated proof auxiliaries and registration consumers.",
            "Generator consumers, exact source ranges, retained interfaces, precision, downstream compilation and kernel replay still require validation.",
        ],
    }
    (output / "opportunities.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "candidates": len(all_candidates), "rounds": len(rounds), "archival_exclusions": len(exclusions)}), flush=True)


if __name__ == "__main__":
    main()
