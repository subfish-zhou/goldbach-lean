#!/usr/bin/env python3
"""Export the complete four-library import and compiled-Const explorer.

Only tools/ProjectStructure.lean is interpreted; mathematical modules are read
from their existing ModuleData, never rebuilt. Output must be a new directory;
the publishable route is OUTPUT/structure. An optional API bundle supplies only
links whose actual HTML anchors exist. Without it, commit-pinned source links
remain available for every module and declaration.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import html
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
from urllib.parse import quote, unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
LIBRARIES = ("Goldbach", "MathlibNt", "AnalyticNumberTheory", "PrimeNumberTheoremAnd")
SOURCE_REPO = "https://github.com/subfish-zhou/goldbach-lean"
EDGE_TYPES = ("type", "value", "recursorRHS")
SCOPES = ("local", "local-extra", "outside-local-census")
SCHEMA = 1
ENTRY_POINTS = (
    ("Chen 1+2", "Goldbach", "Goldbach.chen_theorem"),
    ("Li–Liu natural witnesses", "Goldbach.OnePlusOneNine", "Goldbach.one_plus_one_nine"),
    ("Li–Liu real witnesses", "Goldbach.OnePlusOneNine", "Goldbach.one_plus_one_nine_real"),
    ("Li–Liu strict count", "Goldbach.OnePlusOneNine", "Goldbach.one_plus_one_nine_count"),
    ("Li–Liu coefficient family", "Goldbach.OnePlusOneNine", "Goldbach.one_plus_one_nine_lower_bound"),
    ("Both public interfaces", "Goldbach.All", None),
)


def read_json(path):
    return json.loads(Path(path).read_text())


def write_json(path, data):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, separators=(",", ":")) + "\n")


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def source_path(module):
    return Path(*module.split(".")).with_suffix(".lean")


def modules_in(root):
    result = []
    for library in LIBRARIES:
        paths = list((root / library).rglob("*.lean"))
        if (root / (library + ".lean")).is_file():
            paths.append(root / (library + ".lean"))
        result.extend(".".join(p.relative_to(root).with_suffix("").parts) for p in paths)
    if len(set(result)) != len(result) or not result:
        raise ValueError("Empty or duplicate source module inventory")
    return sorted(result)


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def revision_checked(revision, modules):
    revision = revision or git("rev-parse", "HEAD")
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("Expected an exact 40-character lowercase source revision")
    if git("cat-file", "-t", revision) != "commit":
        raise ValueError("Source revision is not a commit")
    # Verify actual source bytes, not just that the requested commit exists.
    entries = git("ls-tree", "-r", revision, "--", *LIBRARIES,
                  *(x + ".lean" for x in LIBRARIES)).splitlines()
    blobs = {line.split("\t", 1)[1]: line.split()[2] for line in entries}
    for module in modules:
        relative = source_path(module).as_posix()
        data = (ROOT / relative).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if blobs.get(relative) != blob:
            raise ValueError(f"Source differs from revision {revision}: {relative}")
    committed = {p for p in blobs if p.endswith(".lean")}
    if committed != {source_path(m).as_posix() for m in modules}:
        raise ValueError("Source revision and working tree have different module inventories")
    return revision


def normalize_declarations(raw):
    if raw["constNames"] != [d["name"] for d in raw["declarations"]]:
        raise ValueError("ModuleData.constNames / constants census mismatch")
    result = {}
    for row in raw["declarations"]:
        row = dict(row)
        for edge in EDGE_TYPES:
            row[edge] = sorted(set(row[edge]))
        old = result.get(row["name"])
        if old is not None and old != row:
            # Module-system exported/server parts can contain axiom-shaped
            # signatures whose theorem/opaque body is in the private part.
            # Prefer the body-bearing record, but only with identical type
            # Const references; other conflicting signatures remain errors.
            shell, body = (old, row) if row["hasValue"] else (row, old)
            if (shell["kind"] == "axiom" and not shell["hasValue"]
                    and body["hasValue"] and shell["type"] == body["type"]
                    and not shell["value"] and not shell["recursorRHS"]):
                row = body
            else:
                raise ValueError(f"Conflicting declaration across object parts: {row['name']}")
        result[row["name"]] = row
    return sorted(result.values(), key=lambda d: d["name"])


def classify(name, owners, extras):
    if name in owners:
        return {"scope": "local", "modules": owners[name]}
    if name in extras:
        return {"scope": "local-extra", "modules": extras[name]}
    return {"scope": "outside-local-census", "modules": []}


def cyclic_components(graph):
    """Iterative Kosaraju; return only nontrivial SCCs and self loops.

    Never discard edges to make a DAG. The UI detects ancestor revisits and
    exposes SCC membership; even a one-node recursive cluster is retained.
    """
    visited, order = set(), []
    reverse = {n: [] for n in graph}
    for node, targets in graph.items():
        for target in targets:
            if target not in graph:
                raise ValueError(f"Dangling graph target: {target}")
            reverse[target].append(node)
        if node in visited:
            continue
        visited.add(node)
        stack = [(node, iter(targets))]
        while stack:
            current, remaining = stack[-1]
            target = next(remaining, None)
            if target is None:
                order.append(current)
                stack.pop()
            elif target not in visited:
                visited.add(target)
                stack.append((target, iter(graph[target])))
    visited.clear()
    components = []
    for node in reversed(order):
        if node in visited:
            continue
        stack, members = [node], []
        visited.add(node)
        while stack:
            current = stack.pop()
            members.append(current)
            for target in reverse[current]:
                if target not in visited:
                    visited.add(target)
                    stack.append(target)
        if len(members) > 1 or node in graph[node]:
            components.append(sorted(members))
    return sorted(components, key=lambda c: c[0])


class AnchorParser(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.ids = set()

    def handle_starttag(self, tag, attrs):
        value = dict(attrs).get("id")
        if value is not None:
            self.ids.add(value)


def api_links(api):
    """Use verified doc-gen links, never manufacture auxiliary anchors."""
    if api is None:
        return {}, set()
    api = Path(api).resolve()
    data = read_json(api / "declarations/declaration-data.bmp")
    cache, links, pages = {}, {}, set()
    for name, decl in data["declarations"].items():
        parsed = urlsplit(decl["docLink"])
        if parsed.scheme or parsed.netloc:
            continue
        relative = unquote(parsed.path).removeprefix("./")
        path = (api / relative).resolve()
        if not path.is_relative_to(api) or not path.is_file():
            raise ValueError(f"Missing or unsafe API page: {decl['docLink']}")
        if path not in cache:
            parser = AnchorParser()
            parser.feed(path.read_text())
            cache[path] = parser.ids
        if not parsed.fragment or unquote(parsed.fragment) not in cache[path]:
            raise ValueError(f"Missing API anchor: {decl['docLink']}")
        links[name] = "../../docs/" + quote(relative, safe="/") + "#" + parsed.fragment
        pages.add(".".join(Path(relative).with_suffix("").parts))
    for module in modules_in(ROOT):
        if (api / source_path(module).with_suffix(".html")).is_file():
            pages.add(module)
    return links, pages


def closure(start, graph):
    seen, queue = set(), [start]
    while queue:
        node = queue.pop()
        if node not in seen:
            seen.add(node)
            queue.extend(graph[node])
    return seen


def module_proof_roles(owners, graph, module_count):
    """Membership means at least one census declaration is actually referenced."""
    roots = {
        "Chen 1+2": ["Goldbach.chen_theorem"],
        "Li–Liu existence": ["Goldbach.one_plus_one_nine", "Goldbach.one_plus_one_nine_real"],
        "Li–Liu count": ["Goldbach.one_plus_one_nine_count", "Goldbach.one_plus_one_nine_lower_bound"],
    }
    roles = [[] for _ in range(module_count)]
    for label, names in roots.items():
        reached = set().union(*(closure(name, graph) for name in names))
        providers = {mid for name in reached for mid in owners.get(name, [])}
        for mid in sorted(providers):
            roles[mid].append(label)
    return roles


def projection(owners):
    nodes = read_json(ROOT / "blueprint/nodes.json")
    graph = read_json(ROOT / "blueprint/graph.json")
    projected = []
    for node in nodes:
        name = node["declaration"]
        if name not in owners:
            raise ValueError(f"Blueprint declaration not found in actual constNames: {name}")
        projected.append({"label": node["label"], "name": name,
                          "title": node["title"], "chapter": node["chapter"],
                          "modules": owners[name]})
    labels = {n["label"] for n in projected}
    if labels != set(graph["nodes"]):
        raise ValueError("Blueprint node inventories disagree")
    edges = graph["edges"]
    if any(a not in labels or b not in labels for a, b in edges):
        raise ValueError("Dangling Blueprint edge")
    return {"schemaVersion": SCHEMA, "kind": "hand-selected-blueprint-projection",
            "edgeDirection": "prerequisite-to-consumer",
            "edgeMeaning": "Compiled dependencies among hand-selected explanatory nodes; not the complete Const or import graph",
            "nodes": projected, "edges": edges, "url": "../../blueprint/index.html"}


def build_structure(output, *, source_revision=None, api=None, batch_size=64, extraction_cache=None):
    output = Path(output).resolve()
    if output.exists():
        raise ValueError("Output already exists; choose a new directory")
    if not 1 <= batch_size <= 256:
        raise ValueError("Batch size must be between 1 and 256")
    modules = modules_in(ROOT)
    revision = revision_checked(source_revision, modules)
    links, api_pages = api_links(api)
    objects = ROOT / ".lake/build/lib/lean"
    missing = [m for m in modules if not (objects / source_path(m).with_suffix(".olean")).is_file()]
    if missing:
        raise ValueError("Missing compiled modules; build libraries first: " + ", ".join(missing[:12]))
    support = ["lean-toolchain", "lake-manifest.json", "lakefile.toml", "tools/ProjectStructure.lean",
               "scripts/build_project_structure.py", "blueprint/nodes.json", "blueprint/graph.json",
               "website/structure/panel.html", "website/structure/explorer.js", "website/structure/explorer.css"]
    support_hashes = {p: digest(ROOT / p) for p in support}
    inputs = []
    for module in modules:
        source = ROOT / source_path(module)
        obj = objects / source_path(module).with_suffix(".olean")
        parts = [obj] + [Path(str(obj) + s) for s in (".server", ".private") if Path(str(obj) + s).exists()]
        if obj.with_suffix(".ir.sig").exists():
            parts += [obj.with_suffix(".ir.sig"), obj.with_suffix(".ir")]
        inputs.append({"module": module, "source": {"path": str(source.relative_to(ROOT)), "sha256": digest(source)},
                       "objects": [{"path": str(p.relative_to(ROOT)), "sha256": digest(p)} for p in parts]})
    # Temporary output is not published on errors; mathematical inputs are read-only.
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="structure-run-", dir=output.parent) as temp:
        temp = Path(temp)
        structure, rawdir = temp / "publish/structure", temp / "raw"
        structure.mkdir(parents=True)
        cache_key = hashlib.sha256(json.dumps([inputs, digest(ROOT / "tools/ProjectStructure.lean")], sort_keys=True).encode()).hexdigest()
        if extraction_cache:
            rawdir = Path(extraction_cache).resolve() / cache_key
        rawdir.mkdir(parents=True, exist_ok=True)
        for start in range(0, len(modules), batch_size):
            manifest = temp / "batch.tsv"
            rows = []
            for i in range(start, min(start + batch_size, len(modules))):
                cached, checksum = rawdir / f"{i}.json", rawdir / f"{i}.sha256"
                if cached.is_file() and checksum.is_file() and checksum.read_text().strip() == digest(cached):
                    continue
                src = ROOT / source_path(modules[i])
                obj = objects / source_path(modules[i]).with_suffix(".olean")
                rows.append(f"{src}\t{obj}\t{rawdir / f'{i}.json'}")
            manifest.write_text("\n".join(rows) + "\n")
            proc = subprocess.run(["lake", "env", "lean", "--run", "tools/ProjectStructure.lean", str(manifest)],
                                  cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if proc.returncode:
                raise RuntimeError(f"ModuleData batch {start} failed:\n{proc.stdout}")
            for row in rows:
                rawpath = Path(row.split("\t")[2])
                rawpath.with_suffix(".sha256").write_text(digest(rawpath) + "\n")
            print(f"ModuleData {min(start + batch_size, len(modules))}/{len(modules)}", flush=True)
        owners, extras, module_rows = {}, {}, []
        module_ids = {m: i for i, m in enumerate(modules)}
        for i, module in enumerate(modules):
            raw = read_json(rawdir / f"{i}.json")
            declarations = normalize_declarations(raw)
            if set(raw["sourceImports"]) != set(raw["compiledImports"]):
                raise ValueError(f"Source/compiled import mismatch: {module}")
            for name in {d["name"] for d in declarations}:
                owners.setdefault(name, []).append(i)
            for name in set(raw["extraConstNames"]):
                extras.setdefault(name, []).append(i)
            imports = sorted(set(raw["sourceImports"]))
            relative = source_path(module).as_posix()
            module_rows.append({"id": i, "name": module, "library": module.split(".")[0],
                                "source": f"{SOURCE_REPO}/blob/{revision}/{quote(relative, safe='/')}",
                                "api": "../../docs/" + quote(relative[:-5] + ".html", safe="/") if module in api_pages else None,
                                "imports": [module_ids[x] for x in imports if x in module_ids],
                                "externalImports": [x for x in imports if x not in module_ids],
                                "declarationCount": len(declarations), "shard": f"modules/{i}.json"})
        graph = {}
        signatures = {}
        counts = Counter()
        kinds = Counter()
        search = []
        search_files = []
        for i, module in enumerate(modules):
            raw = read_json(rawdir / f"{i}.json")
            raw["declarations"] = normalize_declarations(raw)
            raw["constNames"] = [d["name"] for d in raw["declarations"]]
            references = {n for d in raw["declarations"] for edge in EDGE_TYPES for n in d[edge]}
            targets = {n: classify(n, owners, extras) for n in sorted(references)}
            declarations = []
            for d in raw["declarations"]:
                name = d["name"]
                # Repeated generated equation names retain every actual provider.
                # Merge graph nodes only if their complete reference signatures agree.
                if name in signatures and signatures[name] != d:
                    raise ValueError(f"Different compiled reference signatures for shared name: {name}")
                first = name not in signatures
                signatures[name] = d
                graph[name] = {n for edge in EDGE_TYPES for n in d[edge] if n in owners}
                if first:
                    kinds[d["kind"]] += 1
                    for edge in EDGE_TYPES:
                        for n in d[edge]:
                            counts[f"{edge}:{targets[n]['scope']}"] += 1
                declarations.append({"name": name, "kind": d["kind"], "hasValue": d["hasValue"],
                                     "api": links.get(name), "refs": {edge: d[edge] for edge in EDGE_TYPES},
                                     "cycle": None})
                search.append([name, i, d["kind"]])
            shard = {"schemaVersion": SCHEMA, "module": i, "constNames": raw["constNames"],
                     "extraConstNames": sorted(set(raw["extraConstNames"])),
                     "targets": targets, "declarations": declarations}
            write_json(structure / module_rows[i]["shard"], shard)
            if (i + 1) % 128 == 0 or i + 1 == len(modules):
                path = f"search/{len(search_files)}.json"
                write_json(structure / path, {"schemaVersion": SCHEMA, "declarations": search})
                search_files.append({"path": path, "count": len(search)})
                search = []
        components = cyclic_components(graph)
        cycle_owner = {name: i for i, group in enumerate(components) for name in group}
        for i, group in enumerate(components):
            write_json(structure / f"cycles/{i}.json", {"schemaVersion": SCHEMA, "id": i,
                       "members": [[name, owners[name]] for name in group]})
        for module in module_rows:
            shard = read_json(structure / module["shard"])
            for d in shard["declarations"]:
                d["cycle"] = cycle_owner.get(d["name"])
            write_json(structure / module["shard"], shard)
        import_graph = {m["id"]: set(m["imports"]) for m in module_rows}
        import_cycles = cyclic_components(import_graph)
        entries = []
        for label, module, name in ENTRY_POINTS:
            mid = module_ids[module]
            entries.append({"label": label, "module": mid, "declaration": name,
                            "declarationModules": owners.get(name, []), "edgeType": "module-import",
                            "directImports": module_rows[mid]["imports"],
                            "reachableModuleCountIncludingEntry": len(closure(mid, import_graph)),
                            "reachableDeclarationCountIncludingEntry": len(closure(name, graph)) if name else None})
        roles = module_proof_roles(owners, graph, len(modules))
        for module, labels in zip(module_rows, roles):
            module["proofRoles"] = labels
        bp = projection(owners)
        write_json(structure / "blueprint-projection.json", bp)
        write_json(structure / "modules.json", {"schemaVersion": SCHEMA, "modules": module_rows,
                   "entries": entries, "searchShards": search_files,
                   "cycles": [{"id": i, "size": len(group), "shard": f"cycles/{i}.json"} for i, group in enumerate(components)],
                   "importCycles": import_cycles})
        input_document = {"modules": inputs, "support": support_hashes,
                          "apiIndex": digest(Path(api) / "declarations/declaration-data.bmp") if api else None}
        write_json(structure / "inputs.json", input_document)
        report = {"schemaVersion": SCHEMA, "source_revision": revision, "scope": "full-four-library",
                  "input_fingerprint": digest(structure / "inputs.json"),
                  "module_count": len(modules), "libraries": dict(Counter(m["library"] for m in module_rows)),
                  "declaration_count": len(owners), "declaration_kinds": dict(kinds),
                  "declaration_record_count": sum(m["declarationCount"] for m in module_rows),
                  "multiple_census_name_count": sum(len(ms) > 1 for ms in owners.values()),
                  "extra_const_name_count": len(extras),
                  "module_import_edge_count": sum(len(m["imports"]) for m in module_rows),
                  "external_module_import_edge_count": sum(len(m["externalImports"]) for m in module_rows),
                  "const_reference_counts": {f"{e}:{s}": counts[f"{e}:{s}"] for e in EDGE_TYPES for s in SCOPES},
                  "cyclic_declaration_components": len(components), "declarations_in_cycles": len(cycle_owner),
                  "cyclic_import_components": len(import_cycles),
                  "blueprint_node_count": len(bp["nodes"]), "blueprint_edge_count": len(bp["edges"]),
                  "api_link_count": sum(n in links for n in owners),
                  "proof_role_scope": "A module has a role when at least one actual census declaration is in the named endpoint's static Const closure; import reachability is separate",
                  "ownership": "Exact ModuleData.constNames, cross-checked against constants; all providers retained for repeated names, never namespace inference",
                  "edge_types": {"module-import": "consumer -> direct parsed source import; compiled imports cross-checked",
                                 "type": "declaration -> Expr.const in compiled type",
                                 "value": "declaration -> Expr.const in theorem proof / definition / opaque value",
                                 "recursorRHS": "declaration -> Expr.const in recursor rule RHS",
                                 "blueprint": "hand-selected explanatory prerequisite -> consumer"},
                  "reference_scopes": {"local": "Present in local constNames; modules lists ALL actual census providers",
                                       "local-extra": "Owned only by local extraConstNames; no ConstantInfo body available",
                                       "outside-local-census": "External or unresolved boundary; no package/owner inferred from namespace"},
                  "limits": ["Static Expr.const references, not arbitrary reflection, tactics, runtime calls, or dynamic name lookup",
                             "Projection metadata and inductive/constructor metadata are not Const occurrences",
                             "References are unique per declaration, edge type and target, not occurrence multiplicities",
                             "Repeated names retain all census providers; name graphs are merged only after identical reference signatures are checked",
                             "Outside-local-census targets are retained by exact name, not recursively expanded",
                             "Cycles and self-references are retained; the original declaration graph is not assumed to be a DAG",
                             "Reads existing objects; checks source revision and import headers, fingerprints bytes, does not rerun kernel verification",
                             "Generated declarations without verified API anchors link to their owning module source"],
                  "lean_version": subprocess.check_output(["lake", "env", "lean", "--version"], cwd=ROOT, text=True).strip()}
        write_json(structure / "build-info.json", report)
        for name in ("panel.html", "explorer.js", "explorer.css"):
            shutil.copy2(ROOT / "website/structure" / name, structure / name)
        # Detect concurrent changes in source/object bytes during extraction.
        for item in inputs:
            for file in [item["source"], *item["objects"]]:
                if digest(ROOT / file["path"]) != file["sha256"]:
                    raise ValueError(f"Input changed during export: {file['path']}")
        for path, expected in support_hashes.items():
            if digest(ROOT / path) != expected:
                raise ValueError(f"Support input changed during export: {path}")
        verify_export(structure, expected_modules=modules, api=api)
        (temp / "publish").rename(output)
    return report


def verify_export(structure, *, expected_modules=None, api=None):
    """Independent readback gate for every module, name, edge and UI shard."""
    structure = Path(structure)
    info, index = read_json(structure / "build-info.json"), read_json(structure / "modules.json")
    if info["schemaVersion"] != SCHEMA or index["schemaVersion"] != SCHEMA:
        raise ValueError("Unsupported schema")
    modules = index["modules"]
    names = [m["name"] for m in modules]
    if len(set(names)) != len(names) or len(names) != info["module_count"]:
        raise ValueError("Module census mismatch")
    if expected_modules is not None and set(names) != set(expected_modules):
        raise ValueError("Incomplete source module coverage")
    if [m["id"] for m in modules] != list(range(len(modules))):
        raise ValueError("Module IDs must be contiguous")
    if digest(structure / "inputs.json") != info["input_fingerprint"]:
        raise ValueError("Input fingerprint mismatch")
    owners, extras, declarations, all_shards = {}, {}, {}, []
    actual_api = api_links(api)[0] if api else None
    for m in modules:
        if m["library"] not in LIBRARIES or any(i not in range(len(modules)) for i in m["imports"]):
            raise ValueError("Invalid module/import schema")
        if len(set(m["imports"])) != len(m["imports"]):
            raise ValueError("Duplicate import edge")
        expected_source = f"{SOURCE_REPO}/blob/{info['source_revision']}/{quote(source_path(m['name']).as_posix(), safe='/')}"
        if m["source"] != expected_source or not re.fullmatch(r"modules/\d+\.json", m["shard"]):
            raise ValueError("Invalid source/shard link")
        shard = read_json(structure / m["shard"])
        if shard["schemaVersion"] != SCHEMA or shard["module"] != m["id"]:
            raise ValueError("Module shard identity mismatch")
        if shard["constNames"] != [d["name"] for d in shard["declarations"]] or len(shard["declarations"]) != m["declarationCount"]:
            raise ValueError("Declaration census mismatch")
        for d in shard["declarations"]:
            if d["name"] in declarations and declarations[d["name"]] != d:
                raise ValueError("Different reference signatures for shared constant name")
            owners.setdefault(d["name"], []).append(m["id"])
            declarations[d["name"]] = d
            if d["kind"] in ("theorem", "definition", "opaque") and not d["hasValue"]:
                raise ValueError("Missing required proof/definition value")
            if d["api"] is not None:
                if not d["api"].startswith("../../docs/") or "#" not in d["api"]:
                    raise ValueError("Invalid API route")
                if actual_api is not None and actual_api.get(d["name"]) != d["api"]:
                    raise ValueError("API link does not match verified anchor")
        for name in shard["extraConstNames"]:
            extras.setdefault(name, []).append(m["id"])
        all_shards.append(shard)
    counts, graph, counted = Counter(), {}, set()
    for shard in all_shards:
        used = set()
        for d in shard["declarations"]:
            if set(d["refs"]) != set(EDGE_TYPES):
                raise ValueError("Missing edge type")
            first = d["name"] not in counted
            counted.add(d["name"])
            graph[d["name"]] = set()
            for edge, refs in d["refs"].items():
                if refs != sorted(set(refs)):
                    raise ValueError("Noncanonical/duplicate references")
                for name in refs:
                    used.add(name)
                    target = shard["targets"][name]
                    if target != classify(name, owners, extras):
                        raise ValueError("Wrong actual reference owner/classification")
                    if first:
                        counts[f"{edge}:{target['scope']}"] += 1
                    if target["scope"] == "local":
                        graph[d["name"]].add(name)
        if used != set(shard["targets"]):
            raise ValueError("Unused or missing target entries")
    expected_counts = {f"{e}:{s}": counts[f"{e}:{s}"] for e in EDGE_TYPES for s in SCOPES}
    if expected_counts != info["const_reference_counts"] or len(owners) != info["declaration_count"]:
        raise ValueError("Reference/declaration totals disagree")
    search = {}
    for item in index["searchShards"]:
        if not re.fullmatch(r"search/\d+\.json", item["path"]):
            raise ValueError("Unsafe search shard")
        rows = read_json(structure / item["path"])
        if rows["schemaVersion"] != SCHEMA or len(rows["declarations"]) != item["count"]:
            raise ValueError("Search shard count mismatch")
        for name, module, kind in rows["declarations"]:
            if module in search.get(name, []) or module not in owners.get(name, []) or declarations[name]["kind"] != kind:
                raise ValueError("Invalid search declaration/owner")
            search.setdefault(name, []).append(module)
    if search != owners:
        raise ValueError("Search does not cover all declarations")
    if sum(len(ms) for ms in owners.values()) != info["declaration_record_count"] or sum(len(ms) > 1 for ms in owners.values()) != info["multiple_census_name_count"]:
        raise ValueError("Repeated-name census counts disagree")
    components = cyclic_components(graph)
    if len(components) != info["cyclic_declaration_components"] or len(index["cycles"]) != len(components):
        raise ValueError("SCC count mismatch")
    cyc = {n: i for i, group in enumerate(components) for n in group}
    for d in declarations.values():
        if d["cycle"] != cyc.get(d["name"]):
            raise ValueError("Incorrect SCC membership")
    for i, group in enumerate(components):
        row = index["cycles"][i]
        expected = {"id": i, "size": len(group), "shard": f"cycles/{i}.json"}
        if row != expected or read_json(structure / row["shard"])["members"] != [[n, owners[n]] for n in group]:
            raise ValueError("Incorrect cycle shard")
    import_graph = {m["id"]: set(m["imports"]) for m in modules}
    if sum(map(len, import_graph.values())) != info["module_import_edge_count"]:
        raise ValueError("Import count mismatch")
    if sum(len(m["externalImports"]) for m in modules) != info["external_module_import_edge_count"]:
        raise ValueError("External import count mismatch")
    if dict(Counter(m["library"] for m in modules)) != info["libraries"]:
        raise ValueError("Library counts disagree")
    if dict(Counter(d["kind"] for d in declarations.values())) != info["declaration_kinds"]:
        raise ValueError("Declaration kind counts disagree")
    if len(extras) != info["extra_const_name_count"] or len(cyc) != info["declarations_in_cycles"]:
        raise ValueError("Extra-name/cycle counts disagree")
    if sum(bool(d["api"]) for d in declarations.values()) != info["api_link_count"]:
        raise ValueError("API link count mismatch")
    if cyclic_components(import_graph) != index["importCycles"] or len(index["importCycles"]) != info["cyclic_import_components"]:
        raise ValueError("Import SCC mismatch")
    roles = module_proof_roles(owners, graph, len(modules))
    if any(m.get("proofRoles") != role for m, role in zip(modules, roles)):
        raise ValueError("Module proof-role classification mismatch")
    if len(index["entries"]) != len(ENTRY_POINTS):
        raise ValueError("Missing public entry")
    for entry, (label, module, name) in zip(index["entries"], ENTRY_POINTS):
        mid = names.index(module)
        if entry["label"] != label or entry["module"] != mid or entry["declaration"] != name or entry["directImports"] != modules[mid]["imports"]:
            raise ValueError("Incorrect public entry")
        if entry["reachableModuleCountIncludingEntry"] != len(closure(mid, import_graph)):
            raise ValueError("Incorrect entry import closure")
        if name and (entry["declarationModules"] != owners[name] or entry["reachableDeclarationCountIncludingEntry"] != len(closure(name, graph))):
            raise ValueError("Incorrect entry Const closure")
    # These direct entry dependencies are public-interface acceptance criteria.
    required = {"Goldbach": {"Goldbach.Theorem"},
                "Goldbach.Theorem": {"Goldbach.Statement", "MathlibNt.ChensTheoremUnconditional"},
                "Goldbach.OnePlusOneNine": {"MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorQuantitative"},
                "Goldbach.All": {"Goldbach", "Goldbach.OnePlusOneNine"}}
    for name, wanted in required.items():
        actual = {names[i] for i in modules[names.index(name)]["imports"]}
        if actual != wanted:
            raise ValueError(f"Unexpected real entry imports: {name}: {actual}")
    bp = read_json(structure / "blueprint-projection.json")
    if len(bp["nodes"]) != info["blueprint_node_count"] or len(bp["edges"]) != info["blueprint_edge_count"]:
        raise ValueError("Blueprint counts disagree")
    labels = {n["label"] for n in bp["nodes"]}
    if any(owners.get(n["name"]) != n["modules"] for n in bp["nodes"]) or any(a not in labels or b not in labels for a, b in bp["edges"]):
        raise ValueError("Invalid Blueprint projection")
    page = (structure / "panel.html").read_text()
    for route in ("../../docs/", "../../blueprint/", "../../index.html", "explorer.css", "explorer.js"):
        if route not in page:
            raise ValueError(f"Missing navigation route: {route}")
    for asset in ("explorer.css", "explorer.js"):
        if not (structure / asset).is_file():
            raise ValueError(f"Missing asset: {asset}")
    return {"module_count": len(modules), "declaration_count": len(owners),
            "module_import_edge_count": info["module_import_edge_count"],
            "const_reference_counts": expected_counts, "search_coverage": len(search),
            "declaration_record_count": sum(len(ms) for ms in owners.values()),
            "multiple_census_name_count": sum(len(ms) > 1 for ms in owners.values()),
            "cyclic_declaration_components": len(components), "entries": index["entries"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="New output directory; writes OUTPUT/structure")
    parser.add_argument("--source-revision", help="Exact source commit; defaults to actual git HEAD")
    parser.add_argument("--api", type=Path, help="Verified full API bundle (optional; otherwise source-only links)")
    parser.add_argument("--batch-size", type=int, default=64)
    parser.add_argument("--extraction-cache", type=Path, help="Private resumable cache keyed by all input and extractor hashes")
    args = parser.parse_args()
    report = build_structure(args.output, source_revision=args.source_revision, api=args.api, batch_size=args.batch_size, extraction_cache=args.extraction_cache)
    print(json.dumps(report, ensure_ascii=False, indent=2))
    print(f"Verified complete explorer: {args.output.resolve() / 'structure'}")


if __name__ == "__main__":
    main()
