#!/usr/bin/env python3
"""Build project-only doc-gen4 API pages from already compiled Lean artifacts."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import html
import json
import os
from pathlib import Path
import posixpath
import re
import shutil
import subprocess
import tempfile
from urllib.parse import quote, unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
LIBRARIES = ("Goldbach", "MathlibNt", "AnalyticNumberTheory", "PrimeNumberTheoremAnd")
MATHLIB_DOCS = "https://leanprover-community.github.io/mathlib4_docs/"
SOURCE_REPO = "https://github.com/subfish-zhou/goldbach-lean"
DOCGEN_REV = "498457dedc5bf2eb884c5100804ef24c96b92a08"
# Legacy relative URLs in migrated AnalyticNumberTheory module docstrings.
LEGACY_MODULE_LINKS = {
    "LargeSieve.WellSpaced": "AnalyticNumberTheory.LargeSieve.WellSpaced",
    "LargeSieve.PanTypeIAssembly": "AnalyticNumberTheory.LargeSieve.PanTypeIAssembly",
}
ATTR = re.compile(r'\b(href|src)=("|\')(.*?)\2', re.DOTALL)


def run(args, *, cwd=ROOT, env=None, capture=False):
    print("+", " ".join(map(str, args)), flush=True)
    return subprocess.run(list(map(str, args)), cwd=cwd, env=env, check=True,
                          text=True, stdout=subprocess.PIPE if capture else None).stdout


def modules_in(root):
    paths = []
    for library in LIBRARIES:
        if (root / f"{library}.lean").exists():
            paths.append(root / f"{library}.lean")
        paths.extend((root / library).rglob("*.lean"))
    return sorted(str(p.relative_to(root).with_suffix("")).replace(os.sep, ".") for p in paths)


def source_path(module):
    return Path(*module.split(".")).with_suffix(".lean")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def preflight(root, artifacts, modules):
    for name in ("lean-toolchain", "lake-manifest.json"):
        if (root / name).read_bytes() != (artifacts / name).read_bytes():
            raise ValueError(f"Artifact checkout has a different {name}")
    if (root / "docbuild/lean-toolchain").read_text().strip() != (root / "lean-toolchain").read_text().strip():
        raise ValueError("Documentation and theorem toolchains differ")
    missing = []
    for module in modules:
        source = source_path(module)
        if digest(root / source) != digest(artifacts / source):
            raise ValueError(f"Artifact source differs: {source}")
        olean = artifacts / ".lake/build/lib/lean" / source.with_suffix(".olean")
        if not olean.is_file():
            missing.append(module)
    if missing:
        raise ValueError("Compile the selected modules first with lake build: " + ", ".join(missing[:12]))


def dependency_roots(artifacts):
    manifest = json.loads((artifacts / "lake-manifest.json").read_text())
    roots = [artifacts / ".lake/build/lib/lean"]
    for package in manifest["packages"]:
        path = artifacts / manifest["packagesDir"] / package["name"] / ".lake/build/lib/lean"
        if path.is_dir():
            roots.append(path.resolve())
    return roots


def external_link(module_path, fragment, source_root, all_modules, manifest, mathlib_docs):
    module = module_path.removesuffix(".html").replace("/", ".")
    root = module.split(".")[0]
    if module in all_modules:
        # A deliberately partial build links omitted project modules to their source.
        return source_root + "/" + module_path.removesuffix(".html") + ".lean"
    if root == "Architect":
        package = next(p for p in manifest["packages"] if p["name"] == "LeanArchitect")
        return ("https://github.com/hanwenzhu/LeanArchitect/blob/" + package["rev"]
                + "/" + module_path.removesuffix(".html") + ".lean")
    # Mathlib's API site includes its imported libraries and Lean core. This is
    # intentionally a moving documentation endpoint, not a version-pinned proof input.
    known = {"Mathlib", "Batteries", "Aesop", "Qq", "Plausible", "ImportGraph",
             "LeanSearchClient", "ProofWidgets", "Cli", "Init", "Lean", "Std", "Lake"}
    if root not in known:
        raise ValueError(f"No external documentation mapping for {module}")
    return mathlib_docs.rstrip("/") + "/" + quote(module_path, safe="/") + ("#" + fragment if fragment else "")


def rewrite_site(site, all_modules, manifest, source_root, mathlib_docs):
    """Rewrite only missing module-page URLs, not assets or existing local pages."""
    external_urls = set()
    anchor_cache = {}

    def link(value, page):
        parsed = urlsplit(html.unescape(value))
        if parsed.scheme or parsed.netloc:
            if parsed.scheme in {"http", "https"} or parsed.netloc:
                external_urls.add(html.unescape(value))
            return value
        if not parsed.path or parsed.path.startswith("/"):
            return value
        rel = posixpath.normpath(posixpath.join(page.parent.as_posix(), unquote(parsed.path)))
        if rel.startswith("../"):
            raise ValueError(f"Link escapes site: {page}: {value}")
        target_page = site / rel
        auxiliary = re.fullmatch(r"(.+)\.(?:_proof_\d+|_aux_\d+|ctorIdx)",
                                 unquote(parsed.fragment))
        if auxiliary and target_page.is_file() and rel.endswith(".html"):
            # doc-gen4 omits compiler auxiliaries; link to their actual owner,
            # and only when that owner's anchor exists on this same page.
            if rel not in anchor_cache:
                anchor_cache[rel] = {html.unescape(x) for x in re.findall(
                    r'\bid="([^"]*)"', target_page.read_text())}
            anchors = anchor_cache[rel]
            if unquote(parsed.fragment) not in anchors and auxiliary[1] in anchors:
                return parsed._replace(fragment=quote(auxiliary[1], safe="")).geturl()
        if target_page.exists() or not rel.endswith(".html"):
            return value
        if rel.endswith(".html"):
            legacy = rel[:-5].replace("/", ".")
            if legacy in LEGACY_MODULE_LINKS:
                canonical = LEGACY_MODULE_LINKS[legacy]
                if canonical not in all_modules:
                    raise ValueError(f"Missing canonical module for legacy URL: {legacy}")
                rel = canonical.replace(".", "/") + ".html"
                if (site / rel).is_file():
                    target = posixpath.relpath(rel, page.parent.as_posix())
                    if parsed.query:
                        target += "?" + parsed.query
                    if parsed.fragment:
                        target += "#" + parsed.fragment
                    return target
        target = external_link(rel, parsed.fragment, source_root, all_modules, manifest, mathlib_docs)
        external_urls.add(target)
        return target

    def markup(text, page):
        def replace(match):
            target = link(match[3], page)
            if target == match[3]:
                return match[0]
            return f'{match[1]}={match[2]}{html.escape(target, quote=True)}{match[2]}'
        return ATTR.sub(replace, text)

    for file in site.rglob("*.html"):
        file.write_text(markup(file.read_text(), file.relative_to(site)))

    def data(value, key=""):
        if isinstance(value, dict):
            return {k: data(v, k) for k, v in value.items()}
        if isinstance(value, list):
            return [data(v, key) for v in value]
        if isinstance(value, str):
            if key in {"url", "docLink"}:
                return link(value, Path("index.html"))
            if key == "header":
                return markup(value, Path("index.html"))
        return value

    for file in (site / "declarations").glob("*.bmp"):
        file.write_text(json.dumps(data(json.loads(file.read_text())), ensure_ascii=False, separators=(",", ":")))
    return sorted(external_urls)


def verify_site(site, modules, *, site_root=None):
    index = json.loads((site / "declarations/declaration-data.bmp").read_text())
    for required in ("index.html", "search.html", "search.js", "find/index.html",
                     "declarations/header-data.bmp", "navbar.html", "style.css"):
        if not (site / required).is_file():
            raise ValueError(f"Missing documentation asset: {required}")
    for module in modules:
        path = source_path(module).with_suffix(".html")
        if not (site / path).is_file() or module not in index["modules"]:
            raise ValueError(f"Module missing from documentation or search: {module}")
    page_ids = {}
    for name, decl in index["declarations"].items():
        parsed = urlsplit(decl["docLink"])
        page = site / unquote(parsed.path)
        if page not in page_ids:
            page_ids[page] = {html.unescape(value) for value in re.findall(r'\bid="([^"]*)"', page.read_text())} if page.is_file() else set()
        if unquote(parsed.fragment) not in page_ids[page]:
            raise ValueError(f"Search target is missing: {name}")
    verify_local_links(site, boundary=site_root, find_routes=[site / "find/index.html"],
                       page_ids=page_ids)
    return len(index["declarations"])


def verify_local_links(site, *, boundary=None, find_routes=(), page_ids=None):
    """Check HTML links inside an explicit deployment boundary."""
    boundary = (boundary or site).resolve()
    find_routes = {path.resolve() for path in find_routes}
    page_ids = {} if page_ids is None else page_ids
    for file in site.rglob("*.html"):
        for match in ATTR.finditer(file.read_text()):
            parsed = urlsplit(html.unescape(match[3]))
            if parsed.scheme or parsed.netloc:
                continue
            path = (file.parent / unquote(parsed.path)).resolve() if parsed.path else file.resolve()
            if not path.is_relative_to(boundary) or not path.exists():
                raise ValueError(f"Broken local link: {file.relative_to(site)}: {match[3]}")
            if path.is_dir():
                path = path / "index.html"
            if not path.is_file():
                raise ValueError(f"Broken local link: {file.relative_to(site)}: {match[3]}")
            # Only explicitly declared find routes may interpret #doc in JavaScript.
            if parsed.fragment and unquote(parsed.fragment).lower() != "top" and path.suffix == ".html" and path not in find_routes:
                if path not in page_ids:
                    page_ids[path] = {html.unescape(value) for value in re.findall(r'\bid="([^"]*)"', path.read_text())}
                if unquote(parsed.fragment) not in page_ids[path]:
                    raise ValueError(f"Broken local anchor: {file.relative_to(site)}: {match[3]}")


def decorate_homepage(site, include_blueprint):
    """Put project navigation inside the generator's main content region."""
    page = site / "index.html"
    text = page.read_text()
    if 'id="goldbach-introduction"' in text:
        return
    links = [f'<a href="{SOURCE_REPO}">Source repository</a>']
    if (site / "Goldbach/Statement.html").is_file():
        links.append('<a href="Goldbach/Statement.html#Goldbach.ChenTheorem">Theorem statement</a>')
    if (site / "Goldbach/Theorem.html").is_file():
        links.append('<a href="Goldbach/Theorem.html#Goldbach.chen_theorem">Verified proof</a>')
        links.append('<a href="Goldbach/Theorem.html#Goldbach.representation_lower_bound">Representation bound</a>')
    if (site / "Goldbach/OnePlusOneNine.html").is_file():
        links.append('<a href="Goldbach/OnePlusOneNine.html#Goldbach.one_plus_one_nine">Li–Liu 1+1.9 theorem</a>')
        links.append('<a href="Goldbach/OnePlusOneNine.html#Goldbach.one_plus_one_nine_count">Strict 0.0004 prime-count bound</a>')
    if include_blueprint:
        links.append('<a href="blueprint/index.html">Proof Blueprint</a>')
    introduction = (
        '<div id="goldbach-introduction"><h1>Goldbach Lean</h1>'
        '<p>Lean 4 API documentation for Chen\'s 1+2 theorem and the Li–Liu 1+1.9 theorem, with separate public interfaces.</p>'
        '<p>' + ' &middot; '.join(links) + '</p></div>'
    )
    heading = '<h1>Welcome to the documentation page </h1>'
    if text.count(heading) != 1:
        raise ValueError("Unexpected doc-gen4 homepage structure")
    text = text.replace(heading, introduction)
    text = text.replace('<title>Index</title>', '<title>Goldbach Lean — API documentation</title>')
    page.write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", action="append", help="Render only this module (repeatable; default: all four libraries)")
    parser.add_argument("--artifacts-from", type=Path, default=ROOT,
                        help="Read already compiled artifacts and packages from a matching checkout; never builds there")
    parser.add_argument("--output", type=Path, default=ROOT / "docbuild/.lake/build/api",
                        help="New output directory; must not already exist")
    parser.add_argument("--blueprint", type=Path, help="Copy an already generated Blueprint HTML directory to blueprint/")
    parser.add_argument("--mathlib-docs", default=MATHLIB_DOCS, help="Upstream dependency API base URL")
    parser.add_argument("--jobs", type=int, default=2, help="Concurrent module renderers (default: 2)")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    artifacts = args.artifacts_from.resolve()
    output = args.output.resolve()
    if output.exists():
        parser.error("Output already exists; choose a new --output directory (stale pages are never reused)")
    if args.blueprint and not (args.blueprint / "index.html").is_file():
        parser.error("--blueprint must contain index.html")
    all_modules = modules_in(ROOT)
    modules = sorted(set(args.module or all_modules))
    if not modules or not set(modules) <= set(all_modules):
        parser.error("Select existing modules from the four project libraries")
    preflight(ROOT, artifacts, modules)
    env = dict(os.environ)
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    docbuild = ROOT / "docbuild"
    # The committed documentation manifest pins all documentation dependencies.
    run(["lake", "--wfail", "build", "goldbach-docs"], cwd=docbuild, env=env)
    doc_path = run(["lake", "env", "printenv", "LEAN_PATH"], cwd=docbuild, env=env, capture=True).strip()
    doc_roots = [str((docbuild / p).resolve()) for p in doc_path.split(os.pathsep) if p]
    env["LEAN_PATH"] = os.pathsep.join([str(p) for p in dependency_roots(artifacts)] + doc_roots)
    env.setdefault("LEAN_NUM_THREADS", "2")
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    source_root = f"{SOURCE_REPO}/blob/{revision}"
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    work_parent = docbuild / ".lake/build"
    work_parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="api-run-", dir=work_parent))
    module_file = work / "modules.txt"
    module_file.write_text("\n".join(modules) + "\n")
    executable = docbuild / ".lake/build/bin/goldbach-docs"
    def render_one(module):
        analysis_log = run([executable, "module", work, module_file, module, source_root],
                           cwd=ROOT, env=env, capture=True)
        if analysis_log:
            print(analysis_log, end="", flush=True)
        if "WARNING: Failed to obtain information" in analysis_log:
            raise ValueError(f"doc-gen4 omitted declaration information in {module}")

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = {pool.submit(render_one, module): module for module in modules}
        try:
            for number, future in enumerate(as_completed(futures), 1):
                future.result()
                print(f"[{number}/{len(modules)}] {futures[future]}", flush=True)
        except BaseException:
            for future in futures:
                future.cancel()
            raise
    run([executable, "index", work, module_file], cwd=ROOT, env=env)
    site = work / "doc"
    external = rewrite_site(site, all_modules, manifest, source_root, args.mathlib_docs)
    if args.blueprint:
        shutil.copytree(args.blueprint, site / "blueprint")
    decorate_homepage(site, bool(args.blueprint))
    count = verify_site(site, modules)
    report = {
        "source_revision": revision, "docgen_revision": DOCGEN_REV,
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "mathlib_revision": next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib"),
        "dependency_documentation": args.mathlib_docs,
        "scope": "full" if modules == all_modules else "partial",
        "renderer_jobs": args.jobs,
        "modules": modules, "module_count": len(modules), "declaration_count": count,
        "external_url_count": len(external), "blueprint_included": bool(args.blueprint),
    }
    (site / "build-info.json").write_text(json.dumps(report, indent=2) + "\n")
    (site / ".nojekyll").touch()
    output.parent.mkdir(parents=True, exist_ok=True)
    shutil.move(str(site), output)
    print(json.dumps(report, indent=2))
    print(f"Verified API site: {output}")


if __name__ == "__main__":
    main()
