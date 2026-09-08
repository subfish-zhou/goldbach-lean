#!/usr/bin/env python3
"""Assemble a project homepage, verified Lean API docs and a rendered Blueprint.

No Lean compilation or API rendering is performed. Inputs remain untouched.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import posixpath
import re
import shutil
import tempfile

from build_docs import ROOT, SOURCE_REPO, verify_local_links, verify_site


def add_project_navigation(site):
    api = site / "docs"
    navbar = api / "navbar.html"
    text = navbar.read_text()
    marker = '<h3>General documentation</h3>'
    if 'id="goldbach-project-links"' not in text:
        if text.count(marker) != 1:
            raise ValueError("Unexpected API navbar structure")
        links = ('<div id="goldbach-project-links">'
                 '<div class="nav_link"><a href="../index.html">Project home</a></div>'
                 '<div class="nav_link"><a href="../blueprint/index.html">Lean Blueprint</a></div>'
                 '</div>')
        navbar.write_text(text.replace(marker, marker + links))
    index = api / "index.html"
    text = index.read_text().replace('href="blueprint/index.html"',
                                     'href="../blueprint/index.html"')
    index.write_text(text)
    for page in (site / "blueprint").rglob("*.html"):
        text = page.read_text()
        if 'id="goldbach-project-links"' in text:
            continue
        header = re.search(r'<body[^>]*>\s*<header(?:\s[^>]*)?>.*?</header>', text, re.S)
        if header is None:
            raise ValueError(f"Unexpected Blueprint page header: {page.name}")
        home = posixpath.relpath(site / "index.html", page.parent)
        docs = posixpath.relpath(api / "index.html", page.parent)
        links = ('<div id="goldbach-project-links" style="font:14px/1.8 system-ui,sans-serif; padding:8px 0">'
                 f'<a href="{home}">Project home</a> · <a href="{docs}">Lean Doc</a></div>')
        position = header.end() - len('</header>')
        page.write_text(text[:position] + links + text[position:])
    for page in site.rglob("*.html"):
        text = page.read_text()
        if re.search(r'rel=[\"\'](?:shortcut )?icon[\"\']', text):
            continue
        icon = posixpath.relpath(site / "favicon.svg", page.parent)
        page.write_text(text.replace('</head>', f'<link rel="icon" href="{icon}" type="image/svg+xml"></head>', 1))


def assemble(api, blueprint, output, *, templates=ROOT / "website", source_revision=None):
    api, blueprint, output = api.resolve(), blueprint.resolve(), output.resolve()
    if output.exists():
        raise ValueError("Output already exists; choose a new directory")
    report = json.loads((api / "build-info.json").read_text())
    if report.get("scope") != "full":
        raise ValueError("The project homepage requires a full API build")
    revision = report["source_revision"]
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("Expected a full source revision in API build-info.json")
    api_revision = revision
    revision = source_revision or api_revision
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("Expected a full source revision for the website")
    blueprint_info = blueprint / "build-info.json"
    blueprint_report = json.loads(blueprint_info.read_text()) if blueprint_info.exists() else {}
    if blueprint_report and blueprint_report.get("source_revision") != revision:
        raise ValueError("Blueprint source revision differs from the website source revision")
    modules = report["modules"]
    if report["module_count"] != len(modules) or len(set(modules)) != len(modules):
        raise ValueError("Inconsistent API module inventory")
    if not (blueprint / "index.html").is_file():
        raise ValueError("Blueprint index.html is missing")
    output.parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="site-run-", dir=output.parent))
    # Older API bundles contained Blueprint at their own root. It now has a
    # sibling route; never mutate or remove the original input bundle.
    def ignore(path, names):
        return {"blueprint"} if Path(path).resolve() == api else set()
    shutil.copytree(api, work / "docs", ignore=ignore)
    shutil.copytree(blueprint, work / "blueprint")
    for name in ("home.css", "favicon.svg"):
        shutil.copy2(templates / name, work / name)
    homepage = (templates / "index.html").read_text()
    replacements = {
        "@@SOURCE_ROOT@@": f"{SOURCE_REPO}/blob/{revision}",
        "@@TREE_ROOT@@": f"{SOURCE_REPO}/tree/{revision}",
        "@@SHORT_REVISION@@": revision[:7],
    }
    for old, new in replacements.items():
        homepage = homepage.replace(old, new)
    if "@@" in homepage:
        raise ValueError("Unexpanded homepage template marker")
    (work / "index.html").write_text(homepage)
    add_project_navigation(work)
    count = verify_site(work / "docs", modules, site_root=work)
    if count != report["declaration_count"]:
        raise ValueError("API declaration census changed during assembly")
    api_report = dict(report, blueprint_included=False, project_home="../index.html")
    (work / "docs/build-info.json").write_text(json.dumps(api_report, indent=2) + "\n")
    assembled = dict(report, website_source_revision=revision,
                     api_source_revision=api_revision,
                     blueprint_source_revision=blueprint_report.get("source_revision"),
                     layout="project-home", api_path="docs/",
                     blueprint_path="blueprint/", blueprint_included=True,
                     homepage_sha256=hashlib.sha256((work / "index.html").read_bytes()).hexdigest())
    (work / "build-info.json").write_text(json.dumps(assembled, indent=2) + "\n")
    (work / ".nojekyll").touch()
    verify_local_links(work, find_routes=[work / "docs/find/index.html"])
    shutil.move(str(work), output)
    return assembled


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--api", type=Path, required=True)
    parser.add_argument("--blueprint", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=ROOT / "docbuild/.lake/build/site")
    parser.add_argument("--source-revision", help="Website/Blueprint commit when reusing an older API artifact")
    args = parser.parse_args()
    report = assemble(args.api, args.blueprint, args.output, source_revision=args.source_revision)
    print(json.dumps({k: v for k, v in report.items() if k != "modules"}, indent=2))
    print(f"Verified project website: {args.output.resolve()}")


if __name__ == "__main__":
    main()
