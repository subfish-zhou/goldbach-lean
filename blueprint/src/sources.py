"""Link blueprint nodes to the source positions exported by LeanArchitect."""

from pathlib import Path
import re
import subprocess
from urllib.parse import quote


def ProcessOptions(options, document):
    root = Path(__file__).resolve().parents[2]
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True
    ).strip()

    def source_links():
        locations = {}
        artifacts = root / ".lake/build/blueprint/module/Goldbach/Blueprint.artifacts"
        for path in artifacts.glob("*.tex"):
            match = re.search(
                r"\\lean\{([^}]+)\}\s*% at (.+):(\d+)\.\d+-",
                path.read_text(),
            )
            if match:
                declaration, source, line = match.groups()
                relative = Path(source).resolve().relative_to(root)
                locations[declaration] = (
                    "https://github.com/subfish-zhou/goldbach-lean/blob/"
                    f"{revision}/{quote(relative.as_posix())}#L{int(line) + 1}"
                )
        for graph in document.userdata["dep_graph"]["graphs"].values():
            for node in graph.nodes:
                declarations = node.userdata.get("leandecls", [])
                node.userdata["lean_urls"] = [
                    (declaration, locations[declaration])
                    for declaration in declarations
                ]

    document.addPostParseCallbacks(160, source_links)