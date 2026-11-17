#!/usr/bin/env python3
"""Check that `DiagonaLean/Foundations/` depends on no problem folder. Run by CI.

`Foundations/` holds general results that problem folders build on, so it may depend only on
itself and on the base the problem folders share: `Synthetic` (the notions of reduction and
undecidability) and `Halt` (the source problem). The check follows imports transitively, so
importing a `Synthetic` module that imports `PCP` also fails. Code that only one problem uses
belongs in that problem's folder, as `MPCP/Normalize/` and `KACommUndecidable/KleeneAlgebra/` do.

Usage: python3 scripts/check_layering.py [ROOT]   (ROOT defaults to the repository root)
"""

import re
import sys
from pathlib import Path

LAYER = "DiagonaLean.Foundations"
# Top-level folders `LAYER` may depend on, besides itself.
ALLOWED = {"DiagonaLean.Foundations", "DiagonaLean.Synthetic", "DiagonaLean.Halt"}

IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$", re.M)


def folder(module: str) -> str:
    return ".".join(module.split(".")[:2])


def imports(root: Path) -> dict[str, list[str]]:
    """Each module under `DiagonaLean/`, with the `DiagonaLean` modules it imports."""
    result = {}
    for path in sorted((root / "DiagonaLean").rglob("*.lean")):
        module = ".".join(path.relative_to(root).with_suffix("").parts)
        text = re.sub(r"/-.*?-/", "", path.read_text(encoding="utf-8"), flags=re.S)
        names = [n for line in IMPORT.findall(text) for n in line.split()]
        result[module] = [n for n in names if n.startswith("DiagonaLean.")]
    return result


def main() -> int:
    root = Path(sys.argv[1] if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent)
    graph = imports(root)
    errors = []
    for start in sorted(m for m in graph if folder(m) == LAYER):
        # Breadth-first search, remembering how each module was reached.
        parent = {start: None}
        queue = [start]
        while queue:
            module = queue.pop(0)
            for dep in graph.get(module, []):
                if dep in parent:
                    continue
                parent[dep] = module
                if folder(dep) in ALLOWED:
                    queue.append(dep)
                    continue
                chain = [dep]
                while parent[chain[-1]] is not None:
                    chain.append(parent[chain[-1]])
                errors.append(f"{start} depends on {folder(dep)}: " + " -> ".join(reversed(chain)))
    for error in errors:
        print(error)
    modules = sum(folder(m) == LAYER for m in graph)
    if errors:
        print(f"check_layering: {len(errors)} forbidden "
              f"{'dependency' if len(errors) == 1 else 'dependencies'}; "
              f"{LAYER} may depend only on {', '.join(sorted(ALLOWED))}")
        return 1
    print(f"check_layering: {modules} modules in {LAYER} checked, no forbidden dependencies")
    return 0


if __name__ == "__main__":
    sys.exit(main())
