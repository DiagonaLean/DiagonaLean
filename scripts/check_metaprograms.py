#!/usr/bin/env python3
"""Reject metaprograms that change the environment in the library's sources. Run by CI.

`#check_reductions` reads the environment, and a metaprogram can write it: add a declaration that
the kernel never checked (`debug.skipKernelTC`), or copy the compiled code of an honest stub onto a
classical definition (`run_cmd` with `addDecl` and `IR.declMapExt.addEntry`), which the kernel and
`lean4checker` accept. This script forbids, outside comments, the commands that run code at
elaboration time and the functions that change the environment, except where `ALLOWED` permits
them. It is a check against mistakes and casual tricks, not a sandbox: a tactic written with `elab`
runs arbitrary code, so the library's `elab` tactics are reviewed by hand.

Usage: python3 scripts/check_metaprograms.py [ROOT]   (ROOT defaults to the repository root)
"""

import re
import sys
from pathlib import Path

# Each pattern, with what it does. Matched against the source with comments removed.
FORBIDDEN = {
    r"\brun_cmd\b|\brun_elab\b|\brun_meta\b": "runs code at elaboration time",
    r"#eval\b": "runs code at elaboration time",
    r"\b(builtin_)?initialize\b": "runs code when the module is loaded",
    r":\s*command\b|\bCommandElabM?\b|\bcommand_elab\b": "defines a command, which can change the environment",
    r"\bdebug\.": "sets a debug option, such as `debug.skipKernelTC`",
    r"\bunsafe\b": "is `unsafe` code",
    r"\bimplemented_by\b|\bextern\b": "replaces compiled code",
    r"\baddDecl\b|\baddAndCompile\b|\bcompileDecls?\b": "adds a declaration from a metaprogram",
    r"\bmodifyEnv\b|\bsetEnv\b": "changes the environment from a metaprogram",
    r"\baddEntry\b|\bmodifyState\b|\bsetState\b|\bdeclMapExt\b": "changes an environment extension",
    r"\bevalConst\b|\bevalExpr\b": "runs code at elaboration time",
}

# Files, relative to the repository root, and the patterns they may use.
ALLOWED = {
    # defines `#check_reductions`, whose messages name the escape hatches it reports
    "DiagonaLean/Synthetic/ReductionCheck.lean": {
        r":\s*command\b|\bCommandElabM?\b|\bcommand_elab\b",
        r"\bunsafe\b",
        r"\bimplemented_by\b|\bextern\b",
    },
    # not imported by `DiagonaLean.lean`; evaluates a reduction to show that it runs
    "DiagonaLean/Synthetic/EvalExample.lean": {r"#eval\b"},
}


def strip_comments(src: str) -> str:
    """`src` with `--` comments and (nested) `/- -/` comments, docstrings included, blanked out.
    Line breaks are kept, so line numbers are unchanged. String literals are kept."""
    out = []
    i, depth, n = 0, 0, len(src)
    in_string = False
    while i < n:
        c, nxt = src[i], src[i + 1] if i + 1 < n else ""
        if depth == 0 and in_string:
            out.append(c)
            if c == "\\" and nxt:
                out.append(nxt)
                i += 2
                continue
            if c == '"':
                in_string = False
            i += 1
        elif depth == 0 and c == '"':
            in_string = True
            out.append(c)
            i += 1
        elif c == "/" and nxt == "-":
            depth += 1
            out.append("  ")
            i += 2
        elif depth > 0 and c == "-" and nxt == "/":
            depth -= 1
            out.append("  ")
            i += 2
        elif depth > 0:
            out.append("\n" if c == "\n" else " ")
            i += 1
        elif c == "-" and nxt == "-":
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def main() -> int:
    root = Path(sys.argv[1] if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent)
    files = sorted((root / "DiagonaLean").rglob("*.lean")) + [root / "DiagonaLean.lean"]
    failures = 0
    for path in files:
        rel = path.relative_to(root).as_posix()
        code = strip_comments(path.read_text(encoding="utf-8"))
        for pattern, why in FORBIDDEN.items():
            if pattern in ALLOWED.get(rel, set()):
                continue
            for m in re.finditer(pattern, code):
                line = code.count("\n", 0, m.start()) + 1
                print(f"{rel}:{line}: `{m.group(0).strip()}` {why}")
                failures += 1
    if failures:
        print(f"check_metaprograms: {failures} forbidden uses; see the docstring of "
              "scripts/check_metaprograms.py")
        return 1
    print(f"check_metaprograms: {len(files)} files checked, no forbidden uses")
    return 0


if __name__ == "__main__":
    sys.exit(main())
