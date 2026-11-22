#!/usr/bin/env python3
"""Apply `scripts/rename-packages.tsv` (phase 3.3): rename reduction packages, keep the old names
as deprecated aliases, and move the use sites and the docs to the new names.

  scripts/rename_packages.py decls GROUP...   rename the declarations of these groups, add aliases
  scripts/rename_packages.py uses [FILE...]   rewrite every use the build reports as deprecated
                                              (the whole library, or the given `lake env lean` files)
  scripts/rename_packages.py docs GROUP...    rename backticked mentions in comments and Markdown

The steps are idempotent: a renamed declaration is not found again, and `uses` only acts on the
build's deprecation warnings. Run it from the repository root; it also works on a branch that
predates the renaming (an intern's branch, say): `uses` then moves that branch's own use sites.
"""

import re
import subprocess
import sys
from pathlib import Path

MAP = Path("scripts/rename-packages.tsv")
SINCE = "2026-11-23"


def load(groups=None):
    rows = []
    for line in MAP.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        g, old, new, kind = line.split("\t")
        if groups is None or g in groups:
            rows.append((g, old, new, kind))
    return rows


def lean_files():
    out = subprocess.run(["git", "ls-files", "DiagonaLean/*.lean", "DiagonaLean/**/*.lean"],
                         capture_output=True, text=True, check=True).stdout.split()
    return [Path(p) for p in out]


def find_decl(short):
    """The file and line index of `def short` (the short name, not followed by a name character)."""
    rx = re.compile(r"^(?:noncomputable |protected |private )*def " + re.escape(short) + r"(?![\w'])")
    hits = []
    for p in lean_files():
        for i, l in enumerate(p.read_text().split("\n")):
            if rx.match(l):
                hits.append((p, i))
    return hits


def block(lines, i):
    """The start (docstring and attributes) and the end (exclusive) of the declaration at line i."""
    a = i
    while a > 0:
        prev = lines[a - 1]
        if prev.startswith("@[") or re.match(r"^open .* in$", prev):
            a -= 1
        elif prev.rstrip().endswith("-/"):
            j = a - 1
            while not lines[j].lstrip().startswith("/--"):
                j -= 1
            a = j
            break
        else:
            break
    b = i + 1
    while b < len(lines) and lines[b].strip() and not lines[b].startswith("end "):
        b += 1
    return a, b


def ns_at(lines, i):
    """The namespace at line i, from the `namespace` and `end` lines before it."""
    stack = []
    for l in lines[:i]:
        m = re.match(r"^namespace (\S+)", l)
        if m:
            stack.append(m.group(1))
        m = re.match(r"^end (\S+)\s*$", l)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
    return ".".join(stack)


def alias_text(short, new):
    return [f"/-- The former name of `{new}`. -/",
            f"@[deprecated DiagonaLean.{new} (since := \"{SINCE}\")]",
            f"abbrev {short} := @DiagonaLean.{new}"]


def decls(groups):
    for g, old, new, kind in load(groups):
        short = old.split(".")[-1]
        hits = find_decl(short)
        # keep only the hit whose namespace matches: the old name's namespace, after `DiagonaLean.`
        ns = "DiagonaLean." + ".".join(old.split(".")[:-1])
        hits = [(p, i) for p, i in hits if ns_at(p.read_text().split("\n"), i) == ns]
        if len(hits) != 1:
            print(f"skip {old}: {len(hits)} candidate declarations")
            continue
        p, i = hits[0]
        lines = p.read_text().split("\n")
        a, b = block(lines, i)
        if kind == "def":
            lines[i] = re.sub(r"def " + re.escape(short) + r"(?![\w'])",
                              f"def _root_.DiagonaLean.{new}", lines[i], count=1)
            lines[b:b] = [""] + alias_text(short, new)
        else:
            lines[a:b] = alias_text(short, new)
        p.write_text("\n".join(lines))
        print(f"{kind:5} {old} -> {new}  ({p}:{i + 1})")


WARN = re.compile(r"^(?:warning: )?(?P<file>[^:\s]+):(?P<line>\d+):(?P<col>\d+):(?: warning:)? "
                  r"`(?P<old>[^`]+)` has been deprecated: [Uu]se `(?P<new>[^`]+)` instead")


def in_diagonalean_namespace(text):
    return re.search(r"^namespace DiagonaLean\b", text, re.M) is not None


def uses(files):
    cmd = [["lake", "env", "lean", f] for f in files] or [["lake", "build"]]
    out = "\n".join(subprocess.run(c, capture_output=True, text=True).stdout for c in cmd)
    mapping = {"DiagonaLean." + old: "DiagonaLean." + new for _, old, new, _ in load()}
    edits = {}
    for l in out.split("\n"):
        m = WARN.match(l)
        if not m or m["old"] not in mapping:
            continue
        edits.setdefault(m["file"], []).append((int(m["line"]), int(m["col"]), m["old"], m["new"]))
    n = 0
    for f, es in edits.items():
        p = Path(f)
        lines = p.read_text().split("\n")
        inside = in_diagonalean_namespace(p.read_text())
        for ln, col, old, new in sorted(set(es), reverse=True):
            s = lines[ln - 1]
            m = re.compile(r"@?[\w.']+").match(s, col)
            if not m:
                print(f"no identifier at {f}:{ln}:{col}")
                continue
            tok = m.group(0)
            parts = tok.lstrip("@").split(".")
            short = old.split(".")[-1]
            if short not in parts:
                # the warning points at a macro call, not at the name: fix by hand
                print(f"not the old name at {f}:{ln}:{col}: `{tok}`")
                continue
            rest = parts[parts.index(short) + 1:]  # a field after the name, as in `r.f`
            at = "@" if tok.startswith("@") else ""
            name = new[len("DiagonaLean."):] if inside else new
            lines[ln - 1] = s[:col] + at + ".".join([name] + rest) + s[m.end():]
            n += 1
        p.write_text("\n".join(lines))
    print(f"rewrote {n} uses in {len(edits)} files")
    return n


def docs(groups):
    rows = load(groups)
    files = [Path(p) for p in subprocess.run(["git", "ls-files", "*.md", "*.lean"], capture_output=True,
                                             text=True, check=True).stdout.split()]
    # longest old names first, so that `undecidableMPCP` does not rewrite `undecidableMPCPOf`
    rows.sort(key=lambda r: -len(r[1].split(".")[-1]))
    for p in files:
        s = p.read_text()
        t = s
        for _, old, new, _ in rows:
            short = old.split(".")[-1]
            # a backticked span that mentions the old name, qualified or not, outside an alias line
            rx = re.compile(r"(?<![\w'.])(?:[\w]+\.)*" + re.escape(short) + r"(?![\w'])")

            def span(m):
                return rx.sub(new, m.group(0))
            t = re.sub(r"`[^`\n]*`", span, t)
        if t != s:
            p.write_text(t)
            print(f"docs: {p}")


if __name__ == "__main__":
    cmd, args = sys.argv[1], sys.argv[2:]
    if cmd == "decls":
        decls(set(args))
    elif cmd == "uses":
        uses(args)
    elif cmd == "docs":
        docs(set(args))
    else:
        sys.exit(__doc__)
