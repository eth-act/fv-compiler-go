#!/usr/bin/env python3
"""No-sorry scan (docs/GATE.md): every tracked .lean file, with comments (nested /- -/ and --)
and string literals removed, must not contain the tactics/terms `sorry` or `admit`.

usage: scripts/no-sorry.py      prints "<file>:<line>: <token>" per hit and a count line;
                                exit 1 on any hit
"""
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TOKEN = re.compile(r"(?<![\w.'!?])(sorry|admit)(?![\w'!?])")


def strip(src):
    """src with comments and string literals replaced by spaces (newlines kept)."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        c = src[i]
        if depth:
            if src.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif src.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
        elif src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            j = min(j + 1, n)
            out.append("".join("\n" if ch == "\n" else " " for ch in src[i:j]))
            i = j
        else:
            out.append(c)
            i += 1
    return "".join(out)


def main():
    files = subprocess.run(["git", "ls-files", "*.lean"], cwd=ROOT, check=True,
                           capture_output=True, text=True).stdout.split()
    hits = 0
    for f in files:
        with open(os.path.join(ROOT, f), encoding="utf-8") as h:
            text = strip(h.read())
        for ln, line in enumerate(text.split("\n"), 1):
            for m in TOKEN.finditer(line):
                print(f"{f}:{ln}: {m.group(1)}")
                hits += 1
    print(f"lean files scanned: {len(files)}, sorry/admit: {hits}")
    sys.exit(1 if hits else 0)


if __name__ == "__main__":
    main()
