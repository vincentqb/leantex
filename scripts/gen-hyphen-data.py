#!/usr/bin/env python3
"""Regenerate LeanTex/Core/HyphenData.lean from hyph-en-us.tex."""

import argparse
import pathlib
import shutil
import subprocess

NOTICE = """/-
Generated from hyph-en-us.tex (hyph-utf8); do not edit by hand.
Regenerate with: python3 scripts/gen-hyphen-data.py

title: Hyphenation patterns for American English
copyright: Copyright (C) 1990, 2004, 2005 Gerard D.C. Kuiken
licence: Copying and distribution of this file, with or without
modification, are permitted in any medium without royalty provided the
copyright notice and this notice are preserved.
hyphenmins: left 2, right 3
-/
"""


def default_source() -> pathlib.Path:
    if not shutil.which("kpsewhich"):
        raise SystemExit("kpsewhich not found; pass the path to hyph-en-us.tex")
    path = subprocess.run(
        ["kpsewhich", "hyph-en-us.tex"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    if not path:
        raise SystemExit("kpsewhich could not find hyph-en-us.tex")
    return pathlib.Path(path)


def block(text: str, command: str) -> str:
    marker = rf"\{command}{{"
    start = text.find(marker)
    if start < 0:
        raise SystemExit(f"source has no {marker}")
    lines = text[start + len(marker) :].splitlines()
    body = []
    for line in lines:
        line = line.split("%", 1)[0].strip()
        if line == "}":
            break
        if line:
            body.extend(line.split())
    return " ".join(body)


def lean_string(value: str) -> str:
    return value.replace("\\", "\\\\").replace('"', '\\"')


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", nargs="?", type=pathlib.Path)
    parser.add_argument(
        "--output",
        type=pathlib.Path,
        default=pathlib.Path("LeanTex/Core/HyphenData.lean"),
    )
    args = parser.parse_args()
    source = args.source or default_source()
    text = source.read_text(encoding="ascii")
    patterns = block(text, "patterns")
    exceptions = block(text, "hyphenation")
    output = (
        NOTICE
        + "namespace LeanTex.Core.HyphenData\n\n"
        + f'def patterns : String := "{lean_string(patterns)}"\n\n'
        + f'def exceptions : String := "{lean_string(exceptions)}"\n\n'
        + "end LeanTex.Core.HyphenData\n"
    )
    args.output.write_text(output, encoding="ascii")
    print(f"wrote {args.output}: {len(patterns.split())} patterns, "
          f"{len(exceptions.split())} exceptions")


if __name__ == "__main__":
    main()
