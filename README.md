# leantex

leantex compiles a LaTeX-shaped `.tex` document straight to PDF 2.0 or HTML
in one fast run — no TeX installation, no preamble, no aux-file reruns.

## Quick start

Prerequisite on macOS: the Xcode Command Line Tools, for the linker
(`xcode-select --install`).

```
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh
lake build
./.lake/build/bin/leantex path/to/doc.tex
```

elan reads `lean-toolchain` and fetches the pinned Lean (v4.34.0) by itself;
`lake build` takes a few minutes cold. Two more invocations from
`leantex --help`:

```
leantex doc.tex -o out.html     the output name picks the backend
leantex doc.tex --watch         rebuild on every change
```

## Fonts

leantex finds fonts by scanning the system directories (on macOS
`/System/Library/Fonts`, its `Supplemental` folder, `/Library/Fonts`, and
`~/Library/Fonts`; on Linux `/usr/share/fonts` and `~/.fonts`), plus a TeX
Live tree when MacTeX/TeX Live is installed (asked of `kpsewhich`). Add
directories with `--font-dir` or the `LEANTEX_FONT_PATH` environment variable
(colon-separated). The first build with fonts scans once and caches under
`~/.cache/leantex` (or `$XDG_CACHE_HOME/leantex`). A document that declares
no `\fonts` gets a default sans face resolved from the same scan;
`LEANTEX_FONT=<path to a .ttf/.otf>` overrides it. macOS `.ttc` font
collections are not yet readable and are skipped.

## Try it

`tests/corpus/*.tex` are ready-made examples. `declared.tex`, `layout.tex`,
and `paragraphs.tex` need no particular font. The rest declare `\fonts`:
`fill.tex`, `links.tex`, `palette.tex`, and `tokens.tex` name DejaVu
Serif/Sans (`latex-idioms.tex` names the same two via `\babelfont`,
`fonts.tex` adds DejaVu Sans Mono), and `resume.tex` names Nimbus
Roman/Sans — a named family must be installed, and a missing one is error
E0403, which lists the families that are installed. `talk.tex` and
`theme-modern.tex` exercise slide features that are not implemented yet and
stop with E0307.

This engine has only ever been built on Linux; macOS support is by
construction, not yet by test. A Mac user is the first to verify the quick
start above — if it fails, please report the exact command and the full
error output (font problems come out as E040x with the paths searched).

Linux note: the `LEAN_CC`/`LIBRARY_PATH` exports in AGENTS.md work around
this Amazon Linux 2 host's old glibc and are needed nowhere else; macOS
needs nothing.
