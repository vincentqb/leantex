# leantex

A document engine written in Lean 4. Compile TeX, Markdown, or a Lean,
Python, shell, C, C++, Rust or Java source file to PDF 2.0 or self-contained
HTML on Linux and macOS.

## Install

Install [elan](https://github.com/leanprover/elan), then build from source,
with this repository's clone URL in place of `<repository-url>`.
On macOS, install the Xcode Command Line Tools first (`xcode-select --install`).

```sh
git clone <repository-url> leantex
cd leantex
lake build
export PATH="$PWD/.lake/build/bin:$PATH"
leantex testdata/corpus/resume.tex
```

elan downloads the Lean version pinned by the repository.

## Build documents

```sh
leantex document.tex                     # PDF beside the source
leantex document.tex -o document.html    # HTML with embedded assets
leantex document.md -o document.pdf      # Markdown input
leantex Module.lean -o Module.html       # A Lean, Python, shell, C, C++, Rust or Java file
leantex document.tex --watch             # Rebuild on changes
```

Declare `\output{formats=pdf,html}` in a document to build both formats. A Lean
file's statements come from the facts its project writes with
`lake exe leantex-export`, a small Lake package in `export/`; leantex never runs
Lean.
`leantex --help` shows all options, and the [guide](docs/guide.md) covers
output and diagnostics, TeX and Markdown, code files, fonts and themes, and
images and code.

## Cite

```bibtex
@software{leantex,
  author = {Quenneville-B{\'e}lair, Vincent},
  title  = {leantex},
  note   = {A document engine written in Lean 4},
  year   = {2026},
  url    = {https://github.com/vincentqb/leantex},
}
```

## Licence

[Apache-2.0](LICENSE); vendored parts, such as the Pygments port, the fonts,
the CommonMark spec and the external corpora, keep the licences stated beside
them.
