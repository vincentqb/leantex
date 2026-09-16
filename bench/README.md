# Benchmarks

Run from the repository root after `lake build`:

```bash
./scripts/bench.sh
```

The harness regenerates `lorem.tex`, then reports median wall time over five
fresh process invocations. Set `N` to change the sample count. This is a
reference comparison, not semantic equivalence: lualatex loads a much larger
system and implements much more.

## Baseline — 2026-09-15

AMD EPYC 9R14 host; LuaHBTeX 1.24.0 (TeX Live 2026/Homebrew).

| Input | Size | leantex | lualatex | Ratio |
|---|---:|---:|---:|---:|
| `paragraphs.tex` | 1,043 B | 14 ms | 486 ms | 34.7× faster |
| generated `lorem.tex` | 129,507 B, 30 pages | 573 ms | 982 ms | 1.7× faster |

The large case is layout-bound; the `-v` phase trace attributes roughly 520 ms
to line breaking and page assembly. Keep this baseline when optimizing M6.
