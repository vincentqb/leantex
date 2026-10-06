# Document regression corpus

These documents are entirely invented. They retain structural combinations
that have exposed rendering defects without copying private text, topics,
identities, paths, or assets.

Run `lake test`. The checks use bundled fonts and inspect emitted
PDF and typed HTML, including PDF validity and HTML resource closure.
Document-specific guards check visible content, geometry, styles, and page
structure. Unexpected warnings and all errors fail the suite.

Each entry point declares `\documentclass` and has one case in
`Tests.RegressionDecks` or `Tests.RegressionDiagrams`. The suite checks that
the registry and entry points agree. Included fragments, Markdown, and
local styles are exercised through those documents.
