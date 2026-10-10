import Tests.DiagAudit
import Tests.PremiseScan
import Tests.ToolMemo
import Tests.SvgImages
import Tests.SvgValidation
import Tests.SvgTerminal
import Tests.ProcessRuntime
import Tests.PictureAssets
import Tests.World
import Tests.MachineLoss
import scripts.LandCore

/-!
# The world premises: what leantex assumes of everything that is not Lean

Below the driver stand the Lean runtime, the host and the programs the
engine, the suite and the scripts spawn. A row here is one assumption about
that residue, as a value: what it is, how far it reaches (a build's ordinary
path, a fallback, an oracle, development), the one sentence it asserts, what
relies on it, and what tries to falsify it, the check it is owed, or why no
check can exist. A premise is a theorem's hypothesis or a row here, never an
axiom.

A check stands on a row only if it runs the residue the row is about: the
real runtime, the real filesystem, the real tool, and fails when the
premise does. A test of the code that relies on the premise, driven by a
stand-in (a simulated runner, an invented witness, a decoder fed invented
output), tries the consumer and is not a check of the premise; nor is a
check that reads the tool's committed output against itself.

`premiseChecks` holds the rows to the source (`Tests/PremiseScan.lean` reads
it). It reads every spawn site of the engine: the runtime's spawn
primitives, every function that forwards a tool it was handed to one of
them, and the host programs that ask `Host.answer` to run one, through the
one program a route declares may ask (proofs, which no build runs, are no
site). Each tool an engine site can run needs a render- or fallback-reach
row, and each such row a site that still runs its tool. It reads the suite
and the scripts the same way for the tools they name, outright or through a
binding it can read, each of which needs a row of any reach.
`toolchainSpawnChecks` holds the scan's own premise: the toolchain the
engine's imports reach starts a process only through those primitives.
-/

open LeanTex.Core LeanTex.Cli
open DiagAudit (Pin suiteText)
open Tests (listingProviderChecks svgDoctypeChecks htmlContainedSvgColorChecks publicationPathChecks)

namespace Premises

/-- What stands outside Lean. A tool is filed under one spelling; a spawn
spelling reaches the row whose spelling has the same last path component. -/
inductive Residue where
  | runtime
  | tool (name : String)
  | host (fact : String)
  | oracle (name : String)
  | dev (name : String)

/-- How far a premise reaches. `render`: a build that meets the input runs
it, because no native path reads that input. `fallback`: a build runs it only
where a native path declined. `oracle` and `dev`: only a report, an oracle or
a development script runs it. -/
inductive Reach where
  | render
  | fallback
  | oracle
  | dev
  deriving BEq, Repr

/-- A declaration a statement leans on, pinned by elaborating it where the
row is written, so a rename fails the build. -/
structure Decl where
  name : Lean.Name
  seen : Unit

/-- `decl% n`: a pin to the declaration `n`. -/
syntax "decl%" ident : term
macro_rules
  | `(decl% $n) => `(Premises.Decl.mk $(Lean.quote n.getId) (let _ := @$n; ()))

/-- What relies on a premise: a theorem that takes it as a hypothesis, or a
gate, by file and declaration, whose `-- premise:` marker names `pin`. -/
inductive Consumer where
  | thm (pin : Pin)
  | gate (file decl : String) (pin : Pin)

def Consumer.pin : Consumer → Pin
  | .thm p | .gate _ _ p => p

/-- A theorem consumer pins a theorem; a gate pins what its marker names, a
check or a theorem. -/
def Consumer.wellPinned : Consumer → Bool
  | .thm p => (p matches .thm ..)
  | .gate _ _ p => !(p matches .tier ..)

/-- One world assumption. `consumers` take it as a hypothesis or gate on
it; `transfers` are theorems proved of pure values that state a fact of the
shipped run only while it holds; `guards` the validators that check every
reply it covers, so a tool row premises what the tool draws and never what
enters the IR. `sites` are the declarations, by file, whose decision rests on
it, and `tools` the further spellings an oracle or development row covers.
`checks` (blocks the suite runs), `scriptChecks` (blocks a script runs) and
`scripts` try to falsify it; `owed` is the check that could and is not
written yet; `unchecked` says why no check can exist. `retiring` names the
units whose landing removes the premise, and so owes this row's edit in the
same commit. -/
structure Premise where
  name : String
  residue : Residue
  reach : Reach
  statement : String
  consumers : List Consumer := []
  transfers : List Pin := []
  guards : List Decl := []
  sites : List (String × String) := []
  checks : List Pin := []
  scriptChecks : List (String × Decl) := []
  scripts : List String := []
  tools : List String := []
  owed : Option String := none
  unchecked : Option String := none
  retiring : List String := []

def Premise.tool? (p : Premise) : Option String :=
  match p.residue with
  | .tool n => some n
  | _ => none

def Premise.watched (p : Premise) : Bool :=
  !(p.checks.isEmpty && p.scriptChecks.isEmpty && p.scripts.isEmpty)

/-- A spawn whose wait has no time limit, by file and declaration, with the
units retiring it: what `host-bounded` excepts by name. -/
def unbudgeted : List (String × String × List String) := []

/-- host-bounded's exception clause, read off the exceptions, so the
statement names each one while it stands and none once it is gone. -/
def exceptedClause (excepted : List (String × String × List String)) : String :=
  match excepted.map fun (f, d, _) => s!"{stemOf f}.{d}" with
  | [] => ""
  | names => s!", except the unbudgeted spawns in {" and ".intercalate names}"

/-- The rows: the runtime and the host, the engine's tools, then the oracles
and development. -/
def registry : List Premise := [
  { name := "lean-runtime", residue := .runtime, reach := .render
    statement := "The compiled runtime runs each definition as its kernel-checked meaning and each BaseIO primitive as one step of the opaque world token that Init/System/ST.lean threads, with out-of-memory, signals and runtime faults outside the model."
    transfers := [thm% Host.record_replay_exact, thm% Host.recordIO_fst_exact]
    sites := [("Main.lean", "main")]
    unchecked := some "It is the language's own semantics, which every proof in the tree shares, so no check written in Lean can falsify it." },
  { name := "toolchain-spawns", residue := .runtime, reach := .render
    statement := "The pinned toolchain's library starts a process only through IO.Process.spawn, which IO.Process.output and IO.Process.run call, in every module the engine's imports reach, and the library the build links is the one its shipped sources describe."
    sites := [("Tests/PremiseScan.lean", "primitives")]
    checks := [check% toolchainSpawnChecks] },
  { name := "host-bounded", residue := .host "process", reach := .render
    statement := s!"Every host call the driver makes returns, because RunBounded.runBounded holds each tool run to a wall-clock budget and then kills its process group{exceptedClause unbudgeted}, because each file the driver reads is a regular file, which Host.answer's read enforces and the reads outside it do not, and because each path it writes in place, an artifact or a cache file, is absent or a regular file, which no write checks."
    transfers := [thm% PicCache.overrun_retried_exact, thm% Boundary.withdrawStep_unfinished_exact]
    sites := [("LeanTex/Cli/RunBounded.lean", "runBounded"), ("LeanTex/Cli/Host.lean", "answer"),
      ("LeanTex/Cli/Publication.lean", "publish"), ("LeanTex/Cli/FontDiscovery.lean", "scanRootsIn")]
    checks := [check% Tests.processRuntimeChecks, check% Tests.World.checks]
    scripts := ["scripts/runboundprobe.lean"]
    owed := some "Put a FIFO where the driver reads a document, an image and a font and where it writes an artifact and a cache file, and require every call to refuse it and return, which checks the driver's guard rather than the host and retires the file clauses once it passes." },
  { name := "atomic-publication", residue := .host "filesystem", reach := .render
    statement := "Renaming a staged file onto its destination within one directory replaces the destination atomically for every reader, so a cache file AtomicFile publishes is read whole or not at all, and an answer whose envelope fails its content key reads as a miss."
    transfers := [thm% ConvCache.refusal_replays_exact]
    sites := [("LeanTex/Cli/AtomicFile.lean", "write"), ("LeanTex/Cli/ConvCache.lean", "decode")]
    checks := [check% Tests.toolMemoChecks] },
  { name := "content-keys", residue := .host "cache inputs", reach := .render
    statement := "No two inputs one cache meets share a content key, though Flate.contentKey is two FNV-1a passes from two seeds, a 128-bit key that resists no chosen collision."
    sites := [("LeanTex/Cli/ConvCache.lean", "slotName"), ("LeanTex/Cli/Compression.lean", "cachePath"),
      ("LeanTex/Cli/PictureAssets.lean", "key"), ("LeanTex/Cli/Driver.lean", "imageCachePath")]
    unchecked := some "No check can enumerate the inputs a cache will meet, and a cryptographic key would retire the premise instead." },
  { name := "cache-trust", residue := .host "cache directory", reach := .render
    statement := "Every file under the cache directory was written by a leantex build of the same user, since an answer whose envelope checks is served, and the envelope is a checksum anyone can compute."
    sites := [("LeanTex/Cli/FontDiscovery.lean", "cacheDir"), ("LeanTex/Cli/ConvCache.lean", "decode"),
      ("LeanTex/Cli/PictureAssets.lean", "previous")]
    unchecked := some "A checksum anyone can compute cannot tell a planted answer from a written one, and the driver reads no owner or mode of the directory that holds it." },
  { name := "exec-failure", residue := .host "process", reach := .render
    statement := "A command the runtime cannot execute exits 255 with the single stderr line `could not execute external process` and the quoted command, a working directory it cannot enter exits 255 with `could not change directory to` and the directory, a child a signal ended exits 128 plus the signal, and a program a shell cannot find, or whose dynamic loader cannot start it, exits 127."
    consumers := [.gate "LeanTex/Cli/Publication.lean" "svgVerdict" (check% Tests.machineLossChecks)]
    transfers := [thm% PicCache.probed_absent_exact, thm% PicCache.unlogged_retried_exact]
    sites := [("LeanTex/Cli/ImageAssets.lean", "runChecked"), ("LeanTex/Cli/World.lean", "execFailed")]
    checks := [check% Tests.processRuntimeChecks]
    owed := some "Start a program whose shared library is missing and require exit 127 with the loader's line on its stderr." },
  { name := "tool-identity", residue := .host "filesystem", reach := .render
    statement := "An executable whose resolved path, size and modification time are unchanged, and every regular file of its name earlier on PATH likewise, answers as it did, though an update to a TeX package, to a font luaotfload indexes from the TeX tree or from the directories fontconfig's configuration lists, or to a shared library such as cairo, Poppler, librsvg or libxml2 moves no such witness and can leave a cached answer stale, of which the converters' cache rules out only the fonts, storing an answer only for an SVG xmllint finds free of text and fonts or a PDF that embeds every font, and a change of mode moves no stamp either, so an earlier file of the name made executable starts in place of the one the memo answered for."
    transfers := [thm% PicCache.versionStep_remembered_exact, thm% PicCache.versionStep_changed_exact,
      thm% World.ToolPath.probe_located_mem]
    sites := [("LeanTex/Cli/ToolProbe.lean", "witness"), ("LeanTex/Cli/World.lean", "witness"),
      ("LeanTex/Cli/ConvCache.lean", "identify"),
      ("LeanTex/Cli/ImageAssets.lean", "convert")]
    owed := some "Change a file a cached tool reads beside itself, such as a TeX package, under an unchanged executable, and require the next build to ask the tool again." },
  { name := "tool-determinism", residue := .host "tools", reach := .render
    statement := "For one tool identity and one request, what the engine reads of the reply is the same on every run: a page's content and resources, an SVG's bytes, a token stream."
    transfers := [thm% PicCache.step_cold_exact, thm% PicCache.remembers_verdict_exact,
      thm% ConvCache.refusal_replays_exact]
    sites := [("LeanTex/Cli/ConvCache.lean", "cached"), ("LeanTex/Cli/PictureAssets.lean", "fulfil")]
    owed := some "Build every corpus document twice from cold caches and require identical artifacts." },
  { name := "env-independence", residue := .host "environment", reach := .render
    statement := "A tool's answer depends on the environment it inherits only through what its identity records, though RunBounded passes the whole inherited environment and no identity records any of it, so TEXINPUTS, TEXMFHOME, FONTCONFIG_FILE and LANG all reach the tools."
    sites := [("LeanTex/Cli/RunBounded.lean", "runBounded")]
    owed := some "Run each tool under two inherited environments that differ in TEXINPUTS, FONTCONFIG_FILE and LANG, and require the same answer."
    retiring := ["tool-env-closed"] },
  { name := "path-lookup", residue := .host "PATH", reach := .render
    statement := "World.ToolPath.probe starts the file execvp starts, the first regular file of the name on PATH the OS accepts, with relative and empty entries read from the driver's working directory, which PictureAssets.produce does not do, since it runs the bare name in its scratch directory, where a relative or empty entry names another file than the one the witness describes."
    transfers := [thm% World.ToolPath.probeGo_exact, thm% World.ToolPath.probe_unset_exact]
    sites := [("LeanTex/Cli/World.lean", "probe"), ("LeanTex/Cli/PictureAssets.lean", "produce")]
    checks := [check% Tests.World.checks, check% listingProviderChecks]
    owed := some "Run the picture fallback under a PATH whose relative entry names another lualatex, and require the run to execute the witnessed file." },
  { name := "version-spelling", residue := .host "tools", reach := .render
    statement := "A tool's version banner is the same whichever spelling of its path starts it, since ToolPath.probe starts a candidate by its PATH-joined path where earlier builds started the bare name, and one memo answers for both."
    sites := [("LeanTex/Cli/World.lean", "version"), ("LeanTex/Cli/ToolProbe.lean", "identify")]
    owed := some "Start each tool the engine asks a version of by its bare name and by its resolved path, and require the same first line." },
  { name := "tool-exits", residue := .host "tools", reach := .render
    statement := "No converter or validator the engine runs exits 126 or above for a verdict of its own, as xmllint, xsltproc, pdftocairo and rsvg-convert document, so ImageAssets.runChecked reads 126 and 127 as a run that never started and 128 and above as an attempt that reached no verdict, and remembers neither."
    sites := [("LeanTex/Cli/ImageAssets.lean", "runChecked")]
    owed := some "Run each converter and validator on malformed and missing input, and require every exit below 126." },
  { name := "process-group", residue := .host "process", reach := .render
    statement := "A tool's descendants stay in the process group its setsid spawn starts, so the runtime's Child.kill, which sends SIGKILL to that whole group, ends them, and a tool finishes its writers before it exits."
    transfers := [thm% ConvCache.inconclusive_retried_exact, thm% PicCache.overrun_retried_exact]
    sites := [("LeanTex/Cli/RunBounded.lean", "runBounded")]
    checks := [check% Tests.processRuntimeChecks]
    scripts := ["scripts/runboundprobe.lean"] },
  { name := "font-files", residue := .host "filesystem", reach := .render
    statement := "A font file is what its path, size and modification time say, and a font directory lists what its modification time says, so the font scan's two caches answer as a fresh scan would."
    sites := [("LeanTex/Cli/FontDiscovery.lean", "scanRootsIn")]
    scripts := ["scripts/fontcache-check.lean"] },
  { name := "font-cache-writes", residue := .host "filesystem", reach := .render
    statement := "No build reads the font scan's metadata or listing cache while another build rewrites it, since both are written in place, where a line cut short can read as a rejected font or a directory with fewer entries."
    sites := [("LeanTex/Cli/FontDiscovery.lean", "scanRootsIn")]
    owed := some "Race two builds over one cache directory and require each to read the font set a fresh scan finds." },
  { name := "artifact-readers", residue := .host "filesystem", reach := .render
    statement := "No reader opens an artifact while a build rewrites it, since Publication.publish writes the PDF, the HTML and the markdown twin in place."
    sites := [("LeanTex/Cli/Publication.lean", "publish")]
    unchecked := some "Whether a reader opens an artifact mid-write is the reader's schedule, which no build observes, and publishing by rename would retire the premise." },
  { name := "path-identity", residue := .host "filesystem", reach := .render
    statement := "Two destinations whose existing prefixes IO.FS.realPath resolves to different paths name different files unless one has several hard links, which the publication preflight refuses, though on a filesystem that folds case or normalizes names two such paths can name one file."
    consumers := [.gate "LeanTex/Cli/Driver.lean" "build" (check% publicationPathChecks)]
    sites := [("LeanTex/Cli/PublicationPaths.lean", "conflict")]
    checks := [check% publicationPathChecks]
    owed := some "Publish two formats whose names differ only in case on a case-folding filesystem and require the preflight to refuse them." },
  { name := "tex-font-roots", residue := .host "TeX tree", reach := .render
    statement := "The TeX distribution whose lualatex, luatex or tex comes first on PATH keeps its OpenType and TrueType fonts in the trees TexFontTrees.trees lists beside that program's real path, so the directories TexFontTrees.roots finds hold the faces that distribution's own font search finds."
    sites := [("LeanTex/Cli/TexFontTrees.lean", "roots"), ("LeanTex/Cli/Driver.lean", "texFontDirs")]
    scripts := ["scripts/texfonts-report.lean"] },
  { name := "engine-environment", residue := .host "environment", reach := .render
    statement := "The driver reads PATH to choose tools, XDG_CACHE_HOME and HOME to place its cache, HOME, LEANTEX_FONT and LEANTEX_FONT_PATH to extend the font environment, TMPDIR, TMP, TEMP and TEMPDIR to place a run's scratch directory, and NO_COLOR for terminal colour, and the artifact depends on none of them except through the tools and faces they select."
    sites := [("LeanTex/Cli/FontDiscovery.lean", "cacheDir"), ("LeanTex/Cli/FontDiscovery.lean", "extraDirs"),
      ("LeanTex/Cli/FontAssembly.lean", "buildFontSet"), ("LeanTex/Cli/Driver.lean", "Ui.mk'"),
      ("LeanTex/Cli/Host.lean", "scratchRoot")]
    owed := some "Build one document under two environments that select the same tools and faces, and require identical artifacts." },
  { name := "clock-free", residue := .host "clock", reach := .render
    statement := "The monotonic clock reaches an artifact only where a tool run overruns its budget, which ships the loss the unfinished attempt is named by, such as a failed run under E0382 for a boundary picture, an uncoloured listing under W0393 or a placeholder image under W0602."
    sites := [("LeanTex/Cli/RunBounded.lean", "runBounded"), ("LeanTex/Cli/AtomicFile.lean", "write")]
    owed := some "Build one document whose tool runs overrun and one whose runs finish, and require the artifacts to differ only by the losses the overruns name." },
  { name := "lualatex", residue := .tool "lualatex", reach := .fallback
    statement := "lualatex draws a picture outside the native subset as the document's own lualatex build would, given the standalone wrapper the engine writes, and Image.probe and Image.plan read every page it returns before the IR holds it."
    guards := [decl% Image.probe, decl% Image.plan]
    sites := [("LeanTex/Cli/PictureAssets.lean", "produce"), ("LeanTex/Cli/Driver.lean", "resolvePictures")]
    owed := some "Compare each fallback picture with the same picture in the document's own lualatex build." },
  { name := "kpsewhich", residue := .oracle "kpsewhich", reach := .oracle
    statement := "kpsewhich prints, for --show-path=.otf and --show-path=.ttf, the directories where lualatex finds fonts, which the TeX font report holds the engine's own directories to, and names the files of the TeX tree the generators read."
    sites := [("scripts/texfonts-report.lean", "kpsewhichRoots"), ("scripts/gen-hyphen-data.lean", "main")]
    tools := ["kpsewhich"]
    owed := some "Compare kpsewhich's font directories with the directories lualatex opens a font from." },
  { name := "python3", residue := .tool "python3", reach := .render
    statement := "The Pygments python3 imports, a normal installation before the wheel TeX Live keeps beside latexminted, classifies a listing as a lualatex build's minted does, and ListingReply.decode and ListingReply.lookup_contract check every reply before the IR holds it."
    guards := [decl% ListingReply.decode, decl% ListingReply.lookup_contract]
    sites := [("LeanTex/Cli/ListingHighlight.lean", "fulfil")]
    owed := some "Compare the installed Pygments' classification of each corpus listing with the reference build's, token by token." },
  { name := "xmllint", residue := .tool "xmllint", reach := .render
    statement := "xmllint parses an SVG input as libxml2 does, loading no network resource or catalog, so the SAX, XPath and doctype passes judge the very bytes the converter then reads."
    consumers := [.gate "LeanTex/Cli/ImageAssets.lean" "checkSvgFile" (check% svgDoctypeChecks)]
    sites := [("LeanTex/Cli/ImageAssets.lean", "checkSvgFile")]
    scriptChecks := [("scripts/svg-check.lean", decl% Tests.svgValidationChecks),
      ("scripts/svg-check.lean", decl% Tests.svgTerminalDriverChecks)] },
  { name := "xsltproc", residue := .tool "xsltproc", reach := .render
    statement := "xsltproc applies the terminal-frame stylesheet to an animated SVG as XSLT 1.0 says, with no network, DTD attributes or writes."
    sites := [("LeanTex/Cli/ImageAssets.lean", "convert")]
    scriptChecks := [("scripts/svg-check.lean", decl% Tests.svgTerminalBoundaryChecks),
      ("scripts/svg-check.lean", decl% Tests.svgTerminalDriverChecks)] },
  { name := "rsvg-convert", residue := .tool "rsvg-convert", reach := .render
    statement := "rsvg-convert renders a validated SVG to PDF or SVG as librsvg draws it, and Image.probePdf, ImageAssets' private finishSvg and HtmlDoc.emitClosed check every file it writes before an artifact holds it."
    guards := [decl% Image.probePdf, decl% HtmlDoc.emitClosed]
    sites := [("LeanTex/Cli/ImageAssets.lean", "convert")]
    checks := [check% htmlContainedSvgColorChecks]
    scriptChecks := [("scripts/svg-check.lean", decl% Tests.svgValidationChecks),
      ("scripts/svg-check.lean", decl% Tests.svgTerminalBoundaryChecks)]
    scripts := ["scripts/html-oracle.lean"] },
  { name := "pdftocairo", residue := .tool "pdftocairo", reach := .render
    statement := "pdftocairo renders the selected page of a PDF to SVG as Poppler draws it, and ImageAssets' private finishSvg and HtmlDoc.emitClosed check every file it writes before the HTML holds it."
    guards := [decl% HtmlDoc.emitClosed]
    sites := [("LeanTex/Cli/ImageAssets.lean", "pdfSvg"), ("LeanTex/Cli/ImageAssets.lean", "picFace")]
    checks := [check% htmlContainedSvgColorChecks]
    scriptChecks := [("scripts/svg-check.lean", decl% Tests.svgValidationChecks)]
    scripts := ["scripts/html-oracle.lean"] },
  { name := "browsers", residue := .oracle "browsers", reach := .oracle
    statement := "The target browsers render the emitted HTML, CSS, SVG and MathML as their specifications say and run the slides class's constant keyboard script as ECMAScript says, a premise about the artifact that lies outside the build."
    transfers := [thm% HtmlDoc.backend_gaps_agree, thm% HtmlDoc.deck_script_constant,
      thm% HtmlDoc.deck_script_gated, thm% HtmlDoc.floor_covered_script_gated]
    sites := [("scripts/html-oracle.lean", "main")]
    scripts := ["scripts/html-oracle.lean"] },
  { name := "pandoc-reader", residue := .oracle "pandoc", reach := .oracle
    statement := "pandoc's CommonMark reader reads a markdown twin as CommonMark 0.31.2 says, with no extension but the pipe tables a table twin names, and its HTML writer writes what it read, so a twin the reader hop reads back to its page's text is one a CommonMark reader reads."
    sites := [("scripts/commonmark.lean", "hopTool")]
    tools := ["pandoc"]
    owed := some "Read the vendored CommonMark spec's examples through pandoc's reader and HTML writer, and require each to match its expected HTML under the hop's declared normalizations." },
  { name := "playwright", residue := .oracle "node", reach := .oracle
    statement := "node and the cached Playwright module drive the browsers and report what they computed unaltered, for the HTML, PDF and rhythm oracles."
    sites := [("scripts/html-oracle.lean", "playwrightCandidates"), ("scripts/rhythm.lean", "main")]
    tools := ["node"]
    unchecked := some "The oracles read each browser only through them, so no check stands outside the harness." },
  { name := "lualatex-reference", residue := .oracle "lualatex", reach := .oracle
    statement := "The committed parity references, the probes' measurements and the differentials' readings are what an unmodified TeX Live's lualatex, and luatex for hyphenation, produce from the synthetic sources, so they stand for LaTeX's own behaviour."
    sites := [("scripts/parity-regen.lean", "main"), ("scripts/cancel-diff.lean", "main"),
      ("scripts/hyphen-diff.lean", "main")]
    tools := ["lualatex", "luatex"]
    owed := some "Regenerate every parity reference on a second TeX Live installation and require none to move." },
  { name := "pdf-readers", residue := .oracle "PDF readers", reach := .oracle
    statement := "Poppler, Ghostscript, pypdf, PDFium as the host's Chrome runs it and pdf.js as the host Firefox's omni.ja ships it read a written PDF as ISO 32000-2 says, veraPDF judges PDF/A-4 and PDF/UA-2 as those standards say, and ImageMagick measures the distance between rasters as it documents, so where the readers agree with the engine's own reader the page is what the file states."
    sites := [("scripts/pdf-oracles.lean", "main"), ("scripts/ink-oracle.lean", "main")]
    tools := ["pdftotext", "pdfinfo", "pdffonts", "pdftoppm", "gs", "magick", "verapdf", "chrome"]
    scripts := ["scripts/pdf-oracles.lean"] },
  { name := "zlib", residue := .oracle "zlib", reach := .oracle
    statement := "The zlib python3 links inflates a stream as RFC 1950 and RFC 1951 say, so a stream it reads back as the input is a conforming one."
    sites := [("scripts/flate-fuzz.lean", "main")]
    unchecked := some "It is the reference implementation the compressor is held to, so nothing in the tree stands above it." },
  { name := "tex-tree", residue := .dev "TeX tree", reach := .dev
    statement := "The host's TeX tree holds the declaring files the generators read, unicode-math's table, tuenc.def, latex.ltx and the hyphenation patterns, so a regenerated data module is what that TeX distribution ships."
    sites := [("scripts/gen-mathsym-data.lean", "main"), ("scripts/gen-textsym-data.lean", "main"),
      ("scripts/gen-hyphen-data.lean", "main")]
    owed := some "Regenerate every data module from the host's TeX tree and require each committed module unchanged." },
  { name := "iconv-tables", residue := .dev "iconv", reach := .dev
    statement := "The host's iconv decodes one byte of WINDOWS-1252, ISO-8859-15 and MACINTOSH as the mapping tables it carries do, so the generated encoding tables are those tables, apart from the two Mac OS Roman rows the generator takes from Apple's own table."
    sites := [("scripts/gen-encoding-data.lean", "iconvByte")]
    tools := ["iconv"]
    owed := some "Regenerate the encoding tables from the host's iconv and require the committed module unchanged." },
  { name := "pygments-tables", residue := .dev "Pygments", reach := .dev
    statement := "The installed Pygments answers style queries as a lualatex build's minted reads them, so the generated style table and its oracle file are the reference's own."
    sites := [("scripts/gen-pygments-style-data.lean", "main")]
    owed := some "Build a minted listing of every token type in every shipped style under lualatex and require each token's colour and weights in its PDF to equal the oracle file's." },
  { name := "git", residue := .dev "git", reach := .dev
    statement := "git reads and updates repository state as its documentation says, so the sha the landing gates, pushes and reads back is the sha main holds."
    transfers := [thm% Land.step_pinned, thm% Land.trace_writes_owned]
    sites := [("scripts/land.lean", "main")]
    tools := ["git"]
    scripts := ["scripts/land.lean"] },
  { name := "fonttools", residue := .dev "fontTools", reach := .dev
    statement := "fontTools builds the invented icon face from the shapes the generator draws, so the committed face carries those glyphs at the codepoints the fixtures name."
    sites := [("scripts/gen-test-icons.py", "main")]
    owed := some "Regenerate the icon face with fontTools and require each glyph the generator draws at the codepoint it names." },
  { name := "toolchain", residue := .dev "Lean toolchain", reach := .dev
    statement := "The pinned toolchain's lean and lake, which the suite, the scripts and the hook spawn to build and run Lean, elaborate and run a program as that toolchain documents."
    sites := [("scripts/precommit.lean", "main"), ("scripts/oklab-roundtrip.lean", "main")]
    tools := ["lean", "lake"]
    unchecked := some "They build and run every check in the tree, so none stands outside them." },
  { name := "userland", residue := .dev "POSIX utilities", reach := .dev
    statement := "The POSIX utilities the suite and the scripts call behave as POSIX specifies, and shasum hashes as sha256sum does where it is the checksum tool a platform ships, so a synthetic tool the suite writes from them, such as cache-identity-tool or the PATH fixtures' tool, answers as its script says, and a history row names the executable it measured."
    sites := [("Tests/PictureAssets.lean", "pictureAssetToolBody"), ("scripts/runboundprobe.lean", "main"),
      ("Tests/World.lean", "pathChecks")]
    tools := ["sh", "cat", "cmp", "sleep", "mkdir", "chmod", "ln", "base64", "ps", "kill", "date",
      "timeout", "rm", "mktemp", "mkfifo", "sha256sum", "shasum", "cp", "unzip", "cache-identity-tool",
      "renderer-format", "tool"]
    checks := [check% listingProviderChecks, check% Tests.pictureAssetsChecks, check% Tests.World.checks] },
  { name := "absent-tool", residue := .dev "an absent executable", reach := .dev
    statement := "No executable named leantex-premise-absent-tool or leantex-no-such-tool lies on PATH or the C library's default search path, so the suite's spawns of those names meet the runtime's exec failure, which the exec-failure and PATH checks read."
    sites := [("Tests/ProcessRuntime.lean", "processRuntimeChecks"), ("Tests/World.lean", "pathChecks")]
    tools := ["leantex-premise-absent-tool", "leantex-no-such-tool"]
    checks := [check% Tests.processRuntimeChecks, check% Tests.World.checks] },
  { name := "pre-commit-shell", residue := .dev "/bin/sh", reach := .dev
    statement := "git runs the pre-commit trampoline with a POSIX sh, which hands the staged commit to the compiled gate whenever a changed path is one the gate reads."
    sites := [("scripts/precommit.lean", "main")]
    unchecked := some "The trampoline is what starts the gate, so a trampoline that skips it shows only as a commit no gate saw." }]

/-- Tool rows of render reach, rows no check can falsify, and rows owed a
check: counts that fall and rise only when this file says so. -/
def renderToolBaseline : Nat := 5
def uncheckedBaseline : Nat := 8
def owedBaseline : Nat := 21

/-- The spawns that are the budget. -/
def budgetSites : List (String × String) := [("LeanTex/Cli/RunBounded.lean", "runBounded")]

/-- Every engine spawn expression that is no literal, by file, spawner and
expression as written. A site no route reads, and a route no site uses, are
both faults. -/
def routes : List Route := [
  ⟨"LeanTex/Cli/RunBounded.lean", "IO.Process.spawn", "tool", .forwards⟩,
  ⟨"LeanTex/Cli/RunBounded.lean", "LeanTex.Cli.RunBounded.runBounded", "args.cmd", .forwards⟩,
  ⟨"LeanTex/Cli/Host.lean", "LeanTex.Cli.RunBounded.runBounded", "call.tool",
    .asked "LeanTex.Cli.World.ToolPath.probe" "LeanTex/Cli/World.lean" ["probeGo", "bare"]⟩,
  ⟨"LeanTex/Cli/World.lean", "LeanTex.Cli.World.ToolPath.probe", "tool", .forwards⟩,
  ⟨"LeanTex/Cli/ToolProbe.lean", "LeanTex.Cli.World.ToolPath.version", "tool", .forwards⟩,
  ⟨"LeanTex/Cli/Driver.lean", "LeanTex.Cli.ToolProbe.probeVersion", "tool", .pictureTools⟩,
  ⟨"LeanTex/Cli/Driver.lean", "LeanTex.Cli.PictureAssets.fulfil", "tool", .pictureTools⟩,
  ⟨"LeanTex/Cli/ConvCache.lean", "LeanTex.Cli.RunBounded.runBounded", "tool", .forwards⟩,
  ⟨"LeanTex/Cli/ConvCache.lean", "LeanTex.Cli.ConvCache.probeVersion", "tool", .forwards⟩,
  ⟨"LeanTex/Cli/ConvCache.lean", "LeanTex.Cli.ConvCache.identify", "tool", .forwards⟩,
  ⟨"LeanTex/Cli/ConvCache.lean", "LeanTex.Cli.ConvCache.identity", "tools", .forwards⟩,
  ⟨"LeanTex/Cli/ConvCache.lean", "LeanTex.Cli.ConvCache.cachedResult", "tools", .forwards⟩,
  ⟨"LeanTex/Cli/ImageAssets.lean", "LeanTex.Cli.ConvCache.cachedResult", "spec.tools", .conversionTools⟩,
  ⟨"LeanTex/Cli/ImageAssets.lean", "LeanTex.Cli.RunBounded.output", "_", .alias "runTool"⟩,
  ⟨"LeanTex/Cli/ImageAssets.lean", "runTool", "tool", .forwards⟩,
  ⟨"LeanTex/Cli/ImageAssets.lean", "LeanTex.Cli.ImageAssets.runChecked", "spec.tool", .converters⟩,
  ⟨"LeanTex/Cli/PictureAssets.lean", "LeanTex.Cli.RunBounded.runBounded", "command", .derives "tool"⟩,
  ⟨"LeanTex/Cli/PictureAssets.lean", "LeanTex.Cli.PictureAssets.produce", "tool", .forwards⟩]

/-! ## The registry against the scan -/

def engineReach (r : Reach) : Bool := r == .render || r == .fallback

def Premise.names (p : Premise) (tool : String) : Bool :=
  (p.tool?.map (basename · == basename tool)).getD false

def Premise.covers (p : Premise) (tool : String) : Bool :=
  p.names tool || p.tools.any (basename · == basename tool)

/-- Who owes the edit when a premise's subject leaves the tree. -/
def owes (retiring : List String) : String :=
  if retiring.isEmpty then "the commit that removed it owes this edit"
  else s!"{", ".intercalate retiring}, which retires it, owes this edit in the same commit"

/-- What is wrong with the registry against a scan. -/
def judge (rows : List Premise) (excepted : List (String × String × List String))
    (budget : List (String × String)) (sc : Scan) (words : Std.HashSet String) : Array String := Id.run do
  let mut out := sc.faults
  let spawned := sc.tools
  for (tool, s) in spawned do
    unless rows.any (fun p => engineReach p.reach && p.names tool) do
      out := out.push
        s!"{s.file}:{s.line}: the engine spawns '{tool}', and no render- or fallback-reach row names it"
  for p in rows do
    if let some name := p.tool? then
      if engineReach p.reach && !(spawned.any fun (tool, _) => basename tool == basename name) then
        let who := owes p.retiring
        out := out.push s!"{p.name}: no engine spawn site runs '{name}'; delete or rewrite the row ({who})"
  for (tool, s) in sc.suiteTools do
    unless rows.any (·.covers tool) do
      out := out.push
        s!"{s.file}:{s.line}: '{tool}' is spawned there, and no row covers it; name it in the tools of the row whose premise covers it, or give it a row of its own"
  for p in rows do
    for tool in p.tools do
      unless words.contains (basename tool) do
        out := out.push s!"{p.name}: no scanned source spells '{tool}'; drop it from the row's tools"
  let waits := sc.unbudgeted budget
  for (file, decl) in waits do
    unless excepted.any (fun (f, d, _) => f == file && d == decl) do
      out := out.push s!"{file}: {decl} waits on a spawn with no time limit, which host-bounded does not name"
  for (file, decl, retiring) in excepted do
    unless waits.contains (file, decl) do
      let who := owes retiring
      out := out.push s!"{file}: {decl} is excepted from the budget and waits on no spawn; delete the exception ({who})"
  match rows.find? (·.name == "host-bounded") with
  | none => out := out.push "no host-bounded row states the budget"
  | some p =>
    for (file, decl, _) in excepted do
      unless hasStr p.statement s!"{stemOf file}.{decl}" do
        out := out.push s!"host-bounded does not name the excepted {stemOf file}.{decl}"
  return out

def isKebab (s : String) : Bool :=
  !s.isEmpty && s.all fun c => c.isLower || c.isDigit || c == '-'

/-- One self-contained sentence in the repository's public voice. -/
def sentenceFaults (what s : String) : List String :=
  let home := ["/ho" ++ "me/", "/Us" ++ "ers/", "/lo" ++ "cal/", "~/"]
  (if s.isEmpty || !s.endsWith "." then [s!"{what} is not one sentence ending in a period"] else []) ++
  (if hasStr s ". " || hasStr s "\n" then [s!"{what} holds more than one sentence"] else []) ++
  (if home.any (hasStr s ·) then [s!"{what} names a home directory"] else [])

/-- What is wrong with a row on its own: its identity, its words, and the
agreement of its fields. A row nothing tries names the check it is owed or
why none can exist, and a row no check can falsify owes none. -/
def Premise.faults (p : Premise) : List String :=
  (if isKebab p.name then [] else [s!"'{p.name}' is not a kebab-case name"]) ++
  sentenceFaults s!"{p.name}'s statement" p.statement ++
  (match p.unchecked with
    | some why => sentenceFaults s!"{p.name}'s unchecked reason" why
    | none => []) ++
  (match p.owed with
    | some c => sentenceFaults s!"{p.name}'s owed check" c
    | none => []) ++
  (if p.unchecked.isSome && (p.watched || p.owed.isSome) then
      [s!"{p.name}: a premise no check can falsify carries a check or an owed one"]
    else if !p.watched && p.unchecked.isNone && p.owed.isNone then
      [s!"{p.name}: nothing tries the premise, and the row names neither the check it is owed nor why none can exist"]
    else []) ++
  (if p.consumers.isEmpty && p.transfers.isEmpty && p.sites.isEmpty then
      [s!"{p.name} names nothing that relies on it"] else []) ++
  (if p.consumers.all (·.wellPinned) then []
    else [s!"{p.name}: a consumer is neither a theorem nor a gate pinned to a check or a theorem"]) ++
  (if p.transfers.all (· matches .thm ..) then [] else [s!"{p.name}: a transfer is not a theorem"]) ++
  (if p.checks.any (· matches .thm ..) then [s!"{p.name}: a theorem stands among its checks"] else []) ++
  (if p.retiring.all isKebab then [] else [s!"{p.name}: a retiring unit is not a kebab-case name"]) ++
  (if (p.scripts ++ p.scriptChecks.map (·.1)).all (·.startsWith "scripts/") then []
    else [s!"{p.name}: a script lies outside scripts/"]) ++
  (if p.tools.isEmpty || p.reach == .oracle || p.reach == .dev then []
    else [s!"{p.name}: only an oracle or development row lists further tools"]) ++
  (match p.residue, p.reach with
    | .tool _, .render | .tool _, .fallback | .runtime, .render | .host _, .render
    | .host _, .fallback | .oracle _, .oracle | .dev _, .dev => []
    | _, _ => [s!"{p.name}: its reach does not fit its residue"])

def rowFaults (rows : List Premise) : List String :=
  let names := rows.map (·.name)
  (if names.eraseDups.length == names.length then [] else ["two rows share a name"]) ++
    rows.flatMap (·.faults)

def renderTools (rows : List Premise) : Nat :=
  (rows.filter fun p => p.tool?.isSome && p.reach == .render).length

def uncheckedCount (rows : List Premise) : Nat := (rows.filter (·.unchecked.isSome)).length

def owedCount (rows : List Premise) : Nat := (rows.filter (·.owed.isSome)).length

/-- Rows owed a check, split by whether anything tries them yet. -/
def owedFirst (rows : List Premise) : Nat := (rows.filter fun p => p.owed.isSome && !p.watched).length

def owedFurther (rows : List Premise) : Nat := (rows.filter fun p => p.owed.isSome && p.watched).length

/-! ## Gates and script checks against the source -/

/-- Whether declaration `decl` of `file` carries a `-- premise:` marker whose
pin is `pin`, read as the hook reads one: the first word after the colon,
by its last component. -/
def gateMarked (inp : Inputs) (texts : List (String × String)) (file decl pin : String) : Bool := Id.run do
  let some src := inp.files.find? (·.path == file) | return false
  let some text := (texts.find? (·.1 == file)).map (·.2) | return false
  let lines := (src.toks.filter (·.decl == decl)).map (·.line)
  let some first := lines[0]? | return false
  let lo := lines.foldl min first
  let hi := lines.foldl max first
  let rows := (text.splitOn "\n").toArray
  for i in [lo - 1:hi] do
    match (rows[i]?.getD "").splitOn "-- premise:" with
    | _ :: after :: _ =>
      if lastName ((after.trimAscii.toString.splitOn " ").headD "") == lastName pin then return true
    | _ => pure ()
  return false

/-- The token that opens the command token `k` stands in: the nearest one
before it that is first on its line at column 0. -/
def commandHead (ts : Array Tok) (k : Nat) : Option Tok := Id.run do
  for m in [0:k + 1] do
    let t := ts[k - m]!
    if t.first && t.col == 0 then return some t
  return none

/-- Whether `script` runs the block `block`: an identifier the scan read in
it names the block, outside a declaration of it and outside an `open`,
`export` or `import`, which name a block without running it. -/
def scriptCalls (inp : Inputs) (script block : String) : Bool :=
  match inp.files.find? (·.path == script) with
  | none => false
  | some src => (src.named block).any fun k =>
      !src.toks[k]!.declares &&
        !((commandHead src.toks k).any fun h => ["open", "export", "import"].contains h.text)

/-! ## The scan broken once each way -/

def Inputs.edit (inp : Inputs) (path : String) (f : String → String) (raw : String) : Inputs :=
  { inp with files := inp.files.map fun src =>
      if src.path == path then Source.of path (f raw) src.strict else src }

def Inputs.add (inp : Inputs) (path text : String) (strict : Bool := true) : Inputs :=
  { inp with files := inp.files.push (Source.of path text strict) }

/-- A planted tool's row, of render reach, so a plant that spawns `tool`
needs no row of the real registry. -/
def plantedRow (tool : String) (retiring : List String := []) : Premise :=
  { name := "zz-" ++ basename tool, residue := .tool tool, reach := .render
    statement := "A planted tool answers as its plant says."
    sites := [("LeanTex/Cli/ZzPlanted.lean", "zz")]
    unchecked := some "The tool is planted.", retiring }

/-- A planted development row, covering `tool` among its further tools. -/
def plantedDevRow (tool : String) : Premise :=
  { name := "zz-dev", residue := .dev "zz", reach := .dev
    statement := "A planted development tool answers as its plant says."
    sites := [("scripts/zz.lean", "main")], tools := [tool]
    unchecked := some "The tool is planted." }

/-- The registry with host-bounded also naming `excepted`. -/
def namingExcepted (excepted : String) : List Premise :=
  registry.map fun p => if p.name == "host-bounded" then { p with statement := p.statement ++ " " ++ excepted } else p

/-- Whether a mutation broke what it names and nothing else: each fault it
added names one of `needles`, and each needle is named by a fault it added.
A mutation that must stay quiet names none, and so adds none. -/
def broke (added : Array String) (needles : List String) : Bool :=
  needles.all (fun n => added.any (hasStr · n)) && added.all fun f => needles.any (hasStr f ·)

/-- Each mutation, and whether it broke what it names and nothing else. A
mutation's faults are the ones it adds to the faults of the tree it mutates,
so a selftest fires on its own plant alone, whatever else that tree holds.
Every plant is synthetic: a planted source, row, route or budget exception,
a declaration appended to a file the scan must read, a scan of planted
sources alone, or the deletion of whichever engine tool row the registry
holds first. None names a site, a table or a row of the tree, which other
units rework, so a unit that rewrites them owes no edit here. `texts` are the
files the mutations append to, as read. -/
def mutations (inp : Inputs) (texts : List (String × String)) (words : Std.HashSet String) :
    List (String × Bool) :=
  let raw (path : String) := ((texts.find? (·.1 == path)).map (·.2)).getD ""
  let judged (rows : List Premise) (exc : List (String × String × List String)) (i : Inputs) (rs : List Route) :=
    judge rows exc budgetSites (scan i rs) words
  let base := judged registry unbudgeted inp routes
  let added (rows : List Premise) (exc : List (String × String × List String)) (i : Inputs) (rs : List Route) :=
    (judged rows exc i rs).filter (!base.contains ·)
  let breaks (i : Inputs) (rs : List Route) (needles : List String) :=
    broke (added registry unbudgeted i rs) needles
  let plant (path text : String) (needles : List String) := breaks (inp.add path text) routes needles
  let script (path text : String) (needles : List String) := breaks (inp.add path text false) routes needles
  let append (path text : String) := inp.edit path (· ++ text) (raw path)
  let budgetFile := (budgetSites.head?.map (·.1)).getD ""
  let rowed (tool : String) (i : Inputs) (exc : List (String × String × List String)) (needles : List String) :=
    broke (added (registry ++ [plantedRow tool]) exc i routes) needles
  -- Planted sources scanned alone, their own spawns the budget, with host-bounded the one
  -- row beside the planted ones.
  let bounded := (registry.find? (·.name == "host-bounded")).toList
  let alone (files : List (String × String)) (budget : List (String × String)) (window : String)
      (rs : List Route) (rows : List Premise) :=
    judge (bounded ++ rows) [] budget
      (scan { files := (files.map fun (p, s) => Source.of p s).toArray, picTools := window } rs) words
  let wrapped := "namespace LeanTex.Cli.Elsewhere\ndef zzRun (t : String) : IO Unit := discard <| RunBounded.runBounded t #[] \".\"\nend LeanTex.Cli.Elsewhere\n"
  let wrapRoute : Route := ⟨"LeanTex/Cli/ZzWrap.lean", "LeanTex.Cli.RunBounded.runBounded", "t", .forwards⟩
  let scriptRun := "def run (cmd : String) : IO Unit := discard <| IO.Process.output { cmd, args := #[] }\n"
  let spawnOf (e : String) := s!"  discard <| IO.Process.output \{ cmd := {e}, args := #[] }\n"
  let budgeted (tool : String) := s!"discard <| RunBounded.runBounded \"{tool}\" #[] \".\""
  let unread (text : String) :=
    let i := inp.add "scripts/zz-unread.lean" text false
    (scan i routes).blind.any (·.file == "scripts/zz-unread.lean") && breaks i routes []
  let picRoute : Route := ⟨"LeanTex/Cli/ZzPic.lean", "IO.Process.output", "pictureTool", .pictureTools⟩
  let picSite := ("LeanTex/Cli/ZzPic.lean",
    "def zzPic (pictureTool : String) : IO Unit := discard <| IO.Process.output { cmd := pictureTool, args := #[] }")
  let picBudget := [("LeanTex/Cli/ZzPic.lean", "zzPic")]
  -- A planted host vocabulary: `go` asks the run, `zzProbe` hands it the tool,
  -- and the planted interpreter's spawn reads the run's tool.
  let askedWorld := [("LeanTex/Cli/ZzWorld.lean",
      "namespace LeanTex.Cli.ZzWorld\n" ++
      "def go (call : String → ToolCall) (cs : List String) : Prog Unit := .ask (.run (call \"x\")) fun _ => .pure ()\n" ++
      "def zzProbe (tool : String) (call : String → ToolCall) : Prog Unit := go call [tool]\n" ++
      "end LeanTex.Cli.ZzWorld\n"),
    ("LeanTex/Cli/ZzHost.lean",
      "def zzAnswer (call : ToolCall) : IO Unit := discard <| IO.Process.output { cmd := call.tool, args := #[] }")]
  let askedUser := ("LeanTex/Cli/ZzUser.lean",
    "def zz : Prog Unit := ZzWorld.zzProbe \"zz-asked-tool\" fun c => { tool := c, args := #[] }")
  let askedRoute : Route := ⟨"LeanTex/Cli/ZzHost.lean", "IO.Process.output", "call.tool",
    .asked "LeanTex.Cli.ZzWorld.zzProbe" "LeanTex/Cli/ZzWorld.lean" ["go"]⟩
  let askedBudget := [("LeanTex/Cli/ZzHost.lean", "zzAnswer")]
  -- A declaration laid out so no command-position rule sees it, after a
  -- theorem, a budget exception and an asker, each of which would claim it.
  let layouts := [("a docstring before it on its line", "/-- zz -/ "), ("an indentation", "  "),
    ("a set_option ... in before it on its line", "set_option maxHeartbeats 400 in ")]
  let wait (tool : String) := s!"discard <| IO.Process.output \{ cmd := \"{tool}\", args := #[] }"
  let excepted := "LeanTex/Cli/ZzExcepted.lean"
  let laid (lead : String) : List Bool :=
    [plant "LeanTex/Cli/ZzLaid.lean"
       ("theorem zzT : True := trivial\n" ++ lead ++ s!"def zzLaid : IO Unit := {budgeted "zz-laid-tool"}\n")
       ["the engine spawns 'zz-laid-tool'"],
     broke (added (namingExcepted "ZzExcepted.zzExcepted" ++ [plantedRow "zz-laid-wait"])
         (unbudgeted ++ [(excepted, "zzExcepted", [])])
         (inp.add excepted (s!"def zzExcepted : IO Unit := {wait "zz-laid-wait"}\n" ++ lead ++
           s!"def zzLaid : IO Unit := {wait "zz-laid-wait"}\n")) routes)
       [excepted ++ ": zzLaid waits on a spawn with no time limit"],
     broke (alone (askedWorld.map (fun (p, t) => if p == "LeanTex/Cli/ZzWorld.lean" then
           (p, t.replace "def zzProbe" (lead ++ "def zzLaid (c : ToolCall) : Prog Unit := .ask (.run c) fun _ => .pure ()\ndef zzProbe"))
         else (p, t)) ++ [askedUser])
         askedBudget "" [askedRoute] [plantedRow "zz-asked-tool"])
       ["zzLaid asks the host to run a tool outside LeanTex.Cli.ZzWorld.zzProbe"]]
  [("a planted literal spawn of an unregistered tool fires",
     breaks (append "LeanTex/Cli/Driver.lean" s!"\ndef zzPlanted : IO Unit := {budgeted "zz-planted-tool"}\n") routes
       ["the engine spawns 'zz-planted-tool', and no render- or fallback-reach row names it"]),
   ("a planted spawn with no time limit fires",
     rowed "zz-planted-wait" (append "LeanTex/Cli/Driver.lean"
         "\ndef zzPlanted : IO Unit := discard <| IO.Process.output { cmd := \"zz-planted-wait\", args := #[] }\n")
       unbudgeted ["LeanTex/Cli/Driver.lean: zzPlanted waits on a spawn with no time limit"]),
   ("the library's root module is read",
     breaks (append "LeanTex.lean" s!"\ndef zzRoot : IO Unit := {budgeted "zz-root-tool"}\n") routes
       ["the engine spawns 'zz-root-tool'"]),
   ("a planted spawn of a variable no route reads fires",
     plant "LeanTex/Cli/ZzPlanted.lean" "def zzRun (t : String) : IO Unit := discard <| RunBounded.runBounded t #[] \".\""
       ["LeanTex.Cli.RunBounded.runBounded runs 't', which no route"]),
   ("a spawn spelled under another qualification is a site",
     rowed "zz-qualified" (inp.add "LeanTex/Cli/ZzQualified.lean"
         "def zzP := Process.output { cmd := \"zz-qualified\", args := #[] }")
       unbudgeted ["LeanTex/Cli/ZzQualified.lean: zzP waits"]),
   ("an exception from the budget whose spawn is gone fires",
     broke (added (namingExcepted "ZzGone.zzGone") (unbudgeted ++ [("LeanTex/Cli/ZzGone.lean", "zzGone", [])]) inp routes)
       ["zzGone is excepted from the budget and waits on no spawn; delete the exception (the commit that removed it owes this edit)"]),
   ("an exception whose spawn is gone fires though a unit retires it, naming the unit",
     broke (added (namingExcepted "ZzGone.zzGone") (unbudgeted ++ [("LeanTex/Cli/ZzGone.lean", "zzGone", ["zz-unit"])]) inp routes)
       ["zzGone is excepted from the budget and waits on no spawn; delete the exception (zz-unit, which retires it"]),
   ("a budget exception host-bounded does not name fires",
     rowed "zz-wait-tool" (inp.add "LeanTex/Cli/ZzWait.lean"
         "def zzWait : IO Unit := discard <| IO.Process.output { cmd := \"zz-wait-tool\", args := #[] }")
       (unbudgeted ++ [("LeanTex/Cli/ZzWait.lean", "zzWait", [])])
       ["host-bounded does not name the excepted ZzWait.zzWait"]),
   ("a second spawn in the budget's own module is unbudgeted",
     rowed "zz-second-tool" (append budgetFile
         "\ndef zzWait : IO Unit := do\n  let c ← IO.Process.spawn { cmd := \"zz-second-tool\", args := #[] }\n  discard <| c.wait\n")
       unbudgeted [budgetFile ++ ": zzWait waits"]),
   ("a row whose tool nothing spawns fires",
     broke (added (registry ++ [plantedRow "zz-unspawned-tool"]) unbudgeted inp routes)
       ["no engine spawn site runs 'zz-unspawned-tool'; delete or rewrite the row (the commit that removed it owes this edit)"]),
   ("a row whose tool its retiring unit removed fires, naming the unit",
     broke (added (registry ++ [plantedRow "zz-retired-tool" ["zz-unit"]]) unbudgeted inp routes)
       ["no engine spawn site runs 'zz-retired-tool'; delete or rewrite the row (zz-unit, which retires it"]),
   ("a route whose site is gone fires",
     breaks (inp.add "LeanTex/Cli/ZzRoute.lean" "def zzGone (tool : String) : IO Unit := pure ()")
       (⟨"LeanTex/Cli/ZzRoute.lean", "IO.Process.output", "tool", .forwards⟩ :: routes)
       ["route 'LeanTex/Cli/ZzRoute.lean IO.Process.output tool' reads no spawn site"]),
   ("every converter in an Op.spec table needs a row",
     broke (alone [("LeanTex/Cli/ZzTable.lean",
         "private def Op.spec : Op → Spec\n  | .a => ⟨\"zz-converter\", \"svg\"⟩\n  | .b => ⟨\"zz-second-converter\", \"pdf\"⟩\n\n" ++
         "def zzConvert (spec : Spec) : IO Unit := discard <| IO.Process.output { cmd := spec.tool, args := #[] }\n")]
         [("LeanTex/Cli/ZzTable.lean", "zzConvert")] ""
         [⟨"LeanTex/Cli/ZzTable.lean", "IO.Process.output", "spec.tool", .converters⟩] [])
       ["the engine spawns 'zz-converter'", "the engine spawns 'zz-second-converter'"]),
   ("a validator in a Spec.tools table needs a row",
     broke (alone [("LeanTex/Cli/ZzTools.lean",
         "private def Op.spec : Op → Spec\n  | .a => ⟨\"zz-conv-tool\", \"svg\"⟩\n\n" ++
         "private def Spec.tools (s : Spec) : Array String := #[\"zz-validator\"] ++ #[s.tool]\n\n" ++
         "def zzConvert (spec : Spec) : IO Unit := discard <| IO.Process.output { cmd := spec.tools, args := #[] }\n")]
         [("LeanTex/Cli/ZzTools.lean", "zzConvert")] ""
         [⟨"LeanTex/Cli/ZzTools.lean", "IO.Process.output", "spec.tools", .conversionTools⟩]
         [plantedRow "zz-conv-tool"])
       ["the engine spawns 'zz-validator'"]),
   ("a tool in the picture tools window needs a row",
     broke (alone [picSite] picBudget "def picTools : List String := [\"zz-pictool\"]\n" [picRoute] [])
       ["the engine spawns 'zz-pictool'"]),
   ("a picture tool default needs a row",
     broke (alone [picSite, ("LeanTex/Cli/ZzDefault.lean", "def zzTool (doc : Doc) := doc.pictureTool.getD \"zz-default\"")]
         picBudget "def picTools : List String := [\"zz-pictool\"]\n" [picRoute] [plantedRow "zz-pictool"])
       ["the engine spawns 'zz-default'"]),
   ("a spawn in a theorem is no site",
     plant "LeanTex/Cli/ZzProof.lean"
       "theorem zzT : (IO.Process.output { cmd := \"zz-proof-tool\", args := #[] }).isSome = true := rfl" []),
   ("a tool handed to the spawner a host program asks through is a site",
     broke (alone (askedWorld ++ [askedUser]) askedBudget "" [askedRoute] []) ["the engine spawns 'zz-asked-tool'"]),
   ("a run asked outside the asked spawner's askers fires",
     broke (alone (askedWorld ++ [askedUser, ("LeanTex/Cli/ZzStray.lean",
         "import LeanTex.Cli.ZzWorld\ndef zzStray (c : ToolCall) : Prog Unit := .ask (.run c) fun _ => .pure ()")])
         askedBudget "" [askedRoute] [plantedRow "zz-asked-tool"])
       ["zzStray asks the host to run a tool outside LeanTex.Cli.ZzWorld.zzProbe"]),
   ("a run asked in the asked spawner's own file outside its askers fires",
     broke (alone (askedWorld.map (fun (p, t) => if p == "LeanTex/Cli/ZzWorld.lean" then
           (p, t.replace "end LeanTex.Cli.ZzWorld" "def zzHomeStray (c : ToolCall) : Prog Unit := .ask (.run c) fun _ => .pure ()\nend LeanTex.Cli.ZzWorld")
         else (p, t)) ++ [askedUser])
         askedBudget "" [askedRoute] [plantedRow "zz-asked-tool"])
       ["zzHomeStray asks the host to run a tool outside LeanTex.Cli.ZzWorld.zzProbe"]),
   ("a core module that asks the host for a run fires",
     plant "LeanTex/Core/ZzCore.lean"
       ("module\npublic import LeanTex.Cli.World\n" ++
        "def zzCore : LeanTex.Cli.World.Prog Unit := .ask (.run zzCoreCall) fun _ => .pure ()\n")
       ["zzCore asks the host to run a tool outside LeanTex.Cli.World.ToolPath.probe"]),
   ("a module that reaches the host through a re-export and asks a run fires",
     breaks ((inp.add "LeanTex/Cli/ZzRe.lean" "module\npublic import LeanTex.Cli.Host\n").add
         "LeanTex/Cli/ZzReUse.lean"
         "module\nimport LeanTex.Cli.ZzRe\ndef zzReUse : IO Unit := discard <| LeanTex.Cli.Host.runIO (.ask (.run zzReCall) fun _ => .pure ())\n")
       routes ["zzReUse asks the host to run a tool outside LeanTex.Cli.World.ToolPath.probe"]),
   ("an identifier named lemma before a spawn is no proof",
     plant "LeanTex/Cli/ZzLemma.lean"
       ("def zzLemma : IO Unit := do\n  let lemma := 1\n  discard <| RunBounded.runBounded \"zz-lemma-tool\" #[] \".\"\n")
       ["the engine spawns 'zz-lemma-tool'"]),
   ("a theorem's where helper is code",
     plant "LeanTex/Cli/ZzWhereProof.lean"
       ("theorem zzTrue : True := trivial\n  where\n    zzHelper : IO Unit := discard <| RunBounded.runBounded \"zz-where-proof-tool\" #[] \".\"\n")
       ["the engine spawns 'zz-where-proof-tool'"]),
   ("an initializer after a theorem is code",
     plant "LeanTex/Cli/ZzInit.lean"
       ("theorem zzTrue : True := trivial\n\ninitialize do\n  discard <| RunBounded.runBounded \"zz-init-tool\" #[] \".\"\n")
       ["the engine spawns 'zz-init-tool'"]),
   ("a keyword Lean reads as a name opens nothing",
     let ts := lex ("inductive ZzKind where\n  | example\n  | opaque\n  deriving BEq\n\nderiving instance Repr for ZzKind\n\n" ++
       "@[macro zzMacro] def zzNames : Nat := (ZzKind.example, .example, `example, «theorem»).1\n\n" ++
       "def zzQuoted := `(theorem zzQ : True := trivial)\n")
     ts.all (!·.proof) && (ts.filter (·.declares)).map (·.text) == #["ZzKind", "zzNames", "zzQuoted"]),
   ("an indented namespace scopes what it holds",
     plant "LeanTex/Cli/ZzIndented.lean"
       ("module\nimport LeanTex.Cli.World\n  namespace LeanTex.Cli.World.ToolPath\n" ++
        "  def zzIndented (call : String → ToolCall) := probeGo call [\"/usr/bin/zz-indented\"]\n  end LeanTex.Cli.World.ToolPath\n")
       ["zzIndented calls probeGo, which only LeanTex.Cli.World.ToolPath.probe may call"]),
   ("an asker called from outside the asked spawner fires",
     broke (alone (askedWorld ++ [askedUser, ("LeanTex/Cli/ZzBypass.lean",
         "def zzBypass (call : String → ToolCall) : Prog Unit := ZzWorld.go call [\"zz-bypassed\"]")])
         askedBudget "" [askedRoute] [plantedRow "zz-asked-tool"])
       ["zzBypass calls go, which only LeanTex.Cli.ZzWorld.zzProbe may call"]),
   ("a run asked through a pipe fires",
     plant "LeanTex/Cli/ZzPipeAsk.lean"
       "module\nimport LeanTex.Cli.Host\ndef zzPipeAsk (c : LeanTex.Cli.World.ToolCall) : IO Unit := discard <| LeanTex.Cli.Host.answer <| .run c\n"
       ["zzPipeAsk asks the host to run a tool outside LeanTex.Cli.World.ToolPath.probe"]),
   ("a run asked by its bare name inside the run question's namespace fires",
     plant "LeanTex/Cli/ZzInAsk.lean"
       "module\nimport LeanTex.Cli.World\nnamespace LeanTex.Cli.World.Ask\ndef zzInAsk (c : ToolCall) : Ask := run c\nend LeanTex.Cli.World.Ask\n"
       ["zzInAsk asks the host to run a tool outside LeanTex.Cli.World.ToolPath.probe"]),
   ("opening the run question's namespace fires",
     plant "LeanTex/Cli/ZzOpenAsk.lean"
       "module\nimport LeanTex.Cli.Host\nopen LeanTex.Cli.World.Ask in\ndef zzOpenAsk (c : LeanTex.Cli.World.ToolCall) : IO Unit := discard <| LeanTex.Cli.Host.answer (run c)\n"
       ["`open LeanTex.Cli.World.Ask` lets the host's run question be asked"]),
   ("opening an asker by name fires",
     plant "LeanTex/Cli/ZzSel.lean"
       "module\nimport LeanTex.Cli.World\nopen LeanTex.Cli.World.ToolPath (probeGo)\ndef zzSel (call : String → LeanTex.Cli.World.ToolCall) := probeGo call [\"/usr/bin/zz-selective\"]\n"
       ["lets LeanTex.Cli.World.ToolPath.probeGo, which only LeanTex.Cli.World.ToolPath.probe may call"]),
   ("opening the askers' namespace hiding its spawners fires",
     plant "LeanTex/Cli/ZzHide.lean"
       "module\nimport LeanTex.Cli.World\nopen LeanTex.Cli.World.ToolPath hiding probe version\ndef zzHide (call : String → LeanTex.Cli.World.ToolCall) := probeGo call [\"/usr/bin/zz-hidden\"]\n"
       ["lets LeanTex.Cli.World.ToolPath.probeGo, LeanTex.Cli.World.ToolPath.bare, which only"]),
   ("deleting an engine tool's row fires, naming its tool",
     match registry.find? (fun p => p.tool?.isSome && engineReach p.reach) with
     | none => false
     | some p =>
       let tool := basename (p.tool?.getD "")
       let rest := registry.filter (·.name != p.name)
       let suite := (scan inp routes).suiteTools.any (fun (u, _) => basename u == tool) && !rest.any (·.covers tool)
       broke (added rest unbudgeted inp routes)
         ([s!"{tool}', and no render- or fallback-reach row names it"] ++
           if suite then [s!"{tool}' is spawned there, and no row covers it"] else [])),
   ("a run the suite asks of the host is counted, not judged",
     let i := inp.add "Tests/ZzRun.lean"
       "import LeanTex.Cli.Host\ndef zz : IO Unit := discard <| LeanTex.Cli.Host.answer (.run zzCall)" false
     (scan i routes).blind.any (·.file == "Tests/ZzRun.lean") && breaks i routes []),
   ("a spawn in a comment, a docstring or a string is no site",
     plant "LeanTex/Cli/ZzComment.lean"
       ("-- IO.Process.output { cmd := \"zz-commented\" }\n/-- IO.Process.output { cmd := \"zz-commented\" } -/\n" ++
        "/- outer /- inner -/ IO.Process.output { cmd := \"zz-commented\" } -/\n" ++
        "def zzText : String := \"IO.Process.output { cmd := \\\"zz-commented\\\" }\"\n" ++
        "def zzRaw : String := r#\"IO.Process.output { cmd := \"zz-commented\" }\"#\n" ++
        "def zzQuote : Char := '\"'\n") []),
   ("a spawn inside an interpolation is a site",
     plant "LeanTex/Cli/ZzInterp.lean"
       "def zzI : IO String := do return s!\"{(← RunBounded.runBounded \"zz-interp\" #[] \".\").out}\""
       ["the engine spawns 'zz-interp'"]),
   ("an extern declaration fires",
     plant "LeanTex/Cli/ZzExtern.lean" "@[extern \"zz_spawn\"] opaque zzSpawn : IO Unit" ["an extern declaration runs"]),
   ("opening IO.Process fires",
     plant "LeanTex/Cli/ZzOpen.lean" "open IO.Process\n" ["`open IO.Process`"]),
   ("opening IO.Process second on an open line fires",
     plant "LeanTex/Cli/ZzMulti.lean"
       "open LeanTex.Core IO.Process\ndef zz : IO Unit := discard <| output { cmd := \"zz-multi\", args := #[] }"
       ["`open IO.Process`"]),
   ("opening IO and then Process fires",
     plant "LeanTex/Cli/ZzTwice.lean"
       "open IO in\nopen Process in\ndef zz : IO Unit := discard <| output { cmd := \"zz-twice\", args := #[] }"
       ["`open Process`"]),
   ("opening a wrapper's namespace fires",
     plant "LeanTex/Cli/ZzWrapOpen.lean"
       "open LeanTex.Core LeanTex.Cli LeanTex.Cli.RunBounded\ndef zz : IO Unit := discard <| runBounded \"zz-open\" #[] \".\""
       ["`open LeanTex.Cli.RunBounded`"]),
   ("opening a wrapper's namespace for one command fires",
     plant "LeanTex/Cli/ZzOpenIn.lean"
       "open LeanTex.Cli.RunBounded in\ndef zz : IO Unit := discard <| runBounded \"zz-open-in\" #[] \".\""
       ["`open LeanTex.Cli.RunBounded`"]),
   ("exporting a wrapper fires",
     plant "LeanTex/Cli/ZzExport.lean"
       "export LeanTex.Cli.RunBounded (runBounded)\ndef zz : IO Unit := discard <| runBounded \"zz-export\" #[] \".\""
       ["`export LeanTex.Cli.RunBounded`"]),
   ("an open that lists only other declarations is no fault",
     plant "LeanTex/Cli/ZzOpenOther.lean" "open LeanTex.Cli.RunBounded (convBudgetMs)\n" []),
   ("an open that hides every spawner it would expose is no fault",
     plant "LeanTex/Cli/ZzHiding.lean" "open LeanTex.Cli.RunBounded hiding runBounded output\n" []),
   ("an open that renames a spawner fires",
     plant "LeanTex/Cli/ZzRenaming.lean" "open LeanTex.Cli.RunBounded renaming runBounded → zzRun\n"
       ["`open LeanTex.Cli.RunBounded`"]),
   ("a call inside a wrapper's reopened namespace is a site",
     plant "LeanTex/Cli/ZzNs.lean"
       "namespace LeanTex.Cli.RunBounded\ndef zz : IO Unit := discard <| runBounded \"zz-reopened\" #[] \".\"\nend LeanTex.Cli.RunBounded"
       ["the engine spawns 'zz-reopened'"]),
   ("a wrapper under a namespace that is not its file's has its callers read",
     breaks ((inp.add "LeanTex/Cli/ZzWrap.lean" wrapped).add "LeanTex/Cli/ZzCall.lean"
       "def zzCall : IO Unit := LeanTex.Cli.Elsewhere.zzRun \"zz-elsewhere\"") (wrapRoute :: routes)
       ["the engine spawns 'zz-elsewhere'"]),
   ("a top-level wrapper is seen by a module that imports it with import all",
     breaks ((inp.add "LeanTex/Cli/ZzTop.lean"
         "def zzTopRun (t : String) : IO Unit := discard <| RunBounded.runBounded t #[] \".\"").add
         "LeanTex/Cli/ZzAll.lean" "import all LeanTex.Cli.ZzTop\ndef zz : IO Unit := zzTopRun \"zz-import-all\"")
       (⟨"LeanTex/Cli/ZzTop.lean", "LeanTex.Cli.RunBounded.runBounded", "t", .forwards⟩ :: routes)
       ["the engine spawns 'zz-import-all'"]),
   ("a where helper's own parameter fires",
     plant "LeanTex/Cli/ZzWhere.lean"
       "def zzOuter (tool : String) : IO Unit := go \"zz-where\"\nwhere go (t : String) : IO Unit := discard <| IO.Process.output { cmd := t, args := #[] }"
       ["IO.Process.output runs 't', which no route"]),
   ("a literal tool handed through two forwarding wrappers fires",
     breaks (((inp.add "LeanTex/Cli/ZzInner.lean"
         "namespace LeanTex.Cli.ZzInner\ndef produce (tool : String) : IO Unit := discard <| RunBounded.runBounded tool #[] \".\"\nend LeanTex.Cli.ZzInner").add
         "LeanTex/Cli/ZzOuter.lean"
         "namespace LeanTex.Cli.ZzOuter\ndef fulfil (tool : String) : IO Unit := ZzInner.produce tool\nend LeanTex.Cli.ZzOuter").add
         "LeanTex/Cli/ZzUse.lean" "def zz : IO Unit := ZzOuter.fulfil \"zz-chained-tool\"")
       (⟨"LeanTex/Cli/ZzInner.lean", "LeanTex.Cli.RunBounded.runBounded", "tool", .forwards⟩ ::
         ⟨"LeanTex/Cli/ZzOuter.lean", "LeanTex.Cli.ZzInner.produce", "tool", .forwards⟩ :: routes)
       ["the engine spawns 'zz-chained-tool'"]),
   ("a literal tool array handed to a wrapper that iterates it names its tools",
     breaks (inp.add "LeanTex/Cli/ZzEach.lean"
         ("def zzEach (tools : Array String) : IO Unit := do\n  for tool in tools do\n" ++
          "    discard <| RunBounded.runBounded tool #[] \".\"\n\ndef zz : IO Unit := zzEach #[\"zz-each-tool\"]\n"))
       (⟨"LeanTex/Cli/ZzEach.lean", "LeanTex.Cli.RunBounded.runBounded", "tool", .forwards⟩ :: routes)
       ["the engine spawns 'zz-each-tool'"]),
   ("a spawn record piped into a spawner fires",
     plant "LeanTex/Cli/ZzPipe.lean"
       "def zz : IO Unit := discard <| { cmd := \"zz-pipe\", args := #[] : IO.Process.SpawnArgs } |> IO.Process.output"
       ["IO.Process.output runs '_'"]),
   ("a derived route whose let does not read the parameter fires",
     breaks (inp.add "LeanTex/Cli/ZzDerived.lean"
       "def zzD (tool : String) : IO Unit := do\n  let command := \"x\"\n  discard <| RunBounded.runBounded command #[] \".\"")
       (⟨"LeanTex/Cli/ZzDerived.lean", "LeanTex.Cli.RunBounded.runBounded", "command", .derives "tool"⟩ :: routes)
       ["does not read its parameter 'tool'"]),
   ("a derived route whose let also spells a string fires",
     breaks (inp.add "LeanTex/Cli/ZzDerived.lean"
       "def zzD (tool : String) : IO Unit := do\n  let command := if tool.isEmpty then \"zz-derived\" else tool\n  discard <| RunBounded.runBounded command #[] \".\"")
       (⟨"LeanTex/Cli/ZzDerived.lean", "LeanTex.Cli.RunBounded.runBounded", "command", .derives "tool"⟩ :: routes)
       ["spells a string"]),
   ("a spawner passed as a value with no route fires",
     plant "LeanTex/Cli/ZzValue.lean" "def zzV := List.map RunBounded.output []" ["RunBounded.output runs '_'"]),
   ("a forwarding route on a local, not a parameter, fires",
     breaks (inp.add "LeanTex/Cli/ZzLocal.lean"
       "def zzL : IO Unit := do\n  let tool := \"x\"\n  discard <| IO.Process.output { cmd := tool, args := #[] }")
       (⟨"LeanTex/Cli/ZzLocal.lean", "IO.Process.output", "tool", .forwards⟩ :: routes) ["is no parameter"]),
   ("a forwarded wrapper's callers are sites",
     plant "LeanTex/Cli/ZzCaller.lean"
       "def zzC : IO Unit := discard <| RunBounded.output { cmd := \"zz-forwarded\", args := #[] }"
       ["the engine spawns 'zz-forwarded'"]),
   ("a quote char literal opens no string",
     plant "LeanTex/Cli/ZzQuote.lean" s!"def zzQ := ('\"', {budgeted "zz-after-quote"})"
       ["the engine spawns 'zz-after-quote'"]),
   ("a suite spawn of an unregistered tool fires",
     breaks (inp.add "Tests/ZzSuite.lean"
       "def zzS : IO Unit := discard <| IO.Process.output { cmd := \"zz-suite-tool\", args := #[] }" false)
       routes ["'zz-suite-tool' is spawned there, and no row covers it"]),
   ("a script spawn through the script's own wrapper fires",
     script "scripts/zz-script.lean" (scriptRun ++ "def main : IO Unit := run \"zz-script-tool\"") ["'zz-script-tool'"]),
   ("a script's wrapper is no spawner in a script that does not import it",
     breaks ((inp.add "scripts/zz-a.lean" scriptRun false).add "scripts/zz-b.lean"
       "def run (x : String) : IO Unit := pure ()\ndef main : IO Unit := run \"zz-not-a-tool\"" false)
       routes []),
   ("a script tool bound to a constant fires",
     script "scripts/zz-const.lean"
       ("def zzTool : String := \"zz-const-tool\"\n\ndef main : IO Unit := do\n" ++ spawnOf "zzTool") ["'zz-const-tool'"]),
   ("a script tool bound to a constant of a module it imports fires",
     breaks ((inp.add "scripts/ZzLib.lean" "def zzLibTool : String := \"zz-lib-tool\"" false).add
       "scripts/zz-use.lean" ("import scripts.ZzLib\ndef main : IO Unit := do\n" ++ spawnOf "zzLibTool") false)
       routes ["'zz-lib-tool'"]),
   ("a script tool bound by a let fires",
     script "scripts/zz-let.lean"
       ("def main : IO Unit := do\n  let zz := \"zz-let-tool\"\n" ++ spawnOf "zz") ["'zz-let-tool'"]),
   ("a script tool bound by a realPath let, spawned through toString, fires",
     script "scripts/zz-real.lean"
       ("def main : IO Unit := do\n  let zz ← IO.FS.realPath \"zz-real-tool\"\n" ++ spawnOf "zz.toString") ["'zz-real-tool'"]),
   ("a pattern let's alternative is no tool, and its binding names the tool",
     script "scripts/zz-alt.lean"
       ("def main : IO Unit := do\n  let some zz ← ToolProbe.onPath \"zz-alt-bound-tool\" | throw (IO.userError \"zz-alternative\")\n" ++
         spawnOf "zz.toString") ["'zz-alt-bound-tool'"]),
   ("a script for over a written list of tuples names each tool",
     script "scripts/zz-for.lean"
       "def main : IO Unit := do\n  for (c, a) in [(\"zz-for-a\", #[\"-v\"]), (\"zz-for-b\", #[])] do\n    discard <| IO.Process.output { cmd := c, args := a }\n"
       ["'zz-for-a'", "'zz-for-b'"]),
   ("a script for over a let-bound list names its tool",
     script "scripts/zz-list.lean"
       "def main : IO Unit := do\n  let tools := #[(\"zz-list-tool\", #[\"-v\"])]\n  for (c, a) in tools do\n    discard <| IO.Process.output { cmd := c, args := a }\n"
       ["'zz-list-tool'"]),
   ("a match's arms name their tools and its patterns none",
     script "scripts/zz-match.lean"
       ("def main (args : List String) : IO Unit := do\n  let p := match args.headD \"\" with\n    | \"zz-pattern\" => \"zz-arm-tool\"\n    | _ => \"zz-other-arm-tool\"\n" ++ spawnOf "p")
       ["'zz-arm-tool'", "'zz-other-arm-tool'"]),
   ("an if's branches name their tools and its condition none",
     script "scripts/zz-if.lean"
       ("def main (g : String) : IO Unit := do\n  let c := if g.startsWith \"zz-cond\" then \"zz-then-tool\" else \"zz-else-tool\"\n" ++ spawnOf "c")
       ["'zz-then-tool'", "'zz-else-tool'"]),
   ("a path joined to a literal names its last component",
     script "scripts/zz-joined.lean"
       ("def main (dir : System.FilePath) : IO Unit := do\n" ++ spawnOf "(dir / \"bin\" / \"zz-joined-tool\").toString")
       ["/zz-joined-tool' is spawned there"]),
   ("a whole spawn record bound by a let names its cmd field",
     script "scripts/zz-record.lean"
       "def main : IO Unit := do\n  let request : IO.Process.SpawnArgs := { cmd := \"zz-record-tool\", args := #[] }\n  discard <| IO.Process.output request\n"
       ["'zz-record-tool'"]),
   ("a binding the scan cannot read is counted, not judged",
     unread "def main : IO Unit := do\n  let zz ← pickZz\n  discard <| IO.Process.output { cmd := zz, args := #[\"zz-unread\"] }\n"),
   ("the repository's own executables are no residue",
     breaks (inp.add "Tests/ZzSelf.lean"
       "def zzSelf : IO Unit := discard <| IO.Process.output { cmd := \".lake/build/bin/zz-self\", args := #[] }" false)
       routes []),
   ("a further tool no source spells fires",
     broke (added (registry ++ [plantedDevRow "zz-unspelled"]) unbudgeted inp routes)
       ["no scanned source spells 'zz-unspelled'"]),
   ("the picture tools window reads its list and nothing after it",
     picToolsOf "def picTools : List String := [\"zz-a\", \"zz-b\"]\n\ndef zzOther : List String := [\"zz-c\"]\n" ==
       ["zz-a", "zz-b"]),
   ("a mutation that adds a fault beside the one it names breaks more than it names",
     !broke #["zz named", "zz beside"] ["named"]),
   ("a mutation whose named fault did not fire broke nothing it names",
     !broke #["zz named"] ["named", "zz absent"]),
   ("a quiet mutation is one that added no fault",
     broke #[] [] && !broke #["zz"] [])] ++
  layouts.flatMap fun (how, lead) =>
    (["after a theorem", "after a budget exception", "after an asker"].zip (laid lead)).map fun (ctx, ok) =>
      (s!"a declaration with {how}, {ctx}, is its own", ok)

/-- Row-level faults, each planted once. -/
def rowMutations : List (String × Bool) :=
  let base := registry.headD { name := "", residue := .runtime, reach := .render, statement := "" }
  let watched := registry.find? (·.name == "atomic-publication") |>.getD base
  let one (p : Premise) := (rowFaults [p]).isEmpty
  let scripted := ("scripts/svg-check.lean", decl% Tests.svgValidationChecks)
  [("a well-formed row passes", one base && one watched),
   ("two sentences fail", !one { base with statement := "One. Two." }),
   ("a statement with no period fails", !one { base with statement := "no period" }),
   ("a home directory fails", !one { base with statement := "Under /ho" ++ "me/zz the tool runs." }),
   ("an uncheckable row with a check fails", !one { base with checks := [check% Tests.toolMemoChecks] }),
   ("an uncheckable row with a script check fails", !one { base with scriptChecks := [scripted] }),
   ("an uncheckable row with an owed check fails", !one { base with owed := some "Check it." }),
   ("a row nothing tries, with no reason and no owed check, fails", !one { base with unchecked := none }),
   ("a row a script check tries is watched", one { base with unchecked := none, scriptChecks := [scripted] }),
   ("an owed check that is no sentence fails", !one { watched with owed := some "check it" }),
   ("a tool row of oracle reach fails", !one { base with residue := .tool "zz", reach := .oracle }),
   ("further tools on an engine row fail", !one { watched with tools := ["zz"] }),
   ("a row nothing relies on fails", !one { base with sites := [], consumers := [], transfers := [] }),
   ("a gate alone is something that relies on it",
     one { base with sites := [], consumers := [.gate "LeanTex/Cli/Zz.lean" "zz" (check% Tests.toolMemoChecks)] }),
   ("a check pinned as a theorem consumer fails", !one { base with consumers := [.thm (check% Tests.toolMemoChecks)] }),
   ("a gate pinned to a tier item fails", !one { base with consumers := [.gate "f" "d" (.tier "t" "i")] }),
   ("a check pinned as a transfer fails", !one { base with transfers := [check% Tests.toolMemoChecks] }),
   ("a script check outside scripts/ fails",
     !one { watched with scriptChecks := [("Tests/Zz.lean", decl% Tests.svgValidationChecks)] }),
   ("two rows of one name fail", !(rowFaults [base, base]).isEmpty),
   ("the exception clause names each exception, and is empty once none stands",
     exceptedClause [("LeanTex/Cli/ZzA.lean", "zzA", []), ("LeanTex/Cli/ZzB.lean", "zzB", ["zz-unit"])] ==
       ", except the unbudgeted spawns in ZzA.zzA and ZzB.zzB" && exceptedClause [] == "")]

end Premises

open Premises in
/-- Whether `decl` is declared in `file`: by the scan's tokens for a Lean
source it read, else by a line that opens with the declaration, after its
modifiers, in Lean's spelling or Python's. -/
def premiseSiteResolves (inp : Inputs) (file decl : String) : IO Bool := do
  if let some src := inp.files.find? (·.path == file) then
    return (src.named decl).any fun k =>
      let t := src.toks[k]!
      t.declares && (t.text == decl || t.text.endsWith ("." ++ decl))
  let path : System.FilePath := file
  unless ← path.pathExists do return false
  let modifiers := ["public", "private", "protected", "noncomputable"]
  return ((← IO.FS.readFile path).splitOn "\n").any fun line =>
    match (line.splitOn " ").filter (fun w => !w.isEmpty && !modifiers.contains w && !w.startsWith "@[") with
    | kw :: name :: _ => ["def", "theorem", "abbrev"].contains kw && (name == decl || name.startsWith (decl ++ "("))
    | _ => false

open Premises in
/-- The pure core's modules the scan lexes: those that spell a spawner's
namespace, and those that reach the host's vocabulary through their
imports, which could ask it for a run. -/
def coreRead (first : Inputs) (core : Array (String × String)) (needles : List String) :
    Array (String × String) :=
  let hosted := reachers first "LeanTex/Cli/World.lean"
  core.filter fun (p, s) => needles.any (s.contains ·) || hosted.contains (moduleOf p)

open Premises in
/-- What the scan reads of the files as read: the engine's `engine` (every
module outside the pure core, the library's root module, the driver's entry
point, and each core module `coreRead` picks), then the suite's and the
scripts' `lax`. Each file lexes on its own task. -/
def assemble (engine lax : Array (String × String)) : Inputs :=
  let lexAll (files : Array (String × String)) (strict : Bool) : Array Source :=
    (files.map fun (p, s) => Task.spawn fun _ => Source.of p s strict).map Task.get
  let laxTasks := lax.map fun (p, s) => Task.spawn fun _ => Source.of p s false
  let elabText := ((engine.find? (·.1 == "LeanTex/Core/Elab.lean")).map (·.2)).getD ""
  let window := match elabText.splitOn "def picTools" with
    | _ :: after :: _ => "def picTools" ++ (after.take 400).toString
    | _ => ""
  let outside := engine.filter fun (p, _) => !p.startsWith "LeanTex/Core/"
  -- Every engine module's imports, the pure core's included, so a run asked
  -- through a re-export or from a core module is reached however far.
  let graph : Std.HashMap String (Array String) :=
    engine.foldl (fun g (p, s) => g.insert (moduleOf p) (headerImports s)) {}
  let first : Inputs := { files := lexAll outside true, picTools := window, graph }
  let needles := (scan first routes).spawners.toList.filterMap fun s =>
    if s.alias || s.hidden then none
    else some (if s.home.isEmpty then "Process." else lastName s.parent ++ ".")
  let core := coreRead first (engine.filter (·.1.startsWith "LeanTex/Core/")) needles.eraseDups
  { first with files := first.files ++ lexAll core true ++ laxTasks.map Task.get }

open Premises in
/-- What the scan reads (`assemble`), with the raw text of each file outside
the core. -/
def premiseInputs : IO (Inputs × List (String × String)) := do
  let leanIn (dir : String) : IO (Array System.FilePath) := do
    return (← System.FilePath.walkDir dir).filter (·.toString.endsWith ".lean")
  let read (fs : Array System.FilePath) : IO (Array (String × String)) := do
    let mut out := #[]
    for f in fs.qsort (·.toString < ·.toString) do
      out := out.push (f.toString, ← IO.FS.readFile f)
    return out
  let engine ← read (((← leanIn "LeanTex").push "Main.lean").push "LeanTex.lean")
  let tests ← leanIn "Tests"
  let scripts ← leanIn "scripts"
  -- The registry's own strings plant spawns and spell every tool, so it is not read.
  let lax ← read (((tests ++ scripts).push "Tests.lean").filter (·.toString != "Tests/Premises.lean"))
  let outside := engine.filter fun (p, _) => !p.startsWith "LeanTex/Core/"
  return (assemble engine lax, (outside ++ lax).toList)

open Premises in
/-- What of `rows` does not resolve: a pin, a gate's `-- premise:` marker, a
script check its script does not run, a script that is not there, or a site
not declared where the row says. -/
def deadPins (rows : List Premise) (inp : Inputs) (texts : List (String × String)) (suite : String) :
    IO (Array String) := do
  let mut dead : Array String := #[]
  let mut resolved : Array String := #[]
  for p in rows do
    let pins := p.consumers.map (·.pin) ++ p.transfers ++ p.checks
    for pin in pins do
      if resolved.contains pin.name then continue
      if ← pin.resolves suite then resolved := resolved.push pin.name
      else dead := dead.push s!"{p.name}: {pin.name}"
    for c in p.consumers do
      if let .gate file decl pin := c then
        unless gateMarked inp texts file decl pin.name do
          dead := dead.push s!"{p.name}: {file} {decl} carries no `-- premise: {pin.name}` marker"
    for (script, block) in p.scriptChecks do
      unless scriptCalls inp script block.name.toString do
        dead := dead.push s!"{p.name}: {script} runs no {block.name}"
    for s in p.scripts do
      unless ← (System.FilePath.mk s).pathExists do dead := dead.push s!"{p.name}: {s}"
    for (file, decl) in p.sites do
      unless ← premiseSiteResolves inp file decl do
        let who := owes p.retiring
        dead := dead.push s!"{p.name}: {file} {decl} ({who})"
  return dead

open Premises in
/-- **Every world premise is a row, and every row is held.** Rows are well
formed and their pins, scripts and sites resolve: a gate a row names carries
its `-- premise:` marker, and a script check is a block its script runs;
every tool an engine spawn site can run has a render- or fallback-reach row,
and every such row a site; every tool the suite or a script spawns by name
has a row; every spawn with no time limit is one host-bounded names. The
render-path tool, unchecked and owed counts are baselines held in both
directions, and the scan is broken once each way. -/
def premiseChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let start ← IO.monoMsNow
  let faults := rowFaults registry
  t s!"premises: every row is well formed ({faults})" faults.isEmpty
  let suite ← suiteText
  let (inp, texts) ← premiseInputs
  let dead ← deadPins registry inp texts suite
  t s!"premises: every pin, gate, script check, script and site resolves ({dead})" dead.isEmpty
  let planted : Premise :=
    { plantedRow "zz-dead-tool" with
      sites := [("LeanTex/Cli/ZzNowhere.lean", "zzGone")], scripts := ["scripts/zz-no-such-script.lean"] }
  let found ← deadPins [planted] inp texts suite
  t "premises: a row whose site and script are gone is dead, naming both"
    (found.any (hasStr · "ZzNowhere.lean zzGone") && found.any (hasStr · "zz-no-such-script"))
  let synthetic := assemble #[("LeanTex/Cli/World.lean", "module\n"),
      ("LeanTex/Core/ZzAsks.lean", "module\npublic import LeanTex.Core.ZzVia\n"),
      ("LeanTex/Core/ZzVia.lean", "module\npublic import LeanTex.Cli.World\n"),
      ("LeanTex/Core/ZzPure.lean", "module\npublic import LeanTex.Core.Ir\n")]
    #[("Tests/ZzSuite.lean", "def zz := 1\n")]
  t "premises: the scan reads a core module that reaches the host's vocabulary however far, and no other"
    ((synthetic.files.map fun f => (f.path, f.strict)) == #[("LeanTex/Cli/World.lean", true),
      ("LeanTex/Core/ZzAsks.lean", true), ("LeanTex/Core/ZzVia.lean", true), ("Tests/ZzSuite.lean", false)])
  for path in ["LeanTex/Cli/Driver.lean", "LeanTex.lean", (budgetSites.head?.map (·.1)).getD ""] do
    t s!"premises: {path}, which selftests append to, is read" (texts.any (·.1 == path))
  -- The resolvers once each way, in an engine source, a script and Python.
  for (file, decl, expected) in [("LeanTex/Cli/RunBounded.lean", "runBounded", true),
      ("LeanTex/Cli/RunBounded.lean", "zzNoSuchRun", false), ("scripts/land.lean", "main", true),
      ("scripts/land.lean", "zzNoSuchMain", false), ("scripts/gen-test-icons.py", "main", true)] do
    t s!"premises: {file} declares {decl} is {expected}"
      ((← premiseSiteResolves inp file decl) == expected)
  let gate := "LeanTex/Cli/ZzGate.lean"
  let gateText := "def zzGated : IO Unit := do\n  -- premise: Tests.zzGateChecks — a planted gate\n  pure ()\n\ndef zzUngated : IO Unit := pure ()\n"
  let gated := inp.add gate gateText
  let gateTexts := (gate, gateText) :: texts
  t "premises: a gate's marker names its own pin and no other"
    (gateMarked gated gateTexts gate "zzGated" "Tests.zzGateChecks" &&
      !gateMarked gated gateTexts gate "zzGated" "zzOtherChecks" &&
      !gateMarked gated gateTexts gate "zzUngated" "zzGateChecks")
  let caller := "scripts/zz-caller.lean"
  let calls (text : String) (block : String) := scriptCalls (inp.add caller text false) caller block
  let runs := "def main : IO Unit := do\n  let ref ← IO.mkRef []\n  zzBlockChecks ref\n"
  t "premises: a script check is a block the script runs, and no block it only opens or exports"
    (calls ("open Tests (zzBlockChecks)\n\n" ++ runs) "Tests.zzBlockChecks" &&
      !calls runs "Tests.zzOtherChecks" &&
      !calls "open Tests (zzBlockChecks)\nexport Tests (zzBlockChecks)\n\ndef main : IO Unit := pure ()\n"
        "Tests.zzBlockChecks")
  let sc := scan inp routes
  let words := mentioned inp
  let judged := judge registry unbudgeted budgetSites sc words
  t s!"premises: every spawn site runs a registered tool ({judged})" judged.isEmpty
  let render := renderTools registry
  let unchecked := uncheckedCount registry
  let owed := owedCount registry
  t s!"premises: {render} render-path tools, the baseline {renderToolBaseline}"
    (render == renderToolBaseline)
  t s!"premises: {unchecked} premises no check can falsify, the baseline {uncheckedBaseline}"
    (unchecked == uncheckedBaseline)
  t s!"premises: {owed} premises owed a check, the baseline {owedBaseline}"
    (owed == owedBaseline)
  let engine := { inp with files := inp.files.filter (·.strict) }
  let selftest := mutations engine texts words ++ rowMutations
  for (label, fired) in selftest do
    t s!"premises selftest: {label}" fired
  IO.println s!"premises: {registry.length} premises; {unchecked} no check can falsify, {owedFirst registry} owed their first check, {owedFurther registry} owed a further one; {render} render-path tools; the engine spawns {sc.tools.length} spellings at {sc.sites.size} sites, the suite and scripts {sc.suiteTools.length} named tools at {sc.suite.size} sites, {sc.blind.size} sites unread; {(← IO.monoMsNow) - start} ms"
