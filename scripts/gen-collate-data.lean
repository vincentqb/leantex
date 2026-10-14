/-
Regenerate LeanTex/Core/CollateData.lean: the Unicode::Collate::Locale tailorings biber sorts
by, as `Collate`'s weight rows, and biber's `%LOCALE_MAP`, read from the host through perl.
Usage: lake env lean --run scripts/gen-collate-data.lean [path/to/Biber/Constants.pm]
-/

import Std.Data.HashMap
import LeanTex.Core.Hex

open LeanTex.Core

def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

/-- The first copyright line of the default table Unicode::Collate reads
(`Unicode/Collate/allkeys.txt` on perl's `@INC`), as its header states it. -/
def copyrightScript : String :=
  "for my $d (@INC) { my $f = \"$d/Unicode/Collate/allkeys.txt\"; next unless -e $f; " ++
  "open(my $h, '<', $f) or die; while (<$h>) { if (/^# (Copyright .*)$/) { print $1; exit } } " ++
  "exit }"

/-- The Unicode License V3's copyright and permission notice, which must
appear with every copy of the data it covers, under `copyright`: the
default table's own line. -/
def unicodeNotice (copyright : String) : String := s!"UNICODE LICENSE V3

COPYRIGHT AND PERMISSION NOTICE

{copyright}

NOTICE TO USER: Carefully read the following legal agreement. BY
DOWNLOADING, INSTALLING, COPYING OR OTHERWISE USING DATA FILES, AND/OR
SOFTWARE, YOU UNEQUIVOCALLY ACCEPT, AND AGREE TO BE BOUND BY, ALL OF THE
TERMS AND CONDITIONS OF THIS AGREEMENT. IF YOU DO NOT AGREE, DO NOT
DOWNLOAD, INSTALL, COPY, DISTRIBUTE OR USE THE DATA FILES OR SOFTWARE.

Permission is hereby granted, free of charge, to any person obtaining a
copy of data files and any associated documentation (the \"Data Files\") or
software and any associated documentation (the \"Software\") to deal in the
Data Files or Software without restriction, including without limitation
the rights to use, copy, modify, merge, publish, distribute, and/or sell
copies of the Data Files or Software, and to permit persons to whom the
Data Files or Software are furnished to do so, provided that either (a)
this copyright and permission notice appear with all copies of the Data
Files or Software, or (b) this copyright and permission notice appear in
associated Documentation.

THE DATA FILES AND SOFTWARE ARE PROVIDED \"AS IS\", WITHOUT WARRANTY OF ANY
KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT OF
THIRD PARTY RIGHTS.

IN NO EVENT SHALL THE COPYRIGHT HOLDER OR HOLDERS INCLUDED IN THIS NOTICE
BE LIABLE FOR ANY CLAIM, OR ANY SPECIAL INDIRECT OR CONSEQUENTIAL DAMAGES,
OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS,
WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION,
ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THE DATA
FILES OR SOFTWARE.

Except as contained in this notice, the name of a copyright holder shall
not be used in advertising or otherwise to promote the sale, use or other
dealings in these Data Files or Software without prior written
authorization of the copyright holder."

def run (cmd : String) (args : Array String) : IO String := do
  let out ← try IO.Process.output { cmd, args }
    catch _ => die s!"{cmd} not found"
  if out.exitCode != 0 then die s!"{cmd} failed: {out.stderr}"
  return out.stdout

def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n) |>.toUpper

def strLit (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

/-- The default table's elements of the Latin letters and the marks. -/
def weightsScript : String := "
use strict; use warnings;
use Unicode::Collate; use Unicode::Collate::Locale; use Unicode::Normalize;
binmode STDOUT, ':utf8';
my $c = Unicode::Collate->new(normalization => undef, variable => 'non-ignorable');
print \"VERSION $Unicode::Collate::Locale::VERSION \", $c->version, \"\\n\";
print \"LOCALEPM $INC{'Unicode/Collate/Locale.pm'}\\n\";
sub ces { join(',', map { my ($v, $p, $s, $t) = unpack('Cn4', $_); sprintf('%X.%X.%X', $p, $s, $t) } @_) }
for my $u (0x41 .. 0x24F, 0x250 .. 0x2AF, 0x1D00 .. 0x1DBF, 0x1E00 .. 0x1EFF, 0x2C60 .. 0x2C7F,
           0xA720 .. 0xA7FF, 0xAB30 .. 0xAB6F, 0xFB00 .. 0xFB06) {
  my $ch = chr($u);
  next unless $ch =~ /\\p{L}/ && $ch =~ /\\p{Latin}/ && NFD($ch) eq $ch;
  my @w = $c->getWt($u);
  next if grep { (unpack('Cn4', $_))[1] >= 0xFB00 } @w;
  printf \"LETTER %X %s\\n\", $u, ces(@w);
}
for my $m (0x300 .. 0x36F, 0x1AB0 .. 0x1AFF, 0x1DC0 .. 0x1DFF, 0x20D0 .. 0x20FF, 0xFE20 .. 0xFE2F) {
  my @w = $c->getWt($m);
  next unless @w == 1;
  my ($v, $p, $s, $t) = unpack('Cn4', $w[0]);
  printf \"MARK %X %X\\n\", $m, $s if !$p && $s;
}
"

/-- Every tailoring file named on the command line, dumped as lines. -/
def filesScript : String := "
use strict; use warnings;
binmode STDOUT, ':utf8';
for my $f (@ARGV) {
  my $h = do \"Unicode/Collate/Locale/$f.pl\" or die \"cannot read $f.pl\";
  my $b = $h->{backwards};
  $b = defined $b ? (ref $b ? join(',', @$b) : $b) : '';
  print \"FILE $f $b\\n\";
  for my $line (split /\\n/, ($h->{entry} // '')) { print \"E $line\\n\" }
}
"

/-- Locale.pm's `%LocaleFile` (its `qw(...)` list and the assignments after
it) and `%TypeAlias`. -/
def localeTables (pm : String) : Array (String × String) × Array (String × String) := Id.run do
  let mut files : Array (String × String) := #[]
  let qw := ((pm.splitOn "my %LocaleFile = map { ($_, $_) } qw(")[1]?.getD "").splitOn ")" |>.headD ""
  for w in (qw.replace "\n" " ").splitOn " " do
    let w := w.trimAscii.toString
    unless w.isEmpty do files := files.push (w, w)
  for line in pm.splitOn "\n" do
    let l := line.trimAscii.toString
    if l.startsWith "$LocaleFile{'" then
      match l.splitOn "'" with
      | _ :: k :: _ :: v :: _ => files := files.push (k, v)
      | _ => pure ()
  let mut aliases : Array (String × String) := #[]
  let ta := ((pm.splitOn "my %TypeAlias = qw(")[1]?.getD "").splitOn ")" |>.headD ""
  let ws := ((ta.replace "\n" " ").splitOn " ").filter (!·.trimAscii.toString.isEmpty)
  for i in [0:ws.length / 2] do
    aliases := aliases.push (ws[2 * i]!.trimAscii.toString, ws[2 * i + 1]!.trimAscii.toString)
  return (files, aliases)

/-- biber's `%LOCALE_MAP`: language name → locale. -/
def biberMap (pm : String) : Array (String × String) := Id.run do
  let body := ((pm.splitOn "our %LOCALE_MAP = (")[1]?.getD "").splitOn ");" |>.headD ""
  let mut out : Array (String × String) := #[]
  for line in body.splitOn "\n" do
    match line.splitOn "'" with
    | _ :: k :: _ :: v :: _ => out := out.push (k, v)
    | _ => pure ()
  return out

/-- A tertiary weight read as `Collate`'s case row: an uppercase weight of
UTS #10 §7.3.1 (8–12) is `1`, which sorts first as biber's `sortupper`
sorts it, any other `2`. -/
def caseRow (t : Nat) : Nat := if 0x08 ≤ t && t ≤ 0x0C then 1 else 2

structure CE where
  p : Nat
  s : Nat
  t : Nat

def parseCEs (s : String) : Array CE := Id.run do
  let mut out : Array CE := #[]
  for part in (s.splitOn "[").drop 1 do
    let body := (part.splitOn "]").headD ""
    let body := (body.drop 1).toString
    match body.splitOn "." with
    | [p, s, t] =>
      match Hex.value? p.toList, Hex.value? s.toList, Hex.value? t.toList with
      | some p, some s, some t => out := out.push { p, s, t }
      | _, _, _ => pure ()
    | _ => pure ()
  return out

def main (args : List String) : IO UInt32 := do
  let weights ← run "perl" #["-e", weightsScript]
  let mut version := ""
  let mut pmPath := ""
  let mut letters : Array (Nat × Array CE) := #[]
  let mut marks : Array (Nat × Nat) := #[]
  for line in weights.splitOn "\n" do
    match line.splitOn " " with
    | ["VERSION", v, d] => version := s!"Unicode::Collate::Locale {v}, DUCET {d}"
    | ["LOCALEPM", p] => pmPath := p
    | ["LETTER", c, ces] =>
      match Hex.value? c.toList with
      | some c => letters := letters.push (c, parseCEs ("[." ++ "][.".intercalate (ces.splitOn ",") ++ "]"))
      | none => pure ()
    | ["MARK", m, s] =>
      match Hex.value? m.toList, Hex.value? s.toList with
      | some m, some s => marks := marks.push (m, s)
      | _, _ => pure ()
    | _ => pure ()
  if letters.size < 500 || marks.size < 100 || pmPath.isEmpty then
    die s!"perl reported {letters.size} letters and {marks.size} marks"
  -- the Latin letters' primaries span one range of the table
  let prims := letters.flatMap fun (_, ces) => (ces.filter (·.p != 0)).map (·.p)
  let lo := prims.foldl Nat.min prims[0]!
  let hi := prims.foldl Nat.max 0
  let elems (ces : Array CE) : String :=
    ",".intercalate (ces.toList.filterMap fun ce =>
      if ce.p == 0 && ce.s == 0 then none
      else some s!"{hex ce.p}.{hex ce.s}.{if ce.p == 0 then "0" else hex (caseRow ce.t)}")
  let (files, aliases) := localeTables (← IO.FS.readFile pmPath)
  if files.size < 60 then die s!"read {files.size} locales from {pmPath}: the source changed shape"
  let names := (files.map (·.2)).toList.eraseDups.filter (!·.isEmpty)
  let dump ← run "perl" (#["-e", filesScript] ++ names.toArray)
  let mut tailored : Array (String × String × String) := #[]
  let mut outside : Array String := #[]
  let mut cur : Option (String × String) := none
  let mut lines : Array String := #[]
  let flush := fun (cur : Option (String × String)) (lines : Array String)
      (tailored : Array (String × String × String)) (outside : Array String) =>
    Id.run do
    let some (f, bw) := cur | return (tailored, outside)
    let entries := lines.filterMap fun l =>
      let l := ((l.splitOn "#").headD "").trimAscii.toString
      match l.splitOn ";" with
      | [cps, ces] =>
        let cps := ((cps.trimAscii.toString.splitOn " ").filter (!·.isEmpty)).filterMap
          (Hex.value? ·.toList)
        if cps.isEmpty then none else some (cps, parseCEs ces)
      | _ => none
    if entries.isEmpty then return (tailored.push (f, bw, ""), outside)
    if entries.any (fun (_, ces) => ces.any fun ce => ce.p != 0 && (ce.p < lo || ce.p > hi)) then
      return (tailored, outside.push f)
    let rows := entries.map fun (cps, ces) =>
      let e := elems ces
      "+".intercalate (cps.map hex) ++ "=" ++ e
    return (tailored.push (f, bw, " ".intercalate rows.toList), outside)
  for line in dump.splitOn "\n" do
    if line.startsWith "FILE " then
      (tailored, outside) := flush cur lines tailored outside
      match line.splitOn " " with
      | _ :: f :: rest => cur := some (f, " ".intercalate rest |>.trimAscii.toString)
      | _ => cur := none
      lines := #[]
    else if line.startsWith "E " then lines := lines.push (line.drop 2).toString
  (tailored, outside) := flush cur lines tailored outside
  if !tailored.any (·.1 == "sv") || !outside.contains "ja" then
    die "the tailorings read have no Swedish, or carry Japanese: the source changed shape"
  let constants ← match args with
    | p :: _ => pure p
    | [] => do
      let pre := (← run "brew" #["--prefix", "biber"]).trimAscii.toString
      pure s!"{pre}/libexec/lib/perl5/Biber/Constants.pm"
  let bmap := biberMap (← IO.FS.readFile constants)
  if bmap.size < 80 || !bmap.any (·.1 == "swedish") then
    die s!"read {bmap.size} language names from {constants}: the source changed shape"
  let config := (constants.dropEnd "Constants.pm".length).toString ++ "Config.pm"
  let biberVersion := (((← IO.FS.readFile config).splitOn "our $VERSION = '")[1]?.getD
    "?").splitOn "'" |>.headD "?"
  -- The copyright the default table's header states, which its licence notice carries.
  let copyright := (← run "perl" #["-e", copyrightScript]).trimAscii.toString
  unless copyright.startsWith "Copyright " && copyright.endsWith "Unicode, Inc." do
    die s!"allkeys.txt states no Unicode copyright line ('{copyright}'): the source changed shape"
  let pairs (xs : Array (String × String)) : String :=
    ",\n   ".intercalate (xs.toList.map fun (k, v) => s!"({strLit k}, {strLit v})")
  let rows := ",\n   ".intercalate (tailored.toList.map fun (f, bw, es) =>
    s!"({strLit f}, {strLit bw},\n    {strLit es})")
  let letterRows := " ".intercalate (letters.toList.map fun (c, ces) => s!"{hex c}={elems ces}")
  let markRows := " ".intercalate (marks.toList.map fun (m, s) => s!"{hex m}={hex s}")
  let out := s!"module\n\n/-
Generated by scripts/gen-collate-data.lean; do not edit by hand. Regenerate with:
  lake env lean --run scripts/gen-collate-data.lean [path/to/Biber/Constants.pm]

Sources, read from the host and never vendored:
- {version}: the default table's elements of {letters.size} Latin letters and
  {marks.size} combining marks, Locale.pm's locale files and type aliases, and
  each Locale/*.pl tailoring
- Biber::Constants {biberVersion}, `%LOCALE_MAP`
This module carries only data: `Collate` reads it, and its contracts are
checked by the suite.

licence: Unicode::Collate and its tailorings are free software under the
same terms as Perl itself, and Biber::Constants is released under the
Artistic License 2.0. The default table (allkeys.txt) is Unicode data
under the Unicode License V3 (SPDX-License-Identifier: Unicode-3.0), the
copyright its header states, and its copyright and permission notice
follows:

{unicodeNotice copyright}
-/

namespace LeanTex.Core.CollateData

/-- The default table's elements of each Latin letter without a canonical
decomposition, space-separated: the code point, `=`, its elements,
`,`-joined, each `primary.secondary.case` in hexadecimal — the case row `1`
for an uppercase tertiary, `2` otherwise, `0` on an element with no
primary. -/
public def latinLetters : String :=
  {strLit letterRows}

/-- The default table's second-level weight of each combining mark,
space-separated `codepoint=weight` in hexadecimal. -/
public def markWeights : String :=
  {strLit markRows}

/-- The tailoring file of each locale Unicode::Collate::Locale accepts
(Locale.pm `%LocaleFile`; `default` names none). -/
public def localeFiles : List (String × String) :=
  [{pairs files}]

/-- Locale.pm `%TypeAlias`: a variant's short name and the one it stands for. -/
public def typeAliases : List (String × String) :=
  [{pairs aliases}]

/-- Each tailoring file whose weights fall among the Latin letters': its
name, the levels it compares backwards (`2`: French Canadian accents), and
its entries, space-separated — the code points an entry matches, `+`-joined,
then `=` and its elements as `latinLetters` writes them. -/
public def tailorings : List (String × String × String) :=
  [{rows}]

/-- The tailoring files whose weights fall outside the Latin letters': their
scripts sort by the default reading. -/
public def outsideRows : List String :=
  [{", ".intercalate (outside.toList.map strLit)}]

/-- biber's language names and the locales it sorts them by
(`%LOCALE_MAP`, which `locale2bcp47` reads). -/
public def biberLocales : List (String × String) :=
  [{pairs bmap}]

end LeanTex.Core.CollateData
"
  IO.FS.writeFile "LeanTex/Core/CollateData.lean" out
  IO.println s!"wrote {letters.size} letters, {marks.size} marks, {tailored.size} tailorings, \
    {outside.size} outside the rows, {bmap.size} language names"
  return 0
