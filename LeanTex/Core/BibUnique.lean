module

public import LeanTex.Core.Bib
public import Std.Data.HashMap
public import Std.Data.HashSet

/-! biber's uniqueness: what tells two people of one family apart in a
citation (`uniquename`: the given name's initials, or the whole given name,
where the family alone is ambiguous) and two lists of one opening
(`uniquelist`: a truncated list shown past `mincitenames` until it is its
own) — Biber.pm's create_uniquename_info, generate_uniquename,
create_uniquelist_info and generate_uniquelist, and DataList.pm's
set_uniquelist, under biblatex's default uniqueness template (biblatex.def
`\DeclareUniquenameTemplate`: the prefix, under `useprefix`, and the family
are a name's base; its given name is what disambiguates).

biber iterates the two to a fixed point, which is two readings. Whether a
name is ambiguous among every name of every list does not depend on how
much of a list shows, and a list's length depends only on that; the names a
citation shows are then read before the lengths and with them, and a name
the second reading leaves ambiguous keeps what the first gave it
(generate_uniquename's `unless defined`). -/

namespace LeanTex.Core.Bib

/-- biblatex's `uniquename` (biblatex manual §3.1.2.3): off, initials only,
initials or the whole given name (`true`, `full`), and the two variants that
read every name of every list, shown or not. -/
public inductive UniqueName where
  | off
  | init
  | full
  | allinit
  | allfull
  deriving Repr, BEq, Inhabited

/-- How much of a name a citation prints — biblatex's `uniquename` counter:
the base, the given name's initials, or the whole given name. -/
public inductive NamePart where
  | base
  | init
  | full
  deriving Repr, BEq, Inhabited

/-- The options uniqueness reads. -/
public structure UniqueOptions where
  uniquename : UniqueName := .off
  uniquelist : Bool := false
  maxcitenames : Nat := 3
  mincitenames : Nat := 1
  useprefix : Bool := false
  deriving Repr, BEq, Inhabited

/-- A name's parts as text — what biber compares, its LaTeX decoded — and
its given name's initial letters. -/
public structure NameText where
  von : String
  last : String
  first : String
  jr : String
  inits : String
  deriving Repr, BEq, Inhabited

public def NameText.of (n : Name) : NameText :=
  { von := text n.von, last := text n.last, first := text n.first, jr := text n.jr
    inits := text (tokenLetters n.first) }

/-- One entry's labelname list: its names, each as text beside it, and
whether `and others` closes it (biber counts the names before it); the
citation counts its entry's `options` set over the document's, and whether
its entry takes part in uniqueness (`dataonly` takes it out). -/
public structure NameList where
  names : Array Name := #[]
  texts : Array NameText := #[]
  more : Bool := false
  maxCite : Option Nat := none
  minCite : Option Nat := none
  unique : Bool := true
  deriving Repr, BEq, Inhabited

/-- A list's citation counts: its own, else the options'. -/
private def NameList.counts (l : NameList) (o : UniqueOptions) : Nat × Nat :=
  (l.maxCite.getD o.maxcitenames, l.minCite.getD o.mincitenames)

/-- A name list's names, `and others` read off its end. -/
public def NameList.ofValue (v : String) : NameList :=
  let ns := (splitNames v).toList
  let more := ns.getLast? == some "others"
  let names := ((if more then ns.dropLast else ns).map parseNameBiber).toArray
  { names, texts := names.map NameText.of, more }

/-- The text of the list's `i`-th name. -/
private def NameList.textAt (l : NameList) (i : Nat) (n : Name) : NameText :=
  (l.texts[i]?).getD (NameText.of n)

/-- An entry's labelname (biblatex.def `\DeclareLabelname`): the first of
`shortauthor`, `author`, `shorteditor`, `editor` and `translator` that holds
a name, as the field it is and its list — `author`, `editor` and
`translator` only under their `use` options (biblatex's defaults:
`useauthor`, `useeditor`, no `usetranslator`). -/
public def labelNameList (e : Entry) (useauthor : Bool := true) (useeditor : Bool := true)
    (usetranslator : Bool := false) : Option (String × NameList) :=
  let fields := ["shortauthor"] ++ (if useauthor then ["author"] else []) ++ ["shorteditor"] ++
    (if useeditor then ["editor"] else []) ++ (if usetranslator then ["translator"] else [])
  fields.findSome? fun f =>
    (e.field? f).bind fun v =>
      let l := NameList.ofValue v
      if l.names.isEmpty then none else some (f, l)

/-- What uniqueness decides for one list: how many names it shows once
truncated (`uniquelist`; none where `mincitenames` stands), and how much of
each name a citation prints. -/
public structure Unique where
  ul : Option Nat := none
  parts : Array NamePart := #[]
  deriving Repr, BEq, Inhabited

/-- The separator biber joins a name's strings and a list's names with. -/
private def sep : String := String.singleton (Char.ofNat 0x10FFFD)

/-- One name as the template reads it: its base, the strings that add the
given name's initials and then the whole given name — as many as the
option's level reads, the most general first — the part each string stands
for, and the name's identity, its strings joined. -/
private structure Dis where
  base : String
  strings : Array String
  parts : Array NamePart
  key : String

private def Dis.of (un : UniqueName) (useprefix : Bool) (t : NameText) : Dis :=
  let base := (if useprefix then t.von else "") ++ t.last
  let given := t.first
  let inits := t.inits
  let (strings, parts) : Array String × Array NamePart :=
    if given.isEmpty then (#[base], #[.base])
    else match un with
      | .off => (#[base], #[.base])
      | .init | .allinit => (#[base, base ++ inits], #[.base, .init])
      | .full | .allfull => (#[base, base ++ inits, base ++ given], #[.base, .init, .full])
  { base, strings, parts, key := sep.intercalate strings.toList }

/-- For each string, how many names — distinct identities — read it. -/
private def namesOf (ds : Array Dis) : Std.HashMap String Nat := Id.run do
  let mut seen : Std.HashSet (String × String) := {}
  let mut count : Std.HashMap String Nat := {}
  for d in ds do
    for s in d.strings do
      unless seen.contains (s, d.key) do
        seen := seen.insert (s, d.key)
        count := count.insert s (count.getD s 0 + 1)
  return count

/-- The most general part at which a name is the only name of its string. -/
private def partOf (seen : Std.HashMap String Nat) (d : Dis) : Option NamePart :=
  (d.strings.zip d.parts).findSome? fun (s, p) =>
    if seen.get? s == some 1 then some p else none

/-- Whether the name at `i` (from 0) of a list is one a citation reads: under
the `all` variants every name; else one within the list's `uniquelist`, any
name of a list `and others` closes or of one no longer than `maxcitenames`,
and one within `mincitenames`. -/
private def reads (o : UniqueOptions) (l : NameList) (ul : Option Nat) (i : Nat) : Bool :=
  let (mx, mn) := l.counts o
  o.uniquename == .allinit || o.uniquename == .allfull || ul.any (i + 1 ≤ ·) || l.more ||
    l.names.size ≤ mx || i + 1 ≤ mn

/-- A list's names joined, the key biber counts a list or its opening by. -/
private def listKey (xs : Array String) : String := sep.intercalate xs.toList

/-- How many names two lists open with alike. -/
private def opening (a b : Array String) : Nat := Id.run do
  let mut n := 0
  for i in [0:Nat.min a.size b.size] do
    if a[i]? == b[i]? then n := n + 1 else break
  return n

/-- DataList.pm's namelist_differs_index, over the other complete lists
that open as this one does: where this list stops agreeing with the one it
agrees with longest — its last index, when another list holds all of it. -/
private def differsIndex (list : Array String) (finals : Array (Array String)) : Option Nat :=
  let best := finals.foldl (init := none) fun acc l =>
    if l == list then acc
    else
      let c := opening list l
      if c == 0 then acc else some (Nat.max (acc.getD 0) (c - 1))
  best.map fun i => if i + 1 == list.size then i else i + 1

/-- DataList.pm's namelist_differs_nth: some complete list at least as long
agrees with this one before its `n`-th name and differs there. -/
private def differsNth (list : Array String) (n : Nat) (finals : Array (Array String)) : Bool :=
  finals.any fun l => l.size ≥ list.size && l[n - 1]? != list[n - 1]? &&
    l.extract 0 (n - 1) == list.extract 0 (n - 1)

/-- One list's `uniquelist` (generate_uniquelist, set_uniquelist): the
shortest opening no other list shares — none for a list no longer than
`maxcitenames`, which never truncates, or an opening within
`mincitenames`; for a list others repeat whole, the point where it differs
from the list it agrees with longest; and one name less where no list as
long differs at its last, since a longer list's `et al.` already tells it
from a shorter one. -/
private def listLength (o : UniqueOptions) (openings finalCount : Std.HashMap String Nat)
    (finals : Array (Array String)) (l : NameList) (dl : Array String) : Option Nat :=
  let o := { o with maxcitenames := (l.counts o).1, mincitenames := (l.counts o).2 }
  let k := dl.size
  let u := (((List.range k).find? fun m =>
    openings.getD (listKey (dl.extract 0 (m + 1))) 0 == 1).map (· + 1)).getD k
  let nl := dl.extract 0 u
  if u ≤ 1 || k ≤ o.maxcitenames || (u ≤ o.mincitenames && o.mincitenames != k) then none
  else if finalCount.getD (listKey nl) 0 > 1 then
    (differsIndex nl finals).bind fun i => if i == 0 then none else some (i + 1)
  else if k > u && !differsNth nl u finals then some (u - 1)
  else some u

/-- **biber's uniqueness over a reference list's labelname lists**, one
answer per list in the order given: each name's part — from what every
name of every list reads when the lists' lengths are being decided, then
from what the shown names read, before the lengths and with them — and
each list's `uniquelist`, from the parts every name reads. -/
public def uniqueness (o : UniqueOptions) (lists : Array NameList) : Array Unique := Id.run do
  let dis : Array (Array Dis) := lists.map fun l =>
    if !l.unique then #[]
    else l.names.zipIdx.map fun (n, i) =>
      Dis.of o.uniquename (n.useprefix.getD o.useprefix) (l.textAt i n)
  let off := o.uniquename == .off
  let every := namesOf (dis.foldl (init := #[]) (· ++ ·))
  let allParts : Array (Array NamePart) := dis.map (·.map fun d =>
    if off then .base else (partOf every d).getD .base)
  let mut uls : Array (Option Nat) := lists.map fun _ => none
  if o.uniquelist then
    let dls : Array (Array String) := (dis.zip allParts).map fun (ds, ps) =>
      (ds.zip ps).map fun (d, p) => (((d.parts.zip d.strings).find? (·.1 == p)).map (·.2)).getD d.base
    let openings : Std.HashMap String Nat := dls.foldl (init := {}) fun m dl =>
      (List.range dl.size).foldl (init := m) fun m j =>
        let key := listKey (dl.extract 0 (j + 1))
        m.insert key (m.getD key 0 + 1)
    let finalCount : Std.HashMap String Nat := dls.foldl (init := {}) fun m dl =>
      m.insert (listKey dl) (m.getD (listKey dl) 0 + 1)
    let byFirst : Std.HashMap String (Array (Array String)) := dls.foldl (init := {}) fun m dl =>
      match dl[0]? with
      | some f =>
        let g := m.getD f #[]
        if g.contains dl then m else m.insert f (g.push dl)
      | none => m
    uls := (dls.zip lists).map fun (dl, l) =>
      if !l.unique then none
      else dl[0]?.bind fun f => listLength o openings finalCount (byFirst.getD f #[]) l dl
  let shownBy (ul : Array (Option Nat)) : Array Dis :=
    (dis.zip (lists.zip ul)).foldl (init := #[]) fun acc (ds, l, u) =>
      ds.zipIdx.foldl (init := acc) fun acc (d, i) => if reads o l u i then acc.push d else acc
  let first := namesOf (shownBy (lists.map fun _ => none))
  let second := namesOf (shownBy uls)
  let mut out : Array Unique := #[]
  for ((ds, l), u) in (dis.zip lists).zip uls do
    let parts := ds.zipIdx.map fun (d, i) =>
      if off || !l.unique || !reads o l u i then NamePart.base
      else
        let before := if reads o l none i then (partOf first d).getD .base else .base
        (partOf second d).getD before
    out := out.push { ul := u, parts }
  return out

/-- How many of a list's `k` names show where at most `max` show whole: all
of them, or past `max` its `uniquelist`, else `min` (biber's
process_visible_names). -/
public def shownCount (k max min : Nat) (ul : Option Nat) : Nat :=
  if k > max then ul.getD (Nat.min min k) else k

/-- One name as biblatex's `labelname` format prints it at a part
(biblatex.def `\DeclareNameFormat{labelname}`), in TeX: the family — with
its prefix under `useprefix` — then the given name's initials with the
prefix's and the suffix's (the prefix whole under `useprefix`), or the
whole name. -/
public def labelNameTeX (useprefix : Bool) (p : NamePart) (n : Name) : String :=
  let words (ws : List String) : String := " ".intercalate (ws.filter (!·.isEmpty))
  match p with
  | .base => if useprefix then words [n.von, n.last] else n.last
  | .init => words [initials n.first, if useprefix then n.von else initials n.von, n.last,
      initials n.jr]
  | .full => words [n.first, n.von, n.last, n.jr]

/-- A labelname list as a citation prints it, in TeX: the names it shows,
each at its part, joined as biblatex joins them, closed by `et al.` when it
shows fewer than it has or `and others` closes it. -/
public def citeNamesTeX (o : UniqueOptions) (l : NameList) (u : Unique) : String :=
  let k := l.names.size
  let vis := shownCount k (l.counts o).1 (l.counts o).2 u.ul
  let shown := (l.names.extract 0 vis).toList.zipIdx.map fun (n, i) =>
    labelNameTeX (n.useprefix.getD o.useprefix) (u.parts[i]?.getD .base) n
  andJoin (if vis < k || l.more then shown ++ ["others"] else shown)

/-- The key biber groups extradate's letters by for a list (Internals.pm
`_getnamehash_u`): the names a citation shows, each its prefix and family
and as much of its given name as its part prints, and `+` where the list
is truncated or `and others` closes it. -/
public def nameHashKey (o : UniqueOptions) (l : NameList) (u : Unique) : String :=
  let k := l.names.size
  let vis := shownCount k (l.counts o).1 (l.counts o).2 u.ul
  let names := (l.names.extract 0 vis).toList.zipIdx.map fun (n, i) =>
    let t := l.textAt i n
    t.von ++ t.last ++ match u.parts[i]?.getD .base with
      | .full => t.first
      | .init => t.inits
      | .base => ""
  String.join names ++ (if vis < k || l.more then "+" else "")

/-- biber's `namehash` for a list (Internals.pm `_getnamehash`): the names
a citation shows, each whole, and `+` where the list is truncated or `and
others` closes it — uniqueness leaves it, as the names do not change. -/
public def nameHashFull (o : UniqueOptions) (l : NameList) (u : Unique) : String :=
  let k := l.names.size
  let vis := shownCount k (l.counts o).1 (l.counts o).2 u.ul
  let names := (l.names.extract 0 vis).toList.zipIdx.map fun (n, i) =>
    let t := l.textAt i n
    t.von ++ t.last ++ t.first ++ t.jr
  sep.intercalate names ++ (if vis < k || l.more then "+" else "")

end LeanTex.Core.Bib
