module

public import LeanTex.Core.Bib
public import Std.Data.HashMap
public import Std.Data.HashSet

/-! biber's uniqueness: what tells two people of one family, or two lists of one
opening, apart in a citation. -/

namespace LeanTex.Core.Bib

/-- biblatex's `uniquename`: off, initials only, initials or the whole given
name, and the variants that read every name. -/
public inductive UniqueName where
  | off
  | init
  | full
  | allinit
  | allfull
  deriving Repr, BEq, Inhabited

/-- How much of a name a citation prints: the base, the given name's initials,
or the whole given name. -/
public inductive NamePart where
  | base
  | init
  | full
  deriving Repr, BEq, Inhabited

public structure UniqueOptions where
  uniquename : UniqueName := .off
  uniquelist : Bool := false
  maxcitenames : Nat := 3
  mincitenames : Nat := 1
  useprefix : Bool := false
  deriving Repr, BEq, Inhabited

/-- A name's parts as text, as biber compares them, and its
given name's initial letters. -/
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

/-- One entry's labelname list: its names with their text, whether `and others`
closes it, and its citation counts. -/
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

/-- An entry's labelname: the first of `shortauthor`, `author`, `shorteditor`,
`editor` and `translator` holding a name. -/
public def labelNameList (e : Entry) (useauthor : Bool := true) (useeditor : Bool := true)
    (usetranslator : Bool := false) : Option (String × NameList) :=
  let fields := ["shortauthor"] ++ (if useauthor then ["author"] else []) ++ ["shorteditor"] ++
    (if useeditor then ["editor"] else []) ++ (if usetranslator then ["translator"] else [])
  fields.findSome? fun f =>
    (e.field? f).bind fun v =>
      let l := NameList.ofValue v
      if l.names.isEmpty then none else some (f, l)

/-- What uniqueness decides for one list: how many names it shows once
truncated, and how much of each a citation prints. -/
public structure Unique where
  ul : Option Nat := none
  parts : Array NamePart := #[]
  deriving Repr, BEq, Inhabited

/-- The separator biber joins a name's strings and a list's names with. -/
private def sep : String := String.singleton (Char.ofNat 0x10FFFD)

/-- One name as the uniqueness template reads it. -/
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

/-- For each string, how many distinct names read it. -/
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

/-- Whether the name at `i` of a list is one a citation reads. -/
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

/-- DataList.pm's namelist_differs_index over the other
complete lists opening as this one does. -/
private def differsIndex (list : Array String) (finals : Array (Array String)) : Option Nat :=
  let best := finals.foldl (init := none) fun acc l =>
    if l == list then acc
    else
      let c := opening list l
      if c == 0 then acc else some (Nat.max (acc.getD 0) (c - 1))
  best.map fun i => if i + 1 == list.size then i else i + 1

/-- DataList.pm's namelist_differs_nth. -/
private def differsNth (list : Array String) (n : Nat) (finals : Array (Array String)) : Bool :=
  finals.any fun l => l.size ≥ list.size && l[n - 1]? != list[n - 1]? &&
    l.extract 0 (n - 1) == list.extract 0 (n - 1)

/-- One list's `uniquelist`: the shortest opening no other list shares. -/
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

/-- biber's uniqueness over a reference list's labelname
lists, one answer per list in order. -/
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

/-- How many of a list's `k` names show where at most `max` show whole. -/
public def shownCount (k max min : Nat) (ul : Option Nat) : Nat :=
  if k > max then ul.getD (Nat.min min k) else k

/-- One name as biblatex's `labelname` format prints it at a part, in TeX. -/
public def labelNameTeX (useprefix : Bool) (p : NamePart) (n : Name) : String :=
  let words (ws : List String) : String := " ".intercalate (ws.filter (!·.isEmpty))
  match p with
  | .base => if useprefix then words [n.von, n.last] else n.last
  | .init => words [initials n.first, if useprefix then n.von else initials n.von, n.last,
      initials n.jr]
  | .full => words [n.first, n.von, n.last, n.jr]

/-- A labelname list as a citation prints it, in TeX. -/
public def citeNamesTeX (o : UniqueOptions) (l : NameList) (u : Unique) : String :=
  let k := l.names.size
  let vis := shownCount k (l.counts o).1 (l.counts o).2 u.ul
  let shown := (l.names.extract 0 vis).toList.zipIdx.map fun (n, i) =>
    labelNameTeX (n.useprefix.getD o.useprefix) (u.parts[i]?.getD .base) n
  andJoin (if vis < k || l.more then shown ++ ["others"] else shown)

/-- The key biber groups extradate's letters by for a list. -/
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

/-- biber's `namehash` for a list: the names a citation shows, each whole. -/
public def nameHashFull (o : UniqueOptions) (l : NameList) (u : Unique) : String :=
  let k := l.names.size
  let vis := shownCount k (l.counts o).1 (l.counts o).2 u.ul
  let names := (l.names.extract 0 vis).toList.zipIdx.map fun (n, i) =>
    let t := l.textAt i n
    t.von ++ t.last ++ t.first ++ t.jr
  sep.intercalate names ++ (if vis < k || l.more then "+" else "")

end LeanTex.Core.Bib
