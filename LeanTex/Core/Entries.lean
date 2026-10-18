module

public import LeanTex.Core.Parse
import LeanTex.Core.KeyVal

/-! Key=value lists read from raws: one reader for the native declarations' grammar and for LaTeX's
keyval lists, a group standing whole in either, so a value's TeX reaches its reader as the raws it
is. -/

namespace LeanTex.Core.Entries

open LeanTex.Core.Parse

/-- One piece of a list's raws as the reader reads it: a character of a word, with the word's site,
the space between words, or a raw standing whole. -/
public inductive Item where
  | char (c : Char) (pos : Pos)
  | space
  | raw (r : Raw)
  deriving Inhabited

namespace Item

/-- Whether the item is the character `c`, a word's or a symbol's. -/
public def is (c : Char) : Item → Bool
  | .char d _ | .raw (.sym d _) => d == c
  | .space | .raw _ => false

/-- Whether the item is blank: a space, or a whitespace character. -/
public def blank : Item → Bool
  | .char c _ => c.isWhitespace
  | .space => true
  | .raw _ => false

end Item

/-- A list's raws as items, each word character by character. -/
public def itemsOf : List Raw → Array Item → Array Item
  | [], acc => acc
  | .word w p :: rest, acc => itemsOf rest (w.toList.foldl (fun acc c => acc.push (.char c p)) acc)
  | .space :: rest, acc | .par _ :: rest, acc => itemsOf rest (acc.push .space)
  | r :: rest, acc => itemsOf rest (acc.push (.raw r))

/-- The two grammars: the native declarations', whose brackets, parentheses and quotes hold commas,
and LaTeX's keyval lists', whose key and value lose the braces around the whole of them; in either a
group, formula or control symbol stands whole, so no comma in one cuts, where keyval cuts a formula. -/
public inductive Grammar where
  | native
  | keyval
  deriving BEq, Repr

/-- Items as a grammar's atoms: a quoted run whole in the native grammar, every other item alone. -/
private def atomsOf (g : Grammar) : List Item → Array (List Item) → Array (List Item)
  | [], acc => acc
  | i :: rest, acc =>
    if g == .native && i.is '"' then
      let body := rest.takeWhile (!·.is '"')
      atomsOf g (rest.drop (body.length + 1))
        (acc.push (i :: body ++ (rest.drop body.length).take 1))
    else atomsOf g rest (acc.push [i])
termination_by l => l.length
decreasing_by all_goals simp only [List.length_cons, List.length_drop]; omega

private def opens (g : Grammar) (a : List Item) : Bool :=
  match g, a with
  | .native, [i] => i.is '{' || i.is '[' || i.is '('
  | .keyval, [i] => i.is '{'
  | _, _ => false

private def closes (g : Grammar) (a : List Item) : Bool :=
  match g, a with
  | .native, [i] => i.is '}' || i.is ']' || i.is ')'
  | .keyval, [i] => i.is '}'
  | _, _ => false

private def comma (a : List Item) : Bool :=
  match a with
  | [i] => i.is ','
  | _ => false

/-- Items with the blank ones at both ends dropped. -/
private def trimItems (l : List Item) : List Item :=
  ((l.dropWhile Item.blank).reverse.dropWhile Item.blank).reverse

/-- Items cut at their first `=`, in the keyval grammar the first outside braces: those before it,
and those after it where it stands. -/
private def cutItems (g : Grammar) : List Item → Nat → Array Item → List Item × Option (List Item)
  | [], _, acc => (acc.toList, none)
  | i :: rest, depth, acc =>
    if (g == .native || depth == 0) && i.is '=' then (acc.toList, some rest) else
      cutItems g rest (if i.is '{' then depth + 1 else if i.is '}' then depth - 1 else depth)
        (acc.push i)

/-- Items back as raws: a run of characters one word at its first character's site, a space a
space, a raw itself. -/
private def rawsOf : List Item → Option (String × Pos) → Array Raw → Array Raw
  | [], cur, out => match cur with
    | some (w, p) => out.push (.word w p)
    | none => out
  | .char c p :: rest, cur, out =>
    rawsOf rest (some (match cur with | some (w, q) => (w.push c, q) | none => (String.singleton c, p)))
      out
  | .space :: rest, cur, out =>
    rawsOf rest none ((match cur with | some (w, p) => out.push (.word w p) | none => out).push .space)
  | .raw r :: rest, cur, out =>
    rawsOf rest none ((match cur with | some (w, p) => out.push (.word w p) | none => out).push r)

/-- Items as the raws they stand for, trimmed, a keyval key or value without the one group around
the whole of it. -/
private def valueOf (g : Grammar) (l : List Item) : Array Raw :=
  match g, trimItems l with
  | .keyval, [.raw (.group body _)] => body
  | _, t => rawsOf t none #[]

/-- One entry: its raws, its key, and its value's raws as its grammar reads them and as written,
none where it holds no `=`. -/
public structure Entry where
  item : Array Raw
  key : String
  value : Option (Array Raw)
  written : Option (Array Raw)

/-- The entry's text as written. -/
public def Entry.src (e : Entry) : String := rawSrc e.item

/-- A list's entries read from its raws by a grammar: cut at the commas outside its groups, each at
its first `=` outside them, the blank ones dropped. -/
public def read (g : Grammar) (body : Array Raw) : Array Entry :=
  let pieces := KeyVal.splitTopAt (opens g) (closes g) comma
    (atomsOf g (itemsOf body.toList #[]).toList #[]).toList
  pieces.filterMap fun p =>
    let flat := trimItems (p.toList.flatMap id)
    if flat.isEmpty then none else
    -- A keyval item braced whole is read inside its braces.
    let inner := match g, flat with
      | .keyval, [.raw (.group body _)] => trimItems (itemsOf body.toList #[]).toList
      | _, _ => flat
    let (k, v) := cutItems g inner 0 #[]
    some { item := rawsOf flat none #[], key := rawSrc (valueOf g k), value := v.map (valueOf g)
           written := v.map fun l => rawsOf (trimItems l) none #[] }

end LeanTex.Core.Entries
