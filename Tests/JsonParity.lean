module

public import Tests.Support
public import Tests.Support.Rand
public import LeanTex.Core.Json
public import LeanTex.Core.ListingReply
public import Lean.Data.Json

public section

/-! The engine's JSON reader and speller against Lean's own `Lean.Json`, which the compiler no
longer links: the same values, failures, spellings and layouts over invented texts. -/

namespace Tests.JsonParity

open LeanTex.Core LeanTex.Core.JsonText

/-- The engine's value as Lean's. -/
def toLean : Json → Lean.Json
  | .null => .null
  | .bool b => .bool b
  | .num n => .num ⟨n.mantissa, n.exponent⟩
  | .str s => .str s
  | .arr a => .arr (a.attach.map fun ⟨x, _⟩ => toLean x)
  | .obj kvs => Lean.Json.mkObj (kvs.attach.toList.map fun ⟨(k, v), _⟩ => (k, toLean v))
termination_by j => sizeOf j
decreasing_by
  all_goals simp_wf
  · have := Array.sizeOf_lt_of_mem ‹_ ∈ a›; omega
  · have := Array.sizeOf_lt_of_mem ‹_ ∈ kvs›; simp at this; omega

/-- Texts that reach every reachable branch of Lean's reader, failures included. -/
def edgeTexts : List String :=
  ["", " ", "\t\n\r 7 ", "[", "[1", "[1,", "[1,]", "[1 2]", "[1] x", "1 2", "]", "}", ",", ":",
   "{", "{\"a\"", "{\"a\":", "{\"a\":1", "{\"a\" 1}", "{a:1}", "{\"a\":1,}", "{\"a\":1 \"b\":2}",
   "{ }", "[ ]", "[[[[]]]]", "{\"a\":{\"b\":[1,{\"c\":null}]}}", "  {\"b\":1,\"a\":2,\"b\":3}  ",
   "{\"é\":1,\"e\":2,\"z\":3,\"Z\":4,\"\":5}", "tru", "nul", "fals", "true", "false", "null",
   "trueX", "-", "-a", "--1", "-0", "-0.0", "0", "01", "00", "1.", "1.a", "1.5", "1.50", "-12.034",
   "1e", "1e+", "1e-", "1E5", "1e05", "1.5e-3", "2.5E+2", "1e-0", "0.000000000001",
   "123456789012345678901234567890", "1.0e+2", "1e4096", "1e99999999999999999999",
   "12345678901234567890.000000000000000000001e-7", "\"abc", "\"a\u0001b\"", "\"\\\"",
   "\"\\u12\"", "\"\\uZZZZ\"", "\"\\u00e9\"", "\"\\u0000\"", "\"\\ud83d\\ude00\"", "\"\\ud83d\"",
   "\"\\ude00\"", "\"\\ud83d\\u0041\"", "\"\\ud83d\\ud83d\"", "\"\\uD83D\\uDE00\"", "\"\\ud83dx\"",
   "\"\\ud83d\\", "\"\\ud83d\\u", "\"\\ud83d\\ude0\"", "\"\\x\"", "\"\\/\\b\\f\\n\\r\\t\"",
   "\"é😀\"", "é", "😀", "[\"\\uD800\\uDC00\"]", "\"\u007f\"", "[1,\"two\",true,null,{\"k\":[]}]",
   "{\"leantex-lean-export\":2,\"lean\":\"4.0.0\",\"errors\":0}",
   "{\"version\":1,\"provider\":\"Pygments\",\"answers\":[{\"language\":\"lean\",\"source\":\"x\",\"tokens\":[{\"offset\":0,\"kind\":\"Token.Name\",\"text\":\"x\"}]}]}"]

/-- Characters a mutation draws from: JSON's own, escapes' letters, digits, white space and
characters outside ASCII. -/
def alphabet : Array Char :=
  #['{', '}', '[', ']', '"', ',', ':', '\\', 'u', 'd', 'D', 'e', 'E', '.', '+', '-', '0', '1', '9',
    'a', 'f', 't', 'n', 'l', 'r', 's', ' ', '\n', '\t', 'é', '😀', '\x01']

/-- `text` with `count` random edits, each inserting, deleting or replacing one character. -/
def mutate (text : String) (count : Nat) (seed : UInt64) : String × UInt64 := Id.run do
  let mut cs := text.toList.toArray
  let mut s := seed
  for _ in [0:count] do
    let (op, s1) := rand s 3
    let (at_, s2) := rand s1 (cs.size + 1)
    let (pick, s3) := rand s2 alphabet.size
    s := s3
    let c := alphabet[pick]?.getD ' '
    if op == 0 then cs := (cs.extract 0 at_).push c ++ cs.extract at_ cs.size
    else if op == 1 && at_ < cs.size then cs := cs.extract 0 at_ ++ cs.extract (at_ + 1) cs.size
    else cs := cs.modify at_ fun _ => c
  return (String.ofList cs.toList, s)

/-- A random string over `alphabet` of at most seven characters. -/
def genString (seed : UInt64) : String × UInt64 := Id.run do
  let (len, s0) := rand seed 8
  let mut s := s0
  let mut out := ""
  for _ in [0:len] do
    let (pick, s1) := rand s alphabet.size
    s := s1
    out := out.push (alphabet[pick]?.getD 'x')
  return (out, s)

/-- A random value at most `depth` containers deep, its numbers of either sign and any scale. -/
def genValue : Nat → UInt64 → Json × UInt64
  | 0, seed =>
    let (kind, s) := rand seed 4
    match kind with
    | 0 => (.null, s)
    | 1 => let (b, s) := rand s 2; (.bool (b == 1), s)
    | 2 =>
      let (m, s) := rand s 2000001
      let (e, s) := rand s 25
      (.num ⟨(m : Int) - 1000000, e⟩, s)
    | _ => let (t, s) := genString s; (.str t, s)
  | depth + 1, seed => Id.run do
    let (kind, s0) := rand seed 3
    let (count, s1) := rand s0 5
    let mut s := s1
    if kind == 0 then return genValue 0 s
    let mut elems : Array Json := #[]
    let mut members : List (String × Json) := []
    for _ in [0:count] do
      let (v, s2) := genValue depth s
      let (k, s3) := genString s2
      s := s3
      elems := elems.push v
      members := members ++ [(k, v)]
    return (if kind == 1 then .arr elems else Json.mkObj members, s)

/-- The keys a reading is asked for: present, absent and duplicated ones. -/
def keys : List String := ["a", "b", "k", "lean", "errors", "version", "answers", "missing", ""]

/-- Whether the engine refused an exponent past `Json.maxShift` that Lean's reader takes, building
its power of ten or aborting, so Lean is never asked. -/
def refusedShift (text e : String) : Bool :=
  e.endsWith ": exp too large" &&
    let at_ := (String.ofList ((e.toList.drop "offset ".length).takeWhile Char.isDigit)).toNat?.getD 0
    let digits := ((text.toUTF8.extract 0 at_).toList.reverse.takeWhile fun b => 48 ≤ b && b ≤ 57).reverse
    let n := digits.foldl (fun n b => 10 * n + (b.toNat - 48)) 0
    Json.maxShift < n && n ≤ USize.size

/-- Whether both readers agree on a text: the same value, spelled and laid out the same, and the
same reading of each key as each type the engine asks for; or the same failure. -/
def agrees (text : String) : Bool :=
  match Json.parse text with
  | .error e => refusedShift text e || Lean.Json.parse text == .error e
  | .ok a =>
  match Lean.Json.parse text with
  | .error _ => false
  | .ok b =>
    toLean a == b && a.compress == b.compress && a.pretty == b.pretty &&
      keys.all fun k =>
        (a.getObjValAs? Nat k == b.getObjValAs? Nat k) &&
        (a.getObjValAs? String k == b.getObjValAs? String k) &&
        (a.getObjValAs? Bool k == b.getObjValAs? Bool k) &&
        ((a.getObjValAs? (Array Json) k).map (·.map toLean) ==
          b.getObjValAs? (Array Lean.Json) k) &&
        ((a.getObjVal? k).map toLean == b.getObjVal? k) &&
        (toLean (a.getObjValD k) == b.getObjValD k) &&
        ((a.getArr?).map (·.map toLean) == b.getArr?) && (a.getStr? == b.getStr?)

end Tests.JsonParity

open LeanTex.Core LeanTex.Core.JsonText Tests.JsonParity in
/-- The engine reads, spells and lays out JSON as Lean's own `Lean.Json` does. -/
def jsonParityChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let edgeMisses := edgeTexts.filter (!agrees ·)
  t s!"json parity: every edge text reads alike in both readers (differing: {edgeMisses})"
    edgeMisses.isEmpty
  let mut seed : UInt64 := 1017
  let mut misses : Array String := #[]
  for base in edgeTexts do
    for count in [1, 2, 3, 4, 6, 8, 1, 2, 3, 4, 6, 8] do
      let (text, s) := mutate base count seed
      seed := s
      if !agrees text then misses := misses.push text
  t s!"json parity: mutated texts read alike in both readers (differing: {misses.toList.take 5})"
    misses.isEmpty
  let mut spelled : Array String := #[]
  for _ in [0:400] do
    let (v, s) := genValue 3 seed
    seed := s
    let lean := toLean v
    for text in [lean.compress, lean.pretty, lean.pretty 20] do
      if !agrees text then spelled := spelled.push text
    let (text, s) := mutate lean.compress 2 seed
    seed := s
    if !agrees text then spelled := spelled.push text
  t s!"json parity: random values as Lean spells them read alike in both readers \
(differing: {spelled.toList.take 3})" spelled.isEmpty
  let strings := ["", "plain", "quote \" and \\ back", "line\nfeed\rreturn\ttab",
    "\x00\x01\x1f\x7f", "é 😀 ∀", "</script>", "\u2028\u2029"]
  t "json parity: positive exponents within the bound read as Lean reads them"
    (["1e4096", "1E5", "2.5E+2", "[1.0e+2]", "-3e+0", "7E4096"].all agrees)
  let long := "\"" ++ "".pushn 'a' 16000000 ++ "\\u00e9\""
  let spaced := "".pushn ' ' 16000000 ++ "[" ++ "".pushn '1' 1000 ++ "]"
  let readsAlike (text : String) : Bool :=
    match Json.parse text, Lean.Json.parse text with
    | .ok a, .ok b => toLean a == b
    | .error e, .error f => e == f
    | _, _ => false
  t "json parity: a string and white space of sixteen million characters read as Lean reads them"
    (readsAlike long && readsAlike spaced)
  t "json parity: an exponent past the bound is refused where Lean would build its power"
    (["[1e4097]", "1e9999999999"].zip ["offset 7: exp too large", "offset 12: exp too large"]
      |>.all fun (text, why) => match Json.parse text with
        | .error e => e == why
        | .ok _ => false)
  t "json parity: string literals are spelled as Lean spells them"
    (strings.all fun s => Json.renderString s == Lean.Json.renderString s &&
      (Json.str s).compress == (Lean.Json.str s).compress)
  let members : List (String × Json) := [("b", .num ⟨1, 0⟩), ("a", .str "x"), ("b", .null),
    ("é", .arr #[.bool true, .num ⟨-15, 1⟩]), ("A", .obj #[])]
  t "json parity: an object keeps each key's last value, in Lean's key order"
    ((Json.mkObj members).compress ==
      (Lean.Json.mkObj (members.map fun (k, v) => (k, toLean v))).compress)
  let numbers : List JsonNumber := [⟨0, 0⟩, ⟨-7, 0⟩, ⟨15, 1⟩, ⟨-15, 1⟩, ⟨100, 2⟩, ⟨1, 12⟩,
    ⟨123456789, 3⟩, ⟨5, 20⟩, ⟨-1, 40⟩]
  t "json parity: numbers are spelled as Lean spells them"
    (numbers.all fun n => n.toString == (⟨n.mantissa, n.exponent⟩ : Lean.JsonNumber).toString)
  let requests : Array ListingReply.Request :=
    #[{ language := "lean", source := "def x := \"é\"\n" }, { language := "", source := "" }]
  let theirs := (Lean.Json.mkObj [("version", Lean.toJson (1 : Nat)),
    ("requests", Lean.Json.arr (requests.map fun r => Lean.Json.mkObj
      [("language", Lean.toJson r.language), ("source", Lean.toJson r.source)]))]).compress
  t "json parity: a listing batch is spelled byte for byte as Lean spelled it"
    (ListingReply.encode requests == theirs)
