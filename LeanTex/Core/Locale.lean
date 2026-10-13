module

namespace LeanTex.Core

/-! Language as data, babel's design: a locale is a total record of the fields the engine reads,
the shipped ones generated into `LocaleData.lean` from babel's ini files. -/

/-- One kind's cleveref names (cleveref.sty v0.21.4): `\crefname`'s lowercase pair and
`\Crefname`'s capitalised pair, independent strings. -/
public structure CrefName where
  one : String
  many : String
  capOne : String
  capMany : String
  deriving Repr, BEq

/-- One language's reader-visible data, keyed by its BCP 47 tag. -/
public structure Locale where
  /-- BCP 47 language tag (`tag.bcp47` in the ini). -/
  tag : String
  figure : String
  table : String
  /-- The algorithm float's caption word, from algorithm2e's language options. -/
  algorithm : String
  abstract : String
  references : String
  /-- `\proofname` and `\contentsname`: the ini's `captions` `proof` and `contents` keys. -/
  proof : String
  contents : String
  /-- The twelve wide month names, January first (`months.wide.*`). -/
  months : Array String
  /-- The outer and inner quote delimiters (`delimiters.quotes`). -/
  quoteOpen : String
  quoteClose : String
  quoteInnerOpen : String
  quoteInnerClose : String
  /-- Hyphenation minima (`lefthyphenmin`/`righthyphenmin`): the shortest
  fragment a break may leave on each side. -/
  leftMin : Nat
  rightMin : Nat
  /-- cleveref's names per kind (cleveref.sty v0.21.4 language blocks); `crefSection` serves
  every heading level. -/
  crefSection : CrefName
  crefEquation : CrefName
  crefFigure : CrefName
  crefTable : CrefName
  /-- cleveref's algorithm names (cleveref.sty v0.21.4, `\crefname{algorithm}`). -/
  crefAlgorithm : CrefName
  /-- `\crefrange`'s conjunction word (`\crefrangeconjunction` without its
  no-break space: "to", "bis", "à"). -/
  crefRangeTo : String
  /-- The word before a numbered listing's caption: listings.sty's `\lstlistingname` in English,
  cleveref's in French and German. -/
  listing : String
  /-- The decimal marker (`[numbers] decimal` in the ini, CLDR's number
  symbols): what `\num{1.5}` prints between integer and fraction. -/
  decimal : String
  /-- The digit-group separator `\num` sets: the ini's for fr and de, siunitx's thin space in en. -/
  group : String
  deriving Repr, BEq

namespace Locale

/-- babel's language option names to BCP 47 tags, for the shipped locales (babel manual §1.3). -/
public def babelNames : List (String × String) :=
  [("english", "en"), ("american", "en"), ("USenglish", "en"),
   ("british", "en"), ("UKenglish", "en"), ("canadian", "en"),
   ("australian", "en"), ("newzealand", "en"),
   ("french", "fr"), ("francais", "fr"), ("frenchb", "fr"),
   ("canadien", "fr"), ("acadian", "fr"),
   ("german", "de"), ("germanb", "de"), ("ngerman", "de"),
   ("austrian", "de"), ("naustrian", "de")]

/-- The tag a babel language option names: the option table first, else
the name taken as a BCP 47 tag itself (`\selectlanguage{fr}` is legal
babel since 3.43). -/
public def babelTagOf (name : String) : String :=
  (babelNames.lookup name).getD name

end Locale

end LeanTex.Core
