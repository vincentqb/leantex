module

/-! The macro and environment definers the surfaces read, a theorem declaration apart, each once:
what it defines, who spells it and how it treats a name already defined; the definer lists the
readers key on are queries over the one table. -/

namespace LeanTex.Core.Definer

/-- What a definer defines. -/
public inductive Defines where
  | command | environment
  deriving @[expose] BEq, DecidableEq, Repr

/-- Who spells a definer: TeX's primitives, `\let`, the LaTeX kernel, xparse, etoolbox, the
kernel's and letltxmacro's command copies, the engine itself, amsmath, environ and tcolorbox. -/
public inductive Family where
  | tex | letting | latex | xparse | etoolbox | copy | native | amsmath | environ | tcolorbox
  deriving @[expose] BEq, DecidableEq, Repr

/-- How a definer treats a name already defined: defines a new one, redefines one, defines one only
where none stands, or defines whatever stands. -/
public inductive Mode where
  | new | renew | provide | declare
  deriving @[expose] BEq, DecidableEq, Repr

/-- One definer, and whether it expands its body where it stands, assigns globally, and defines a
command whose meaning is a wrapper around its body, as LaTeX's robust commands are. -/
public structure Row where
  name : String
  defines : Defines
  family : Family
  mode : Mode
  expands : Bool
  global : Bool
  wrapper : Bool
  deriving Repr

/-- A definer that keeps its body as written, assigns locally and defines the body itself. -/
@[expose] public def row (name : String) (defines : Defines) (family : Family) (mode : Mode) : Row :=
  ⟨name, defines, family, mode, false, false, false⟩

/-- The macro and environment definers the surfaces read, `\newtheorem` read apart. -/
@[expose] public def table : List Row :=
  [row "def" .command .tex .declare, { row "gdef" .command .tex .declare with global := true },
   { row "edef" .command .tex .declare with expands := true },
   { row "xdef" .command .tex .declare with expands := true, global := true },
   row "let" .command .letting .declare,
   row "newcommand" .command .latex .new, row "renewcommand" .command .latex .renew,
   row "providecommand" .command .latex .provide,
   { row "DeclareRobustCommand" .command .latex .declare with wrapper := true },
   row "NewDocumentCommand" .command .xparse .new,
   row "RenewDocumentCommand" .command .xparse .renew,
   row "ProvideDocumentCommand" .command .xparse .provide,
   row "DeclareDocumentCommand" .command .xparse .declare,
   row "newrobustcmd" .command .etoolbox .new, row "renewrobustcmd" .command .etoolbox .renew,
   row "providerobustcmd" .command .etoolbox .provide,
   row "NewCommandCopy" .command .copy .new, row "RenewCommandCopy" .command .copy .renew,
   row "DeclareCommandCopy" .command .copy .declare, row "LetLtxMacro" .command .copy .declare,
   row "define" .command .native .declare, row "defineenv" .environment .native .declare,
   row "DeclareMathOperator" .command .amsmath .new,
   row "newenvironment" .environment .latex .new,
   row "renewenvironment" .environment .latex .renew,
   row "provideenvironment" .environment .latex .provide,
   row "NewDocumentEnvironment" .environment .xparse .new,
   row "RenewDocumentEnvironment" .environment .xparse .renew,
   row "ProvideDocumentEnvironment" .environment .xparse .provide,
   row "DeclareDocumentEnvironment" .environment .xparse .declare,
   row "NewEnviron" .environment .environ .new, row "RenewEnviron" .environment .environ .renew,
   row "newtcolorbox" .environment .tcolorbox .new,
   row "renewtcolorbox" .environment .tcolorbox .renew]

/-- Whether a row is a TeX definer keeping its body as written. -/
@[expose] public def Row.plainTex (r : Row) : Bool := r.family == .tex && !r.expands

/-- The definer a name spells. -/
@[expose] public def row? (name : String) : Option Row := table.find? (·.name == name)

/-- What the definer a name spells defines, and its family. -/
@[expose] public def kind? (name : String) : Option (Defines × Family) :=
  (row? name).map fun r => (r.defines, r.family)

/-- Whether a name spells a definer of `d` in the family `f` under the mode `m`. -/
@[expose] public def is (name : String) (d : Defines) (f : Family) (m : Mode) : Bool :=
  (row? name).any fun r => r.defines == d && r.family == f && r.mode == m

/-- Whether the definer a name spells expands its body where it stands. -/
@[expose] public def expands (name : String) : Bool := (row? name).any (·.expands)

/-- Whether the definer a name spells assigns globally. -/
@[expose] public def global (name : String) : Bool := (row? name).any (·.global)

/-- The names of the definers a query keeps. -/
@[expose] public def names (keep : Row → Bool) : List String := (table.filter keep).map (·.name)

/-- Whether a row defines a command one of the families `fs` spells. -/
@[expose] public def Row.commandOf (r : Row) (fs : List Family) : Bool :=
  r.defines == .command && fs.contains r.family

/-- The command definers whose next token is the name they define, never a call, but a math
operator's. -/
@[expose] public def namedNext : List String :=
  names fun r => r.defines == .command && r.family != .amsmath

/-- The definers after which a pass reads a control word standing next, directly or as `{\name}`,
as the name bound. -/
@[expose] public def bindsNext : List String :=
  names fun r => r.commandOf [.tex, .letting, .latex, .xparse, .amsmath] || r.family == .native

/-- The environment definers whose begin and end code a pass reads as TeX: LaTeX's but the
providing one, and environ's. -/
@[expose] public def codeEnvs : List String :=
  names fun r => r.defines == .environment &&
    ((r.family == .latex && r.mode != .provide) || r.family == .environ)

/-- The definers whose operands a pass reads as a definition rather than as content. -/
@[expose] public def readAsDefinition : List String :=
  bindsNext ++ codeEnvs ++ names fun r => r.defines == .environment && r.family == .tcolorbox

/-- The xparse environment definers but the providing one. -/
@[expose] public def xparseEnvs : List String :=
  names fun r => r.defines == .environment && r.family == .xparse && r.mode != .provide

/-- The LaTeX and xparse environment definers, whose code runs where each environment opens. -/
@[expose] public def envs : List String :=
  names fun r => r.defines == .environment && (r.family == .latex || r.family == .xparse)

/-- The definers whose two body groups are token lists. -/
@[expose] public def tokenListEnvs : List String :=
  names fun r => r.defines == .environment && (r.family == .latex || r.family == .native)

/-- The command definers after which the definition passes read a name as meaning something new:
TeX's, `\let`, LaTeX's and xparse's but the providing ones, and the engine's. -/
@[expose] public def redefiners : List String :=
  names fun r => (r.commandOf [.tex, .letting, .latex, .xparse] && r.mode != .provide) ||
    r.commandOf [.native]

/-- The command definers whose next token names the macro the definition passes read as defined:
TeX's, `\let`, LaTeX's, xparse's and etoolbox's. -/
@[expose] public def nameDefiners : List String :=
  names fun r => r.commandOf [.tex, .letting, .latex, .xparse, .etoolbox]

/-- The command definers one family spells. -/
@[expose] public def commandsOf (f : Family) : List String := names (·.commandOf [f])

/-- Whether a command definer defines a name only where none stands. -/
@[expose] public def provides (name : String) : Bool :=
  table.any fun r => r.name == name && r.defines == .command && r.mode == .provide

/-- The written definers of a macro, whose lowering is the definition's. -/
@[expose] public def macroDefiners : List String :=
  (names (·.commandOf [.tex, .letting, .latex])).map ("\\" ++ ·)

end LeanTex.Core.Definer
