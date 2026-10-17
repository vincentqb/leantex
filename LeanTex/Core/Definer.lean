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

/-- One definer. -/
public structure Row where
  name : String
  defines : Defines
  family : Family
  mode : Mode
  deriving Repr

/-- The macro and environment definers the surfaces read, `\newtheorem` read apart. -/
@[expose] public def table : List Row :=
  [⟨"def", .command, .tex, .declare⟩, ⟨"gdef", .command, .tex, .declare⟩,
   ⟨"edef", .command, .tex, .declare⟩, ⟨"xdef", .command, .tex, .declare⟩,
   ⟨"let", .command, .letting, .declare⟩,
   ⟨"newcommand", .command, .latex, .new⟩, ⟨"renewcommand", .command, .latex, .renew⟩,
   ⟨"providecommand", .command, .latex, .provide⟩,
   ⟨"DeclareRobustCommand", .command, .latex, .declare⟩,
   ⟨"NewDocumentCommand", .command, .xparse, .new⟩,
   ⟨"RenewDocumentCommand", .command, .xparse, .renew⟩,
   ⟨"ProvideDocumentCommand", .command, .xparse, .provide⟩,
   ⟨"DeclareDocumentCommand", .command, .xparse, .declare⟩,
   ⟨"newrobustcmd", .command, .etoolbox, .new⟩, ⟨"renewrobustcmd", .command, .etoolbox, .renew⟩,
   ⟨"providerobustcmd", .command, .etoolbox, .provide⟩,
   ⟨"NewCommandCopy", .command, .copy, .new⟩, ⟨"RenewCommandCopy", .command, .copy, .renew⟩,
   ⟨"DeclareCommandCopy", .command, .copy, .declare⟩, ⟨"LetLtxMacro", .command, .copy, .declare⟩,
   ⟨"define", .command, .native, .declare⟩, ⟨"defineenv", .environment, .native, .declare⟩,
   ⟨"DeclareMathOperator", .command, .amsmath, .new⟩,
   ⟨"newenvironment", .environment, .latex, .new⟩,
   ⟨"renewenvironment", .environment, .latex, .renew⟩,
   ⟨"provideenvironment", .environment, .latex, .provide⟩,
   ⟨"NewDocumentEnvironment", .environment, .xparse, .new⟩,
   ⟨"RenewDocumentEnvironment", .environment, .xparse, .renew⟩,
   ⟨"ProvideDocumentEnvironment", .environment, .xparse, .provide⟩,
   ⟨"DeclareDocumentEnvironment", .environment, .xparse, .declare⟩,
   ⟨"NewEnviron", .environment, .environ, .new⟩, ⟨"RenewEnviron", .environment, .environ, .renew⟩,
   ⟨"newtcolorbox", .environment, .tcolorbox, .new⟩,
   ⟨"renewtcolorbox", .environment, .tcolorbox, .renew⟩]

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

/-- The definers whose operands a pass reads as a definition rather than as content. -/
@[expose] public def readAsDefinition : List String :=
  bindsNext ++ names fun r => r.defines == .environment &&
    ((r.family == .latex && r.mode != .provide) || r.family == .environ || r.family == .tcolorbox)

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
