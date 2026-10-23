\ProvidesClass{inventedstray}[2026/01/01 v1.0 Invented stray class]
\LoadClass{article}
\RequirePackage{pgffor}
\RequirePackage{etoolbox}
\foreach \x in {A, B}{\expandafter\xdef\csname invented\x\endcsname{\x}}
\newcommand{\inventedhook}{}
\apptocmd{\inventedhook}{\par}{}{}
\newwrite\inventedout
\immediate\openout\inventedout=\jobname.inventedaux
\immediate\write\inventedout{}
\immediate\closeout\inventedout
\AtEndDocument{\input{\jobname.inventedaux}}
\AtBeginDocument{\DeclareSymbolFont{inventedsym}{U}{msb}{m}{n}%
  \DeclareSymbolFontAlphabet{\inventedbb}{inventedsym}}
