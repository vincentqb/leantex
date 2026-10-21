\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{inventedletters}[2026/01/01 v1.0 Invented letters class]
\newif\if@review \@reviewfalse
\DeclareOption{review}{\@reviewtrue}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}
\ProcessOptions\relax
\LoadClass{article}
\newcommand{\journalname}{Invented Letters}
\newcommand{\keywords}[1]{\par\noindent\textbf{Keywords:} #1}
\if@review
  \newcommand{\reviewmark}{Review copy}
\else
  \newcommand{\reviewmark}{Final copy}
\fi
