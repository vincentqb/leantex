\NeedsTeXFormat{LaTeX2e}[2022-06-01]
\ProvidesClass{ltflow}[2026/10/20 v0.1 leantex flow class]
\RequirePackage{ltkeys}
\ExplSyntaxOn
\lt_preset:nn { ltflow } { article }
\bool_if:NTF \l_lt_twoside_bool
  { \use:e { \exp_not:N \LoadClass [ \l_lt_fontsize_tl , twoside ] { \l_lt_base_tl } } }
  { \use:e { \exp_not:N \LoadClass [ \l_lt_fontsize_tl , oneside ] { \l_lt_base_tl } } }
\lt_grid_init:
\cs_new_protected:Npn \lt_flow_design:
  {
    \dim_set_eq:NN \topskip \l_lt_L_dim
    \skip_set:Nn \parskip { 0pt }
    \int_set:Nn \clubpenalty { 10000 }
    \int_set:Nn \widowpenalty { 10000 }
    \int_set:Nn \displaywidowpenalty { 10000 }
    \raggedbottom
    \cs_set:Npn \@listi
      {
        \dim_set_eq:NN \leftmargin \leftmargini
        \skip_set:Nn \topsep { \l_lt_L_dim } \skip_set:Nn \partopsep { 0pt }
        \skip_set:Nn \itemsep { 0pt } \skip_set:Nn \parsep { 0pt }
      }
    \cs_set_eq:NN \@listI \@listi
    \cs_set:Npn \@listii
      {
        \dim_set_eq:NN \leftmargin \leftmarginii
        \dim_set:Nn \labelwidth { \leftmarginii - \labelsep }
        \skip_set:Nn \topsep { 0pt } \skip_set:Nn \partopsep { 0pt }
        \skip_set:Nn \itemsep { 0pt } \skip_set:Nn \parsep { 0pt }
      }
    \cs_set:Npn \@listiii
      {
        \dim_set_eq:NN \leftmargin \leftmarginiii
        \dim_set:Nn \labelwidth { \leftmarginiii - \labelsep }
        \skip_set:Nn \topsep { 0pt } \skip_set:Nn \partopsep { 0pt }
        \skip_set:Nn \itemsep { 0pt } \skip_set:Nn \parsep { 0pt }
      }
    \@listi
    \cs_set_protected:Npn \section
      { \@startsection { section } { 1 } { \z@ } { -2 \l_lt_L_dim } { \l_lt_L_dim }
          { \normalfont \Large \bfseries } }
    \cs_set_protected:Npn \subsection
      { \@startsection { subsection } { 2 } { \z@ } { -\l_lt_L_dim } { \l_lt_L_dim }
          { \normalfont \large \bfseries } }
    \cs_set_protected:Npn \subsubsection
      { \@startsection { subsubsection } { 3 } { \z@ } { -2 \l_lt_L_dim } { \l_lt_L_dim }
          { \normalfont \normalsize \bfseries } }
    \cs_set_protected:Npn \paragraph
      { \@startsection { paragraph } { 4 } { \z@ } { \l_lt_L_dim } { -1em }
          { \normalfont \normalsize \bfseries } }
    \cs_set:Npn \fps@figure { ht }
    \cs_set:Npn \fps@table { ht }
    \cs_set_eq:NN \@addtotoporbot \@addtobot
    \skip_set:Nn \intextsep { \l_lt_L_dim }
    \skip_set:Nn \floatsep { \l_lt_L_dim }
    \skip_set:Nn \textfloatsep { \l_lt_L_dim }
    \cs_set:Npn \topfraction { 1 }
    \cs_set:Npn \textfraction { 0 }
    \tex_skip:D \footins = \l_lt_L_dim \scan_stop:
    \AddToHook { begindocument / before }
      {
        \lt_ladder:
        \lt_geometry:
        \bool_if:NT \l_lt_grid_bool
          { \lua_now:e { ltgrid.enable(\dim_to_decimal_in_sp:n { \l_lt_L_dim }) } }
      }
  }
\lt_flow_design:
\cs_new_protected:Npn \ltflowsource #1#2
  { \bool_lazy_or:nnT { \str_if_eq_p:nn {#1} { all } } { \str_if_eq_p:Vn \l_lt_preset_tl {#1} } {#2} }
\ExplSyntaxOff
\input{ltflowsource.tex}
\def\@maketitle{%
  {\centering
   {\LARGE\bfseries\@title\par}%
   {\@author\par}%
   {\@date\par}}}
\providecommand\abstractname{Abstract}
\@ifundefined{abstract}{\newenvironment{abstract}}{\renewenvironment{abstract}}{%
  \par{\centering\small\bfseries\abstractname\par}%
  \small\list{}{\topsep\z@\partopsep\z@\itemsep\z@\parsep\z@
    \listparindent1.5em\itemindent\z@\rightmargin\leftmargin}\item\relax}
  {\endlist}
\endinput
