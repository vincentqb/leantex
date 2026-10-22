\NeedsTeXFormat{LaTeX2e}[2022-06-01]
\ProvidesClass{ltframe}[2026/10/22 v0.1 leantex frame class]
\RequirePackage{ltkeys}
\ExplSyntaxOn
\lt_preset:nn { ltframe } { talk }
\use:e { \exp_not:N \LoadClass [ t , aspectratio = \l_lt_aspect_tl ] { \l_lt_base_tl } }
\ExplSyntaxOff
\input{ltframesource.tex}
\ExplSyntaxOn
% The stage holds sixteen lines; the body sets a line over the type scale's step.
\dim_new:N \l_lt_frameL_dim
\dim_set:Nn \l_lt_frameL_dim { \paperheight / 16 }
\cs_set_protected:Npe \normalsize
  {
    \exp_not:N \@setfontsize \exp_not:N \normalsize
      { \dim_eval:n { \l_lt_frameL_dim * 1000 / 1200 } } { \dim_use:N \l_lt_frameL_dim }
    \abovedisplayskip = \dim_eval:n { \l_lt_frameL_dim / 2 } \scan_stop:
    \belowdisplayskip = \abovedisplayskip
    \abovedisplayshortskip = \abovedisplayskip
    \belowdisplayshortskip = \abovedisplayskip
  }
\normalsize
% beamerbaselocalstructure.sty's list lengths, in the body's em.
\setlength \leftmargini { 2em }
\setlength \leftmarginii { 2em }
\setlength \leftmarginiii { 2em }
\setlength \labelsep { .5em }
\setlength \labelwidth { \leftmargini }
\addtolength \labelwidth { -\labelsep }
\lt_grid_init:
\lt_ladder:
\setbeamertemplate{headline}{}
\setbeamersize{text~margin~left=2\l_lt_frameL_dim, text~margin~right=2\l_lt_frameL_dim}
\setbeamerfont{frametitle}{size=\large,series=\bfseries}
% The title stands on the second line; every frame's body opens on the third.
\setbeamertemplate{frametitle}
  {
    \nointerlineskip
    \vbox_set_to_ht:Nnn \l_tmpa_box { 1.5\l_lt_frameL_dim }
      { \vfil \hbox { \usebeamerfont{frametitle} \usebeamercolor[fg]{frametitle} \insertframetitle } }
    \box_set_dp:Nn \l_tmpa_box { 0pt }
    \box_use_drop:N \l_tmpa_box
    { \normalsize \vskip -0.25em }
    \skip_vertical:n { -1.5\l_lt_frameL_dim }
  }
\cs_set_protected:Npn \lt_frame_topskip:
  {
    \skip_set:Nn \beamer@frametopskip { 1.5\l_lt_frameL_dim }
    \skip_set:Nn \beamer@framebottomskip { 0pt plus 1fill }
    \skip_set_eq:NN \beamer@frametopskipautobreak \beamer@frametopskip
    \skip_set_eq:NN \beamer@framebottomskipautobreak \beamer@framebottomskip
  }
\define@key { beamerframe } { t } [ true ] { \lt_frame_topskip: }
% The frame number stands on the last line, at the right margin.
\setbeamertemplate{footline}
  {
    \hbox_set:Nn \l_tmpa_box
      {
        \hbox_to_wd:nn { \paperwidth }
          {
            \skip_horizontal:n { 2\l_lt_frameL_dim }
            \footnotesize \hfil \insertframenumber
            \skip_horizontal:n { 2\l_lt_frameL_dim }
          }
      }
    \box_set_dp:Nn \l_tmpa_box { 0pt }
    \box_use:N \l_tmpa_box
    \skip_vertical:n { 0.5\l_lt_frameL_dim }
  }
% A block is its bold title over its body, a blank line around it.
\setbeamertemplate { block~begin }
  {
    \par \addvspace { \l_lt_frameL_dim }
    \tl_if_empty:NF \insertblocktitle { { \bfseries \insertblocktitle \par } }
  }
\setbeamertemplate { block~end } { \par \addvspace { \l_lt_frameL_dim } }
\setbeamertemplate { title~page }
  {
    \vspace* { 3\l_lt_frameL_dim }
    { \Large \bfseries \inserttitle \par }
    \vspace { \l_lt_frameL_dim }
    \tl_if_empty:NF \insertauthor { { \insertauthor \par } }
    \tl_if_empty:NF \insertinstitute { { \insertinstitute \par } }
    \tl_if_empty:NF \insertdate { { \insertdate \par } }
  }
% A frame's body box snaps its lines to the grid (`tex/ltgrid.lua`).
\AddToHook { env / beamer@framepauses / begin } { \lua_now:n { ltgrid.frame() } }
\AddToHook { begindocument / before }
  { \lua_now:e { ltgrid.enable(\dim_to_decimal_in_sp:n { \l_lt_L_dim }) } }
\ExplSyntaxOff
\endinput
