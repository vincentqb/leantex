\NeedsTeXFormat{LaTeX2e}[2022-06-01]
\ProvidesClass{ltframe}[2026/10/22 v0.1 leantex frame class]
\RequirePackage{ltkeys}
\ExplSyntaxOn
\lt_preset:nn { ltframe } { talk }
\use:e { \exp_not:N \LoadClass [ t , aspectratio = \l_lt_aspect_tl ] { \l_lt_base_tl } }
\ExplSyntaxOff
\input{ltframesource.tex}
\ExplSyntaxOn
% The stage holds sixteen lines; the body sets a line over the type scale's step, two lines in from
% either side, half a line from the top, an untitled frame keeping its title's line.
\dim_set:Nn \l_lt_frameL_dim { \paperheight / 16 }
\dim_set:Nn \l_lt_framesize_dim { \l_lt_frameL_dim * 1000 / 1200 }
\dim_set:Nn \l_lt_frameside_dim { 2 \l_lt_frameL_dim }
\dim_set:Nn \l_lt_frametop_dim { \l_lt_frameL_dim / 2 }
\dim_set_eq:NN \l_lt_frameband_dim \l_lt_frameL_dim
\cs_set_nopar:Npn \ltdepth { decks }
\ExplSyntaxOff
\input{ltgridframe.tex}
\ExplSyntaxOn
\msg_new:nnn { ltframe } { size } { class~option~#1~sets~nothing;~the~ltframe~class's~body~follows~its~stage }
\tl_if_empty:NF \l_lt_fontsize_tl { \msg_warning:nnV { ltframe } { size } \l_lt_fontsize_tl }
% The frame number stands on the last line, at the right margin.
\setbeamertemplate{footline}
  {
    \hbox_set:Nn \l_tmpa_box
      {
        \hbox_to_wd:nn { \paperwidth }
          {
            \skip_horizontal:n { \beamer@leftmargin }
            \footnotesize \hfil \insertframenumber
            \skip_horizontal:n { \beamer@rightmargin }
          }
      }
    \box_set_dp:Nn \l_tmpa_box { 0pt }
    \box_use:N \l_tmpa_box
    \skip_vertical:n { 0.5\l_lt_frameL_dim }
  }
\msg_new:nnn { ltframe } { stage }
  { '\iow_char:N\\page\iow_char:N\{~#1~\iow_char:N\}'~sets~the~paper;~the~ltframe~class's~stage~is~its~aspect's }
\keys_define:nn { lt / page }
  {
    size .code:n = \msg_warning:nnn { ltframe } { stage } { size~=~#1 } ,
    width .code:n = \msg_warning:nnn { ltframe } { stage } { width~=~#1 } ,
    height .code:n = \msg_warning:nnn { ltframe } { stage } { height~=~#1 } ,
  }
\ExplSyntaxOff
\endinput
