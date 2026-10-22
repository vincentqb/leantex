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
% Titles set at the step above the body, solid on the grid's leading; a break fills the frame.
\setbeamerfont{frametitle}
  { size = \fontsize { \dim_use:N \l_lt_frameL_dim } { \dim_use:N \l_lt_frameL_dim } , series = \bfseries }
\define@key { beamerframe } { allowframebreaks } [ 1 ]
  { \cs_set:Npn \beamer@autobreakfactor {#1} \beamer@autobreaktrue }
% The title stands on the second line, its subtitle on the third, the body on the line after both,
% a line further below a coloured band.
\box_new:N \l__lt_title_box
\dim_new:N \l__lt_drop_dim
\dim_new:N \l__lt_band_dim
\cs_new_protected:Npn \lt_frame_title:
  {
    \raggedright \usebeamerfont{frametitle}
    \leavevmode \usebeamercolor[fg]{frametitle} \insertframetitle \par
    \tl_if_empty:NF \insertframesubtitle
      {
        \usebeamerfont{framesubtitle}
        \leavevmode \usebeamercolor[fg]{framesubtitle} \insertframesubtitle \par
      }
  }
\setbeamertemplate{frametitle}
  {
    \nointerlineskip
    \vbox_set_top:Nn \l__lt_title_box { \lt_frame_title: }
    \dim_set:Nn \l__lt_drop_dim { 1.5\l_lt_frameL_dim - \box_ht:N \l__lt_title_box }
    \vbox_set:Nn \l__lt_title_box { \lt_frame_title: }
    % A band colour paints the title's band, to half a leading below its last line.
    \ifbeamercolorempty [ bg ] { frametitle } { }
      {
        \dim_set:Nn \l__lt_band_dim
          { \l__lt_drop_dim + \box_ht:N \l__lt_title_box + 0.5\l_lt_frameL_dim }
        \hbox_set:Nn \l_tmpb_box
          {
            \skip_horizontal:n { -\beamer@leftmargin }
            \usebeamercolor [ bg ] { frametitle }
            \rule [ -\l__lt_band_dim ] { \paperwidth } { \l__lt_band_dim }
          }
        \box_set_ht:Nn \l_tmpb_box { 0pt }
        \box_set_dp:Nn \l_tmpb_box { 0pt }
        \box_use_drop:N \l_tmpb_box
        \nointerlineskip
      }
    \skip_vertical:n { \l__lt_drop_dim }
    \box_set_dp:Nn \l__lt_title_box { 0pt }
    \box_use_drop:N \l__lt_title_box
    { \normalsize \vskip -0.25em }
    \skip_vertical:n { -1.5\l_lt_frameL_dim }
    \ifbeamercolorempty [ bg ] { frametitle } { } { \skip_vertical:n { \l_lt_frameL_dim } }
  }
\cs_set_protected:Npn \lt_frame_topskip:
  {
    \skip_set:Nn \beamer@frametopskip { 1.5\l_lt_frameL_dim }
    \skip_set:Nn \beamer@framebottomskip { 0pt plus 1fill }
    \skip_set_eq:NN \beamer@frametopskipautobreak \beamer@frametopskip
    \skip_set_eq:NN \beamer@framebottomskipautobreak \beamer@framebottomskip
  }
\define@key { beamerframe } { t } [ true ] { \lt_frame_topskip: }
\define@key { beamerframe } { c } [ true ] { \lt_frame_topskip: }
\define@key { beamerframe } { b } [ true ] { \lt_frame_topskip: }
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
% A block is its bold title over its body, a blank line around it.
\setbeamertemplate { block~begin }
  {
    \par \addvspace { \l_lt_frameL_dim }
    \tl_if_empty:NF \insertblocktitle { { \bfseries \insertblocktitle \par } }
  }
\setbeamertemplate { block~end } { \par \addvspace { \l_lt_frameL_dim } }
\setbeamertemplate { block~alerted~begin } { \usebeamertemplate { block~begin } }
\setbeamertemplate { block~alerted~end } { \usebeamertemplate { block~end } }
\setbeamertemplate { block~example~begin } { \usebeamertemplate { block~begin } }
\setbeamertemplate { block~example~end } { \usebeamertemplate { block~end } }
\setbeamertemplate { title~page }
  {
    \vspace* { 3\l_lt_frameL_dim }
    { \raggedright \Large \bfseries \inserttitle \par }
    \tl_if_empty:NF \insertsubtitle { { \raggedright \insertsubtitle \par } }
    \vspace { \l_lt_frameL_dim }
    \tl_if_empty:NF \insertauthor { { \insertauthor \par } }
    \tl_if_empty:NF \insertinstitute { { \insertinstitute \par } }
    \tl_if_empty:NF \insertdate { { \insertdate \par } }
  }
% A frame's body box snaps its lines to the grid (`tex/ltgrid.lua`).
\AddToHook { env / beamer@framepauses / begin } { \lua_now:n { ltgrid.frame() } }
\AddToHook { env / beamer@framepauses / end } { \lua_now:n { ltgrid.main() } }
\msg_new:nnn { ltframe } { stage }
  { '\iow_char:N\\page\iow_char:N\{~#1~\iow_char:N\}'~sets~the~paper;~the~ltframe~class's~stage~is~its~aspect's }
\keys_define:nn { lt / page }
  {
    size .code:n = \msg_warning:nnn { ltframe } { stage } { size~=~#1 } ,
    width .code:n = \msg_warning:nnn { ltframe } { stage } { width~=~#1 } ,
    height .code:n = \msg_warning:nnn { ltframe } { stage } { height~=~#1 } ,
  }
% A declared paper is refused, as the grid is the aspect's; declared side margins are the text's.
\AddToHook { begindocument / before }
  {
    \bool_if:NT \l_lt_hmargin_bool
      { \setbeamersize { text~margin~left = \l_lt_hmargin_dim , text~margin~right = \l_lt_hmargin_dim } }
  }
\AddToHook { begindocument / before }
  { \lua_now:e { ltgrid.enable(\dim_to_decimal_in_sp:n { \l_lt_L_dim }) } }
\ExplSyntaxOff
\endinput
