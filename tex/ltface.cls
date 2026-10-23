\NeedsTeXFormat{LaTeX2e}[2022-06-01]
\ProvidesClass{ltface}[2026/10/22 v0.1 leantex face class]
\RequirePackage{ltkeys}
\ExplSyntaxOn
\lt_preset:nn { ltface } { poster }
\use:e { \exp_not:N \LoadClass [ t ] { \l_lt_base_tl } }
% One face per frame at the preset's trim, its safe margin on every side.
\geometry
  {
    paperwidth = \dim_use:N \l_lt_paperwidth_dim , paperheight = \dim_use:N \l_lt_paperheight_dim ,
    hmargin = \dim_use:N \l_lt_hmargin_dim , vmargin = 0pt , head = 0pt , headsep = 0pt , foot = 0pt
  }
\ExplSyntaxOff
\input{ltfacesource.tex}
\ExplSyntaxOn
% A size option sets the body, the last one given.
\clist_map_inline:cn { @raw@opt@ltface.cls }
  {
    \tl_set:Ne \l_tmpa_tl { \tl_trim_spaces:n {#1} }
    \regex_match:nVT { \A \d+ pt \Z } \l_tmpa_tl { \tl_set_eq:NN \l_lt_fontsize_tl \l_tmpa_tl }
  }
% The body at its size, each line a leading of 1.2 of it; the title line kept by a talk alone.
\dim_set:Nn \l_lt_framesize_dim
  {
    \str_case:VnF \l_lt_fontsize_tl
      { { 10pt } { 10pt } { 11pt } { 10.95pt } { 12pt } { 12pt } }
      { \l_lt_fontsize_tl }
  }
\dim_set:Nn \l_lt_frameL_dim { 1.2 \l_lt_framesize_dim }
\dim_set_eq:NN \l_lt_frameside_dim \l_lt_hmargin_dim
\dim_set_eq:NN \l_lt_frametop_dim \l_lt_vmargin_dim
\dim_zero:N \l_lt_frameband_dim
\ExplSyntaxOff
\input{ltgridframe.tex}
\ExplSyntaxOn
% A face carries no frame number; its footline keeps the bottom margin clear.
\setbeamertemplate{footline} { \skip_vertical:n { \l_lt_vmargin_dim } }
% A poster's columns: the count whose column holds nearest its measure in characters of Latin Modern
% Sans within 60 to 75, two leadings between them; a column spans the whole columns nearest its width.
\fp_new:N \l__lt_key_fp
\cs_new:Npn \__lt_chars:n #1
  {
    \fp_eval:n
      {
        trunc ( 450 + 200 * ( #1 - ( 1.415 * \l__lt_alpha_fp + 23.03 ) )
          / ( ( 2.042 - 1.415 ) * \l__lt_alpha_fp + 33.41 - 23.03 ) )
      }
  }
\fp_new:N \l__lt_alpha_fp
\cs_new_protected:Npn \lt_face_columns:
  {
    \fp_set:Nn \l__lt_alpha_fp { 11.965 * \dim_to_fp:n { \l_lt_framesize_dim } }
    \dim_set:Nn \l__lt_gutter_dim { 2 \l_lt_frameL_dim }
    \fp_set:Nn \l__lt_key_fp { inf }
    \int_step_inline:nnn { 1 } { 12 }
      {
        \fp_set:Nn \l_tmpa_fp
          {
            ( \dim_to_fp:n { \paperwidth - 2 \l_lt_frameside_dim } - ( ##1 - 1 )
              * \dim_to_fp:n { \l__lt_gutter_dim } ) / ##1
          }
        \fp_compare:nNnT { \l_tmpa_fp } > { 0 }
          {
            \fp_set:Nn \l_tmpb_fp { \__lt_chars:n { \l_tmpa_fp } }
            \fp_set:Nn \l_tmpb_fp
              {
                ( \l_tmpb_fp >= 600 && \l_tmpb_fp <= 750 ? 0 : 100000 )
                  + abs ( \l_tmpb_fp - 10 * \l_lt_measure_int )
              }
            \fp_compare:nNnT { \l_tmpb_fp } < { \l__lt_key_fp }
              {
                \fp_set_eq:NN \l__lt_key_fp \l_tmpb_fp
                \int_set:Nn \l__lt_cols_int { ##1 }
                \dim_set:Nn \l__lt_colw_dim { \fp_to_dim:n { \l_tmpa_fp } }
              }
          }
      }
  }
% A declared paper or margin sets the face; the columns follow the text width it leaves.
\AddToHook { begindocument / before }
  {
    \geometry
      {
        paperwidth = \dim_use:N \l_lt_paperwidth_dim ,
        paperheight = \dim_use:N \l_lt_paperheight_dim
      }
    \int_compare:nNnT { \l_lt_measure_int } > { 0 } { \lt_face_columns: }
  }
\ExplSyntaxOff
\endinput
