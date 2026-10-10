class article
page 612x792 vmargin 72 hmargin 150
section* h1
  text "tidegauge"
para
  text "A small invented tool that reads a tide gauge log and prints the day’s high and low water. Nothing here describes a real project."
section* 1
  text "Install"
verbatim language sh
  "make install PREFIX=$HOME/.local"
section* 1
  text "Use"
list ordered
  item
    para
      text "Point it at a log:"
    verbatim language sh
      "tidegauge read harbour.log"
  item
    para
      text "Ask for one day:"
    list unordered
      item
        para
          text "by date, "
          styled mono
            italicCorr maybe
            text "--day 2091-03-14"
          italicCorr maybe
          text ";"
      item
        para
          text "or by offset, "
          styled mono
            italicCorr maybe
            text "--days-ago 2"
          text "."
  item
    para
      text "Read the result, which looks like this:"
    quote
      para
        text "High water 06:10 (4.1 m), low water 12:25."
section* 1
  text "Options"
para
  text "| Option | Default | Meaning | |————–|———|——————————–| | "
  styled mono
    italicCorr maybe
    text "--day"
  italicCorr maybe
  text " | today | the day to report | | "
  styled mono
    italicCorr maybe
    text "--units"
  italicCorr maybe
  text " | metres | metres or feet | | "
  styled mono
    italicCorr maybe
    text "--quiet"
  italicCorr maybe
  text " | off | print the numbers and no words |"
section* 1
  text "Progress"
list unordered
  item
    para
      text "[x] read the log format"
  item
    para
      text "[ ] handle a missing reading"
  item
    para
      text "[ ] plot a week of readings"
para
  text "See "
  link "https://example.org/tidegauge/log-format"
    text "the log format"
  text " for the columns each line carries."
-- diagnostics
(none)
