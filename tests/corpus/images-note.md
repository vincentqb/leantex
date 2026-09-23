# The image fixtures

This note is documentation for the image files beside it, not a document
fixture: it is excluded from the golden set, and nothing elaborates it.

`rects.png`, `rects.jpg`, and `rects-alpha.png` are synthetic: flat
coloured rectangles invented for this repository — no image from any real
document. They were generated on 2026-09-17 by:

- `rects.png` — a 30-line Python script (struct + zlib): 64×40 px, 8-bit
  RGB, PNG colour type 2, non-interlaced, no pHYs chunk, one IDAT.
  Rectangles: `#3366cc` at (4,4)–(29,19), `#cc3333` at (34,10)–(59,35),
  `#229954` at (8,24)–(55,31), on white.
- `rects.jpg` — ImageMagick 7 over the same three rectangles:
  `magick -size 64x40 xc:white -fill '#3366cc' -draw 'rectangle 4,4 29,19'
  -fill '#cc3333' -draw 'rectangle 34,10 59,35' -fill '#229954'
  -draw 'rectangle 8,24 55,31' -quality 90 tests/corpus/rects.jpg`
  (baseline JFIF, 3-component YCbCr, no declared density).
- `rects-alpha.png` — the same script shape: 48×32 px, 8-bit RGBA, PNG
  colour type 6, one `#3366cc` rectangle at (4,4)–(43,27) whose alpha fades
  from 255 to 15 left to right, on a fully transparent background.

All take the engine's default density (72 ppi: one pixel is one point), so
`rects.png`/`rects.jpg` are intrinsically 64 pt × 40 pt and
`rects-alpha.png` is 48 pt × 32 pt.
