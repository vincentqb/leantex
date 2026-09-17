# The image fixtures

`rects.png` and `rects.jpg` are synthetic: 64×40 px of flat coloured
rectangles on white, invented for this repository — no image from any real
document. They were generated on 2026-09-17 by:

- `rects.png` — a 30-line Python script (struct + zlib): 8-bit RGB, PNG
  colour type 2, non-interlaced, no pHYs chunk, one IDAT. Rectangles:
  `#3366cc` at (4,4)–(29,19), `#cc3333` at (34,10)–(59,35), `#229954` at
  (8,24)–(55,31).
- `rects.jpg` — ImageMagick 7 over the same three rectangles:
  `magick -size 64x40 xc:white -fill '#3366cc' -draw 'rectangle 4,4 29,19'
  -fill '#cc3333' -draw 'rectangle 34,10 59,35' -fill '#229954'
  -draw 'rectangle 8,24 55,31' -quality 90 tests/corpus/rects.jpg`
  (baseline JFIF, 3-component YCbCr, no declared density).

Both therefore take the engine's default density (72 ppi: one pixel is one
point), so their intrinsic size is 64 pt × 40 pt.
