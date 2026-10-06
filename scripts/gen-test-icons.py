"""Build testdata/corpus/fonts/ExampleIcons-Regular.ttf: an invented icon face
for the leantex test corpus. Five simple geometric glyphs (invented shapes,
drawn here, no outlines copied from any icon font) at the Font Awesome 5
Free codepoints the fixtures reference:

  U+F062 arrow-up        triangle over a stem
  U+F09B github          circle (drawn as an octagon)
  U+F08C linkedin        square with a notch
  U+F0E0 envelope        rectangle with a V fold
  U+F19D graduation-cap  flat diamond over a bar

The codepoints come from fontawesome5-mapping.def (CTAN); the shapes are
original and trivial. Licence: CC0 (see LICENSE-ExampleIcons.txt).

Run: /tmp/fontenv/bin/python scripts/gen-test-icons.py   (needs fontTools)
"""
from fontTools.fontBuilder import FontBuilder
from fontTools.pens.ttGlyphPen import TTGlyphPen

UPM = 1000

def arrow_up(pen):
    pen.moveTo((500, 900)); pen.lineTo((150, 500)); pen.lineTo((350, 500))
    pen.lineTo((350, 100)); pen.lineTo((650, 100)); pen.lineTo((650, 500))
    pen.lineTo((850, 500)); pen.closePath()

def octagon(pen):
    pen.moveTo((350, 900)); pen.lineTo((650, 900)); pen.lineTo((900, 650))
    pen.lineTo((900, 350)); pen.lineTo((650, 100)); pen.lineTo((350, 100))
    pen.lineTo((100, 350)); pen.lineTo((100, 650)); pen.closePath()

def notched_square(pen):
    pen.moveTo((100, 900)); pen.lineTo((900, 900)); pen.lineTo((900, 100))
    pen.lineTo((500, 100)); pen.lineTo((500, 400)); pen.lineTo((100, 400))
    pen.closePath()

def envelope(pen):
    pen.moveTo((100, 800)); pen.lineTo((900, 800)); pen.lineTo((500, 450))
    pen.closePath()
    pen.moveTo((100, 700)); pen.lineTo((450, 400)); pen.lineTo((100, 200))
    pen.closePath()
    pen.moveTo((900, 700)); pen.lineTo((900, 200)); pen.lineTo((550, 400))
    pen.closePath()

def cap(pen):
    pen.moveTo((500, 900)); pen.lineTo((950, 650)); pen.lineTo((500, 400))
    pen.lineTo((50, 650)); pen.closePath()
    pen.moveTo((250, 450)); pen.lineTo((750, 450)); pen.lineTo((750, 150))
    pen.lineTo((250, 150)); pen.closePath()

GLYPHS = {
    "arrowup": (0xF062, arrow_up),
    "github": (0xF09B, octagon),
    "linkedin": (0xF08C, notched_square),
    "envelope": (0xF0E0, envelope),
    "graduationcap": (0xF19D, cap),
}

def main():
    fb = FontBuilder(UPM, isTTF=True)
    order = [".notdef", "space"] + sorted(GLYPHS)
    fb.setupGlyphOrder(order)
    cmap = {0x20: "space"}
    glyphs = {}
    pen = TTGlyphPen(None)
    pen.moveTo((50, 0)); pen.lineTo((50, 700)); pen.lineTo((950, 700))
    pen.lineTo((950, 0)); pen.closePath()
    glyphs[".notdef"] = pen.glyph()
    empty = TTGlyphPen(None)
    glyphs["space"] = empty.glyph()
    for name, (cp, draw) in GLYPHS.items():
        pen = TTGlyphPen(None)
        draw(pen)
        glyphs[name] = pen.glyph()
        cmap[cp] = name
    fb.setupCharacterMap(cmap)
    fb.setupGlyf(glyphs)
    metrics = {n: (1000, 50) for n in order}
    metrics["space"] = (500, 0)
    fb.setupHorizontalMetrics(metrics)
    fb.setupHorizontalHeader(ascent=800, descent=-200)
    fb.setupNameTable({
        "familyName": "Example Icons",
        "styleName": "Regular",
        "fullName": "Example Icons Regular",
        "psName": "ExampleIcons-Regular",
        "copyright": "Invented for the leantex test corpus; CC0.",
    })
    fb.setupOS2(sTypoAscender=800, sTypoDescender=-200, usWinAscent=900,
                usWinDescent=200)
    fb.setupPost()
    fb.save("testdata/corpus/fonts/ExampleIcons-Regular.ttf")
    print("wrote testdata/corpus/fonts/ExampleIcons-Regular.ttf")

if __name__ == "__main__":
    main()
