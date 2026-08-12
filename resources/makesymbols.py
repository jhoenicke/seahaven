#!/usr/bin/env python3
#
# Regenerate the card <symbol> definitions embedded in static/online.html.
#
# The card artwork comes from RevK's SVG-playing-cards project
# (https://github.com/revk/SVG-playing-cards, checked out in
# resources/SVG-playing-cards).  That project builds each card as a
# standalone SVG file with a C tool (makecourt extracts the Inkscape
# layers from svg/*.svg into court.h, makecards composes the cards).
# This script replicates that pipeline in Python and emits the cards as
# a shared <symbol> library, the way online.html uses them:
#
#   - one pip symbol per suit (SC/SD/SH/SS) and one value glyph per
#     rank (V2..VT/VJ/VQ/VK/VA) instead of one per suit+value pair,
#     with the index stroke colour moved to the <use> site,
#   - the court artwork layers as {suit}{value}{layer} symbols
#     (e.g. CJ1..CJ6), extracted from SVG-playing-cards/svg/??.svg,
#   - each complete card as symbol c1..c52 (card = suit*13 + value,
#     suits D,H,S,C, values A=1..K=13) in the 240x336 default geometry
#     of makecards with --no-width-on-use.
#
# Everything mirrors the C tool's integer arithmetic so the output is
# byte-identical with what the tool produces.  Game-specific symbols
# (e, e0-e3, hl) are not generated here.
#
# Usage: makesymbols.py [--update FILE]
#   Without arguments the symbol block (including the <defs> with the
#   court border rect) is written to stdout.  With --update the block
#   is spliced into FILE (typically ../static/online.html), replacing
#   the section between '<svg id="board"' and '<symbol id="e"'.

import re
import sys
import os

SVGDIR = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                      "SVG-playing-cards", "svg")

THO = 1000

# makecards defaults (topmargin defaults to margin)
W, H = 240, 336
PH, VH = 70, 32
MARGIN, TOPMARGIN, CORNER = 12, 12, 12
PIPMARGIN, COURTMARGIN = 5, 2
FONTSIZE = 20

# Suit order of the tool ("SHCD") with the standard two-colour deck.
COLOUR = {"S": "black", "H": "red", "C": "black", "D": "red"}

# pip_path[1] ("New" style), from makecards.c: path, width, height
PIP_PATH = {
    "S": ("M0 -500C100 -250 355 -100 355 185A150 150 0 0 1 55 185A10 10 0 0 0 35 185C35 385 85 400 130 500L-130 500C-85 400 -35 385 -35 185A10 10 0 0 0 -55 185A150 150 0 0 1 -355 185C-355 -100 -100 -250 0 -500Z", 710, 1000),
    "H": ("M0 -300C0 -400 100 -500 200 -500C300 -500 400 -400 400 -250C400 0 0 400 0 500C0 400 -400 0 -400 -250C-400 -400 -300 -500 -200 -500C-100 -500 0 -400 -0 -300Z", 800, 1000),
    "C": ("M30 150C35 385 85 400 130 500L-130 500C-85 400 -35 385 -30 150A10 10 0 0 0 -50 150A210 210 0 1 1 -124 -51A10 10 0 0 0 -110 -65A230 230 0 1 1 110 -65A10 10 0 0 0 124 -51A210 210 0 1 1 50 150A10 10 0 0 0 30 150Z", 933, 997),
    "D": ("M-400 0C-350 0 0 -450 0 -500C0 -450 350 0 400 0C350 0 0 450 0 500C0 450 -350 0 -400 0Z", 800, 1000),
}

# value_path[0] ("Standard" style), stroke width 80 for all
VALUE_PATH = {
    "2": "M-225 -225C-245 -265 -200 -460 0 -460C 200 -460 225 -325 225 -225C225 -25 -225 160 -225 460L225 460L225 300",
    "3": "M-250 -320L-250 -460L200 -460L-110 -80C-100 -90 -50 -120 0 -120C200 -120 250 0 250 150C250 350 170 460 -30 460C-230 460 -260 300 -260 300",
    "4": "M50 460L250 460M150 460L150 -460L-300 175L-300 200L270 200",
    "5": "M170 -460L-175 -460L-210 -115C-210 -115 -200 -200 0 -200C100 -200 255 -80 255 120C255 320 180 460 -20 460C-220 460 -255 285 -255 285",
    "6": "M-250 100A250 250 0 0 1 250 100L250 210A250 250 0 0 1 -250 210L-250 -210A250 250 0 0 1 0 -460C150 -460 180 -400 200 -375",
    "7": "M-265 -320L-265 -460L265 -460C135 -200 -90 100 -90 460",
    "8": "M-1 -50A205 205 0 1 1 1 -50L-1 -50A255 255 0 1 0 1 -50Z",
    "9": "M250 -100A250 250 0 0 1 -250 -100L-250 -210A250 250 0 0 1 250 -210L250 210A250 250 0 0 1 0 460C-150 460 -180 400 -200 375",
    "A": "M-270 460L-110 460M-200 450L0 -460L200 450M110 460L270 460M-120 130L120 130",
    "J": "M50 -460L250 -460M150 -460L150 250A100 100 0 0 1 -250 250L-250 220",
    "Q": "M-260 100C40 100 -40 460 260 460M-175 0L-175 -285A175 175 0 0 1 175 -285L175 285A175 175 0 0 1 -175 285Z",
    "K": "M-285 -460L-85 -460M-185 -460L-185 460M-285 460L-85 460M85 -460L285 -460M185 -440L-170 155M85 460L285 460M185 440L-10 -70",
    "T": "M-260 430L-260 -430M-50 0L-50 -310A150 150 0 0 1 250 -310L250 310A150 150 0 0 1 -50 310Z",
}

# Extra flourish appended to the King of Hearts stroke layer (the axe),
# from makecards.c (non-mirrored variant).
KH_STROKE_EXTRA = "M1020,185l-25,30 30,25M975.9082,215H995m-35,25 35,-55v55"

# Pip placement on court cards, from makecourt.c: (x, y, size, rotate[, border])
COURT_PIPS = {
    "JS": [(910, 1454, 75, 35), (845, 1359, 75, 33), (780, 1261, 75, 33)],
    "QS": [(1188, 1065, 90, -40), (1194, 957, 90, -40), (1096, 967, 90, -40),
           (1022, 1053, 90, -40), (918, 1149, 90, -40), (897, 1274, 90, -40)],
    "KS": [(495, 1388, 90, -10), (528, 1249, 90, -5), (839, 1360, 90, 20),
           (795, 1251, 90, 20)],
    "JH": [(546, 1000, 100, 0), (615, 1000, 100, 180), (883, 1224, 75, 30),
           (915, 1289, 75, 30), (954, 1354, 75, 30), (220, 1367, 75, 60),
           (155, 1272, 75, 60), (52, 1272, 75, 60), (96, 1175, 75, 60)],
    "QH": [(967, 812, 75, 30), (1013, 933, 75, 15), (1041, 1058, 75, 3),
           (1054, 1184, 75, 5), (1068, 1301, 75, 10)],
    "KH": [(988, 1199, 90, 85), (958, 1298, 90, 60), (975, 1089, 90, 110),
           (922, 997, 90, 130)],
    "JC": [(504, 1272, 75, 0), (504, 1156, 75, 0), (826, 1357, 75, 0)],
    "QC": [(1017, 1099, 90, -45), (1125, 1022, 90, -45), (1229, 940, 90, -45)],
    "KC": [(893, 1141, 90, 5), (927, 1279, 90, 15), (992, 1399, 90, 25)],
    "JD": [(650, 1000, 200, 0, 1), (894, 1402, 50, -26), (852, 1377, 50, -22),
           (806, 1361, 50, -14), (757, 1350, 50, -6), (706, 1345, 50, 0),
           (656, 1347, 50, 5), (607, 1353, 50, 10), (560, 1363, 50, 15)],
    "QD": [(650, 1000, 100, 0, 1), (580, 995, 100, 0, 1), (510, 990, 100, 0, 1)],
    "KD": [(650, 1000, 120, 0), (570, 1000, 120, 0), (400, 1360, 170, -15, 1),
           (435, 1235, 150, -10, 1), (453, 1115, 130, -5, 1), (460, 1018, 110, 0, 1),
           (450, 930, 100, 10, 1), (1259, 1000, 90, 60), (1173, 948, 90, 50),
           (1094, 880, 90, 40), (1038, 791, 90, 30)],
}

# Court layers in the order makecards emits them: (Inkscape label, colour)
COURT_LAYERS = [("Gold", "#FC4"), ("Red", "red"), ("Blue", "#44F"),
                ("Black", "black"), ("Stroke", "#44F"), ("Thin", "#44F")]

# Game card numbering: card = suit*13 + value, value 1(A)..13(K)
GAME_SUITS = "DHSC"
GAME_VALUES = "A23456789TJQK"


def cdiv(a, b):
    """C integer division (truncation toward zero)."""
    q = abs(a) // abs(b)
    if (a < 0) != (b < 0):
        q = -q
    return q


def tho(v):
    """Format thousandths the way makecards' stho() does."""
    s = "-" if v < 0 else ""
    v = abs(v)
    t = s + str(v // 1000)
    v %= 1000
    if v % 10:
        t += ".%03d" % v
    elif v % 100:
        t += ".%02d" % (v // 10)
    elif v:
        t += ".%d" % (v // 100)
    return t


def pipwidth(suit, ph):
    return cdiv(PIP_PATH[suit][1] * ph, 1200)


def pipheight(suit, ph):
    return cdiv(PIP_PATH[suit][2] * ph, 1200)


# ---------------------------------------------------------------------------
# Court layer extraction (replicates makecourt.c)

def compact_path(d):
    """Drop the space after a command letter or between a number and the
    following command letter, exactly like makecourt's compaction loop."""
    out = []
    i = 0
    n = len(d)

    def at(j):
        return d[j] if j < n else "\0"

    while i < n:
        c = d[i]
        if (c.isalpha() and at(i + 1).isspace()) or \
           (c.isdigit() and at(i + 1).isspace() and at(i + 2).isalpha()):
            out.append(c)
            i += 2
        else:
            out.append(c)
            i += 1
    return "".join(out)


def extract_layers(svgfile, wanted):
    """Return {label: pathdata} for the wanted Inkscape layers of one card."""
    import xml.etree.ElementTree as ET
    tree = ET.parse(svgfile)
    layers = {}
    for g in tree.iter():
        if not g.tag.endswith("}g") and g.tag != "g":
            continue
        label = None
        for k, v in g.attrib.items():
            if k.endswith("}label") or k == "label":
                label = v
        if label not in wanted or label in layers:
            continue
        parts = []
        for p in g.iter():
            if not (p.tag.endswith("}path") or p.tag == "path"):
                continue
            assert "transform" not in p.attrib, \
                f"Transform found on path in {label} in {svgfile}"
            d = p.get("d")
            if not d:
                continue
            if d.startswith("m "):
                # Inkscape relative start: first space becomes 'l'
                q = d.find(" ", 2)
                if q >= 0 and not d[q + 1].isalpha():
                    d = d[:q] + "l" + d[q + 1:]
                d = "M" + d[1:]
            parts.append(compact_path(d))
        if parts:
            layers[label] = "".join(parts)
    return layers


# ---------------------------------------------------------------------------
# Geometry (replicates makecards.c with default options + --no-width-on-use)

def makebox():
    bw = THO * W - THO * MARGIN * 2 - cdiv(THO * VH * 8, 5)
    bh = THO * H - THO * TOPMARGIN * 2 - cdiv(THO * VH * 8, 5)
    return bw, bh


class Card:
    """One composed card symbol (replicates makecard())."""

    def __init__(self, suit, value):
        self.suit = suit                     # 'D','H','S','C'
        self.value = value                   # 'A','2'..'9','T','J','Q','K'
        self.bw, self.bh = makebox()
        self.parts = []

    def pip(self, x, y, h):
        x -= cdiv(h, 2)
        y -= cdiv(h, 2)
        self.parts.append(f'<use xlink:href="#S{self.suit}" height="{tho(h)}" '
                          f'x="{tho(x)}" y="{tho(y)}"></use>')

    def value_index(self):
        y = -cdiv(THO * H, 2) + THO * max(TOPMARGIN, CORNER)
        self.parts.append(f'<use xlink:href="#V{self.value}" '
                          f'stroke="{COLOUR[self.suit]}" height="{tho(THO * VH)}" '
                          f'x="{tho(-cdiv(THO * W, 2) + THO * MARGIN - cdiv(THO * VH, 5))}" '
                          f'y="{tho(y)}"></use>')
        # suit pip below the value, sized to the same width as the value
        ph2 = cdiv(cdiv(THO * VH * 65, 100) * THO, pipwidth("C", THO))
        y += THO * PIPMARGIN + cdiv(ph2, 2) + THO * VH
        self.pip(-cdiv(THO * W, 2) + THO * MARGIN - cdiv(THO * VH, 5) + cdiv(THO * VH, 2),
                 y, ph2)

    def court_pip(self):
        y = cdiv(self.bh, 2) - cdiv(self.bh * 10, 100)
        sx = cdiv(self.bw * 35, 100)
        if self.bh < cdiv(self.bw * 20, 13):
            sx = cdiv(cdiv(sx * self.bh * 13, self.bw), 20)
        sx -= THO * COURTMARGIN
        x = cdiv(self.bw, 2) - pipwidth(self.suit, cdiv(sx, 2)) - THO * COURTMARGIN
        rightpip = ((self.value == "Q" and self.suit != "H") or
                    (self.value == "J" and self.suit != "S"))
        if not rightpip:
            x = -x
        self.pip(x, -y, sx)

    def side2(self, y):
        """Half of the pips of a number card (side2() in makecards.c)."""
        v = self.value
        px = self.px
        if v in "456789T":
            self.pip(-px, y, THO * PH)
            self.pip(px, y, THO * PH)
        if v in "9T":
            self.pip(-px, cdiv(y, 3), THO * PH)
            self.pip(px, cdiv(y, 3), THO * PH)
        if v in "23":
            self.pip(0, y, THO * PH)
        if v == "8":
            self.pip(0, cdiv(y, 2), THO * PH)
        if v == "T":
            self.pip(0, cdiv(y * 2, 3), THO * PH)

    def side(self):
        """Indices plus one half of the pips (side() in makecards.c)."""
        self.value_index()
        if self.value in "JQK":
            self.court_pip()
        else:
            self.side2(-self.py)

    def build(self):
        n = GAME_SUITS.index(self.suit) * 13 + GAME_VALUES.index(self.value) + 1
        p = self.parts
        p.append(f'    <symbol id="c{n}" viewBox="{tho(-cdiv(THO * W, 2))} '
                 f'{tho(-cdiv(THO * H, 2))} {tho(THO * W)} {tho(THO * H)}">')
        # card background and border
        p.append(f'<rect width="{tho(THO * W - THO)}" height="{tho(THO * H - THO)}" '
                 f'x="{tho(-cdiv(THO * W, 2) + cdiv(THO, 2))}" '
                 f'y="{tho(-cdiv(THO * H, 2) + cdiv(THO, 2))}" '
                 f'rx="{tho(THO * CORNER)}" ry="{tho(THO * CORNER)}" '
                 f'fill="white" stroke="black"></rect>')
        # pip grid positions
        px = cdiv(THO * W, 2) - THO * MARGIN - cdiv(THO * VH * 2, 3)
        py = cdiv(THO * H, 2) - THO * TOPMARGIN - cdiv(THO * VH * 2, 3)
        px = min(px, cdiv(THO * W, 2) - cdiv(THO * PH, 3))
        py = min(py, cdiv(THO * H, 2) - cdiv(THO * PH, 3))
        px -= cdiv(THO * PH * 5, 12) + THO * PIPMARGIN
        py -= pipheight(self.suit, cdiv(THO * PH, 2)) + THO * PIPMARGIN
        self.px, self.py = px, py

        if self.value in "JQK":
            # court artwork, each layer straight and rotated
            for layer in range(1, 7):
                for flip in ("", 'transform="rotate(180)" '):
                    p.append(f'<use {flip}width="{tho(self.bw)}" '
                             f'height="{tho(self.bh)}" x="{tho(-cdiv(self.bw, 2))}" '
                             f'y="{tho(-cdiv(self.bh, 2))}" '
                             f'xlink:href="#{self.suit}{self.value}{layer}"></use>')
        if self.value == "A":
            if self.suit == "S":
                # Ace of spades: large pip with the traditional maker's mark.
                # Only the mark is a link; the pip must stay clickable as a
                # card.
                aw = self.bw
                p.append(f'<use xlink:href="#SS" height="{tho(aw)}" '
                         f'x="{tho(-cdiv(aw, 2))}" y="{tho(-cdiv(aw, 2))}"></use>')
                p.append('<a href="https://www.me.uk/cards">')
                for i, line in enumerate(("www.me.uk", "/cards/")):
                    y = cdiv(self.bh, 2) - cdiv(THO * FONTSIZE * (3 - 2 * i), 2)
                    p.append(f'<text font-size="{FONTSIZE}" font-family="Bariol" '
                             f'fill="black" text-anchor="middle" '
                             f'y="{tho(y)}">{line}</text>')
                p.append('</a>')
            else:
                self.pip(0, 0, THO * PH)
        self.side()
        # centre pips (between the two rotated halves)
        v = self.value
        if v == "9" and self.suit == "C":
            self.pip(0, cdiv(-THO * PH, 10), THO * PH)
        elif v in "359":
            self.pip(0, 0, THO * PH)
        if v in "678":
            self.pip(-px, 0, THO * PH)
            self.pip(px, 0, THO * PH)
        if v == "7":
            self.pip(0, cdiv(-py, 2), THO * PH)
        # the same indices and pips, rotated
        p.append('<g transform="rotate(180)">')
        self.side()
        p.append('</g>')
        if v in "JQK":
            p.append('<use xlink:href="#X" stroke="#44F" fill="none"></use>')
        p.append('</symbol>')
        return "".join(p)


def generate():
    out = []
    bw, bh = makebox()
    out.append('    <svg id="board" width="100%" height="100%" viewBox="0 0 1500 940">')
    out.append('  <defs>')
    out.append(f'    <rect id="X" width="{tho(bw)}" height="{tho(bh)}" '
               f'x="{tho(-cdiv(bw, 2))}" y="{tho(-cdiv(bh, 2))}"></rect>')
    out.append('  </defs>')
    # suit pips
    for s in "CDHS":
        out.append(f'<symbol id="S{s}" viewBox="-600 -600 1200 1200" '
                   f'preserveAspectRatio="xMinYMid">'
                   f'<path d="{PIP_PATH[s][0]}" fill="{COLOUR[s]}"></path></symbol>')
    # value glyphs (stroke colour comes from the <use> site)
    for v in "23456789AJQKT":
        out.append(f'<symbol id="V{v}" viewBox="-500 -500 1000 1000" '
                   f'preserveAspectRatio="xMinYMid">'
                   f'<path d="{VALUE_PATH[v]}" stroke-width="80" '
                   f'stroke-linecap="square" stroke-miterlimit="1.5" '
                   f'fill="none"></path></symbol>')
    # court artwork layers
    yscale = tho(cdiv(cdiv(THO * 20 * bw, 13), bh))
    for value in "JKQ":
        for suit in "CDHS":
            card = value + suit
            layers = extract_layers(os.path.join(SVGDIR, card + ".svg"),
                                    [l for l, _ in COURT_LAYERS])
            emitted = []
            n = 0
            for label, col in COURT_LAYERS:
                d = layers.get(label)
                if not d:
                    print(f"Cannot find {label} in {card}", file=sys.stderr)
                    continue
                n += 1
                if label == "Stroke" and card == "KH":
                    d += KH_STROKE_EXTRA
                if label in ("Stroke", "Thin"):
                    width = 3 if label == "Thin" else 6
                    attrs = (f'stroke="{col}" stroke-linecap="round" '
                             f'stroke-linejoin="round" stroke-width="{width}" '
                             f'fill="none"')
                else:
                    attrs = f'fill="{col}"'
                emitted.append([f'<symbol id="{suit}{value}{n}" '
                                f'preserveAspectRatio="none" viewBox="0 0 1300 2000">'
                                f'<path {attrs} d="{d}"></path>'])
            # pips are embedded in the last layer's symbol
            for pip in COURT_PIPS[card]:
                x, y, s, r = pip[:4]
                border = pip[4] if len(pip) > 4 else 0
                use = (f'<use xlink:href="#S{suit}" height="{s}" '
                       f'transform="translate({x},{2000 - y})scale(1,{yscale})'
                       f'rotate({r})translate({cdiv(-s, 2)},{cdiv(-s, 2)})"')
                if border:
                    use += (f' stroke="#44F" '
                            f'stroke-width="{tho(cdiv(THO * 6 * 1200, s))}" '
                            f'stroke-linejoin="round" stroke-linecap="round"')
                emitted[-1].append(use + "></use>")
            for sym in emitted:
                out.append("".join(sym) + "</symbol>")
    # the 52 cards, in the tool's output filename sort order (2C, 2D, ...)
    out.append('')
    order = sorted(((v, s) for s in GAME_SUITS for v in GAME_VALUES))
    for v, s in order:
        out.append(Card(s, v).build())
    return "\n".join(out) + "\n"


def main():
    text = generate()
    if len(sys.argv) == 3 and sys.argv[1] == "--update":
        fname = sys.argv[2]
        html = open(fname).read()
        pat = re.compile(r'[ \t]*<svg id="board".*?(?=\n[ \t]*<symbol id="e")',
                         re.S)
        if not pat.search(html):
            sys.exit(f"Cannot find symbol section in {fname}")
        open(fname, "w").write(pat.sub(lambda m: text, html))
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
