#!/bin/sh
# Rebuild the SVG figures of docs/theorem3-proof*.md from the standalone
# sources in this directory.  Needs latex (TeX Live) and dvisvgm.
# Glyphs are converted to paths so that the SVGs need no fonts, and the
# white page background is stretched over the margin so that the figures
# stay readable on a dark page.
set -eu
cd "$(dirname "$0")"
for tex in fig*.tex eq*.tex; do
  base=${tex%.tex}
  latex -interaction=nonstopmode -halt-on-error "$tex" >/dev/null
  dvisvgm --no-fonts --exact-bbox --bbox=6pt -o "../$base.svg" "$base.dvi" >/dev/null 2>&1
  python3 - "../$base.svg" <<'EOF'
import re, sys
p = sys.argv[1]
s = open(p).read()
x, y, w, h = re.search(r"viewBox='([^']*)'", s).group(1).split()
s = re.sub(r"<rect x='[^']*' y='[^']*' width='[^']*' height='[^']*' fill='#fff'/>",
           f"<rect x='{x}' y='{y}' width='{w}' height='{h}' fill='#fff'/>", s, count=1)
open(p, 'w').write(s)
EOF
  rm -f "$base.aux" "$base.log" "$base.dvi"
done
