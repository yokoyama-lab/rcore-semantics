# Figure sources

The SVG figures in `docs/fig/` are adapted from [MaYo26] (T. Makino and
T. Yokoyama, RC 2026, LNCS 16626,
[doi:10.1007/978-3-032-30839-9_12](https://doi.org/10.1007/978-3-032-30839-9_12)).
They are redrawn from the authors' own LaTeX source of that paper:
`preamble.tex` holds the macros and TikZ styles copied from it, and each
`fig*.tex` / `eq*.tex` holds one figure. They are not covered by the MIT
license of this repository.

To regenerate the SVGs (needs `latex` from TeX Live, `dvisvgm`, `python3`):

    sh docs/fig/src/build.sh
