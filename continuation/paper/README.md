# Manuscripts and figures

- [English translation, 5 pages](rule110-continuation-en.pdf)
- [Original Russian article, 5 pages](rule110-continuation-ru.pdf)
- [English LaTeX source](rule110-continuation-en.tex)
- [Verification/provenance section included by the source](verification-status.tex)
- [Figure generator](generate_figures.py)

## Build the English PDF

Use a normal XeLaTeX installation with `latexmk`, the packages named in the
source, and the fonts **Noto Serif**, **DejaVu Sans**, and **DejaVu Sans Mono**.
For example, Debian/Ubuntu supplies these through `texlive-xetex`,
`texlive-latex-extra`, `latexmk`, `fonts-noto-core`, and `fonts-dejavu-core`.

From this directory:

```sh
latexmk -xelatex -interaction=nonstopmode -halt-on-error rule110-continuation-en.tex
```

The two vector figures are already included. To regenerate them, install
Python 3.10+, NumPy and Matplotlib, then run:

```sh
python3 generate_figures.py
```

The generator evolves the stated initial configurations directly and checks
coalescence and the displayed difference support. PDF figures are used in the
manuscript; PNG versions are provided for inspection. No AI-generated imagery
is used for these exact diagrams.

## Translation and publication decisions

The English article includes every section, theorem, table, caption, and
reference from the Russian original. Its mathematical scopes are preserved.
The following explicit editorial clarifications are included:

1. In the two-argument decoder, necessity of K means that Z alone is
   insufficient. Necessity of Z follows from presenting both values of Y at
   each fixed K. This is the intended condition used by the proofs.
2. The write and output cell in the return construction is explicitly −1;
   the preceding mention of the left gate input at −2 is not the readout.
3. The stream recurrence is accompanied by Oₙ=qₙ⊕Yₙ, making clear that later
   outputs need not equal the current original bit.
4. The verification section describes the new import-based audits and the
   reconstructed threshold bridge, the four unchanged core files, and the
   fresh common-toolchain build. The Russian PDF is retained as supplied.
5. Reproduction commands use the published `scripts/` paths. Current audit
   records and historical supplied logs have separate locations.

The supplied Russian article has no accompanying Russian LaTeX source in the
upload. It has not been silently reconstructed or modified. The complete
English LaTeX and figure code make the translation rebuildable.

See the [verification report](../verification/REPORT.md) for the actual build
and proof status, and the [relationship note](../docs/relationship.md) for
additional channel-memory deductions kept separate from the translation.
