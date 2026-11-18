# v1.0.0 — 18 November 2026

## Corrected since the supplied draft

- Synchronized the formal Lean source's introductory status with the supplied successful Lean 4.35.0 report. The proof declarations are byte-for-byte identical to the attested source; preserved the original source and the original report for independent verification. CI recompiles the comment-only edited source.
- Rewrote the Russian proof's status statement, separating Lean-checked infinite-lattice results from the unformalized finite-ring proposition and conjecture.
- Added accurate arXiv-required generative AI use disclosure to the English manuscript.
- Rebuilt the PDF with local `latexmk`/`pdflatex`; visual check of all pages.
- Verified the bibliographic naming of Seck-Tuoh-Mora (2006) and maintained existing references.
- Independently recomputed all `2^20` Rule 110 ring configurations through `t=130`: full support from `t=11` through `130`; 2095 images and 12-bit capacity at `t=121`.
- Re-ran the periodic background coverage through `t=2000`: all 3,337,668 pairs covered.
- Added `CITATION.cff`, copyright/license candidates, GitHub Actions CI, reproducibility targets, submission instructions, and SHA-256 manifest.
- Prepared a separate arXiv source ZIP containing only top-level `main.tex`, without the TeX-generated PDF or build intermediates.

## Important scope

Lean proof verified *according to the supplied author compilation report*, with the source hash independently cross-checked. The current environment has no Lean executable, so no fresh Lean compilation was performed here. The new GitHub Actions job is intended to perform that check after upload.

The gap-free support conjecture for all time remains open, and no comprehensive scholarly-priority review has been certified. The arXiv submission is not created by packaging the files.
