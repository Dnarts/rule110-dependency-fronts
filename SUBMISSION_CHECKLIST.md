# Submission checklist — 18 November 2026

## GitHub

1. Confirm the manuscript's human author's name (`Aleksandr Strand`) and permission to distribute all sources.
2. Confirm code license (MIT) and proposed manuscript license (CC BY 4.0), or adjust them before publication.
3. Create a repository (suggested name: `rule110-dependency-fronts`) and upload the **contents** of the GitHub ZIP, preserving `.github/workflows/ci.yml` and the directory structure.
4. Let GitHub Actions run all three jobs; require green Lean, computational and manuscript checks. The supplied local successful Lean 4.35.0 report is source-hash-attested, but the refreshed comment-only header has not been compiled in this environment.
5. Optionally tag `v1.0.0` after CI succeeds. Add an arXiv URL or DOI to `CITATION.cff` only **after** one exists. Do not invent publication identifiers.

## arXiv

1. Upload **arxiv_rule110_source.zip** rather than the GitHub repository ZIP; it contains only `main.tex` at the root.
2. Choose an appropriate category; `nlin.CG` (Cellular Automata and Lattice Gases) is a plausible candidate, subject to moderator and author determination.
3. Confirm title/abstract/author metadata; do not claim a journal publication or DOI that does not exist.
4. Choose the license in the arXiv interface according to the author's rights and preference.
5. Review the PDF built **by arXiv** to ensure that bibliography, equations and mathematics render correctly. arXiv automatically recompiles LaTeX sources.
6. Confirm disclosure of material generative-AI use (included in the manuscript), and assess scholarly priority, accuracy and copyright before submitting.
7. The supplied Lean verification applies only to the four main infinite-lattice theorems. It does not prove general full-interior essentiality or the finite-ring proposition in Lean.

## Remaining external prerequisites

An arXiv account may require endorsement and the submission will be moderated; those are external approval steps, not something included in a ZIP. No GitHub repository or arXiv submission is created by this archive-building process.

Official source-format guidance: https://github.com/arXiv/arxiv-docs/blob/develop/source/help/submit_tex.md
Official moderation and AI disclosure policy: https://github.com/arXiv/arxiv-docs/blob/develop/source/help/moderation/index.md
