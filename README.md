# Exact Worst-Case Dependency Fronts in Rule 110

**Manuscript:** *Exact Worst-Case Dependency Fronts in Rule 110 and Finite-State Certification of Input Essentiality* — Aleksandr Strand (2026).  This repository contains the manuscript, reproducible computational checks, a Lean 4 proof of the infinite-lattice bounds and endpoint sharpness, and verification records.

## Mathematical scope

For Rule 110 on the bi-infinite lattice, let `G_t(u)=(F^t(u))_0` and `D_t` be the set of essential initial coordinates. The work establishes

\[D_t\subseteq[-(t-\lfloor t/3\rfloor),t],\qquad -(t-\lfloor t/3\rfloor),t\in D_t.\]

Thus the minimum **contiguous** sufficient observation window has length

\[m_{\min}(t)=2t+1-\lfloor t/3\rfloor.\]

These statements do **not** imply gap-free interior support at all times. The stronger `D_t=I_t` conjecture is tested computationally for `0 <= t <= 2000` (3,337,668 time-position pairs), using periodic backgrounds of period at most 10.

For finite rings a separate elementary proposition establishes a finite-horizon test for persistence of full input essentiality. The general finite-ring proposition is *not* among the Lean-verified theorems.

## Status and provenance

| Claim | Evidence | Status |
| --- | --- | --- |
| 3-step exclusion and Rule 110 algebraic identities | Python and independent TypeScript, all 128 local cases | FINITE_CHECK |
| Infinite-lattice dependency bounds and sharpness of endpoints | Lean 4.35.0 successful **supplied** compilation report; 4 theorems, no `sorryAx`; source SHA-256 matches report | REPORTED_LEAN_VERIFIED |
| Current formal source | Same theorem/proof declarations, modified documentation header only; GitHub CI recompiles | COMMENT_ONLY_UPDATE; CI PENDING |
| Gap-free essential support, `0 <= t <= 2000` | exact finite search; all 3,337,668 pairs covered | COMPUTATIONAL_EVIDENCE |
| Gap-free support for every horizon | no all-time proof | CONJECTURE |
| Rule 110 `N=20` finite-ring divergence | independent full 2^20-state enumeration for t=0..130 using NumPy | COMPUTATIONALLY_VERIFIED |
| Persistent input-essentiality finite-horizon proposition | mathematical proof in manuscript | MATHEMATICAL_PROOF (NOT LEAN-AUDITED) |
| Novelty / scholarly priority of exact formula | not exhaustively established by a literature review | NOT CERTIFIED |

**Important:** The author-supplied Lean report attests success for the `verification/attested_source/rule110_complete.lean` source (recorded digest). The readable copy at `formal/rule110_complete.lean` changes only the introductory comment. This environment independently checked the digest and equality of the proof bodies but could not rerun Lean. GitHub CI is configured to compile the current copy. The report does not verify the finite-ring theorem or the conjecture.

## Structure

```
paper/main.tex                 LaTeX paper, arXiv-compatible
paper/main.pdf                 prebuilt PDF for reading / GitHub
formal/rule110_complete.lean  theorem statements and proofs
lean-toolchain                pinned Lean 4.35.0
scripts/                     Python, TypeScript and JavaScript verifiers
verification/reports/         recorded outputs and numeric audit
verification/attested_source/ source hashed in the supplied Lean report
docs/proof_ru.md              Russian proof and verification scope
.github/workflows/ci.yml      GitHub Actions for Lean, Python, TS, LaTeX
```

## Reproduction

Required: Python >=3.10, Node.js >=18 and TypeScript compiler, Lean 4.35.0, and TeX Live (LaTeX build). Ring-20 exhaustive check additionally needs NumPy.

```sh
make test
make coverage
make test-ts
python3 -m pip install -r requirements-ring20.txt
make ring20
make lean
make paper
```

`make test` and `make coverage` are standard-library-only Python runs. The three-step exclusion is exhaustive, while the gap-free result applies only to finite times. `make lean` checks four all-time infinite-lattice results; inspect the four `#print axioms` reports at its end.

## arXiv submission

Upload the separately provided **arxiv_rule110_source.zip** (containing `main.tex`, not this repository ZIP). arXiv compiles the source; do not add the prebuilt `main.pdf`, `.log`, `.aux`, or GitHub CI files to the arXiv source submission. Review the arXiv-produced PDF before submitting. For submission category and licensing details, see `SUBMISSION_CHECKLIST.md`.

## Scholarly and licensing notes

This is a preprint, not a peer-reviewed article, and arXiv acceptance and novelty are not guaranteed. The manuscript discloses substantive use of ChatGPT in research and drafting, while human authorship and responsibility remain with the named author. Code license: MIT (`LICENSE-CODE`); proposed paper license: CC BY 4.0 (`LICENSE-PAPER.md`), subject to author confirmation before publication. The arXiv license must be selected by the author during submission.
