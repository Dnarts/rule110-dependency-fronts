# Exact Worst-Case Dependency Fronts in Rule 110

**Aleksandr Strand · 2026**

Research repository for the preprint **[Exact Worst-Case Dependency Fronts in Rule 110 and Finite-State Certification of Input Essentiality](https://zenodo.org/records/24334185)**.

**Published preprint:** [Zenodo record 24334185](https://zenodo.org/records/24334185)  
**Manuscript:** [PDF](paper/main.pdf) · [LaTeX source](paper/main.tex)

## Main results

Let \(G_t(u)=(F^t(u))_0\) be the state of cell 0 after \(t\) synchronous updates of Rule 110 on the bi-infinite lattice, and let \(D_t\) denote the set of essential initial coordinates.

For every \(t\ge 0\), the work proves
\[
D_t\subseteq I_t=\left[-\left(t-\left\lfloor t/3\right\rfloor\right),\ t\right],
\qquad \min D_t= -\left(t-\left\lfloor t/3\right\rfloor\right),
\qquad \max D_t=t.
\]

Hence the shortest **contiguous** initial observation interval sufficient for exact prediction has
\[
m_{\min}(t)=2t+1-\left\lfloor t/3\right\rfloor
\]
sites.

The stronger statement \(D_t=I_t\), asserting that no interior coordinates are missing, is **not proved for all times**. Exhaustive finite-horizon witness search verifies it for \(0\le t\le 2000\), covering **3,337,668** time–coordinate pairs with spatially periodic backgrounds of period at most 10.

For finite periodic rings, the manuscript proves a finite-state criterion for persistent input essentiality and gives an independently exhaustively checked example at \(N=20\), \(t=121\): the image has **2,095** states (12 bits of integer capacity), yet all 20 initial coordinates remain essential.

## Verification scope

| Result | Evidence | Status |
| --- | --- | --- |
| Rule 110 algebra and three-step local exclusion | Exhaustive Python and independent TypeScript checks, 128 local windows | **FINITE_CHECK** |
| Infinite-lattice dependency bounds and essential endpoints | Lean 4.35.0 compilation and axiom reports; four theorems without `sorryAx` | **LEAN_VERIFIED** |
| Gap-free support for \(0\le t\le 2000\) | Exhaustive search of periodic-background witnesses | **FINITE_COMPUTATIONAL_EVIDENCE** |
| Gap-free support for every \(t\) | No universal proof | **CONJECTURE** |
| Finite-ring persistence criterion | Mathematical proof in the manuscript, not formalized in Lean | **MATHEMATICAL_PROOF** |
| Rule 110 ring \(N=20\) example | Exhaustive enumeration of all \(2^{20}\) states | **FINITE_CHECK** |

Lean verification covers the infinite-lattice bounds and endpoint witnesses, **not** the finite-ring theorem or the unrestricted gap-free conjecture. The supplied attestation, independently checked source hash, and GitHub CI results are documented in [verification/VERIFICATION_SCOPE.md](verification/VERIFICATION_SCOPE.md).

## Files

- [paper/main.pdf](paper/main.pdf) and [paper/main.tex](paper/main.tex) — manuscript and LaTeX source.
- [formal/rule110_complete.lean](formal/rule110_complete.lean) — Lean 4 proof, pinned to Lean 4.35.0.
- [scripts/](scripts/) — independent Python/TypeScript verifiers and finite-ring enumeration.
- [verification/](verification/) — machine-readable results, attestation, and reproducibility logs.
- [docs/proof_ru.md](docs/proof_ru.md) — detailed mathematical proof and its limitations (in Russian).

## Reproduce

Requirements: Python 3.10+, Node.js 18+, TypeScript, Lean 4.35.0, and TeX Live / `latexmk` for the manuscript. The exhaustive \(N=20\) test additionally requires NumPy.

```sh
make test                 # local Rule 110 identities and finite checks
make coverage             # all 3,337,668 time–coordinate pairs up to t=2000
make test-ts              # independent TypeScript checks
python3 -m pip install -r requirements-ring20.txt
make ring20               # exhaustive N=20 finite-ring audit
make lean                 # core formal proofs and printed axioms
make paper                # compile LaTeX manuscript
```

## Citation and licenses

**Cite the published preprint:** [Zenodo record 24334185](https://zenodo.org/records/24334185). Machine-readable citation metadata: [CITATION.cff](CITATION.cff).

- **Code:** MIT ([LICENSE](LICENSE), [LICENSE-CODE](LICENSE-CODE)).
- **Manuscript and explanatory notes:** Creative Commons Attribution 4.0 International ([LICENSE-PAPER.md](LICENSE-PAPER.md)).

This is an openly available **preprint, not a peer-reviewed publication**. The all-time gap-free conjecture and claims of scholarly novelty remain outside the verified results. The manuscript discloses material use of ChatGPT; responsibility for the publication rests with the named author.
