# Exact dependency fronts in Rule 110

**Aleksandr Strand · November 2026**

**Final preprint:** [English](paper/v2/en.pdf) · [Русский](paper/v2/ru.pdf) · [简体中文](paper/v2/zh.pdf) · [XeLaTeX sources and fonts](paper/v2)
**First preprint:** [Zenodo, DOI 10.5281/zenodo.24334185](https://doi.org/10.5281/zenodo.24334185) · [PDF](paper/main.pdf) · [TeX](paper/main.tex)

On the infinite one-dimensional lattice, an initial coordinate $j$ is essential for the cell at the origin at time $t$ if two configurations differing only at $j$ can give different outputs. For every nonnegative integer $t$, the exact set of essential coordinates is

$$D_t = [- (t-\lfloor t/3\rfloor),\ t]\cap\mathbb Z.$$

Every one of the $2t+1-\lfloor t/3\rfloor$ coordinates in this interval is essential. The pair of configurations witnessing essentiality can depend on both $t$ and $j$.

## Results and verification

| Result | Evidence |
| --- | --- |
| Universal dependency bounds and both essential endpoints | **LEAN_VERIFIED** · [first proof](formal/rule110_complete.lean) |
| Every interior coordinate is essential for every time | **LEAN_VERIFIED** · [Rails.essential_iff](lean/Rule110Exact.lean) · [compiler output](verification/v2/final.log) |
| Finite base for the full theorem, times 0 through 2484 | [Finite transfer](lean/Finite.lean) and [certificate checker](lean/FiniteBase.lean) for 5,147,263 time–coordinate pairs in 100 blocks |
| All later times | [Five adjoining strips](lean/Late.lean) for every time from 2485 onward |
| Finite-ring persistence criterion | Mathematical proof in the manuscript |
| Ring of 20 sites at time 121 | Independent exhaustive enumeration: 2,095 reachable states, all 20 inputs essential |

The first preprint proved the endpoints and reported a finite search through time 2000. It posed full coverage of the interior for all times as a conjecture. The final preprint proves it. [Verification scope](verification/VERIFICATION_SCOPE.md) · [Earlier proofs, experiments and manuscripts](history/)

## Reproduce

Install the Lean toolchain pinned by `lean-toolchain` (4.35.0) and Python 3.10 or later. Run from the repository root:

```sh
make verify
```

This regenerates the finite witnesses, compiles the proof from source and checks the axiom report for the root theorem. Its only reported dependencies are `propext`, `Classical.choice` and `Quot.sound`.

`make paper-v2` builds the three final manuscripts with XeLaTeX. `make package-v2` assembles the PDFs and uploadable source ZIPs under `dist/v2/`. For the first edition, `make test`, `make coverage`, `make test-ts`, `make ring20`, `make lean` and `make paper` retain their original meanings. The independent TypeScript check requires TypeScript and Node.js, and the ring test requires NumPy.

## Citation and licenses

[Citation metadata](CITATION.cff) · [Release notes](RELEASE_NOTES.md) · [MIT code license](LICENSE-CODE) · [CC BY 4.0 manuscript license](LICENSE-PAPER.md). The bundled fonts have their own notices in [paper/v2/fonts](paper/v2/fonts). These manuscripts are preprints. The author takes responsibility for the work, which was prepared with substantive assistance from ChatGPT.
