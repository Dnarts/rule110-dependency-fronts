# Package roles and dependencies

The [multilingual README](README.md) is the accessible entry point. The
[verification report](verification/REPORT.md) records the checked publication
state. This page explains which files are needed together.

## Formal reproduction

All modules use Lean core only, pinned by [lean-toolchain](lean-toolchain) to
Lean 4.35.0. No Mathlib checkout or original Rule 110 full-proof build is needed.

| Canonical file | Role | Direct project dependencies |
| --- | --- | --- |
| [Rule110RingDecoupling.lean](lean/Rule110RingDecoupling.lean) | Fifteen-state image, exact preperiod/period, all-time essentiality, Rule 90 control | None |
| [Rule110ChiralSeam.lean](lean/Rule110ChiralSeam.lean) | Ether, 63-state certificate, arbitrary-tail induction, phase distinction and orientation control | None |
| [MergeMinimality4.lean](lean/MergeMinimality4.lean) | Complete three-step merger pattern and fixed-sensor lower-bound ingredient | None |
| [ContinuousSubject110.lean](lean/ContinuousSubject110.lean) | Four concrete histories, full-line merger, return, parity streams and reset witness | None |
| [MergeThreshold.lean](lean/MergeThreshold.lean) | One observation class and the exact four-step threshold | MergeMinimality4; ContinuousSubject110 |
| [AxiomAudit.lean](lean/AxiomAudit.lean) | 22 seam dependency reports without a second implementation | Rule110ChiralSeam |
| [RingAxiomAudit.lean](lean/RingAxiomAudit.lean) | 19 ring dependency reports | Rule110RingDecoupling |

The four core modules are independent. The merger and stream modules must be
present together with the threshold bridge to reproduce the complete minimality
statement. The audit modules are needed to reproduce the complete selected
dependency report, rather than just compile the mathematical declarations.

[verify_lean.py](scripts/verify_lean.py) builds these files in a fresh temporary
directory, checks the compiler version, verifies all 79 requested reports, and
rejects unexpected axioms. Historical log files are not inputs to that build.
When invoked through elan, it resolves the package's pinned compiler before
moving into the temporary build directory.

## Independent calculations and reading

| Material | Purpose |
| --- | --- |
| [check_finite.py](scripts/check_finite.py) | Independent implementation from the elementary-rule number; reproduces all finite tables and the channel illustrations |
| [finite-checks.json](verification/finite-checks.json) | Recomputed finite results, including 98 witnesses and the 126-transition seam certificate |
| [English PDF](paper/rule110-continuation-en.pdf) and [LaTeX](paper/rule110-continuation-en.tex) | Complete English translation with reproducible vector figures |
| [Russian PDF](paper/rule110-continuation-ru.pdf) | Original supplied five-page article, preserved byte-for-byte |
| [Hebrew PDF](paper/rule110-continuation-he.pdf) and [source archive](paper/rule110-continuation-he-source.zip) | Complete Hebrew translation, with Noto Sans Hebrew and rebuild instructions |
| [Relationship note](docs/relationship.md) | Exact links to predecessor results and separately identified channel-memory deductions |
| [Supplied originals](archive/supplied/README.md) | Historical provenance, including redundant source and superseded diagnostics |

## Reproduction commands

Run from this directory:

```sh
python3 scripts/check_package.py
python3 scripts/check_finite.py
python3 scripts/verify_lean.py
```

The package check verifies [SHA256SUMS](SHA256SUMS), source/log bindings,
preserved originals, and local Markdown links. These are integrity checks;
the other two commands independently recompute the finite results and proofs.

Install the version named by `lean-toolchain`, or pass an executable explicitly:

```sh
python3 scripts/verify_lean.py --lean /absolute/path/to/lean
```

Fresh outputs go under `build/` by default. The committed
[current audit](verification/current/lean-check.json) records the publication
build, and can be reproduced into a separate directory without overwriting it.

For the English article, use the instructions in [paper/README.md](paper/README.md).

## Preservation policy

The supplied duplicate `AxiomAudit.lean` is kept in the archive. Its canonical
replacement imports the source being audited. A failed historical merger log
is retained with its original source hash and failure status; it is not
represented as a successful check of the current source. Newly reconstructed
files are identified as new work, rather than attributed to the uploaded bundle.
