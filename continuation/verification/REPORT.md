# Publication verification report

## Result

**PASS.** All seven publication Lean modules were rebuilt from source with
Lean 4.35.0 in a fresh temporary build directory. All **79 distinct requested
axiom reports** were reproduced. The reported dependencies are `propext`,
`Quot.sound`, or none; there are no `sorryAx` or native-evaluation trust axioms
in these reports. The four supplied mathematical modules were not modified.

This is a new observed build. Supplied historical logs are retained separately.

- [Machine-readable fresh build record](current/lean-check.json)
- [Independent finite calculations](finite-checks.json)
- [Reproduction runner](../scripts/verify_lean.py)
- [Package roles and dependencies](../MANIFEST.md)
- [Incoming-file identity manifest](../archive/supplied/manifest.json)
- [Complete publication checksums](../SHA256SUMS)
- [Package integrity and link checker](../scripts/check_package.py)

## Toolchain and dependencies

```text
Lean 4.35.0, x86_64-unknown-linux-gnu
Compiler commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc
```

The official `lean-4.35.0-linux.tar.zst` release was checked against its published
SHA-256 before use:

```text
7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d
```

[Official release](https://github.com/leanprover/lean4/releases/tag/v4.35.0).
The project uses Lean core only, with no Mathlib or binary proof cache. The
runner resets `LEAN_PATH` to a fresh build directory, compiles the four core
sources, then compiles their audits and the threshold bridge. It records each
source and log hash, compiler exit code, audit names, and observed dependencies.
It resolves an elan launcher to the pinned compiler before changing directories,
and binds the machine-readable record to the runner's own source hash.

## Formal results and scope

| Result group | Direct audit log | Reports |
| --- | --- | ---: |
| Arbitrary-tail crystal invariant, phase distinction, orientation controls | [AxiomAudit.log](current/AxiomAudit.log) | 22 |
| Exact ring image, minimal preperiod/period, all-time essentiality, Rule 90 control | [RingAxiomAudit.log](current/RingAxiomAudit.log) | 19 |
| Three-step merger classification and fixed-sensor lower-bound ingredient | [MergeMinimality4.log](current/MergeMinimality4.log) | 11 |
| Four histories, full-line merger, return, streams and reset witness | [ContinuousSubject110.log](current/ContinuousSubject110.log) | 24 |
| Existence at 4, lower bound for every admissible time, combined least-time theorem | [MergeThreshold.log](current/MergeThreshold.log) | 3 |
| **Total distinct requested declarations** | | **79** |

The count is a count of selected dependency reports, including helper lemmas;
it is not a claim of 79 independent main theorems. Every source file compiles,
and the nine critical declarations listed by the runner are required to appear
in the report. The same runner also rejects unexpected dependencies.

The unchanged seam source emits **four deprecation warnings** for `if_pos`.
They do not affect compilation or theorem dependencies. The canonical audit
imports that source, avoiding a second copied implementation and duplicate
warnings. [Seam compilation log](current/Rule110ChiralSeam.log).

## Newly supplied bridge

The incoming Russian PDF named `MergeThreshold.lean`, but the attachment set
did not contain it. The publication's [MergeThreshold.lean](../lean/MergeThreshold.lean)
was newly written and actually checked. It:

1. Identifies the two supplied Boolean definitions of Rule 110.
2. Aligns outer-step and inner-step iteration conventions.
3. Proves that complete merger persists at later times.
4. Defines the paper's exact `Protocol T` observation class.
5. Extends the time-three obstruction to every T below four.
6. Translates the original witness coordinate 5 to coordinate 0, including
   sensor 3→−2 and context 0→−5.
7. Constructs the admissible time-four protocol from the supplied four words.
8. Proves `four_is_least`, combining existence and the lower bound.

This reconstruction is publication work, not a retroactive claim that the
missing file was present in the original upload.

## Independent finite checks

[check_finite.py](../scripts/check_finite.py) implements each elementary rule
directly from its rule number, rather than calling Lean or trusting the
supplied tables. It uses only the Python standard library.

| Check | Observed result |
| --- | --- |
| Ring image sizes at times 0 through 7 | 128, 79, 50, 43, 36, 29, 22, 15 |
| Number of essential coordinates at those times | 1, 3, 5, 6, 7, 7, 7, 7 |
| Complete-map periodicity | F⁽²¹⁾=F⁽⁷⁾ on all 128 inputs |
| Eventual graph | Fixed zero plus the stated 14-cycle |
| Late essentiality witnesses | 98 witnesses, one per time residue and coordinate |
| Three-step merger environments | Exactly 8 of 4096; pattern `*10111[Y]1000**` |
| Crystal certificate | Exactly 63 reachable nodes, all 126 transitions valid |
| Four histories | Isolated initial difference, merger at 4, sensor/context values, return at 5 |
| Stream controls | Parity and output identities; donor inversion; external reset witness |
| Rule 90 and Rule 124 controls | Eight-site collapse at 4; mirrored-rule seam failure |
| Derived channel illustration | Uniform four-history conditional information and Λstrict=1 |

The stored JSON includes the witnesses, reachable boundary states, and all
126 boundary transitions. Finite stream tests supplement the formal induction;
they do not establish infinite streams by enumeration. Similarly, the
unbounded-time and infinite-line claims rely on the Lean induction proofs.

## Historical evidence is preserved with its status

The supplied ring audit records Lean **4.33.1**. It is not presented as a
4.35.0 check. The new build establishes the common toolchain independently.

`MergeMinimality4.check.log` records an old failure with `sorryAx` and source
hash `2f450f16d3d7049455c5f70863098797277303b24565d987dee59a15e31b5727`.
The supplied current file has hash
`da41665bb1ab2d72dcb9501560a64d6fda4bca01e01c672822f7606194bdd651`.
It matches the later supplied successful axiom report and compiles in the new
build. The old failure remains in [the source archive](../archive/supplied/README.md).

The original `AxiomAudit.lean` repeats the seam source and adds print commands.
The archived version is intact; the active version imports the canonical
source and asks for the same 22 reports.

## English article and scope of deductions

The English article translates all six sections, four theorems, two tables,
two figures and references. The figures were independently regenerated from
the stated rule and initial configurations. All five final pages were rendered
and visually checked; the final XeLaTeX build has no warnings and all fonts are
embedded. The original Russian PDF remains byte-identical to the upload.

The English text makes the readout cell −1 explicit, states the recurrence's
consequence Oₙ=qₙ⊕Yₙ, clarifies which single argument cannot decode, and updates
the reproduction paths and publication provenance. These editorial changes
are recorded in [paper/README.md](../paper/README.md).

The [relationship note](../docs/relationship.md) adds explicit channel and
memory calculations under named probability assumptions. Those deductions
are not formalized in the Lean modules and are not part of the 79-report count.
The four-step bound concerns the specified common raw sensor and context
protocol, the crystal boundary speed is not claimed optimal, and episodes
are externally reset. No autonomous uninterrupted binary Rule 110 memory
protocol, general learning result, or subjective-experience claim is inferred.
