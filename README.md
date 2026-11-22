# Exact dependency fronts in Rule 110

| Preprint | English | Русский | 简体中文 | עברית |
| --- | --- | --- | --- | --- |
| **I. Exact dependency fronts in Rule 110** | [PDF](paper/v2/en.pdf) | [PDF](paper/v2/ru.pdf) | [PDF](paper/v2/zh.pdf) | [PDF](paper/v2/he.pdf) · [LaTeX](paper/v2/he.tex) |
| **II. 110 OBSERVER: Observability of a System’s Own Past** | [PDF](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/110_OBSERVER_Preprint_en.pdf) | [PDF](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/110_OBSERVER_Preprint.pdf) | [PDF](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/110_OBSERVER_Preprint_zh.pdf) | [PDF](paper/observer/he.pdf) · [LaTeX](paper/observer/he.tex) |
| **III. Essential Inputs and Memory after Coalescence** | [PDF](continuation/paper/rule110-continuation-en.pdf) · [Source](continuation/paper/rule110-continuation-en.tex) | [PDF](continuation/paper/rule110-continuation-ru.pdf) | [中文说明](continuation/README.md#chinese) | [הסבר בעברית](continuation/README.md#hebrew) |

**Zenodo record — Exact Dependency Fronts, Finite Certificates, and Constructive Invariants for Unbounded Time in Rule 110:** [Publication record](https://zenodo.org/records/24435634).

Aleksandr Strand · November 2026

**New continuation:** [English · Русский · 简体中文 · עברית](continuation/README.md) — the exact seven-cell ring, a 63-state arbitrary-tail crystal certificate, the formally completed four-step merger threshold, and a persistent one-bit register across externally reset episodes. [Verification: 79/79 axiom reports](continuation/verification/REPORT.md) · [Sources and reproduction](continuation/MANIFEST.md) · [Connection to Channel Topology and Memory](continuation/docs/relationship.md).

**Продолжение:** точная динамика семиклеточного кольца, защита кристаллического фона при любом правом хвосте, формальное завершение порога слияния и однобитная память между эпизодами. [Описание на четырёх языках](continuation/README.md).

**Paper I** asks which initial cells can change the state of the origin after exactly $t$ steps of Rule 110. It proves an exact asymmetric dependency interval on the infinite line and formalizes the theorem in Lean 4. **110 OBSERVER** asks a different question: can a reader reconstruct a target bit from a limited record? In Rule 110, the sensors’ dependency intervals can cover every relevant input and still produce identical records for two different answers.

**Русский.** Первая работа точно определяет, какие начальные клетки могут повлиять на ответ. Вторая показывает, что даже полное покрытие этих клеток конусами датчиков не гарантирует, что их журнал позволяет восстановить ответ.

**简体中文。** 第一篇论文精确确定哪些初始元胞可能影响目标元胞。第二篇论文表明：即使传感器的依赖区间覆盖了所有相关输入，观测记录仍可能不足以确定答案。

- **Paper I:** [LaTeX sources and fonts](paper/v2) · [Release notes](RELEASE_NOTES.md) · [Citation](CITATION.cff) · [original v2 branch](https://github.com/Dnarts/rule110-dependency-fronts/tree/final-preprint-v2)
- **110 OBSERVER:** [Monograph branch and source index](https://github.com/Dnarts/rule110-dependency-fronts/tree/series/monograph) · [Tagged snapshot](https://github.com/Dnarts/rule110-dependency-fronts/tree/v2.2.1-monograph-multilingual) · [Release notes](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/RELEASE_NOTES.md) · [Checksums](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/SHA256SUMS) · [Citation](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/CITATION.cff)
- **First edition of Paper I:** [Zenodo, DOI 10.5281/zenodo.24334185](https://doi.org/10.5281/zenodo.24334185) · [PDF](paper/main.pdf) · [LaTeX](paper/main.tex). This DOI identifies the first edition, not the final Paper I or the monograph.

<details>
<summary>Abstract · Аннотация · 摘要</summary>

**English.** For the elementary cellular automaton Rule 110, which initial cells can influence the origin after exactly $t$ steps? On the infinite one-dimensional lattice, an initial coordinate is essential if changing that cell alone can change the output. For every nonnegative integer $t$, the set of essential coordinates is exactly

$$D_t = [-(t-\lfloor t/3\rfloor),\ t]\cap\mathbb Z.$$

Every integer between the two dependency fronts is essential. The proof is formalized in Lean 4. The pair of initial configurations witnessing essentiality can depend on the time and the coordinate.

**Русский.** Какие клетки начальной конфигурации могут повлиять на клетку в начале координат через $t$ шагов элементарного клеточного автомата «Правило 110»? На бесконечной одномерной решётке при каждом целом $t\ge 0$ существенны в точности все координаты от $-t+\lfloor t/3\rfloor$ до $t$ включительно. Для каждой такой координаты существует начальная конфигурация, в которой изменение одной этой клетки меняет результат. Теорема о точных границах зависимости и всех промежуточных координатах формализована в Lean 4.

**简体中文。** 对于初等元胞自动机规则 110（Rule 110），哪些初始元胞能影响 $t$ 步后原点的状态？在无限一维格点上，对任意非负整数 $t$，所有本质坐标恰好是从 $-t+\lfloor t/3\rfloor$ 到 $t$ 的整数，包括两个端点。对其中每个坐标，都存在一对仅在该处不同的初始配置，使原点在第 $t$ 步的状态不同。该定理给出了精确的依赖边界，并已用 Lean 4 形式化证明。

</details>

## Paper I: results and verification

| Result | Evidence |
| --- | --- |
| Universal dependency bounds and both essential endpoints | **LEAN_VERIFIED** · [first proof](formal/rule110_complete.lean) |
| Every interior coordinate is essential for every time | **LEAN_VERIFIED** · [Rails.essential_iff](lean/Rule110Exact.lean) · [compiler output](verification/v2/final.log) |
| Finite base for the full theorem, times 0 through 2484 | [Finite transfer](lean/Finite.lean) and [certificate checker](lean/FiniteBase.lean) for 5,147,263 time–coordinate pairs in 100 blocks |
| All later times | [Five adjoining strips](lean/Late.lean) for every time from 2485 onward |
| Finite-ring persistence criterion | Mathematical proof in the manuscript |
| Ring of 20 sites at time 121 | Independent exhaustive enumeration: 2,095 reachable states; each of the 20 initial coordinates is essential for the target cell |

The first preprint proved the endpoints and reported a finite search through time 2000. It posed full coverage of the interior for all times as a conjecture. The final preprint proves it. [Verification scope](verification/VERIFICATION_SCOPE.md) · [Earlier proofs, experiments and manuscripts](history/)

## 110 OBSERVER: what is established

- **Geometric coverage is necessary, not sufficient.** For unrestricted initial configurations on the infinite line, failing to cover even one essential input prevents exact prediction from the sensor log. Covering every essential input still need not distinguish histories that require different answers. [Formal statement and counterexamples](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/observer/Rule110Observer.lean) · [How the two papers fit together](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/docs/series.md)
- **One bit can restore a distinction after merging.** In the displayed four-history construction, flipping one initial cell changes a sensor reading. An external register retains that reading through the merger of the main lattice configurations. After the bit is written back, one ordinary Rule 110 update reconstructs the past value using the remaining local context. Neither the message nor the context alone suffices on those four histories. [Construction and controls](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/sections/04-witnesses.tex)
- **OLMo is a separate development-panel experiment.** A sender chooses one of two rule tokens before seeing the new input. A recipient starts with a fresh KV cache and applies the transmitted rule. It answered 64/64 cases with unequal end bits versus 32/64 for a constant rule token; overall, 124/128 answers and 6/8 complete blocks. The held-out panels and activation-channel experiment were not run in this snapshot. This measures rule transfer through a token; it does not establish internal activation-level correction or subjective experience. [Experiment](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/sections/05-olmo.tex) · [Recorded results](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/observer/two-step-instruct-chat-04/report.json) · [Limits of inference](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/sections/06-boundary.tex)


## Paper III: essential inputs and memory after coalescence

The continuation packages four unchanged supplied mathematical modules with a newly reconstructed and checked `MergeThreshold.lean` bridge. The earlier monograph already stated the four-step threshold; this package connects its lower bound and concrete witness in one Lean theorem under the same observation assumptions. The minimum is **merger at step 4**, with **return at step 5**.

The external register stores parity across episodes, with output `O_n = q_n XOR Y_n`; the lattice is reinitialized by the episode schedule. All seven source/audit modules build on Lean 4.35.0, and the 79 requested dependency reports contain only `propext`, `Quot.sound`, or no axioms. Historical failing logs are preserved separately from the fresh successful build.

- [Accessible multilingual README](continuation/README.md)
- [English article](continuation/paper/rule110-continuation-en.pdf) · [Original Russian article](continuation/paper/rule110-continuation-ru.pdf)
- [Exact file dependencies and reproduction](continuation/MANIFEST.md) · [Current verification report](continuation/verification/REPORT.md)
- [Channel and memory relationships, with assumptions](continuation/docs/relationship.md)


## Reproduce

Use the Lean toolchain pinned by `lean-toolchain` (4.35.0) and Python 3.10 or later. Run each command from the root of the corresponding checkout.

| Checkout | Verify | Build PDFs |
| --- | --- | --- |
| `main` or `final-preprint-v2` | `make verify` | `make paper-v2`; `make package-v2` also assembles the PDFs and source archives |
| `v2.2.1-monograph-multilingual` | `make verify-series`; `make verify-observer` runs only the Python checks | `make monograph` for Russian; `make translations` for English and Chinese |

On `main`, verification regenerates the finite certificates, builds the Lean proof and checks the axiom report for `Rails.essential_iff`: `propext`, `Classical.choice` and `Quot.sound`. The monograph verification adds the observer Lean module and finite witness checks. Its Python scripts recompute the OLMo counts from stored outputs; they do not run new inference. Paper I uses XeLaTeX with `latexmk`; the monograph supports Tectonic or XeLaTeX with `latexmk`.

[Paper I verification scope](verification/VERIFICATION_SCOPE.md) · [Monograph geometry log](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/verification/monograph/geometry-axioms.log) · [Observer axiom log](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/verification/monograph/observer-axioms.log) · [Monograph archive](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/archive/README.md)

For the original research package, `make test`, `make coverage`, `make test-ts`, `make ring20`, `make lean` and `make paper` retain their original meanings. The independent TypeScript check requires TypeScript and Node.js; the ring test requires NumPy.

## Licenses

[MIT code license](LICENSE-CODE) · [CC BY 4.0 manuscript license](LICENSE-PAPER.md). Bundled fonts have separate notices in [paper/v2/fonts](paper/v2/fonts). These manuscripts are preprints. The author takes responsibility for the work, which was prepared with substantive assistance from ChatGPT.
