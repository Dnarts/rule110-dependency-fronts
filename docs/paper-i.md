> **Серия:** 110 OBSERVER — Точная наблюдаемость, причинное самообращение и границы вывода<br>
> **Документ:** Paper I · прежнее введение<br>
> **Статус:** SOURCE EDITION<br>
> **Карта серии:** [Монография](../110_OBSERVER_Preprint.pdf) · [Индекс](../README.md) · [Источники и разделы](series.md) · [Архив](../archive/README.md)<br>
> **Зависимости:** Теорема Rails.essential_iff.

# Paper I · Exact dependency fronts in Rule 110

**Source edition of Paper I** · [Canonical Russian original](../archive/paper-i/Rule110_Final_Preprint.pdf) ·  [English PDF](../archive/paper-i/en.pdf) · [Русский PDF](../archive/paper-i/ru.pdf) · [简体中文 PDF](../archive/paper-i/zh.pdf)

Aleksandr Strand · November 2026

<details>
<summary>Abstract · Аннотация · 摘要</summary>

**English.** For the elementary cellular automaton Rule 110, which initial cells can influence the origin after exactly $t$ steps? On the infinite one-dimensional lattice, an initial coordinate is essential if changing that cell alone can change the output. For every nonnegative integer $t$, the set of essential coordinates is exactly

$$D_t = [-(t-\lfloor t/3\rfloor),\ t]\cap\mathbb Z.$$

Every integer between the two dependency fronts is essential. The proof is formalized in Lean 4. The pair of initial configurations witnessing essentiality can depend on the time and the coordinate.

**Русский.** Какие клетки начальной конфигурации могут повлиять на клетку в начале координат через $t$ шагов элементарного клеточного автомата «Правило 110»? На бесконечной одномерной решётке при каждом целом $t\ge 0$ существенны в точности все координаты от $-t+\lfloor t/3\rfloor$ до $t$ включительно. Для каждой такой координаты существует начальная конфигурация, в которой изменение одной этой клетки меняет результат. Теорема о точных границах зависимости и всех промежуточных координатах формализована в Lean 4.

**简体中文。** 对于初等元胞自动机规则 110（Rule 110），哪些初始元胞能影响 $t$ 步后原点的状态？在无限一维格点上，对任意非负整数 $t$，所有本质坐标恰好是从 $-t+\lfloor t/3\rfloor$ 到 $t$ 的整数，包括两个端点。对其中每个坐标，都存在一对仅在该处不同的初始配置，使原点在第 $t$ 步的状态不同。该定理给出了精确的依赖边界，并已用 Lean 4 形式化证明。

</details>

[Final preprint sources and fonts](../paper/v2)

**First preprint:** [Zenodo, DOI 10.5281/zenodo.24334185](https://doi.org/10.5281/zenodo.24334185) · [PDF](../archive/superseded/first-edition-en.pdf) · [TeX](../paper/main.tex)

## Results and verification

| Result | Evidence |
| --- | --- |
| Universal dependency bounds and both essential endpoints | **LEAN_VERIFIED** · [first proof](../formal/rule110_complete.lean) |
| Every interior coordinate is essential for every time | **LEAN_VERIFIED** · [Rails.essential_iff](../lean/Rule110Exact.lean) · [compiler output](../verification/v2/final.log) |
| Finite base for the full theorem, times 0 through 2484 | [Finite transfer](../lean/Finite.lean) and [certificate checker](../lean/FiniteBase.lean) for 5,147,263 time–coordinate pairs in 100 blocks |
| All later times | [Five adjoining strips](../lean/Late.lean) for every time from 2485 onward |
| Finite-ring persistence criterion | Mathematical proof in the manuscript |
| Ring of 20 sites at time 121 | Independent exhaustive enumeration: 2,095 reachable states, all 20 inputs essential |

The first preprint proved the endpoints and reported a finite search through time 2000. It posed full coverage of the interior for all times as a conjecture. The final preprint proves it. [Verification scope](../verification/VERIFICATION_SCOPE.md) · [Earlier proofs, experiments and manuscripts](../history/)

## Reproduce

Install the Lean toolchain pinned by `lean-toolchain` (4.35.0) and Python 3.10 or later. Run from the repository root:

```sh
make verify
```

This regenerates the finite witnesses, compiles the proof from source and checks the axiom report for the root theorem. Its only reported dependencies are `propext`, `Classical.choice` and `Quot.sound`.

`make paper-v2` builds the three final manuscripts with XeLaTeX. `make package-v2` assembles the PDFs and uploadable source ZIPs under `dist/v2/`. For the first edition, `make test`, `make coverage`, `make test-ts`, `make ring20`, `make lean` and `make paper` retain their original meanings. The independent TypeScript check requires TypeScript and Node.js, and the ring test requires NumPy.

## Citation and licenses

[Citation metadata](../CITATION.cff) · [Release notes](../RELEASE_NOTES.md) · [MIT code license](../LICENSE-CODE) · [CC BY 4.0 manuscript license](../LICENSE-PAPER.md). The bundled fonts have their own notices in [paper/v2/fonts](../paper/v2/fonts). These manuscripts are preprints. The author takes responsibility for the work, which was prepared with substantive assistance from ChatGPT.
