> **Серия:** 110 OBSERVER — Точная наблюдаемость, причинное самообращение и границы вывода<br>
> **Документ:** История выпусков<br>
> **Статус:** VERSIONED<br>
> **Карта серии:** [Монография](110_OBSERVER_Preprint.pdf) · [Индекс](README.md) · [Источники и разделы](docs/series.md) · [Архив](archive/README.md)<br>
> **Зависимости:** Датированные состояния геометрии и экспериментального среза.

# Единый препринт 110 OBSERVER

**Редакционная правка `v2.2.1-monograph-multilingual`.** В трёх изданиях адреса слотов получили префикс `leaf:`. Из приложения C можно перейти к условной теореме T6 в §6. В русском тексте имя Uzay Macar приведено полностью, а при первом упоминании модели выделено написание OLMo. Исходные измерения и реестр относятся к тому же экспериментальному срезу.

**Многоязычный выпуск `v2.2-monograph-multilingual`.** Редакция от 20 ноября 2026 г. доступна на [русском](110_OBSERVER_Preprint.pdf), [английском](110_OBSERVER_Preprint_en.pdf) и [упрощённом китайском](110_OBSERVER_Preprint_zh.pdf). Каждый перевод включает семь разделов, три приложения и библиографию. Русский PDF совпадает с выпуском `v2.1-monograph-dev` по SHA-256.

**Редакция `v2.1-monograph-dev`.** В аннотации назван внешний однобитный регистр, техническое доказательство теоремы 3.8 собрано в приложении A. На рассмотренной dev-панели OLMo передача выбранного правила дала 64/64 правильных ответа на различающих строках, постоянный токен A — 32/64. В §7 задан будущий опыт T3 и выведен потолок 75% для фиксированного адреса на сбалансированной панели. Эксперимент имеет статус `NOT_RUN`. [Контрольные суммы всего комплекта](SHA256SUMS)

20 ноября 2026 г. · Геометрия решётки и прежние издания представлены в архиве. Главный файл для цитирования — [единая монография](./110_OBSERVER_Preprint.pdf). Lean 4.35.0 на arm64 воспроизвёл все 263 модуля доказательства о решётке и 11 объявлений наблюдателя с их реальными импортами. [Журнал геометрии](verification/monograph/geometry-axioms.log) · [Журнал наблюдателя](verification/monograph/observer-axioms.log)

Статус OLMo относится к dev-срезу после варианта A. Формулировки об открытой гипотезе ниже относятся к первому выпуску.

# Combined preprint v2.0.0

The Lean theorem `Rails.essential_iff` settles all-time gap-free essentiality on the infinite lattice. The proof combines a finite base for t < 2485 with five strips for t ≥ 2485. The English, Russian and Simplified Chinese manuscripts, their typesetting sources, the proof generator and compiler reports are included.

The first manuscript and its [Zenodo record](https://doi.org/10.5281/zenodo.24334185) remain available. The notes below describe that edition at publication time.

# Research package v1.0.0 — 18 November 2026

This file documents the preparation and verification of the first reproducible Rule 110 research package. It is a historical build record, not a publication-submission guide.

## Research and verification changes

- Synchronized the formal Lean source's introductory status with the successful supplied Lean 4.35.0 report; declarations and proofs were not changed. Preserved the attested source and report for independent verification.
- Updated the Russian proof's status to distinguish Lean-checked infinite-lattice theorems from the non-formalized finite-ring proposition and open conjecture.
- Added the manuscript's disclosure of substantive ChatGPT assistance and compiled the four-page PDF.
- Independently enumerated all \(2^{20}\) Rule 110 ring configurations through \(t=130\); at \(t=121\), obtained 2,095 future states and all 20 essential initial sites.
- Re-ran the periodic-background witness search through \(t=2000\), covering all 3,337,668 pairs.
- Added machine-readable citation metadata, licensing notes, checksums, reproducibility targets, and GitHub Actions checks.
- The repository now links to the published [Zenodo preprint](https://zenodo.org/records/24334185).

## Verification boundaries

GitHub Actions independently compiled the four principal Lean 4.35.0 infinite-lattice theorems. The supplied attestation is retained with its source hash. The all-time gap-free essentiality statement remains an open conjecture; the general finite-ring theorem is a human mathematical proof rather than a Lean theorem. A comprehensive prior-art/novelty evaluation has not been certified.
