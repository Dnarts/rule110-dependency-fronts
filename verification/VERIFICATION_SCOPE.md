> **Серия:** 110 OBSERVER — Точная наблюдаемость, причинное самообращение и границы вывода<br>
> **Документ:** Paper I · границы проверок<br>
> **Статус:** VERIFICATION<br>
> **Карта серии:** [Монография](../110_OBSERVER_Preprint.pdf) · [Индекс](../README.md) · [Источники и разделы](../docs/series.md) · [Архив](../archive/README.md)<br>
> **Зависимости:** Отчёты первого издания и полного доказательства.

# Verification scope

## Unified monograph, 20 November 2026

The macOS arm64 rebuild with Lean 4.35.0 compiled all 263 modules in the import closure of `Rule110Exact`. Compiling `observer/Rule110Observer.lean` against those outputs produced eleven axiom reports. The two reports are published alongside this edition. [Geometry](monograph/geometry-axioms.log) · [Observer](monograph/observer-axioms.log)

## Combined preprint (v2)

Lean 4.35.0 checks `Rails.essential_iff` on the infinite lattice for every natural time and every integer input coordinate. Its finite part covers 5,147,263 pairs through t=2484. The five strips of `Rails.late_all` cover all later times. The [root report](v2/final.log) lists exactly `[propext, Classical.choice, Quot.sound]`. Run `make verify` for a fresh build. The finite-ring proposition remains a mathematical proof in the manuscript.

## First preprint (v1)

The ledger below documents the scope of the first publication.


## `LEAN_ATTESTED_INPUT`

`reports/lean_check_status_supplied.txt` came with the user-uploaded archive. It reports:

- `lean rule110_complete.lean` on Lean 4.35.0 (arm64-apple-darwin): exit 0, no errors or warnings.
- The four main theorems `left_dependency_bound`, `right_dependency_bound`, `left_endpoint_essential`, and `right_endpoint_essential` depend on `propext`, `Quot.sound`, and for the endpoint theorems `Classical.choice` (no `sorryAx`).
- Exact SHA-256 of `attested_source/rule110_complete.lean` matched the supplied status file when this package was rebuilt.

The current author-facing `../formal/rule110_complete.lean` differs from that attested source **only in its introductory documentation comment**. The declarations and proofs after the first `-/` are byte-for-byte identical. The human author or GitHub Actions should rerun Lean on the current file for a fresh compiler log.

## `FINITE_CHECK`

`rule110_certificate.py`, `rule110_crosscheck.ts`: all local cases; small finite rings; traveling-defect base recurrence. Python and TypeScript are independently implemented. No implication of an all-time proof by finite enumeration.

## `COMPUTATIONAL_EVIDENCE`

All 3,337,668 pairs `(t,j)` for `0 <= t <= 2000` were covered by periodic-background witnesses with periods <=10. The tests run on periodic rings with a correctly non-wrapping defect support for this time horizon. This does not prove all-time gap-free interior support.

## `RING20_EXHAUSTIVE`

NumPy vectorization enumerates all 2^20 initial states. For every time t=0..130, it computes the entire output map, and tests essentiality of every coordinate j. At t=121, the future image has 2,095 states (12 bits) while all 20 input sites remain essential. The audit also confirms all 20 are essential for each t=11..130.

## `HUMAN_MATHEMATICAL_PROOF`

The finite-state all-time certification proposition follows from eventual periodicity of finite deterministic maps; it is not in the Lean module. Scholarly originality/prior-art status is not established solely by the checks.
