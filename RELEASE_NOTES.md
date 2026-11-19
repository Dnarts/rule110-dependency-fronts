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
