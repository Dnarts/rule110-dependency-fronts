# Supplied originals and historical checks

These files preserve the eleven incoming attachments. The filename of the
Russian PDF was normalized from `rule110-continuation-ru(1).pdf` to
`rule110-continuation-ru.pdf`; its bytes are unchanged. The
[manifest](manifest.json) records every original filename, archived path,
byte count and SHA-256.

- The four mathematical `.lean` files are also the unchanged canonical files
  in [../../lean](../../lean/).
- The supplied `AxiomAudit.lean` duplicates the complete seam implementation
  and appends 22 print commands. Removing those commands reproduces the seam
  source text, apart from surrounding whitespace. The canonical audit instead
  imports the canonical seam module.
- `Rule110RingDecoupling.axioms.txt` records an earlier Lean 4.33.1 build. It is
  historical evidence; the publication was checked afresh on Lean 4.35.0.
- `MergeMinimality4.check.log` is an **unsuccessful historical build** (exit 1,
  with `sorryAx`) of source SHA-256
  `2f450f16d3d7049455c5f70863098797277303b24565d987dee59a15e31b5727`.
  That hash differs from the supplied current source's
  `da41665bb1ab2d72dcb9501560a64d6fda4bca01e01c672822f7606194bdd651`.
- `MergeMinimality4.axioms.txt` identifies that current source and records a
  later successful check. The fresh publication build independently checks it.
- The seam and stream reports are also retained as supplied. They are not
  substituted for fresh compilation.

`MergeThreshold.lean` was named in the supplied article but not included among
the attachments. Its publication implementation is newly reconstructed in
[../../lean/MergeThreshold.lean](../../lean/MergeThreshold.lean).

Use [the current report](../../verification/REPORT.md) and
[fresh audit records](../../verification/current/lean-check.json) for the
publication's verification status.
