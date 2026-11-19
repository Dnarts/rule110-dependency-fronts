For every nonnegative time t, the essential inputs of Rule 110 on the infinite line are exactly the integers from −(t − floor(t/3)) through t. The single-bit witness may vary with the input coordinate and time.

The attached English, Russian and Simplified Chinese PDFs each have a corresponding XeLaTeX source ZIP. GitHub's source archive contains the proof and certificate generator. Run `make verify` with Python 3.10+ and Lean 4.35.0. The compiler reports `[propext, Classical.choice, Quot.sound]` for `Rails.essential_iff`.

[Root theorem](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.0.0/lean/Rule110Exact.lean) · [First preprint on Zenodo](https://doi.org/10.5281/zenodo.24334185)
