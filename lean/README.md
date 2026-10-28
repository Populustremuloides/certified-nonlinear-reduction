# General Lean proofs

This package contains the nine general named manuscript results, balancing and
their supporting bridges. `paper_correspondence.json` records their dimensions,
norms, quantifiers, hypotheses and scoped notation. `source_manifest.json`
records the unchanged proof-source hashes.

```sh
lake --keep-toolchain update
python3 apply_dependency_patch.py
lake exe cache get
lake build Populus
```

Lean and Mathlib are pinned. The build patch only changes ProofWidgets frontend
build configuration. General proofs contain no trained model coefficients.
The Python pipeline exports fresh numerical inputs under `runs/*/lean` and
checks their exact integer matrix witnesses when Lean verification is enabled.
The original two frozen-example results are retained in the local supplementary
audit package; they are not asserted for retrained coefficients. See the main
README and validation note for the exact scope of compilation and checks.
