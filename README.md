# Learning Nonlinear Predictors with Certified Stable Reductions

This source repository collects the manuscript, physical MEMS simulation,
state-inclusive neural predictor, balanced reduction, certificate checker and
Lean proofs. It distributes no trained models. Every run generates its own
physical data, weights, certificates, loss curves and evaluation figures locally.

Public repository: [Populustremuloides/certified-nonlinear-reduction](https://github.com/Populustremuloides/certified-nonlinear-reduction).

This is the permanent editing home. Open `paper/main.tex` in TeX Desk or open
this folder using its `.texdesk.json`. See [validation status](docs/validation.md)
for the precise tested scope. A full rehearsal was explicitly waived for this
cleanup; no empirical-equivalence claim is inferred from that decision.

## Run the experiment

Use Python 3.10, 3.11 or 3.12 and a TeX distribution with pdfLaTeX. Install Lean
through elan if you want the formal checks in the same run. Then, from this
repository:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements-reference.txt
python -m pip install -e '.[dev]'
./run.sh
```

The default command uses `configs/paper.json` and writes to `runs/reproduction`.
It refuses to overwrite an existing run. Choose another `--output` directory for
another seed/configuration. Training is a CPU experiment, not a quick demo.
Progress and elapsed time are printed as each stage completes. Frozen weights
are never downloaded or required.

For a short integration check:

```sh
stable-reduction run --config configs/smoke.json --output runs/smoke --skip-paper --skip-lean
```

The smoke configuration deliberately uses a coarser clock, two physical
protocols per group and two training updates. It tests the pipeline, not the
paper's accuracy, convergence or instability result. Its figures are labeled by
the run metadata. `--skip-lean` and `--skip-paper` explicitly omit those stages.

## Read the results

- `training/losses.pdf` shows full, reduced and development prediction losses
  against optimizer updates. Regularization is recorded separately in the logs.
- `training/stopping.json` distinguishes a measured plateau after step-size
  recovery from reaching the configured update limit.
- `evaluation/figure.pdf` compares full and reduced predictions with the physical
  reference, shows the nine-state response and sweeps reduction order.
- `evaluation/reserved_metrics.csv` contains every reserved-case result, including
  stopped rollouts and observed-prefix error lower bounds.
- `evaluation/qualification.json` reports accuracy, certification and numerical
  growth as separate gates. It never declares a successful instability contrast
  merely because the pipeline completed.
- `evaluation/certificate_r*/` contains the actual deployed linear blocks,
  bounded-real witnesses and directed-rounding reports.
- `lean/` inside a run contains exact coefficient exports, integer witnesses,
  generated Lean statements, a manifest and, after verification, the build log.

Use `--require-paper-contrast` to return a nonzero exit status when any declared
accuracy/certification/growth gate fails. A fresh run can still be useful without
reproducing the selected historical instability contrast. Inspect its curves and
qualification report before making scientific claims.

## Relationship to the published experiment

The predictor recurrence, 96 physical coordinates, eight added observables,
normalization, balanced projection, full/reduced prediction objective, closure
terms and certificate mathematics follow the manuscript implementation.
`provenance/source_extraction.json` identifies the original routines used here.

The published experiment continued several earlier fits. This package replaces
those unavailable warm starts with explicit fresh initialization, autonomous
observable regression, window warm-up and full-horizon fitting. It is a new
from-scratch training recipe, not a replay of the entire historical optimization
chain. Its empirical equivalence to the published result requires a full run;
a passing smoke test does not establish it. No checkpoint or seed is selected
using reserved tests or observed reduced instability.

The canonical manuscript is `paper/main.tex`. Building it retains the reported
numbers and figure. Fresh results live in run reports and never replace the
publication records automatically. `results/published/` contains saved metrics
without weights. `provenance/manuscript_snapshot.json` records the editing-home
migration. Historical material is retained outside this source package.

## Lean and generated data

`lean/` at the repository root contains unchanged sources for the nine general
manuscript results, with Lean and Mathlib pinned. No trained coefficients are
embedded there. See `lean/paper_correspondence.json` for their scope.

Python exports exact rational interpretations of the locally stored binary
coefficients and proposes integer congruence witnesses. Generated Lean checks
matrix products and positivity inequalities using `decide +kernel`, then applies
the library soundness theorems. Successful compilation establishes those matrix
facts; the general library supplies the nonlinear small-gain implications.
It does not prove physical prediction accuracy, IEEE execution correctness or
that a fresh model satisfies the published example's non-contraction result.
That example-specific formal audit remains in the local dissertation archive.
The historical manuscript's example-specific Lean links refer to that archive.

Before the first formal build:

```sh
cd lean
lake --keep-toolchain update
python3 apply_dependency_patch.py
lake exe cache get
lake build Populus
cd ..
```

These are source dependencies and proof caches, not trained-model downloads.
The generated numerical proofs can take substantially longer than the Python
interval checks. A skipped or failed Lean stage is recorded as such.

## Work on the source

```sh
python -m pytest -q
stable-reduction paper
stable-reduction export /tmp/certified-stable-reductions-public
```

After committing edits in the dissertation, use `make publish` to update the
standalone repository with source-only history. `make publish-dry-run` previews
the source boundary. This keeps the paper in the dissertation repository without
a nested Git repository or a second maintained source copy.

The exporter uses an allowlist and rejects checkpoints, NumPy data archives,
compiled Lean objects, symlinks and generated coefficient files in the source
payload. Run outputs, private audit evidence, local environments and writing
history are excluded. No reuse license has been assigned to the original
source; third-party components retain their notices. See the notices file.
