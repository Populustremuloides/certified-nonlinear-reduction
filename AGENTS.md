# Paper repository rules

Every edited TeX document starts with a comment requiring one sentence per source
line. Keep the complete manuscript, references and appendix in paper/main.tex.

Never commit checkpoints, generated model coefficients, physical caches or run
outputs. All generated products belong in runs/. Use the source-only exporter.
Do not replace the published model's results with a fresh run's results silently.

Show and inspect prediction loss versus actual optimizer updates whenever fitting
or assessing a model. Report validation, stopping criteria and resource limits.
An update limit or rejected-step stall is not a measured plateau.

The normalized and raw models use the same data and algorithm. Never select a
checkpoint or seed using reserved cases or the presence of instability. Report
missing accuracy, certification or instability gates explicitly.

Lean coefficient definitions are generated from exact local data products. Do
not assert that compiled general theorems verify a fresh numerical instance.
Do not transfer the published model's non-contraction theorem to retrained weights.
