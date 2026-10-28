.PHONY: run smoke test paper lean export
PYTHON ?= python3
run:
	$(PYTHON) -m stable_reduction.cli run
smoke:
	$(PYTHON) -m stable_reduction.cli run --config configs/smoke.json --output runs/smoke --skip-lean --skip-paper
test:
	$(PYTHON) -m pytest -q
paper:
	$(PYTHON) -m stable_reduction.cli paper
lean:
	cd lean && lake build Populus
export:
	@test -n "$(DEST)" || (echo 'Set DEST to a new destination directory'; exit 1)
	$(PYTHON) -m stable_reduction.cli export "$(DEST)"

.PHONY: publish publish-dry-run
publish:
	$(PYTHON) scripts/publish.py
publish-dry-run:
	$(PYTHON) scripts/publish.py --dry-run
