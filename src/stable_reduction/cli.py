"""Single-command orchestration. Every generated model stays in the run directory."""

import argparse
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time
import traceback

# Control oversubscription before importing numerical libraries.
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("MPLBACKEND", "Agg")
os.environ.setdefault(
    "MPLCONFIGDIR",
    str(Path(os.environ.get("TMPDIR", "/tmp")) / "stable-reduction-matplotlib"),
)


def root():
    return Path(__file__).resolve().parents[2]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    run = sub.add_parser(
        "run", help="Generate data, train, freeze, test, certify, plot, and build"
    )
    run.add_argument("--config", type=Path, default=root() / "configs/paper.json")
    run.add_argument("--output", type=Path, default=root() / "runs/reproduction")
    run.add_argument("--skip-paper", action="store_true")
    run.add_argument("--skip-lean", action="store_true")
    run.add_argument(
        "--require-paper-contrast",
        action="store_true",
        help="Exit nonzero unless accuracy/certification/growth gates all pass",
    )
    sub.add_parser(
        "paper",
        help="Compile the publication manuscript without changing its numerical claims",
    )
    export = sub.add_parser(
        "export",
        help="Export source only, with no checkpoints or generated coefficients",
    )
    export.add_argument("destination", type=Path)
    args = p.parse_args()
    if args.command == "paper":
        subprocess.run(
            ["/bin/sh", "compile_paper.sh"], cwd=root() / "paper", check=True
        )
        return
    if args.command == "export":
        from .release import export

        export(root(), args.destination)
        return
    from .data import generate, write, sha
    from .training import train
    from .evaluation import evaluate
    from .lean_export import export_run, verify_run
    import torch
    import numpy as np

    torch.set_default_dtype(torch.float64)
    torch.set_num_threads(1)
    cfg = json.loads(args.config.read_text())
    folder = args.output.resolve()
    import shutil

    if not args.skip_lean and shutil.which("lake") is None:
        p.error("Install Lean through elan, or explicitly use --skip-lean.")
    if (
        not args.skip_paper
        and shutil.which("pdflatex") is None
        and not Path("/Library/TeX/texbin/pdflatex").exists()
    ):
        p.error("Install pdfLaTeX, or explicitly use --skip-paper.")
    # Check storage before starting the full physical-data cache.
    protocol_count = (
        (6 + 4 + 6) if not cfg.get("protocol_limit") else 3 * cfg["protocol_limit"]
    )
    expected = int(
        protocol_count
        * (round(cfg["data_horizon_us"] / cfg["dt_us"]) + 1)
        * 96
        * 8
        * 1.25
        + 100_000_000
    )
    probe = folder.parent
    while not probe.exists():
        probe = probe.parent
    if shutil.disk_usage(probe).free < expected:
        p.error(
            f"This run needs approximately {expected/1e9:.2f} GB of free disk for data and outputs; choose a larger volume with --output."
        )
    # Refuse any overwrite, including failed runs. Each run is an immutable record.
    folder.mkdir(parents=True, exist_ok=False)
    env = dict(
        python=sys.version,
        platform=platform.platform(),
        packages={
            n: importlib.metadata.version(n)
            for n in ["numpy", "scipy", "torch", "matplotlib", "mpmath"]
        },
    )
    write(folder / "environment.json", env)
    write(folder / "config.json", cfg)
    from .data import RESERVED

    sources = {
        str(p.relative_to(root())): sha(p) for p in (root() / "src").rglob("*.py")
    }
    write(folder / "source_hashes.json", sources)
    write(
        folder / "precommit.json",
        dict(
            seed=cfg["seed"],
            selection="Development prediction loss only. Never select on instability or reserved tests.",
            reserved_protocols=RESERVED,
            config_sha256=sha(folder / "config.json"),
            historical_weights_used=False,
        ),
    )
    started = time.monotonic()
    stage = "initializing"
    status = dict(complete=False, smoke=cfg.get("smoke", False), stages={})
    try:
        for stage, action in [
            ("data", lambda: generate(folder / "data", cfg)),
            ("training", lambda: train(folder, cfg)),
            (
                "reserved_data",
                lambda: generate(folder / "data", cfg, groups=("reserved",)),
            ),
            ("evaluation", lambda: evaluate(folder, cfg)),
            ("lean_export", lambda: export_run(folder)),
        ]:
            now = time.monotonic()
            print(json.dumps(dict(stage=stage, status="started")), flush=True)
            result = action()
            status["stages"][stage] = dict(
                seconds=time.monotonic() - now, complete=True
            )
            if stage == "evaluation":
                status["qualification"] = result
            write(folder / "status.json", status)
        if not args.skip_lean:
            stage = "lean_verification"
            verify_run(root() / "lean", folder)
            status["stages"][stage] = dict(complete=True)
        if not args.skip_paper:
            stage = "paper"
            subprocess.run(
                ["/bin/sh", "compile_paper.sh"], cwd=root() / "paper", check=True
            )
            status["stages"][stage] = dict(
                complete=True,
                scope="Published manuscript; fresh numerical results are in the run report, not substituted into the paper.",
            )
        status.update(complete=True, elapsed_seconds=time.monotonic() - started)
        write(folder / "status.json", status)
        print(json.dumps(dict(output=str(folder), **status)), flush=True)
        if (
            args.require_paper_contrast
            and not status["qualification"]["paper_contrast_reproduced"]
        ):
            raise SystemExit(2)
    except Exception:
        status.update(
            complete=False,
            failed_stage=stage,
            error=traceback.format_exc(),
            elapsed_seconds=time.monotonic() - started,
        )
        write(folder / "status.json", status)
        raise


if __name__ == "__main__":
    main()
