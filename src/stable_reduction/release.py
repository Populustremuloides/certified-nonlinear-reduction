"""Source-only export with an explicit allowlist; never copy generated runs."""

from pathlib import Path
import hashlib
import json
import shutil

DIRECTORIES = [
    "src",
    "tests",
    "configs",
    "docs",
    "scripts",
    "provenance",
    "results",
    "lean",
    "paper",
]
FILES = [
    "README.md",
    "pyproject.toml",
    "requirements-reference.txt",
    "Makefile",
    ".gitignore",
    "AGENTS.md",
    "THIRD_PARTY_NOTICES.md",
    "run.sh",
    ".texdesk.json",
    "texdesk.workspace.json",
]
EXCLUDED = {
    ".git",
    ".lake",
    "__pycache__",
    ".pytest_cache",
    "build",
    "output",
    "runs",
    "LocalRun",
    "code_supplement",
    "evidence",
    "writing-history",
    ".texdesk-build",
    ".DS_Store",
}
FORBIDDEN = {
    ".pt",
    ".pth",
    ".ckpt",
    ".onnx",
    ".safetensors",
    ".npz",
    ".npy",
    ".olean",
    ".ilean",
    ".pyc",
    ".bin",
    ".pkl",
    ".pickle",
    ".h5",
    ".hdf5",
}


def export(root, destination):
    root = Path(root).resolve()
    destination = Path(destination).resolve()
    if destination == root or root in destination.parents:
        raise ValueError("Export outside the source tree")
    if destination.exists():
        raise FileExistsError("Refusing to overwrite export")
    destination.mkdir(parents=True)
    try:
        for name in FILES:
            if (root / name).is_file():
                shutil.copy2(root / name, destination / name)
        for name in DIRECTORIES:
            for path in (root / name).rglob("*"):
                rel = path.relative_to(root)
                if any(p in EXCLUDED or p.endswith(".egg-info") for p in rel.parts):
                    continue
                if path.name.endswith((".swp", ".swo", ".swx", "~")):
                    continue
                if path.is_symlink():
                    raise ValueError("Public export contains a symlink: " + str(rel))
                if not path.is_file():
                    continue
                if path.suffix.lower() in FORBIDDEN:
                    raise ValueError(
                        "Public source tree contains a generated binary/data product: "
                        + str(rel)
                    )
                if path.name in [
                    "dyadic_parameters.json",
                    "integer_positivity_certificates.json",
                    "coefficients.json",
                ] or path.name.startswith("Frozen"):
                    raise ValueError(
                        "Trained-coefficient proof input would be exported: " + str(rel)
                    )
                target = destination / rel
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(path, target)
        inventory = {
            str(p.relative_to(destination)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in destination.rglob("*")
            if p.is_file()
        }
        (destination / "SOURCE_MANIFEST.json").write_text(
            json.dumps(dict(files=inventory, models_included=False), indent=2) + "\n"
        )
    except Exception:
        # Preserve a failed export for inspection; it is never called complete.
        (destination / "EXPORT_FAILED.txt").write_text(
            "Export failed. Do not publish this directory.\n"
        )
        raise
    print(destination)
