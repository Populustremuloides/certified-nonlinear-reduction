#!/usr/bin/env python3
"""Publish only the committed paper subtree, never dissertation history."""
from pathlib import Path
import argparse
import json
import subprocess
import sys
import tempfile

SOURCE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SOURCE / "src"))
from stable_reduction.release import export


def git(*args, capture=True):
    return (
        subprocess.check_output(["git", "-C", str(SOURCE), *args], text=True).strip()
        if capture
        else subprocess.run(["git", "-C", str(SOURCE), *args], check=True)
    )


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--dry-run", action="store_true")
    p.add_argument(
        "--remote",
        default="https://github.com/Populustremuloides/certified-nonlinear-reduction.git",
    )
    p.add_argument("--branch", default="main")
    args = p.parse_args()
    repository = Path(git("rev-parse", "--show-toplevel")).resolve()
    prefix = SOURCE.relative_to(repository).as_posix()
    if prefix == ".":
        prefix = ""
    with tempfile.TemporaryDirectory(prefix="stable-reduction-publish-") as temp:
        target = Path(temp) / "source"
        export(SOURCE, target)
        expected = set(
            json.loads((target / "SOURCE_MANIFEST.json").read_text())["files"]
        )
    raw = subprocess.check_output(
        ["git", "-C", str(repository), "ls-files", "-z", "--", prefix or "."]
    )
    tracked = {
        str(Path(x.decode()).relative_to(prefix)) if prefix else x.decode()
        for x in raw.split(b"\0")
        if x
    }
    if tracked != expected:
        raise SystemExit(
            "Public source boundary differs from tracked files. Commit all intended source files and remove any private tracked files first.\nMissing: "
            + repr(sorted(expected - tracked))
            + "\nUnexpected: "
            + repr(sorted(tracked - expected))
        )
    subprocess.run(
        ["git", "-C", str(repository), "diff", "--quiet", "HEAD", "--", prefix or "."],
        check=True,
    )
    print(
        json.dumps(
            dict(
                repository=args.remote,
                branch=args.branch,
                source_files=len(tracked),
                models_included=False,
                dissertation_history_included=False,
                dry_run=args.dry_run,
            )
        ),
        flush=True,
    )
    if args.dry_run:
        return
    sha = (
        git("subtree", "split", "--prefix=" + prefix, "HEAD")
        if prefix
        else git("rev-parse", "HEAD")
    )
    if len(sha) != 40 or any(c not in "0123456789abcdef" for c in sha):
        raise SystemExit("Unexpected source commit ID")
    subprocess.run(
        [
            "git",
            "-C",
            str(repository),
            "push",
            args.remote,
            sha + ":refs/heads/" + args.branch,
        ],
        check=True,
    )
    print("Published source commit " + sha)


if __name__ == "__main__":
    main()
