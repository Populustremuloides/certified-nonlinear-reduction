"""Python data products -> exact integer witnesses -> kernel-checked Lean facts.

Python proposes a congruence. Lean recomputes its products and inequalities.
No trained coefficients are source-controlled, and no fresh run inherits the
published example's non-contraction theorem.
"""

import hashlib
import json
import re
from pathlib import Path
import shutil
import subprocess
import numpy as np
import torch
from .data import sha, write

IMPORT = "Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction"


def exact(array, E):
    a = np.asarray(array, dtype=np.float64)
    if not np.isfinite(a).all():
        raise ValueError("Nonfinite proof input")
    result = []
    for value in a.flat:
        n, d = float(value).as_integer_ratio()
        power = d.bit_length() - 1
        if power > E:
            raise ValueError("Insufficient dyadic denominator")
        result.append(n * (1 << (E - power)))
    return np.array(result, dtype=object).reshape(a.shape)


def positive(z):
    if not np.array_equal(z, z.T):
        raise ValueError("Exact witness matrix is not symmetric")
    floating = np.array(z, dtype=float)
    floating /= np.max(abs(floating))
    L = np.linalg.cholesky((floating + floating.T) / 2)
    inv = np.linalg.inv(L.T)
    for rexp in [40, 60, 80]:
        R = np.array(
            [round(float(v) * (1 << rexp)) for v in inv.flat], dtype=object
        ).reshape(z.shape)
        S = R.T @ z @ R
        margins = [
            int(S[i, i]) - sum(abs(int(S[i, j])) for j in range(len(S)) if j != i)
            for i in range(len(S))
        ]
        if min(margins) > 0:
            return R, S
    raise ValueError("Exact congruence certificate failed; no claim exported")


def table(name, a):
    """Balanced decision trees, matching the existing kernel-checkable exporter."""
    shape = a.shape
    values = [str(int(x)) for x in a.flat]

    def choices(vals, index, offset=0):
        if len(vals) == 1:
            return vals[0]
        mid = len(vals) // 2
        return f"(if {index} < {offset+mid} then {choices(vals[:mid],index,offset)} else {choices(vals[mid:],index,offset+mid)})"

    chunks = [values[i : i + 32] for i in range(0, len(values), 32)]
    lines = [
        f'def {name}_chunk_{i} (j : ℕ) : ℤ := {choices(v,"j")}'
        for i, v in enumerate(chunks)
    ]
    lines.append(
        f'def {name}_chunk (i : ℕ) : ℕ → ℤ := {choices([name+"_chunk_"+str(i) for i in range(len(chunks))],"i")}'
    )
    lines.append(
        f"def {name} : Matrix (Fin {shape[0]}) (Fin {shape[1]}) ℤ := fun i j => {name}_chunk ((i.val*{shape[1]}+j.val)/32) ((i.val*{shape[1]}+j.val)%32)"
    )
    return lines


def emit_check(arrays, prefix, kind, index):
    source = {k: arrays[prefix + "_" + k] for k in ["A", "K", "P", "O"]}
    source["X"] = arrays[prefix + "_" + kind + "_X"]
    source["g"] = arrays[prefix + "_" + kind + "_g"]
    E = max(
        float(v).as_integer_ratio()[1].bit_length() - 1
        for a in source.values()
        for v in np.asarray(a).flat
    )
    D = 1 << E
    a, x, o = exact(source["A"], E), exact(source["X"], E), exact(source["O"], E)
    control = kind == "control"
    b = exact(source["P"], E) if control else 2 * exact(source["K"], E)
    g = int(exact(source["g"], E))
    c = 2 if control else 1
    ax = a.T @ x
    top = c * (D * D * x - ax @ a - D * (o.T @ o))
    cross = -c * (ax @ b)
    bottom = D * g * g * np.eye(b.shape[1], dtype=object) - c * (b.T @ x @ b)
    z = np.block([[top, cross], [cross.T, bottom]])
    RX, SX = positive(x)
    RQ, SQ = positive(z)
    items = dict(A=a, B=b, O=o, X=x, RX=RX, SX=SX, RQ=RQ, SQ=SQ)
    lines = [f"namespace Channel{index}", f"def D : ℤ := {D}"]
    for name, array in items.items():
        lines.extend(table(name, array))
    lines.append(f"def g : ℤ := {g}")
    check = "integerControlBoundedRealCheck" if control else "integerBoundedRealCheck"
    lines += [
        f"theorem accepted : {check} D A B O X RX SX g RQ SQ = true := by decide +kernel",
        f"theorem real_storage_and_gain : 0 ≤ (g:ℝ)/(D:ℝ) ∧ (scaledIntMatrix D X).PosDef ∧ (-boundedRealMatrix (scaledIntMatrix D A) "
        + (
            "((Real.sqrt 2) • scaledIntMatrix D B)"
            if control
            else "(scaledIntMatrix D B)"
        )
        + f" (scaledIntMatrix D O) (scaledIntMatrix D X) ((g:ℝ)/(D:ℝ))).PosSemidef := {check}_sound D A B O X RX SX g RQ SQ accepted",
        f"end Channel{index}",
    ]
    payload = {
        name: dict(shape=list(a.shape), entries=[str(int(v)) for v in a.flat])
        for name, a in items.items()
    }
    payload.update(
        denominator=str(D), gain=str(g), control_sqrt_two_rationalization=control
    )
    return lines, payload


def export_run(folder):
    folder = Path(folder)
    out = folder / "lean"
    out.mkdir(exist_ok=True)
    ckpath = folder / "training/normalized_selected.pt"
    ck = torch.load(ckpath, weights_only=False)
    # All neural coefficients are exported exactly, not only the linear certificate.
    model = {}
    for name, t in ck["model"].items():
        array = t.detach().numpy()
        ratios = [float(v).as_integer_ratio() for v in array.flat]
        model[name] = dict(
            shape=list(array.shape), ratios=[[str(n), str(d)] for n, d in ratios]
        )
    write(
        out / "coefficients.json",
        dict(
            checkpoint_sha256=sha(ckpath),
            arrays=model,
            interpretation="Exact stored binary floats as rational real constants.",
        ),
    )
    lines = [
        f"import {IMPORT}.ExecutableControlWitness",
        "namespace LocalRun",
        "open Populus.ModelReduction.Certified",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "set_option Elab.async false",
    ]
    entries = []
    sources = {}
    channels = []
    for path in sorted((folder / "evaluation").glob("certificate_r*/witness.npz")):
        report = json.loads((path.parent / "report.json").read_text())
        if not report["certifies_nonlinear_recurrence"]:
            continue
        with np.load(path) as arrays:
            for prefix in ["full", "reduced"]:
                for kind in ["autonomous", "control"]:
                    key = (
                        (prefix, kind)
                        if prefix == "full"
                        else (path.parent.name, prefix, kind)
                    )
                    if key in channels:
                        continue
                    channel_lines, payload = emit_check(
                        arrays, prefix, kind, len(entries)
                    )
                    lines.extend(channel_lines)
                    entries.append(dict(channel=list(key), payload=payload))
                    channels.append(key)
        sources[str(path.relative_to(folder))] = sha(path)
    declarations = [
        f"LocalRun.Channel{i}.real_storage_and_gain" for i in range(len(entries))
    ]
    lines += ["end LocalRun"] + ["#print axioms " + name for name in declarations]
    (out / "LocalCertificates.lean").write_text("\n".join(lines) + "\n")
    write(out / "integer_witnesses.json", dict(certificates=entries))
    write(
        out / "manifest.json",
        dict(
            checkpoint_sha256=sha(ckpath),
            coefficients_sha256=sha(out / "coefficients.json"),
            source_witnesses=sources,
            generated_lean_sha256=sha(out / "LocalCertificates.lean"),
            integer_witnesses_sha256=sha(out / "integer_witnesses.json"),
            declarations=declarations,
            verified=False,
            scope="Fresh matrix witness facts only until Lean compilation succeeds. General nonlinear implications are separate library results.",
        ),
    )


def verify_run(lean, folder):
    lean = Path(lean).resolve()
    folder = Path(folder).resolve()
    out = folder / "lean"
    manifest = json.loads((out / "manifest.json").read_text())
    for key, name in [
        ("coefficients_sha256", "coefficients.json"),
        ("generated_lean_sha256", "LocalCertificates.lean"),
        ("integer_witnesses_sha256", "integer_witnesses.json"),
    ]:
        if manifest[key] != sha(out / name):
            raise ValueError("Changed generated proof input: " + name)
    if manifest["checkpoint_sha256"] != sha(folder / "training/normalized_selected.pt"):
        raise ValueError("Changed model after Lean export")
    for path, digest in manifest["source_witnesses"].items():
        if sha(folder / path) != digest:
            raise ValueError("Changed certificate after Lean export")
    if shutil.which("lake") is None:
        raise RuntimeError(
            "Install the pinned Lean toolchain through elan, or explicitly use --skip-lean."
        )
    registry = json.loads((lean / "paper_correspondence.json").read_text())
    general_declarations = [
        x["target_declaration"] for x in registry["required_results"]
    ]
    audit = out / "GeneralAxiomAudit.lean"
    audit.write_text(
        "import Populus\n"
        + "\n".join("#print axioms " + d for d in general_declarations)
        + "\n"
    )
    with (out / "build.log").open("w") as log:

        commands = []
        if not (lean / ".lake/packages/mathlib").exists():
            commands += [
                ["lake", "--keep-toolchain", "update"],
                ["python3", "apply_dependency_patch.py"],
                ["lake", "exe", "cache", "get"],
            ]
        commands += [
            ["lake", "build", "Populus"],
            ["lake", "env", "lean", str(audit)],
            ["lake", "env", "lean", str(out / "LocalCertificates.lean")],
        ]
        for command in commands:
            if command == ["lake", "build", "Populus"]:
                preflight_general(lean)
            print(
                json.dumps(
                    dict(
                        stage="lean_verification",
                        command=command,
                        log=str(out / "build.log"),
                    )
                ),
                flush=True,
            )
            subprocess.run(
                command, cwd=lean, stdout=log, stderr=subprocess.STDOUT, check=True
            )

    found = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
        (out / "build.log").read_text(),
    )
    expected = set(general_declarations + manifest["declarations"])
    axioms = {
        name: sorted(x.strip() for x in values.split(",") if x.strip())
        for name, values in found
        if name in expected
    }
    if set(axioms) != expected:
        raise ValueError("Incomplete Lean axiom audit")
    for name, values in axioms.items():
        if not set(values) <= set(["propext", "Classical.choice", "Quot.sound"]):
            raise ValueError("Unexpected axioms in " + name)
    manifest["axioms"] = axioms
    manifest["verified"] = True
    manifest["scope"] = (
        "Lean compiled the general library and generated exact matrix witness facts. This is not a new proof of published frozen-model non-contraction, nor an IEEE/plant-accuracy theorem."
    )
    write(out / "manifest.json", manifest)


def preflight_general(lean):
    """Refuse drift in the reviewed source and dependency boundary."""
    lean = Path(lean)
    spec = json.loads((lean / "source_manifest.json").read_text())
    for name, digest in spec["sources"].items():
        if sha(lean / name) != digest:
            raise ValueError(
                "General Lean source differs from reviewed snapshot: " + name
            )
    correspondence = json.loads((lean / "paper_correspondence.json").read_text())
    if sha(lean.parent / "paper/main.tex") != correspondence["source_sha256"]:
        raise ValueError(
            "Manuscript changed; review its proof correspondence before refreshing any hashes."
        )
    dependencies = json.loads((lean / "package_manifest.json").read_text())[
        "dependencies"
    ]
    for name, entry in dependencies.items():
        path = lean / ".lake/packages" / name
        revision = subprocess.check_output(
            ["git", "-C", str(path), "rev-parse", "HEAD"], text=True
        ).strip()
        if revision != entry["revision"]:
            raise ValueError("Lean dependency revision differs: " + name)
        patch = subprocess.check_output(
            ["git", "-C", str(path), "diff", "HEAD", "--no-ext-diff", "--binary"]
        )
        if patch and hashlib.sha256(patch).hexdigest() != entry.get(
            "allowed_patch_sha256"
        ):
            raise ValueError("Unreviewed Lean dependency patch: " + name)
