from pathlib import Path
import json
import numpy as np
import pytest
import torch
from stable_reduction.model import Model
from stable_reduction.rollout import segment_for
from stable_reduction.interval import iv_matrix, positive_ldl
from stable_reduction.certification import storage, verify
from stable_reduction.lean_export import exact, positive, emit_check
from stable_reduction.release import export
from stable_reduction.training import plateau


@pytest.fixture(autouse=True)
def dtype():
    torch.set_default_dtype(torch.float64)
    torch.set_num_threads(1)


@pytest.fixture
def model():
    data = dict(
        A=0.8 * np.eye(96),
        readout=np.eye(96),
        observation=np.r_[np.eye(96), np.ones((1, 96)) / 96],
        feature_physical_scale=np.ones(96),
        port=np.ones((96, 1)) * 0.01,
    )
    m = Model(data)
    m.nominal.data[96:, 96:] = 0.7 * torch.eye(8)
    return m


def test_state_reconstruction_and_origin(model):
    z = torch.randn(7, 96)
    assert torch.equal(model.lift(z)[:, :96], z)
    assert torch.equal(model.lift(torch.zeros(1, 96)), torch.zeros(1, 104))
    assert torch.equal(
        model.step(torch.zeros(1, 104), torch.zeros(1, 1), model.tensors()),
        torch.zeros(1, 104),
    )


def test_global_envelopes_and_scripted_gradient(model):
    for scale in [1e-6, 1.0, 1e6]:
        z = torch.randn(9, 104) * scale
        u = torch.randn(9, 1) * scale
        a, c = model.factors(z, u)
        assert torch.all(a.norm(dim=1) <= z.norm(dim=1) * (1 + 1e-12))
        assert torch.all(c.norm(dim=1) <= np.sqrt(2) * u[:, 0].abs() * (1 + 1e-12))
    z = torch.randn(2, 104) * 0.01
    u = torch.ones(2, 1) * 0.1
    parameters = [p for p in model.parameters() if p.requires_grad]
    gradients = []
    outputs = []
    for scripted in [False, True]:
        model.zero_grad()
        s = z.clone()
        for _ in range(4):
            s = (
                segment_for(model).step(s, u, model.tensors())
                if scripted
                else model.step(s, u, model.tensors())
            )
        s.square().sum().backward()
        outputs.append(s.detach())
        gradients.append(
            torch.cat(
                [
                    (
                        p.grad.flatten()
                        if p.grad is not None
                        else torch.zeros_like(p).flatten()
                    )
                    for p in parameters
                ]
            )
        )
    torch.testing.assert_close(outputs[0], outputs[1], rtol=1e-12, atol=1e-14)
    torch.testing.assert_close(gradients[0], gradients[1], rtol=1e-11, atol=1e-13)


def test_directed_witness_and_exact_export():
    a = np.array([[0.5]])
    b = np.array([[0.1]])
    o = np.array([[1.0]])
    X, g = storage(a, b, o, "autonomous")
    assert verify(iv_matrix(a), iv_matrix(b), iv_matrix(o), X, g)["gain_upper"] < 1
    with pytest.raises(ValueError):
        positive_ldl(iv_matrix(np.array([[-1.0]])))
    arrays = dict(
        full_A=a,
        full_K=b / 2,
        full_P=b,
        full_O=o,
        full_autonomous_X=X,
        full_autonomous_g=np.array(g),
    )
    lean, payload = emit_check(arrays, "full", "autonomous", 0)
    assert "decide +kernel" in "\n".join(lean)
    assert "native_decide" not in "\n".join(lean)
    assert payload["control_sqrt_two_rationalization"] is False
    for v, i in zip(a.flat, exact(a, 80).flat):
        assert int(i) * float(v).as_integer_ratio()[1] == float(v).as_integer_ratio()[
            0
        ] * (1 << 80)


def test_source_export_rejects_model(tmp_path):
    src = tmp_path / "source"
    (src / "src").mkdir(parents=True)
    (src / "src/model.pt").write_bytes(b"model")
    with pytest.raises(ValueError, match="generated binary"):
        export(src, tmp_path / "release")


def test_plateau_is_componentwise():
    cfg = dict(patience=3, relative_improvement=0.005)
    h = [
        dict(full_prediction=1.0, reduced_prediction=1.0, primary_prediction=11.0)
        for _ in range(4)
    ]
    assert plateau(h, cfg)
    h[-1]["reduced_prediction"] = 0.9
    assert not plateau(h, cfg)


def test_checkpointing_keeps_gradients_across_chunks(model):
    from stable_reduction.training import loss

    torch.manual_seed(12)
    V = torch.eye(104)[:, :19]
    W = V.T
    pack = dict(
        truth=torch.randn(2, 402, 97) * 0.01,
        z=torch.randn(2, 402, 96) * 0.01,
        u=torch.randn(2, 401, 1) * 0.1,
        az=torch.randn(8, 96) * 0.01,
        an=torch.randn(8, 96) * 0.01,
        closure_energy=torch.ones(2),
    )
    vectors = []
    values = []
    for checkpointed in [False, True]:
        model.zero_grad()
        value, _ = loss(model, V, W, pack, grad=checkpointed)
        value.backward()
        vectors.append(
            torch.cat(
                [
                    (
                        p.grad.flatten()
                        if p.grad is not None
                        else torch.zeros_like(p).flatten()
                    )
                    for p in model.parameters()
                    if p.requires_grad
                ]
            )
        )
        values.append(value.detach())
    torch.testing.assert_close(values[0], values[1], rtol=1e-12, atol=1e-13)
    torch.testing.assert_close(vectors[0], vectors[1], rtol=1e-9, atol=1e-11)


def test_rejected_updates_are_not_a_plateau():
    cfg = dict(patience=3, relative_improvement=0.005)
    h = [
        dict(
            full_prediction=1.0,
            reduced_prediction=1.0,
            primary_prediction=11.0,
            accepted_updates=0,
        )
        for _ in range(4)
    ]
    assert not plateau(h, cfg)


def test_lean_preflight_rejects_changed_manuscript(tmp_path):
    import hashlib
    from stable_reduction.lean_export import preflight_general

    lean = tmp_path / "lean"
    lean.mkdir()
    paper = tmp_path / "paper"
    paper.mkdir()
    (paper / "main.tex").write_text("% One sentence per source line.\nOriginal.\n")
    (lean / "Tiny.lean").write_text("example : True := True.intro\n")
    digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    (lean / "source_manifest.json").write_text(
        json.dumps({"sources": {"Tiny.lean": digest(lean / "Tiny.lean")}})
    )
    (lean / "paper_correspondence.json").write_text(
        json.dumps({"source_sha256": digest(paper / "main.tex")})
    )
    (lean / "package_manifest.json").write_text(json.dumps({"dependencies": {}}))
    preflight_general(lean)
    (paper / "main.tex").write_text("% One sentence per source line.\nChanged.\n")
    with pytest.raises(ValueError, match="Manuscript changed"):
        preflight_general(lean)


def test_export_excludes_local_audit_and_history(tmp_path):
    source = tmp_path / "source"
    (source / "src").mkdir(parents=True)
    (source / "src" / "public.py").write_text("value = 1\n")
    for name in ["code_supplement", "evidence", "writing-history"]:
        folder = source / "paper" / name
        folder.mkdir(parents=True)
        (folder / "private.pt").write_bytes(b"local model or private evidence")
    target = tmp_path / "public"
    export(source, target)
    assert (target / "src/public.py").exists()
    assert not list(target.rglob("*.pt"))
    assert not (target / "paper/code_supplement").exists()
