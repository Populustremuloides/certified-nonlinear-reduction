"""Quantity colors, model line styles, and predictions against physical truth."""

from pathlib import Path
import json
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.ticker import FuncFormatter, MaxNLocator, NullLocator

# Preserve the paper's encoding: color = quantity; line style = normalization.
COLORS = ["#b53663", "#188875", "#7757a4"]
STYLES = {"truth": "-", "normalized": (0, (6, 2.5)), "raw": (0, (1, 1.7))}
CHARCOAL = "#343a40"


def style():
    plt.rcParams.update(
        {
            "font.family": "DejaVu Sans",
            "font.size": 9,
            "axes.titlesize": 10,
            "pdf.fonttype": 42,
            "svg.fonttype": "none",
            "axes.spines.top": False,
            "axes.spines.right": False,
        }
    )


def plot_losses(histories, path):
    style()
    fig, axes = plt.subplots(1, 3, figsize=(10, 2.8), layout="constrained")
    for ax, key, title in zip(
        axes,
        ["full_prediction", "reduced_prediction", "development_primary"],
        [
            "Full prediction loss",
            "Reduced prediction loss",
            "Development prediction loss",
        ],
    ):
        for arm, rows in histories.items():
            if rows:
                ax.plot(
                    [r["update"] for r in rows],
                    [r[key] for r in rows],
                    color=CHARCOAL,
                    ls=STYLES[arm],
                    label=arm.capitalize(),
                )
        ax.set(
            xlabel="Optimizer updates",
            ylabel="Relative squared error",
            title=title,
            yscale="log",
        )
    for ax in axes:
        ax.xaxis.set_major_locator(MaxNLocator(integer=True))
    boundaries = [
        r["update"]
        for rows in histories.values()
        for r in rows
        if r["phase"] == "full" and r["phase_update"] == 0
    ]
    if boundaries:
        boundary = min(boundaries)
        for ax in axes:
            ax.axvline(boundary, color="#b6b6b6", lw=0.7, zorder=0)
        axes[1].annotate(
            "Best warm-up model restored",
            xy=(boundary, 1),
            xycoords=("data", "axes fraction"),
            xytext=(4, -4),
            textcoords="offset points",
            va="top",
            fontsize=7,
            rotation=90,
        )
    axes[0].legend(frameon=False)
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(path.with_suffix(".png"), dpi=160)
    fig.savefig(path.with_suffix(".pdf"))
    plt.close(fig)


def main_figure(folder, cfg):
    style()
    folder = Path(folder)
    data = np.load(folder / "evaluation/illustrated.npz")
    report = json.loads((folder / "evaluation/report.json").read_text())
    fig = plt.figure(figsize=(8.6, 5.8))
    if cfg.get("smoke"):
        fig.suptitle(
            "Integration test (coarse clock, two training updates)",
            y=0.995,
            fontsize=10,
        )
    grid = fig.add_gridspec(
        2,
        2,
        hspace=0.65,
        wspace=0.32,
        top=0.74 if cfg.get("smoke") else 0.78,
        bottom=0.10,
    )
    time = data["time_us"]
    u = data["input"]
    axes = []
    for cell in [(0, 0), (0, 1), (1, 0)]:
        sub = grid[cell].subgridspec(2, 1, height_ratios=[4.5, 1], hspace=0.16)
        ax = fig.add_subplot(sub[0])
        control = fig.add_subplot(sub[1], sharex=ax)
        control.step(time, u, where="post", color=CHARCOAL, lw=0.9)
        control.set(xlabel="Time (µs)")
        control.set_ylabel("V", rotation=0, labelpad=8)
        control.set_yticks([0, 5.5])
        ax.tick_params(labelbottom=False)
        axes.append(ax)
    a, b, c = axes
    d = fig.add_subplot(grid[1, 1])
    for ax, key, title in [
        (a, "full", "A   Selected physical states (3 of 96)\n(full model, 104 states)"),
        (
            b,
            "r" + str(cfg["target_rank"]),
            f"B   Selected physical states (3 of 96)\n(reduced model, {cfg['target_rank']} states)",
        ),
    ]:
        for i, color in enumerate(COLORS):
            ax.plot(
                time,
                data["truth"][:, i],
                color=color,
                ls=STYLES["truth"],
                alpha=0.65,
                lw=1.1,
            )
            for arm in ["normalized", "raw"]:
                ax.plot(
                    time,
                    data[arm + "_" + key][:, i],
                    color=color,
                    ls=STYLES[arm],
                    lw=1.1,
                )
        ax.set(title=title, ylabel="Deviation\n(training RMS units)")
    for arm in ["normalized", "raw"]:
        c.plot(time, data[arm + "_r9_norm"], color=CHARCOAL, ls=STYLES[arm], lw=1.2)
        rows = [
            r for r in report["illustrated"] if r["arm"] == arm and r["rank"] != 104
        ]
        d.plot(
            [r["rank"] for r in rows],
            [
                100
                * (
                    r["state_nrmse"]
                    if r["state_nrmse"] is not None
                    else r["observed_prefix_error_lower_bound"]
                )
                for r in rows
            ],
            color=CHARCOAL,
            ls=STYLES[arm],
            lw=1.2,
        )
    c.set(title="C   Output norm (9 states)", ylabel="Output norm")
    c.set_yscale("symlog", linthresh=1.0)
    d.set(
        title="D   Prediction error versus reduction order",
        xlabel="Retained dimension",
        ylabel="State NRMSE (%)",
        yscale="log",
    )
    d.yaxis.set_major_formatter(FuncFormatter(lambda x, _: f"{x:g}"))
    d.yaxis.set_minor_formatter(FuncFormatter(lambda x, _: f"{x:g}"))
    d.xaxis.set_major_locator(MaxNLocator(integer=True))
    for ax in axes:
        ax.set_xlim(0, time[-1])
        ax.xaxis.set_major_locator(MaxNLocator(nbins=4, integer=True))
        ax.xaxis.set_minor_locator(NullLocator())
    fig.legend(
        handles=[
            Line2D([], [], color=CHARCOAL, ls=STYLES[k], label=l)
            for k, l in [
                ("truth", "Physical reference"),
                ("normalized", "Normalized residuals"),
                ("raw", "Unnormalized residuals"),
            ]
        ],
        loc="upper center",
        bbox_to_anchor=(0.5, 0.955 if cfg.get("smoke") else 1),
        ncol=3,
        frameon=False,
    )
    fig.legend(
        handles=[
            Line2D([], [], color=color, label=label)
            for color, label in zip(
                COLORS, ["Gap deviation", "Rate of gap³", "Pressure deviation"]
            )
        ],
        loc="upper center",
        bbox_to_anchor=(0.5, 0.90 if cfg.get("smoke") else 0.945),
        ncol=3,
        frameon=False,
    )
    for ext in ["pdf", "png", "svg"]:
        fig.savefig(folder / "evaluation" / ("figure." + ext), dpi=180)
    plt.close(fig)
