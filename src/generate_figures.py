"""Deterministic regeneration of Figures 1 and 2.

Determinism
-----------
No random sampling is used anywhere.  Figure 1 plots a *stride sample* of the
hypotenuse-sorted triple list: with N triples and a target of TARGET points,
the stride is ``max(1, N // TARGET)`` and the plotted subset is exactly

    triples[::stride]

together with the full record sequence, which is always overlaid in its
entirety.  The same input therefore always yields the same figure.  PNG
creation-date metadata is suppressed so that repeated runs are byte-identical.

Floating point is used here for plotting only; every record and every spine
value is computed exactly elsewhere.
"""

from __future__ import annotations

from math import log10, sqrt
from pathlib import Path
from typing import List, Sequence

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

from enumerate_triples import Triple  # noqa: E402
from verify_records import Record  # noqa: E402

TARGET_SAMPLE_POINTS = 6000
_PNG_METADATA = {"Software": "pell-spine-optimal-separator", "Date": None}


def sample_stride(n_triples: int, target: int = TARGET_SAMPLE_POINTS) -> int:
    """Stride used to subsample the triple list for Figure 1."""
    return max(1, n_triples // target)


def figure_1_separation_cloud(
    triples: Sequence[Triple], records: Sequence[Record], path: Path
) -> Path:
    """Delta_k against hypotenuse c, log-log, with the line Delta_k = 1/c."""
    stride = sample_stride(len(triples))
    sample: List[Triple] = list(triples[::stride])

    xs = [t.c for t in sample]
    ys = [t.d / t.c for t in sample]
    rx = [r.c for r in records]
    ry = [r.d / r.c for r in records]

    fig, ax = plt.subplots(figsize=(7.2, 5.0))
    ax.scatter(xs, ys, s=2.0, c="0.62", linewidths=0, label=f"primitive triples (every {stride}th, by c)")

    if rx:
        cmin, cmax = min(rx), max(rx)
        line_c = [cmin, cmax]
        ax.plot(line_c, [1.0 / cmin, 1.0 / cmax], color="C0", lw=1.2, ls="--",
                label=r"$\Delta k = 1/c$  (spine)")
        ax.scatter(rx, ry, s=42, marker="s", facecolors="none", edgecolors="C3",
                   linewidths=1.4, zorder=3, label="record minima")

    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("hypotenuse $c$")
    ax.set_ylabel(r"$\Delta k = (b-a)/c$")
    ax.set_title(r"Normalized separation $\Delta k$ against hypotenuse")
    ax.grid(True, which="major", alpha=0.25)
    ax.legend(loc="lower left", framealpha=0.95, fontsize=9)
    fig.tight_layout()
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(path, dpi=150, metadata=_PNG_METADATA)
    plt.close(fig)
    return path


def figure_2_record_staircase(records: Sequence[Record], path: Path) -> Path:
    """The record staircase in log coordinates, plus the successive ratios.

    The right panel makes explicit that the finite ratios c_{j+1}/c_j only
    approach 3 + 2*sqrt(2); they are not all equal to it.
    """
    limit = 3.0 + 2.0 * sqrt(2.0)
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.0, 4.4))

    cs = [r.c for r in records]
    dks = [r.d / r.c for r in records]

    ax1.step(cs, dks, where="post", color="C0", lw=1.1, label="record staircase")
    ax1.scatter(cs, dks, s=42, marker="s", facecolors="none", edgecolors="C3",
                linewidths=1.4, zorder=3, label="spine elements")
    if cs:
        ax1.plot([min(cs), max(cs)], [1.0 / min(cs), 1.0 / max(cs)],
                 color="0.5", lw=0.9, ls=":", zorder=1, label=r"$\Delta k = 1/c$")
    ax1.set_xscale("log")
    ax1.set_yscale("log")
    ax1.set_xlabel("hypotenuse $c$")
    ax1.set_ylabel(r"$\Delta k$")
    ax1.set_title(r"Record staircase ($\log c$ vs $\log \Delta k$, slope $-1$)")
    ax1.grid(True, which="major", alpha=0.25)
    ax1.legend(loc="lower left", fontsize=9)

    if len(cs) > 1:
        js = list(range(1, len(cs)))
        ratios = [cs[i] / cs[i - 1] for i in js]
        ax2.plot(js, ratios, marker="o", ms=5, color="C3", lw=1.0,
                 label=r"finite ratios $c_{j+1}/c_j$")
        ax2.axhline(limit, color="C0", ls="--", lw=1.2,
                    label=r"limit $3+2\sqrt{2} = 5.8284\ldots$")
        ax2.set_xlabel("step $j$")
        ax2.set_ylabel(r"$c_{j+1}/c_j$")
        ax2.set_title("Successive ratios approach the limit (they do not equal it)")
        ax2.grid(True, alpha=0.25)
        ax2.legend(loc="lower right", fontsize=9)
        pad = max(0.02, (limit - min(ratios)) * 0.25)
        ax2.set_ylim(min(ratios) - pad, limit + pad)

    fig.tight_layout()
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(path, dpi=150, metadata=_PNG_METADATA)
    plt.close(fig)
    return path


def first_step_drop(records: Sequence[Record]) -> float:
    """log10 of the first staircase drop; the manuscript quotes log10(29/5)."""
    if len(records) < 2:
        return float("nan")
    return log10(records[1].c / records[0].c)
