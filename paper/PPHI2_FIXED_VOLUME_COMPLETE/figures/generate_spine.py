#!/usr/bin/env python3
"""Generate the proof-dependency diagram from a fixed, documented layout."""
from __future__ import annotations

import hashlib
import shutil
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch

ROOT = Path(__file__).resolve().parents[1]
GENERATED = ROOT / "figures" / "generated"
EMBEDDED = ROOT / "figures" / "weak_limit_spine.png"

INK = "#24323A"
PALETTE = ["#285F8F", "#0D7377", "#418457", "#B2761D", "#A24B55", "#496F78", "#607B46", "#315F72"]
FILL = ["#EAF1F7", "#E8F3F1", "#EAF2EC", "#F7F0E4", "#F6EDEF", "#EBF1F2", "#EEF2E8", "#EAF0F2"]


def node(ax, center, y, title, body, color, fill):
    x = center - 1.25
    box = FancyBboxPatch(
        (x, y - 0.75), 2.50, 1.50,
        boxstyle="round,pad=0.03,rounding_size=0.08",
        linewidth=1.35, edgecolor=color, facecolor=fill, zorder=2,
    )
    ax.add_patch(box)
    ax.text(center, y + 0.28, title, ha="center", va="center",
            fontsize=8.4, fontweight="bold", color=INK, zorder=3)
    ax.text(center, y - 0.28, body, ha="center", va="center",
            fontsize=7.3, color=INK, linespacing=1.15, zorder=3)


def arrow(ax, start, end, color="#53636B", rad=0.0):
    ax.add_patch(FancyArrowPatch(
        start, end, arrowstyle="-|>", mutation_scale=12,
        linewidth=1.45, color=color,
        connectionstyle=f"arc3,rad={rad}", shrinkA=3, shrinkB=3, zorder=1,
    ))


def main() -> int:
    GENERATED.mkdir(parents=True, exist_ok=True)
    fig, ax = plt.subplots(figsize=(7.2, 4.45), constrained_layout=True)
    fig.patch.set_facecolor("white")
    ax.set_facecolor("white")
    ax.set_xlim(0, 12)
    ax.set_ylim(0, 10)
    ax.axis("off")

    centers = [1.5, 4.5, 7.5, 10.5]
    top_y, bottom_y = 7.5, 3.3
    top = [
        ("1. Finite-source laws", r"$\mu_n^{L,m}$; $N=n+1$"),
        ("2. Uniform moment", r"$H^{-2}$ energy $\leq C_{L,m}$"),
        ("3. Tightness", r"compact $H^{-2}$" + "\n" + r"into $H^{-3}$"),
        ("4. Prokhorov", r"subsequence limit $\nu$"),
    ]
    bottom = [
        ("8. Whole sequence", r"$\mu_n\Rightarrow\mu_{\rm free}$"),
        ("7. Borel uniqueness", "finite cylinders\ndetermine law"),
        ("6. Limit inherits", r"the target marginals"),
        ("5. Finite-mode limits", "periodic-resolvent\nGaussian"),
    ]

    for i, ((title, body), x) in enumerate(zip(top, centers)):
        node(ax, x, top_y, title, body, PALETTE[i], FILL[i])
    for i, ((title, body), x) in enumerate(zip(bottom, centers)):
        node(ax, x, bottom_y, title, body, PALETTE[4 + i], FILL[4 + i])

    for i in range(3):
        arrow(ax, (centers[i] + 1.29, top_y), (centers[i + 1] - 1.29, top_y), PALETTE[i + 1])
    arrow(ax, (centers[3], top_y - 0.78), (centers[3], bottom_y + 0.78), PALETTE[4])
    for i in range(3, 0, -1):
        arrow(ax, (centers[i] - 1.29, bottom_y), (centers[i - 1] + 1.29, bottom_y), PALETTE[i + 4])

    ax.text(
        6, 0.82,
        r"Boundary: the limit is identified by its finite Fourier marginals; no covariance operator is constructed on the carrier.",
        ha="center", va="center", fontsize=7.4, color="#49575E",
    )
    ax.text(6, 9.15, "Tightness plus cylinder identification closes the full sequence",
            ha="center", va="center", fontsize=10.2, fontweight="bold", color=INK)

    png_source = GENERATED / "weak_limit_spine.png"
    pdf_source = GENERATED / "weak_limit_spine.pdf"
    fig.savefig(png_source, dpi=450, facecolor="white")
    fig.savefig(pdf_source, facecolor="white")
    plt.close(fig)
    shutil.copyfile(png_source, EMBEDDED)

    digest = hashlib.sha256(png_source.read_bytes()).hexdigest()
    print(f"Generated {png_source.relative_to(ROOT)} and {pdf_source.relative_to(ROOT)}")
    print(f"Embedded PNG: {EMBEDDED.relative_to(ROOT)} (sha256 {digest})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
