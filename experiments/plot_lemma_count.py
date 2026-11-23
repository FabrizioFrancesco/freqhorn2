#!/usr/bin/env python3
"""Plot the total number of lemmas per layer count from lemma_count.txt (written by lemma_count.sh).

Examples (from the repository root):
  python3 experiments/plot_lemma_count.py
  python3 experiments/plot_lemma_count.py -o experiments/lemma_count.pdf
"""

import argparse
import os
import re

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter, MaxNLocator

DIR = os.path.dirname(os.path.abspath(__file__))

# heart_attack_50x3_s0.smt2 -> 3 hidden layers
NAME = re.compile(r"x(?P<layers>\d+)_s\d+\.smt2$")

SERIES = "#2a78d6"
INK = "#0b0b0b"
MUTED = "#898781"
GRID = "#e1e0d9"
AXIS = "#c3c2b7"
SURFACE = "#fcfcfb"


def read_counts(path):
    points = []
    with open(path) as f:
        next(f)  # header
        for line in f:
            cols = line.split()
            if len(cols) < 4 or cols[3] == "-":
                continue
            m = NAME.search(cols[0])
            if m:
                points.append((int(m.group("layers")), int(cols[3])))
    return sorted(points)


def plot(points, out):
    xs, ys = zip(*points)
    fig, ax = plt.subplots(figsize=(7, 4.2), facecolor=SURFACE)
    ax.set_facecolor(SURFACE)

    ax.plot(xs, ys, color=SERIES, linewidth=2, marker="o", markersize=7,
            markeredgecolor=SURFACE, markeredgewidth=2, zorder=3)
    ax.annotate(f"{ys[-1]:,}", (xs[-1], ys[-1]), xytext=(0, 10),
                textcoords="offset points", ha="center", color=INK, fontsize=10)

    ax.set_title("Total lemmas by number of hidden layers (heart_attack_50xK, sample 0)",
                 loc="left", color=INK, fontsize=11)
    ax.set_xlabel("hidden layers K", color=MUTED)
    ax.set_ylabel("lemmas", color=MUTED)
    ax.xaxis.set_major_locator(MaxNLocator(integer=True))
    ax.yaxis.set_major_formatter(FuncFormatter(lambda v, _: f"{v:,.0f}"))
    ax.set_ylim(0, max(ys) * 1.12)
    ax.grid(axis="y", color=GRID, linewidth=0.8)
    ax.set_axisbelow(True)
    ax.tick_params(colors=MUTED, length=0)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    ax.spines["bottom"].set_color(AXIS)

    fig.tight_layout()
    fig.savefig(out, dpi=200, facecolor=SURFACE)
    print(f"wrote {out}")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("input", nargs="?", default=os.path.join(DIR, "lemma_count.txt"))
    ap.add_argument("-o", "--output", default=os.path.join(DIR, "lemma_count.png"))
    args = ap.parse_args()

    points = read_counts(args.input)
    if not points:
        raise SystemExit(f"no lemma counts found in {args.input}")
    plot(points, args.output)


if __name__ == "__main__":
    main()
