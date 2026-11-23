#!/usr/bin/env python3
"""Generate synthetic ReLU networks of growing size and their XAI benchmarks.

Every network has W inputs, L hidden layers of W ReLU neurons and one linear output
(binary classification: class 1 iff output >= 0, as in nnet2smt_tie_break.py), so all
layers have the same width and the encoding needs no padding. Networks are generated for
every W in --widths and L in --depths, i.e. with L*(W*W + W) + W + 1 parameters each.

Weights are random (no training). The output bias is set so that random inputs in
[0, 1]^W split about evenly between the two classes, and one sample per class (or
--samples-per-class) is picked among them, preferring inputs on which no hidden layer is
entirely inactive. Each sample is encoded with nnet2smt_tie_break.py:

  preprocessing/synth/synth_<W>x<L>.nnet           the network (NNet format)
  preprocessing/synth/synth_<W>x<L>_samples.csv    its samples, row i = sample s<i>
  bench_xai_synth/class<c>/synth_<W>x<L>_s<i>.smt2 one file per sample, by class c

Examples (from the repository root):
  python3 preprocessing/gen_xai_synth.py
  python3 preprocessing/gen_xai_synth.py --widths 2,4,8,16,32 --depths 1,2,3 -j 4
  python3 experiments/run_xai_experiments.py bench_xai_synth

Weights, biases and inputs are decimals with --decimals digits, so the converter writes
them unchanged (it rounds |v| <= 1e-4 to 0, hence no weight is that small), and the class
of a sample is computed exactly with rationals, as the CHC encoding sees it. Generation
is deterministic: each network only depends on --seed, its width and its depth.
"""

import argparse
import csv
import math
import os
import random
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction

PREPROCESSING = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(PREPROCESSING)
CONVERTER = os.path.join(PREPROCESSING, "nnet2smt_tie_break.py")
DEFAULT_NNET_DIR = os.path.join(PREPROCESSING, "synth")
DEFAULT_OUT = os.path.join(ROOT, "bench_xai_synth")

CLASSES = (0, 1)
CANDIDATE_INPUTS = 200   # random inputs drawn to centre the output and pick the samples
MAX_ATTEMPTS = 20        # networks re-drawn when the output is constant on the candidates


def int_list(s):
    return [int(v) for v in s.split(",") if v]


def number_of_parameters(width, depth):
    return depth * (width * width + width) + width + 1


def decimal(rng, low, high, decimals, nonzero=False):
    """A random decimal string in [low, high] with the given number of digits.
    With nonzero, |value| >= 2 * 10^-decimals, which the converter does not round to 0."""
    scale = 10 ** decimals
    while True:
        k = rng.randint(math.ceil(low * scale), math.floor(high * scale))
        if not nonzero or abs(k) >= 2:
            return format_decimal(k, decimals)


def format_decimal(k, decimals):
    sign = "-" if k < 0 else ""
    k = abs(k)
    return "%s%d.%0*d" % (sign, k // 10 ** decimals, decimals, k % 10 ** decimals)


def random_layer(rng, rows, cols, decimals):
    # He-uniform scale keeps activations from vanishing or exploding with depth
    bound = math.sqrt(6.0 / cols)
    weights = [[decimal(rng, -bound, bound, decimals, nonzero=True)
                for _ in range(cols)] for _ in range(rows)]
    biases = [decimal(rng, -0.1, 0.1, decimals, nonzero=True)
              for _ in range(rows)]
    return weights, biases


def units(s):
    """A decimal string from format_decimal as an integer number of 10^-decimals."""
    return int(s.replace(".", ""))


def forward(layers, x, decimals):
    """Exact output of the network (ReLU on hidden layers, linear output layer), and
    whether every hidden layer has an active neuron. Computed on integers: after n
    layers, h holds the values times 10^(decimals*(n+1))."""
    scale = 10 ** decimals
    h = [units(v) for v in x]
    alive = True
    for n, (weights, biases) in enumerate(layers):
        h = [sum(units(w) * v for w, v in zip(row, h)) + units(b) * scale ** (n + 1)
             for row, b in zip(weights, biases)]
        if n != len(layers) - 1:
            h = [max(v, 0) for v in h]
            alive = alive and any(h)
    return Fraction(h[0], scale ** (len(layers) + 1)), alive


def output_bias(raw, decimals, min_class_size):
    """Units of an output bias that splits the outputs near their median, halfway
    between two distinct outputs, so that no output lands on the boundary (e.g. the
    constant output of inputs on which a whole hidden layer is inactive)."""
    scale = 10 ** decimals
    v = sorted(raw)
    n = len(v)
    splits = sorted((i for i in range(min_class_size, n - min_class_size + 1) if v[i - 1] != v[i]),
                    key=lambda i: abs(2 * i - n))
    for i in splits:
        t = round((v[i - 1] + v[i]) / 2 * scale)
        # |bias| = 10^-decimals would be rounded to 0 by the converter
        if v[i - 1] * scale < t < v[i] * scale and abs(t) != 1:
            return -t
    return None


def generate_network(width, depth, args):
    """Layers [(weights, biases)] and a list of (class, output, input) samples."""
    rng = random.Random("%d-%dx%d" % (args.seed, width, depth))
    for _ in range(MAX_ATTEMPTS):
        layers = [random_layer(rng, width, width, args.decimals) for _ in range(depth)]
        out_weights, _ = random_layer(rng, 1, width, args.decimals)
        layers.append((out_weights, ["0." + "0" * args.decimals]))

        inputs = [[decimal(rng, 0, 1, args.decimals) for _ in range(width)]
                  for _ in range(CANDIDATE_INPUTS)]
        evaluated = [forward(layers, x, args.decimals) for x in inputs]
        bias_k = output_bias([out for out, _ in evaluated], args.decimals, args.samples_per_class)
        if bias_k is None:
            continue
        layers[-1] = (out_weights, [format_decimal(bias_k, args.decimals)])

        by_class = {c: [] for c in CLASSES}
        for x, (raw, alive) in zip(inputs, evaluated):
            out = raw + Fraction(bias_k, 10 ** args.decimals)
            by_class[1 if out >= 0 else 0].append((not alive, abs(out), out, x))
        samples = []
        for c in CLASSES:
            # typical samples, around the median distance from the boundary,
            # preferring inputs on which every hidden layer has an active neuron
            alive = [t for t in by_class[c] if not t[0]]
            pool = sorted(alive if len(alive) >= args.samples_per_class else by_class[c])
            mid = len(pool) // 2 - args.samples_per_class // 2
            for _, _, out, x in pool[mid:mid + args.samples_per_class]:
                samples.append((c, out, x))
        return layers, samples
    sys.exit("synth_%dx%d: no output bias splits the classes after %d attempts, try another --seed"
             % (width, depth, MAX_ATTEMPTS))


def write_nnet(path, width, depth, layers):
    sizes = [width] * (depth + 1) + [1]
    with open(path, "w") as f:
        f.write("// Synthetic ReLU network generated by gen_xai_synth.py\n")
        f.write("%d,%d,%d,%d,\n" % (depth + 1, width, 1, width))
        f.write(",".join(map(str, sizes)) + ",\n")
        f.write("0,\n")
        f.write("0," * width + "\n")         # input minimums
        f.write("1," * width + "\n")         # input maximums
        f.write("0," * (width + 1) + "\n")   # means (inputs and output)
        f.write("1," * (width + 1) + "\n")   # ranges (inputs and output)
        for weights, biases in layers:
            for row in weights:
                f.write(",".join(row) + ",\n")
            for b in biases:
                f.write(b + ",\n")


def write_samples(path, width, samples):
    with open(path, "w", newline="") as f:
        out = csv.writer(f)
        out.writerow(["x%d" % i for i in range(width)] + ["class"])
        for c, _, x in samples:
            out.writerow(x + [c])


def convert(nnet, smt2, c, x):
    subprocess.run([sys.executable, CONVERTER, nnet, smt2, str(c), ",".join(x)], check=True)


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--widths", type=int_list, default=int_list("2,3,4,5,6,8,10,12,15,20,25,30,40,50"),
                   help="neurons per layer, comma separated (default: %(default)s)")
    p.add_argument("--depths", type=int_list, default=int_list("1,2,3,4,5"),
                   help="numbers of hidden layers, comma separated (default: %(default)s)")
    p.add_argument("--samples-per-class", type=int, default=1,
                   help="samples per class and network (default: %(default)s)")
    p.add_argument("--decimals", type=int, default=4,
                   help="digits of weights, biases and inputs (default: %(default)s)")
    p.add_argument("--seed", type=int, default=0, help="random seed (default: %(default)s)")
    p.add_argument("--nnet-dir", default=DEFAULT_NNET_DIR,
                   help="folder for .nnet and sample files (default: preprocessing/synth)")
    p.add_argument("--out", default=DEFAULT_OUT, help="benchmark folder (default: bench_xai_synth)")
    p.add_argument("-j", "--jobs", type=int, default=1, help="parallel conversions (default: %(default)s)")
    args = p.parse_args()

    if args.decimals < 4:
        sys.exit("--decimals must be at least 4: the converter rounds |v| <= 1e-4 to 0")

    os.makedirs(args.nnet_dir, exist_ok=True)
    for c in CLASSES:
        os.makedirs(os.path.join(args.out, "class%d" % c), exist_ok=True)

    nets = sorted(((w, d) for w in args.widths for d in args.depths),
                  key=lambda wd: (number_of_parameters(*wd), wd))
    print("%-14s %10s  %s" % ("network", "parameters", "sample outputs (class 0 | class 1)"))

    jobs = []
    for width, depth in nets:
        name = "synth_%dx%d" % (width, depth)
        layers, samples = generate_network(width, depth, args)
        nnet = os.path.join(args.nnet_dir, name + ".nnet")
        write_nnet(nnet, width, depth, layers)
        write_samples(os.path.join(args.nnet_dir, name + "_samples.csv"), width, samples)
        for i, (c, _, x) in enumerate(samples):
            smt2 = os.path.join(args.out, "class%d" % c, "%s_s%d.smt2" % (name, i))
            jobs.append((nnet, smt2, c, x))
        outs = " | ".join(" ".join("%.3f" % float(out) for c2, out, _ in samples if c2 == c)
                          for c in CLASSES)
        print("%-14s %10d  %s" % (name, number_of_parameters(width, depth), outs))

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        list(pool.map(lambda job: convert(*job), jobs))

    print("Generated %d networks and %d files in %s" % (len(nets), len(jobs), args.out))


if __name__ == "__main__":
    main()
