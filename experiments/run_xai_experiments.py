#!/usr/bin/env python3
"""Run xaihorn on the XAI benchmark folders, collect runtimes into a CSV, and plot them.

Examples (from the repository root):
  # run every instance of two benchmark sets, 4 jobs in parallel, 10 min timeout
  python3 experiments/run_xai_experiments.py bench_xai_ha bench_xai_ob -j 4 --timeout 600

  # only the first 10 samples of each network (s0..s9)
  python3 experiments/run_xai_experiments.py bench_xai_mnist_compact_padding --max-samples 10

  # re-draw the plots from an existing CSV without running anything
  python3 experiments/run_xai_experiments.py --plot-only

A folder is searched with its subfolders, so the class<c>/ folders written by
preprocessing/sort.py are included, and c is recorded in the CSV column "class". A class
folder can also be given on its own (e.g. bench_xai_ha/class0): its set is still bench_xai_ha.

Instances already present in the CSV are skipped (use --rerun to run them again),
so an interrupted run can be resumed with the same command.

Status of a run:
  sat      xaihorn printed "sat" (invariant found and checked)
  unknown  xaihorn printed "unknown"
  done     exited with code 0 without a verdict (e.g. SKIP_CHECKS=true in XAI.hpp)
  timeout  killed after --timeout seconds
  error    non-zero exit code
Runtimes of "sat" and "done" runs are counted as completed in the plots.
"""

import argparse
import csv
import os
import re
import subprocess
import sys
import threading
import time
import zlib
from concurrent.futures import ThreadPoolExecutor, as_completed

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_BIN = os.path.join(ROOT, "build", "tools", "xai", "xaihorn")
DEFAULT_OUT = os.path.join(ROOT, "experiments", "results")

# heart_attack_50x3_s17.smt2 -> network heart_attack_50x3, width 50, layers 3, sample 17
NAME = re.compile(r"^(?P<network>.*?(?P<width>\d+)x(?P<layers>\d+))(?:_s(?P<sample>\d+))?\.smt2$")

# bench_xai_ha/class1/heart_attack_50x3_s17.smt2 -> class 1
CLASS_DIR = re.compile(r"^class(?P<cls>\d+)$")

FIELDS = ["set", "file", "network", "width", "layers", "sample", "class",
          "status", "time_s", "returncode"]
COMPLETED = ("sat", "done")


def parse_name(fname):
    m = NAME.match(fname)
    if not m:
        return {"network": fname[:-len(".smt2")], "width": "", "layers": "", "sample": ""}
    return {"network": m.group("network"), "width": int(m.group("width")),
            "layers": int(m.group("layers")),
            "sample": int(m.group("sample")) if m.group("sample") else ""}


def collect_instances(dirs, max_samples):
    instances = []
    for d in dirs:
        d = os.path.normpath(d)
        bench_set = os.path.basename(d)
        if CLASS_DIR.match(bench_set):
            bench_set = os.path.basename(os.path.dirname(os.path.abspath(d)))
        for sub, _, files in os.walk(d):
            m = CLASS_DIR.match(os.path.basename(sub))
            for f in files:
                if not f.endswith(".smt2"):
                    continue
                info = parse_name(f)
                if max_samples is not None and info["sample"] != "" and info["sample"] >= max_samples:
                    continue
                instances.append(dict(info, set=bench_set, file=f, path=os.path.join(sub, f),
                                      **{"class": int(m.group("cls")) if m else ""}))
    instances.sort(key=lambda r: (r["set"], str(r["network"]), r["layers"] or 0, r["sample"] or 0))
    return instances


def run_one(inst, args, log_dir):
    cmd = [args.bin, "--to", str(args.z3_to), inst["path"]]
    os.makedirs(os.path.join(log_dir, inst["set"]), exist_ok=True)
    log_base = os.path.join(log_dir, inst["set"], inst["file"][:-len(".smt2")])
    with open(log_base + ".out", "w") as out, open(log_base + ".err", "w") as err:
        start = time.monotonic()
        try:
            proc = subprocess.run(cmd, stdout=out, stderr=err, timeout=args.timeout)
            elapsed = time.monotonic() - start
            rc = proc.returncode
        except subprocess.TimeoutExpired:
            elapsed, rc = float(args.timeout), ""
    if rc == "":
        status = "timeout"
    else:
        with open(log_base + ".err") as err:
            verdict = err.read().split()
        verdict = verdict[-1] if verdict else ""
        if verdict in ("sat", "unknown"):
            status = verdict
        elif rc == 0:
            status = "done"
        else:
            status = "error"
    row = {k: inst[k] for k in FIELDS if k in inst}
    row.update(status=status, time_s="%.3f" % elapsed, returncode=rc)
    return row


def read_csv(path):
    if not os.path.exists(path):
        return []
    with open(path) as f:
        return list(csv.DictReader(f))


def run_experiments(args, csv_path, log_dir):
    instances = collect_instances(args.dirs, args.max_samples)
    previous = read_csv(csv_path)
    if previous and list(previous[0].keys()) != FIELDS:
        sys.exit("%s has different columns than %s: use another --csv" % (csv_path, ", ".join(FIELDS)))
    if args.rerun:
        todo_keys = {(i["set"], i["file"]) for i in instances}
        previous = [r for r in previous if (r["set"], r["file"]) not in todo_keys]
        with open(csv_path, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=FIELDS)
            w.writeheader()
            w.writerows(previous)
    done = {(r["set"], r["file"]) for r in previous}
    todo = [i for i in instances if (i["set"], i["file"]) not in done]
    print("%d instances, %d already in %s, %d to run"
          % (len(instances), len(instances) - len(todo), csv_path, len(todo)))
    if not todo:
        return

    new_file = not os.path.exists(csv_path)
    lock = threading.Lock()
    with open(csv_path, "a", newline="") as f:
        w = csv.DictWriter(f, fieldnames=FIELDS)
        if new_file:
            w.writeheader()
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures = [pool.submit(run_one, i, args, log_dir) for i in todo]
            for n, fut in enumerate(as_completed(futures), 1):
                row = fut.result()
                with lock:
                    w.writerow(row)
                    f.flush()
                print("[%d/%d] %s/%s: %s %ss"
                      % (n, len(todo), row["set"], row["file"], row["status"], row["time_s"]))


# ---------------------------------------------------------------- plotting

def plot(csv_path, out_dir, timeout, fmt):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    rows = read_csv(csv_path)
    if not rows:
        print("no results in %s" % csv_path)
        return
    sets = sorted({r["set"] for r in rows})
    colors = plt.rcParams["axes.prop_cycle"].by_key()["color"]
    # with --plot-only the timeout may be unknown: use the largest recorded one
    to_line = timeout or max(float(r["time_s"]) for r in rows)

    # 1) runtime vs number of layers: median of completed runs, 25-75% band, every run as a dot
    fig, ax = plt.subplots(figsize=(8, 5))
    for c, s in enumerate(sets):
        col = colors[c % len(colors)]
        srows = [r for r in rows if r["set"] == s and r["layers"] != ""]
        layers = sorted({int(r["layers"]) for r in srows})
        meds, lo, hi, xs = [], [], [], []
        for k in layers:
            t = sorted(float(r["time_s"]) for r in srows
                       if int(r["layers"]) == k and r["status"] in COMPLETED)
            if t:
                xs.append(k)
                meds.append(percentile(t, 50))
                lo.append(percentile(t, 25))
                hi.append(percentile(t, 75))
        ok = [r for r in srows if r["status"] in COMPLETED]
        bad = [r for r in srows if r["status"] not in COMPLETED]
        ax.scatter([int(r["layers"]) + jitter(r) for r in ok], [float(r["time_s"]) for r in ok],
                   s=6, alpha=0.25, color=col)
        ax.scatter([int(r["layers"]) + jitter(r) for r in bad], [to_line] * len(bad),
                   s=18, marker="x", color=col)
        ax.plot(xs, meds, marker="o", color=col, label=s)
        ax.fill_between(xs, lo, hi, color=col, alpha=0.15)
    ax.axhline(to_line, color="grey", linestyle="--", linewidth=0.8)
    ax.set_yscale("log")
    ax.set_xlabel("number of hidden layers")
    ax.set_ylabel("runtime (s)")
    ax.set_title("xaihorn runtime per network depth\n(median and 25-75% of completed runs; x = timeout/unknown/error)")
    ax.grid(True, which="both", alpha=0.3)
    ax.legend()
    save(fig, os.path.join(out_dir, "runtime_vs_layers." + fmt))

    # 2) cactus plot: instances completed within a given time
    fig, ax = plt.subplots(figsize=(8, 5))
    for c, s in enumerate(sets):
        t = sorted(float(r["time_s"]) for r in rows if r["set"] == s and r["status"] in COMPLETED)
        total = sum(1 for r in rows if r["set"] == s)
        ax.step(t, range(1, len(t) + 1), where="post", color=colors[c % len(colors)],
                label="%s (%d/%d)" % (s, len(t), total))
    ax.set_xscale("log")
    ax.set_xlabel("runtime (s)")
    ax.set_ylabel("instances completed")
    ax.yaxis.get_major_locator().set_params(integer=True)
    ax.set_title("xaihorn cactus plot")
    ax.grid(True, which="both", alpha=0.3)
    ax.legend()
    save(fig, os.path.join(out_dir, "cactus." + fmt))

    # 3) summary table on stdout
    print("\n%-34s %6s %6s %6s %8s %8s %6s %10s %10s"
          % ("network", "runs", "sat", "done", "unknown", "timeout", "error", "median_s", "max_s"))
    for s in sets:
        for net in sorted({r["network"] for r in rows if r["set"] == s},
                          key=lambda n: [int(x) if x.isdigit() else x for x in re.split(r"(\d+)", n)]):
            nrows = [r for r in rows if r["set"] == s and r["network"] == net]
            st = [r["status"] for r in nrows]
            t = sorted(float(r["time_s"]) for r in nrows if r["status"] in COMPLETED)
            print("%-34s %6d %6d %6d %8d %8d %6d %10s %10s"
                  % (net, len(nrows), st.count("sat"), st.count("done"), st.count("unknown"),
                     st.count("timeout"), st.count("error"),
                     "%.2f" % percentile(t, 50) if t else "-", "%.2f" % t[-1] if t else "-"))


def percentile(sorted_vals, p):
    if len(sorted_vals) == 1:
        return sorted_vals[0]
    k = (len(sorted_vals) - 1) * p / 100.0
    i = int(k)
    j = min(i + 1, len(sorted_vals) - 1)
    return sorted_vals[i] + (sorted_vals[j] - sorted_vals[i]) * (k - i)


def jitter(row):
    # deterministic horizontal spread so samples of the same network do not overlap
    return ((zlib.crc32(row["file"].encode()) % 1000) / 1000.0 - 0.5) * 0.3


def save(fig, path):
    fig.tight_layout()
    fig.savefig(path, dpi=200)
    print("wrote %s" % path)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("dirs", nargs="*", default=[os.path.join(ROOT, "bench_xai_ha"), os.path.join(ROOT, "bench_xai_ob")],
                   help="benchmark folders (default: bench_xai_ha bench_xai_ob)")
    p.add_argument("--bin", default=DEFAULT_BIN, help="xaihorn binary (default: %(default)s)")
    p.add_argument("--timeout", type=float, default=600, help="wall-clock timeout per instance in s (default: 600)")
    p.add_argument("--z3-to", type=int, default=1000, help="xaihorn --to, Z3 timeout in ms (default: 1000)")
    p.add_argument("-j", "--jobs", type=int, default=1,
                   help="parallel runs (default: 1; more jobs make runtimes noisier)")
    p.add_argument("--max-samples", type=int, help="only run samples s0..s<N-1> of each network")
    p.add_argument("--out", default=DEFAULT_OUT, help="output folder for CSV, logs and plots (default: %(default)s)")
    p.add_argument("--csv", help="results CSV (default: <out>/runtimes.csv)")
    p.add_argument("--rerun", action="store_true", help="re-run instances already in the CSV")
    p.add_argument("--plot-only", action="store_true", help="only plot the existing CSV")
    p.add_argument("--format", default="pdf", choices=["pdf", "png", "svg"], help="plot format (default: pdf)")
    args = p.parse_args()

    os.makedirs(args.out, exist_ok=True)
    csv_path = args.csv or os.path.join(args.out, "runtimes.csv")

    if not args.plot_only:
        if not os.access(args.bin, os.X_OK):
            sys.exit("xaihorn binary not found: %s (build it or pass --bin)" % args.bin)
        for d in args.dirs:
            if not os.path.isdir(d):
                sys.exit("not a folder: %s" % d)
        run_experiments(args, csv_path, os.path.join(args.out, "logs"))

    plot(csv_path, args.out, None if args.plot_only else args.timeout, args.format)


if __name__ == "__main__":
    main()
