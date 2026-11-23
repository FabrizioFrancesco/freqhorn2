#!/usr/bin/env python3
"""Sort XAI benchmark files into class<c>/ subfolders by the class their query encodes.

The class is read from the negated property in the query (the last rule of the file),
as written by nnet2smt_tie_break.py, also after remove_arrays.py:

  (not (>= x0 0))                      binary, class 1
  (not (< x0 0))                       binary, class 0
  (not (and (> xc x0) ... (>= xc xn)))  multiclass, class c (also the old all->= encoding)

Every .smt2 under a folder (subfolders included) goes to <folder>/class<c>/<file>, so
running it again on a sorted folder changes nothing. Files whose query is not recognised
are reported and left where they are. Only the end of each file is read.

Examples (from the repository root):
  python3 preprocessing/sort.py --dry-run          # every bench_xai* folder, show the moves
  python3 preprocessing/sort.py bench_xai_ha bench_xai_ob
  python3 preprocessing/sort.py encoding_no_arrays/bench_xai_ha --copy
"""

import argparse
import glob
import os
import re
import shutil
import sys
from collections import Counter
from fractions import Fraction

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

TAIL = 1 << 16             # bytes read from the end of a file, doubled until the query fits
VAR = re.compile(r"^x(\d+)$")
NUMERAL = re.compile(r"^-?\d+(\.\d+)?$")
TOKEN = re.compile(r"[()]|[^\s()]+")


def query_property(path):
    """The (not ...) conjunct of the query, as text."""
    size = os.path.getsize(path)
    tail = TAIL
    with open(path, "rb") as f:
        while True:
            f.seek(max(0, size - tail))
            text = f.read().decode("utf-8", "replace")
            # the query body is the last application of inv in the file
            start = text.rfind("(inv ")
            if start >= 0:
                neg = text.find("(not ", start)
                if neg >= 0:
                    end = matching_paren(text, neg)
                    if end is not None:
                        return text[neg:end]
            if tail >= size:
                return None
            tail *= 2


def matching_paren(text, i):
    depth = 0
    for j in range(i, len(text)):
        if text[j] == "(":
            depth += 1
        elif text[j] == ")":
            depth -= 1
            if depth == 0:
                return j + 1
    return None


def parse(text):
    stack = [[]]
    for tok in TOKEN.findall(text):
        if tok == "(":
            stack.append([])
        elif tok == ")":
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(tok)
    return stack[0][0]


def is_zero(atom):
    return isinstance(atom, str) and NUMERAL.match(atom) and Fraction(atom) == 0


def class_of(prop):
    """The class whose property is negated in prop, or None if not recognised."""
    if not (isinstance(prop, list) and len(prop) == 2 and prop[0] == "not"):
        return None
    body = prop[1]
    if not isinstance(body, list) or not body:
        return None

    # binary: one output x0, class 1 iff x0 >= 0
    if len(body) == 3 and body[1] == "x0" and is_zero(body[2]):
        return {">=": 1, "<": 0}.get(body[0])

    # multiclass: x_c compared with every other output
    comparisons = body[1:] if body[0] == "and" else [body]
    classes = set()
    for cmp in comparisons:
        if not (isinstance(cmp, list) and len(cmp) == 3 and cmp[0] in (">", ">=")):
            return None
        left, right = VAR.match(str(cmp[1])), VAR.match(str(cmp[2]))
        if not left or not right:
            return None
        classes.add(int(left.group(1)))
    return classes.pop() if len(classes) == 1 else None


def default_folders():
    return sorted(d for d in glob.glob(os.path.join(ROOT, "bench_*"))
                  if os.path.isdir(d) and os.path.basename(d).lower().startswith("bench_xai"))


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("folders", nargs="*", help="benchmark folders (default: every bench_xai* folder)")
    p.add_argument("--copy", action="store_true", help="copy the files instead of moving them")
    p.add_argument("-n", "--dry-run", action="store_true", help="only print what would be done")
    p.add_argument("-v", "--verbose", action="store_true", help="print every move")
    args = p.parse_args()

    folders = args.folders or default_folders()
    unrecognised = 0
    for folder in folders:
        if not os.path.isdir(folder):
            sys.exit("not a folder: %s" % folder)
        files = sorted(glob.glob(os.path.join(folder, "**", "*.smt2"), recursive=True))
        counts, changed = Counter(), 0
        for path in files:
            text = query_property(path)
            c = class_of(parse(text)) if text else None
            if c is None:
                print("unrecognised query, left in place: %s" % path, file=sys.stderr)
                unrecognised += 1
                continue
            counts[c] += 1
            dest = os.path.join(folder, "class%d" % c, os.path.basename(path))
            if os.path.abspath(dest) == os.path.abspath(path):
                continue
            changed += 1
            if args.verbose or args.dry_run:
                print("%s %s -> %s" % ("copy" if args.copy else "move", path, dest))
            if not args.dry_run:
                os.makedirs(os.path.dirname(dest), exist_ok=True)
                (shutil.copy2 if args.copy else shutil.move)(path, dest)
        if not args.dry_run and not args.copy:
            remove_empty_subfolders(folder)
        summary = ", ".join("class%d: %d" % (c, n) for c, n in sorted(counts.items()))
        verb = ("copy" if args.copy else "move") if args.dry_run else ("copied" if args.copy else "moved")
        print("%s: %d files (%s), %d %s%s" % (os.path.relpath(folder), len(files), summary or "none",
              changed, "to " if args.dry_run else "", verb))
    if unrecognised:
        sys.exit("%d files with an unrecognised query" % unrecognised)


def remove_empty_subfolders(folder):
    for d, _, _ in sorted(os.walk(folder), key=lambda t: -len(t[0])):
        if d != folder and not os.listdir(d):
            os.rmdir(d)


if __name__ == "__main__":
    main()
