#!/usr/bin/env python3
"""
Remove the weight and bias arrays from the XAI neural-network CHC benchmarks
(bench_XAI_toy/, bench_xai_ha/) and write them in CHC-COMP format for Golem.

The encoding stays the same: one predicate with the layer counter, and the
same rules. Only the arrays go:
  - the fact fixes their entries and the transition copies them, so they are
    dropped from the predicate and every read (select ...) is replaced by the
    constant the fact gives it;
  - a read indexed by the counter is split on the values the transition guard
    allows, e.g. with (or (= counter 0) (= counter 1)) a right-hand side
    becomes (ite (= counter 0.0) <layer 0> <layer 1>);
  - define-funs (max, ReLU) are inlined, the counter becomes Real if it is Int
    (toy files) and numerals are written as reals: Golem accepts QF_LRA or
    QF_LIA, not both.
Anything outside this shape (a read the fact doesn't fix, arrays changed by a
rule, Int variables other than the counter, ...) is an error, not a guess.

Usage:
  remove_arrays.py IN.smt2                         # print to stdout
  remove_arrays.py IN.smt2 -o OUT.smt2
  remove_arrays.py IN1.smt2 IN2.smt2 ... -o OUTDIR   # OUTDIR/<same name>

Then:  golem -l QF_LRA -e spacer --print-witness --validate OUT.smt2
"""

import argparse
import os
import re
import sys
from fractions import Fraction


class ConversionError(Exception):
    pass


# ---------------------------------------------------------------- s-expressions

NUMERAL = re.compile(r'^-?[0-9]+(\.[0-9]+)?$')
TOKEN = re.compile(r'\|[^|]*\||;[^\n]*|[()]|[^\s()]+')


def parse(text):
    """Top-level s-expressions; numerals become Fractions, other atoms stay strings."""
    out, stack = [], []
    for tok in TOKEN.findall(text):
        if tok.startswith(';'):
            continue
        if tok == '(':
            stack.append([])
        elif tok == ')':
            if not stack:
                raise ConversionError('unbalanced )')
            e = stack.pop()
            (stack[-1] if stack else out).append(e)
        else:
            atom = Fraction(tok) if NUMERAL.match(tok) else tok
            (stack[-1] if stack else out).append(atom)
    if stack:
        raise ConversionError('unbalanced (')
    return out


def num_str(q):
    """Exact real numeral: 2 -> 2.0, -0.88 -> (- 0.88), 1/3 -> (/ 1.0 3.0)."""
    if q < 0:
        return '(- %s)' % num_str(-q)
    d, k2, k5 = q.denominator, 0, 0
    while d % 2 == 0:
        d, k2 = d // 2, k2 + 1
    while d % 5 == 0:
        d, k5 = d // 5, k5 + 1
    if d != 1:
        return '(/ %d.0 %d.0)' % (q.numerator, q.denominator)
    k = max(k2, k5)
    digits = str(q.numerator * 10 ** k // q.denominator).rjust(k + 1, '0')
    return '%s.%s' % (digits[:len(digits) - k], digits[len(digits) - k:] or '0')


def to_str(e):
    if isinstance(e, Fraction):
        return num_str(e)
    if isinstance(e, list):
        return '(' + ' '.join(to_str(x) for x in e) + ')'
    return e


def atoms(e):
    if isinstance(e, list):
        for x in e:
            yield from atoms(x)
    elif isinstance(e, str):
        yield e


def subst(e, m):
    """Replace symbols by m, respecting let scopes."""
    if isinstance(e, str):
        return m.get(e, e)
    if not isinstance(e, list):
        return e
    if e and e[0] == 'let':
        bound = {n for n, _ in e[1]}
        inner = {k: v for k, v in m.items() if k not in bound}
        return ['let', [[n, subst(x, m)] for n, x in e[1]], subst(e[2], inner)]
    return [subst(x, m) for x in e]


def norm_sort(s):
    # bench_xai_ha writes predicate sorts as ((Real)(Real) ...)
    if isinstance(s, list) and len(s) == 1:
        return norm_sort(s[0])
    return s


def is_array(s):
    return isinstance(s, list) and s[0] == 'Array'


def select_chain(e):
    """(select (select A i) j) -> ('A', [i, j]); None if e is not a select on a symbol."""
    idx = []
    while isinstance(e, list) and len(e) == 3 and e[0] == 'select':
        idx.append(e[2])
        e = e[1]
    if not idx or not isinstance(e, str):
        return None
    return e, idx[::-1]


def is_int(q):
    return isinstance(q, Fraction) and q.denominator == 1


# ---------------------------------------------------------------- input (Z3 fixedpoint format)

class Chc:
    def __init__(self, sexprs):
        self.vars = {}    # declare-var: name -> sort (in declaration order)
        self.funs = {}    # define-fun: name -> (params, body)
        self.rels = {}    # declare-rel: name -> [sort]
        self.rules = []   # (body conjuncts, head)
        self.query = None
        for e in sexprs:
            if not isinstance(e, list) or not e:
                raise ConversionError('unexpected top-level %s' % to_str(e))
            cmd = e[0]
            if cmd == 'declare-var':
                self.vars[e[1]] = norm_sort(e[2])
            elif cmd == 'define-fun':
                self.funs[e[1]] = ([p[0] for p in e[2]], e[4])
            elif cmd == 'declare-rel':
                self.rels[e[1]] = [norm_sort(s) for s in e[2]]
            elif cmd == 'rule':
                r = e[1]
                if isinstance(r, list) and r and r[0] == '=>':
                    body, head = r[1], r[2]
                else:
                    body, head = 'true', r
                conj = body[1:] if isinstance(body, list) and body and body[0] == 'and' else [body]
                self.rules.append(([c for c in conj if c != 'true'], head))
            elif cmd == 'query':
                self.query = e[1]
            elif cmd in ('set-logic', 'set-info', 'set-option', 'check-sat', 'exit'):
                pass
            else:
                raise ConversionError('unsupported command %s' % cmd)


# ---------------------------------------------------------------- conversion

class Converter:
    def __init__(self, chc):
        self.chc = chc
        if chc.query is None or chc.rels.get(chc.query) != []:
            raise ConversionError('expected (query P) with P a 0-ary relation')
        preds = [p for p in chc.rels if p != chc.query]
        if len(preds) != 1:
            raise ConversionError('expected one predicate besides the query, found %s' % preds)
        self.inv = preds[0]
        self.sorts = chc.rels[self.inv]
        self.arr_pos = [i for i, s in enumerate(self.sorts) if is_array(s)]
        self.table = {}          # (array position, indices) -> constant from the fact
        self.counter_pos = None  # inv position of the variable indexing the arrays
        self.names = set(chc.vars) | set(chc.funs) | set(chc.rels)
        self.n_fresh = 0
        self.splits = set()

    # -- rule anatomy

    def is_app(self, c):
        return isinstance(c, list) and c and c[0] == self.inv

    def is_query_head(self, h):
        return h == self.chc.query or h == [self.chc.query]

    def array_args(self, app):
        """{array variable: position} of an inv application."""
        args = {}
        for p in self.arr_pos:
            a = app[1 + p]
            if not isinstance(a, str) or not is_array(self.chc.vars.get(a)) or a in args:
                raise ConversionError('array argument %d of %s must be a distinct array variable'
                                      % (p, to_str(app)[:80]))
            args[a] = p
        return args

    def anatomy(self, conj, head):
        apps = [c for c in conj if self.is_app(c)]
        rest = [c for c in conj if not self.is_app(c)]
        if len(apps) > 1:
            raise ConversionError('nonlinear rule (%d applications of %s)' % (len(apps), self.inv))
        if any(self.chc.query in atoms(c) for c in rest):
            raise ConversionError('%s used in a rule body' % self.chc.query)
        if not (self.is_app(head) or self.is_query_head(head)):
            raise ConversionError('unexpected head %s' % to_str(head))
        return (apps[0] if apps else None), rest

    # -- the fact: read the array contents

    def read_fact(self, rest, head):
        arrays = self.array_args(head)
        kept = []
        for c in rest:
            if not set(atoms(c)) & set(arrays):
                kept.append(c)
                continue
            key, val = self.array_entry(c, arrays)
            if self.table.get(key, val) != val:
                raise ConversionError('the fact gives two values to %s' % to_str(c))
            self.table[key] = val
        return kept

    def array_entry(self, c, arrays):
        if isinstance(c, list) and len(c) == 3 and c[0] == '=':
            for sel, val in ((c[1], c[2]), (c[2], c[1])):
                ch = select_chain(sel)
                if (isinstance(val, Fraction) and ch and ch[0] in arrays
                        and all(isinstance(i, Fraction) for i in ch[1])):
                    return (arrays[ch[0]], tuple(ch[1])), val
        raise ConversionError('the fact constrains an array other than (= (select ...) constant): %s'
                              % to_str(c)[:120])

    # -- a transition: arrays copied, reads indexed by the counter

    def drop_copies(self, app, head, rest):
        body_arr = {p: v for v, p in self.array_args(app).items()}
        head_arr = {p: v for v, p in self.array_args(head).items()}
        kept = list(rest)
        for p in self.arr_pos:
            hv, bv = head_arr[p], body_arr[p]
            if hv == bv:
                continue
            for c in kept:
                if c in (['=', hv, bv], ['=', bv, hv]):
                    kept.remove(c)
                    break
            else:
                raise ConversionError('array argument %d (%s) is not copied by the transition' % (p, hv))
        extra = set(head_arr.values()) - set(body_arr.values())
        for c in kept:
            if set(atoms(c)) & extra:
                raise ConversionError('the transition constrains the new arrays: %s' % to_str(c)[:120])
        return kept

    @staticmethod
    def index_vars(rest, arrays):
        found = set()

        def walk(e):
            if not isinstance(e, list):
                return
            ch = select_chain(e)
            if ch and ch[0] in arrays:
                for i in ch[1]:
                    if isinstance(i, str):
                        found.add(i)
                    elif not isinstance(i, Fraction):
                        raise ConversionError('array index %s is neither a constant nor a variable'
                                              % to_str(i))
                return
            for x in e:
                walk(x)

        for c in rest:
            walk(c)
        return found

    @staticmethod
    def guard_values(rest, v):
        """Values k of a conjunct (or (= v k1) ... (= v kn)) or (= v k)."""
        def value(d):
            if isinstance(d, list) and len(d) == 3 and d[0] == '=':
                if d[1] == v and isinstance(d[2], Fraction):
                    return d[2]
                if d[2] == v and isinstance(d[1], Fraction):
                    return d[1]
            return None

        for c in rest:
            ds = c[1:] if isinstance(c, list) and c and c[0] == 'or' else [c]
            vals = [value(d) for d in ds]
            if vals and None not in vals:
                return vals
        return None

    # -- folding: inline define-funs, replace array reads, simplify constants

    def fresh(self, base):
        while True:
            self.n_fresh += 1
            n = '%s_%d' % (base, self.n_fresh)
            if n not in self.names:
                return n

    def inline(self, f, args):
        params, body = self.chc.funs[f]
        m, binds = {}, []
        for p, a in zip(params, args):
            if isinstance(a, list):
                n = self.fresh(p)
                binds.append([n, a])
                m[p] = n
            else:
                m[p] = a
        body = subst(body, m)
        return ['let', binds, body] if binds else body

    def fold(self, e, arrays):
        if not isinstance(e, list) or not e:
            return e
        h = e[0]
        if h == 'let':
            binds = [(n, self.fold(x, arrays)) for n, x in e[1]]
            body = self.fold(e[2], arrays)
            keep, m = [], {}
            for n, x in binds:
                uses = sum(1 for a in atoms(body) if a == n)
                if uses <= 1 or not isinstance(x, list):
                    m[n] = x
                else:
                    keep.append([n, x])
            if m:
                body = self.fold(subst(body, m), arrays)
            return ['let', keep, body] if keep else body
        args = [self.fold(x, arrays) for x in e[1:]]
        if h == 'select':
            ch = select_chain([h] + args)
            if ch and ch[0] in arrays and all(isinstance(i, Fraction) for i in ch[1]):
                key = (arrays[ch[0]], tuple(ch[1]))
                if key in self.table:
                    return self.table[key]
            return [h] + args
        if h in self.chc.funs:
            return self.fold(self.inline(h, args), arrays)
        if len(args) == 2 and all(isinstance(a, Fraction) for a in args):
            x, y = args
            cmp = {'=': x == y, '<': x < y, '<=': x <= y, '>': x > y, '>=': x >= y}
            if h in cmp:
                return 'true' if cmp[h] else 'false'
        if h == 'ite' and args[0] in ('true', 'false'):
            return args[1] if args[0] == 'true' else args[2]
        if h == 'not' and args[0] in ('true', 'false'):
            return 'false' if args[0] == 'true' else 'true'
        if h in ('and', 'or'):
            unit, zero = ('true', 'false') if h == 'and' else ('false', 'true')
            if zero in args:
                return zero
            args = [a for a in args if a != unit]
            if not args:
                return unit
            if len(args) == 1:
                return args[0]
        return [h] + args

    def split(self, e, arrays, v, vals):
        """e under the guard v in vals: (ite (= v k1) e[k1] (ite ... e[kn]))."""
        cases = [(k, self.fold(subst(e, {v: k}), arrays)) for k in vals]
        out = cases[-1][1]
        if all(x == out for _, x in cases):
            return out
        self.splits.add(v)
        for k, x in reversed(cases[:-1]):
            out = ['ite', ['=', v, k], x, out]
        return out

    def convert_conj(self, c, arrays, v, vals):
        syms = set(atoms(c))
        if v is None or not syms & set(arrays) or v not in syms:
            return self.fold(c, arrays)
        if isinstance(c, list) and len(c) == 3 and c[0] == '=' and isinstance(c[1], str) \
                and c[1] not in arrays and c[1] not in set(atoms(c[2])):
            return ['=', c[1], self.split(c[2], arrays, v, vals)]
        return self.split(c, arrays, v, vals)

    # -- whole system

    def strip(self, app):
        return [app[0]] + [a for i, a in enumerate(app[1:]) if i not in self.arr_pos]

    def convert(self):
        rules = [(self.anatomy(conj, head), head) for conj, head in self.chc.rules]
        facts = [r for r in rules if r[0][0] is None and self.is_app(r[1])]
        if len(facts) != 1:
            raise ConversionError('expected exactly one fact for %s, found %d' % (self.inv, len(facts)))

        out = []
        for (app, rest), head in rules:
            if app is None and self.is_app(head):
                rest, arrays = self.read_fact(rest, head), {}
            elif app is None:
                arrays = {}
            else:
                if self.is_app(head):
                    rest = self.drop_copies(app, head, rest)
                arrays = self.array_args(app)
            vs = self.index_vars(rest, arrays)
            if len(vs) > 1:
                raise ConversionError('arrays indexed by several variables: %s' % sorted(vs))
            v = vs.pop() if vs else None
            vals = None
            if v is not None:
                vals = self.guard_values(rest, v)
                if vals is None:
                    raise ConversionError('no guard (or (= %s k) ...) bounds the array index %s' % (v, v))
                pos = app.index(v) - 1 if v in app[1:] else None
                if pos is None or (self.counter_pos not in (None, pos)):
                    raise ConversionError('array index %s is not a fixed argument of %s' % (v, self.inv))
                self.counter_pos = pos
            conj = [self.convert_conj(c, arrays, v, vals) for c in rest]
            conj = [c for c in conj if c != 'true']
            for c in conj:
                left = set(atoms(c)) & {a for a, s in self.chc.vars.items() if is_array(s)}
                if left:
                    raise ConversionError('array read not fixed by the fact (%s) in %s'
                                          % (', '.join(sorted(left)), to_str(c)[:160]))
            out.append(((self.strip(app) if app else None), conj,
                        self.strip(head) if self.is_app(head) else 'false', app, head, rest))
        self.check_ints(out)
        return out

    def check_ints(self, rules):
        """Int is allowed only for the counter, fixed to an integer by the fact and
        incremented by an integer by the transitions: then it only takes integer
        values, so declaring it Real changes nothing."""
        cp = self.counter_pos
        for i, s in enumerate(self.sorts):
            if s == 'Int' and i != cp:
                raise ConversionError('argument %d of %s is Int and is not the counter' % (i, self.inv))
        for _, conj, _, app, head, rest in rules:
            ints = {a for a in atoms(conj) if self.chc.vars.get(a) == 'Int'}
            ok = {x[1 + cp] for x in (app, head) if cp is not None and self.is_app(x)}
            if ints - ok:
                raise ConversionError('Int variables other than the counter: %s' % sorted(ints - ok))
            if cp is None or self.sorts[cp] != 'Int':
                continue
            if app is None:
                c = head[1 + cp]
                if not any(defines(d, c, is_int) for d in conj):
                    raise ConversionError('the fact does not fix the Int counter %s to an integer' % c)
            elif self.is_app(head):
                hc, bc = head[1 + cp], app[1 + cp]
                inc = (lambda x: isinstance(x, list) and len(x) == 3 and x[0] == '+'
                       and ((x[1] == bc and is_int(x[2])) or (x[2] == bc and is_int(x[1]))))
                if not any(defines(d, hc, inc) for d in conj):
                    raise ConversionError('the transition does not set the Int counter %s to %s + integer'
                                          % (hc, bc))

    def sort_of(self, name):
        s = self.chc.vars[name]
        return 'Real' if s == 'Int' else s

    def emit(self, rules, source):
        sorts = ['Real' if s == 'Int' else s for i, s in enumerate(self.sorts) if i not in self.arr_pos]
        lines = [
            '; %s without arrays, in CHC-COMP format (Golem).' % source,
            '; Generated by encoding_no_arrays/remove_arrays.py: same predicate and rules,',
            '; the weight/bias arrays are replaced by the constants the fact gives them%s.'
            % (', split on the values of %s' % ', '.join(sorted(self.splits)) if self.splits else ''),
            '(set-logic HORN)',
            '',
            '(declare-fun %s (%s) Bool)' % (self.inv, ' '.join(to_str(s) for s in sorts)),
            '',
        ]
        for app, conj, head, _, _, _ in rules:
            body = ([app] if app else []) + conj
            used = set(atoms(body)) | set(atoms(head))
            qvars = [v for v in self.chc.vars if v in used]
            lines.append('(assert')
            if qvars:
                lines.append('\t(forall (%s)' % ' '.join('(%s %s)' % (v, to_str(self.sort_of(v)))
                                                          for v in qvars))
            ind = '\t\t' if qvars else '\t'
            if not body:
                lines.append(ind + to_str(head))
            else:
                lines.append(ind + '(=>')
                if len(body) == 1:
                    lines.append(fmt_conj(body[0], ind + '\t'))
                else:
                    lines.append(ind + '\t(and')
                    lines.extend(fmt_conj(c, ind + '\t\t') for c in body)
                    lines.append(ind + '\t)')
                lines.append(ind + '\t' + to_str(head))
                lines.append(ind + ')')
            if qvars:
                lines.append('\t)')
            lines.append(')')
            lines.append('')
        lines.append('(check-sat)')
        return '\n'.join(lines) + '\n'


def defines(d, v, ok):
    """d is (= v e) or (= e v) with ok(e)."""
    return (isinstance(d, list) and len(d) == 3 and d[0] == '='
            and ((d[1] == v and ok(d[2])) or (d[2] == v and ok(d[1]))))


def is_case(e):
    return (isinstance(e, list) and len(e) == 4 and e[0] == 'ite' and isinstance(e[1], list)
            and len(e[1]) == 3 and e[1][0] == '=' and isinstance(e[1][2], Fraction))


def fmt_conj(c, ind):
    """One conjunct per line; a split right-hand side gets one line per counter value."""
    if isinstance(c, list) and len(c) == 3 and c[0] == '=' and is_case(c[2]):
        lines = [ind + '(= %s' % to_str(c[1])]
        e, close = c[2], 1
        while is_case(e):
            lines.append(ind + '\t(ite %s %s' % (to_str(e[1]), to_str(e[2])))
            e, close = e[3], close + 1
        lines.append(ind + '\t' + to_str(e) + ')' * close)
        return '\n'.join(lines)
    return ind + to_str(c)


def convert_file(path):
    with open(path) as f:
        chc = Chc(parse(f.read()))
    conv = Converter(chc)
    rules = conv.convert()
    return conv.emit(rules, os.path.basename(path)), conv


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('inputs', nargs='+')
    ap.add_argument('-o', '--output', help='output file (one input) or directory')
    args = ap.parse_args()

    to_dir = args.output and (len(args.inputs) > 1 or os.path.isdir(args.output)
                              or not args.output.endswith('.smt2'))
    if to_dir:
        os.makedirs(args.output, exist_ok=True)
    elif args.output and os.path.dirname(args.output):
        os.makedirs(os.path.dirname(args.output), exist_ok=True)
    failed = 0
    for path in args.inputs:
        try:
            text, conv = convert_file(path)
        except (ConversionError, OSError) as err:
            print('%s: %s' % (path, err), file=sys.stderr)
            failed += 1
            continue
        if not args.output:
            sys.stdout.write(text)
            continue
        dest = os.path.join(args.output, os.path.basename(path)) if to_dir else args.output
        with open(dest, 'w') as f:
            f.write(text)
        print('%s -> %s (%d array entries inlined)' % (path, dest, len(conv.table)), file=sys.stderr)
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
