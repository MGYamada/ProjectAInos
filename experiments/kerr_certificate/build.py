"""Assemble ProjectAinos/GeneralRelativity/Kerr.lean from template.lean and generated parts."""
import os
import pickle
import sys
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from kast import r, c, M, a, S, D, from_sympy, lean, deriv_term, ne_hyps, dep  # noqa: E402
from gen import G, Sx, Dx, to_atoms, nz  # noqa: E402

ORDER = ['M', 'a', 'r', 'c']
HYPS = {'hS': 'sig a r c ≠ 0', 'hD': 'del M a r ≠ 0', 'hc1': 'c - 1 ≠ 0', 'hc2': 'c + 1 ≠ 0',
        'h1c': '1 - c ^ 2 ≠ 0'}
HORDER = ['hS', 'hD', 'hc1', 'hc2', 'h1c']


def wrap(text, indent, width=100):
    """Wrap `text` into lines of at most `width` characters; the first line starts with
    `indent` spaces, the next ones with `indent + 4`. Breaks are preferred between binders
    `) (` and after operators, and never next to `≠`, `:`, `^`, `=`."""
    words = text.split(' ')
    groups = []
    for w in words:
        if groups and (groups[-1].split(' ')[-1] in ('≠', ':', '^', '=')
                       or w in (':', '=', '≠', '^')):
            groups[-1] += ' ' + w
        else:
            groups.append(w)
    lines = []
    cur = []
    first = True

    def width_of(gs, first):
        return (indent if first else indent + 4) + len(' '.join(gs))
    for g in groups:
        if not cur or width_of(cur + [g], first) <= width:
            cur.append(g)
            continue
        # find a good break inside cur: after a group ending with ')' followed by '('
        cand = [n for n in range(1, len(cur)) if cur[n - 1].endswith(')') and
                cur[n].startswith('(') and width_of(cur[:n], first) >= width * 0.6]
        cand2 = [n for n in range(1, len(cur)) if cur[n - 1] in ('+', '-', '*', '/', ':=', '→',
                                                                  '=', '<;>')
                 and width_of(cur[:n], first) >= width * 0.6]
        n = cand[-1] if cand else (cand2[-1] if cand2 else len(cur))
        lines.append(' ' * (indent if first else indent + 4) + ' '.join(cur[:n]))
        first = False
        cur = cur[n:] + [g]
        while width_of(cur, first) > width and len(cur) > 1:
            lines.append(' ' * (indent + 4) + ' '.join(cur[:-1]))
            cur = cur[-1:]
    lines.append(' ' * (indent if first else indent + 4) + ' '.join(cur))
    for ln in lines:
        assert len(ln) <= width, ln
    return '\n'.join(lines)


def node_vars(node, acc=None):
    if acc is None:
        acc = set()
    k = node[0]
    if k == 'var':
        acc.add(node[1])
    elif k == 'atom':
        acc.update(['a', 'r', 'c'] if node[1] == 'S' else ['M', 'a', 'r'])
    elif k in ('neg', 'pow'):
        node_vars(node[1], acc)
    elif k in ('add', 'sub', 'mul', 'div'):
        node_vars(node[1], acc)
        node_vars(node[2], acc)
    return acc


def node_atoms(node, acc=None):
    if acc is None:
        acc = set()
    k = node[0]
    if k == 'atom':
        acc.add(node[1])
    elif k in ('neg', 'pow'):
        node_atoms(node[1], acc)
    elif k in ('add', 'sub', 'mul', 'div'):
        node_atoms(node[1], acc)
        node_atoms(node[2], acc)
    return acc


def den_hyps(node, acc=None):
    """The nonzero hypotheses needed for the denominators of the node."""
    if acc is None:
        acc = set()
    k = node[0]
    if k == 'div':
        den_hyps(node[1], acc)
        ne_hyps(node[2], acc)
        den_hyps(node[2], acc)
    elif k in ('neg', 'pow'):
        den_hyps(node[1], acc)
    elif k in ('add', 'sub', 'mul'):
        den_hyps(node[1], acc)
        den_hyps(node[2], acc)
    return acc


def pows(node, var, acc=None):
    if acc is None:
        acc = set()
    k = node[0]
    if k == 'pow' and dep(node, var):
        acc.add(node[2])
    if k in ('neg', 'pow'):
        pows(node[1], var, acc)
    elif k in ('add', 'sub', 'mul', 'div'):
        pows(node[1], var, acc)
        pows(node[2], var, acc)
    return acc


def args_str(vs):
    return ' '.join(v for v in ORDER if v in vs)


def hyp_binders(hs):
    return ' '.join(f'({h} : {HYPS[h]})' for h in HORDER if h in hs)


def hyp_args(hs):
    return ' '.join(h for h in HORDER if h in hs)


class Fn:
    """A named function of (M a r c) with an AST."""

    def __init__(self, name, node, public, doc=None, nat_exp=False):
        self.name = name
        self.node = node
        self.vars = node_vars(node)
        self.public = public
        self.doc = doc
        self.nat_exp = nat_exp

    def call(self, rname='r', cname='c'):
        sub = {'M': 'M', 'a': 'a', 'r': rname, 'c': cname}
        return ' '.join([self.name] + [sub[v] for v in ORDER if v in self.vars])

    def defn(self):
        out = []
        if self.doc:
            out.append(wrap(f'/-- {self.doc} -/', 0))
        pre = '' if self.public else 'private '
        out.append(f'{pre}def {self.name} ({args_str(self.vars)} : ℝ) : ℝ :=')
        out.append(wrap(lean(self.node, nat_exp=self.nat_exp), 2))
        return '\n'.join(out) + '\n'


def deriv_lemma(fn, dfn, var):
    """A lemma `HasDerivAt (fun s => fn ...) (dfn ...) var`."""
    hyps = set()
    term = deriv_term(fn.node, var, hyps)
    hyps |= den_hyps(dfn.node)
    vs = fn.vars | dfn.vars | {var}
    lam = fn.call('s', 'c') if var == 'r' else fn.call('r', 's')
    lines = [wrap(f'private theorem hasDerivAt_{fn.name}_{var} ({args_str(vs)} : ℝ)'
                  + (' ' + hyp_binders(hyps) if hyps else '') + ' :', 0)]
    lines.append(wrap(f'HasDerivAt (fun s => {lam}) ({dfn.call()}) {var} := by', 4))
    lines.append(f'  unfold {fn.name} {dfn.name}')
    lines.append(wrap(f'refine HasDerivAt.congr_deriv {term} ?_', 2))
    ps = pows(fn.node, var)
    if ps:
        lemmas = ['Nat.cast_ofNat', 'Nat.reduceSub'] + (['pow_one'] if 2 in ps else [])
        lines.append(f'  simp only [{", ".join(lemmas)}]')
    lines += tail(hyps, fn.vars | dfn.vars, f'hasDerivAt_{fn.name}_{var}')
    return '\n'.join(lines) + '\n', hyps


FS_CLOSES = {'hasDerivAt_grr_c'}


def tail(hyps, vs, name=None):
    """Generalize Σ and Δ, clear denominators, substitute, ring."""
    out = []
    if name in FS_CLOSES:
        return ['  field_simp']
    hasS = {'a', 'r', 'c'} <= vs
    hasD = {'M', 'a', 'r'} <= vs
    out.append('  generalize hSd : sig a r c = S' + (' at hS ⊢' if 'hS' in hyps else ''))
    if 'M' in vs:
        out.append('  generalize hDd : del M a r = D' + (' at hD ⊢' if 'hD' in hyps else ''))
    out.append('  field_simp')
    out.append('  unfold sig at hSd')
    if 'M' in vs:
        out.append('  unfold del at hDd')
        out.append('  subst hSd hDd')
    else:
        out.append('  subst hSd')
    out.append('  ring')
    del hasS, hasD
    return out


# ---------------------------------------------------------------- coefficients
def N(n):
    return ('num', n)


def V(x):
    return ('var', x)


def mul(*xs):
    acc = xs[0]
    for x in xs[1:]:
        acc = ('mul', acc, x)
    return acc


ONE_C2 = ('sub', N(1), ('pow', V('c'), 2))
AS, AD = ('atom', 'S'), ('atom', 'D')
COEF_NODES = {
    'gtt': ('neg', ('sub', N(1), ('div', mul(N(2), V('M'), V('r')), AS))),
    'gtp': ('neg', ('div', mul(N(2), V('M'), V('a'), V('r'), ONE_C2), AS)),
    'grr': ('div', AS, AD),
    'gcc': ('div', AS, ONE_C2),
    'gpp': ('mul', ('add', ('add', ('pow', V('r'), 2), ('pow', V('a'), 2)),
                    ('div', mul(N(2), V('M'), ('pow', V('a'), 2), V('r'), ONE_C2), AS)),
            ONE_C2),
}
COEF_DOC = {
    'gtt': 'The coefficient `g_tt = −(1 − 2Mr/Σ)` of the Kerr metric.',
    'gtp': 'The coefficient `g_tφ = −2Mar(1 − χ²)/Σ` of the Kerr metric.',
    'grr': 'The coefficient `g_rr = Σ/Δ` of the Kerr metric.',
    'gcc': 'The coefficient `g_χχ = Σ/(1 − χ²)` of the Kerr metric.',
    'gpp': 'The coefficient `g_φφ = (r² + a² + 2Ma²r(1 − χ²)/Σ)(1 − χ²)` of the Kerr metric.',
}
SUBS = {S: Sx, D: Dx}


def to_sympy(node):
    k = node[0]
    if k == 'num':
        return sp.Integer(node[1])
    if k == 'var':
        return {'r': r, 'c': c, 'M': M, 'a': a}[node[1]]
    if k == 'atom':
        return Sx if node[1] == 'S' else Dx
    if k == 'neg':
        return -to_sympy(node[1])
    if k == 'pow':
        return to_sympy(node[1]) ** node[2]
    x, y = to_sympy(node[1]), to_sympy(node[2])
    return {'add': x + y, 'sub': x - y, 'mul': x * y, 'div': x / y}[k]


def zero_or_fn(expr, name, public=False, doc=None):
    if sp.simplify(expr) == 0:
        return None
    return Fn(name, from_sympy(to_atoms(expr)), public, doc, nat_exp=True)


coef = {}
for nm, node in COEF_NODES.items():
    f = Fn(nm, node, True, COEF_DOC[nm])
    ex = to_sympy(node)
    dr = zero_or_fn(sp.diff(ex, r), f'd{nm}_r')
    dc = zero_or_fn(sp.diff(ex, c), f'd{nm}_c')
    coef[nm] = (f, ex, dr, dc)

# ---------------------------------------------------------------- Christoffel entries
def cname(k, i, j):
    i, j = min(i, j), max(i, j)
    return f'chris{k}_{i}{j}'


chris = {}
for (k, i, j) in nz:
    e = to_atoms(G[k][i][j])
    doc = (f'The Christoffel symbol `Γ^{k}_{{{i}{j}}}`' +
           (f' `= Γ^{k}_{{{j}{i}}}`' if i != j else '') + ' of the Kerr metric.')
    f = Fn(cname(k, i, j), from_sympy(e), True, doc)
    dr = zero_or_fn(sp.diff(G[k][i][j], r), f'd{cname(k, i, j)}_r')
    dc = zero_or_fn(sp.diff(G[k][i][j], c), f'd{cname(k, i, j)}_c')
    chris[(k, i, j)] = (f, G[k][i][j], dr, dc)


def chris_at(k, i, j):
    key = (k, min(i, j), max(i, j))
    return chris.get(key)


def gen_entries():
    out = []
    for key in sorted(chris):
        out.append(chris[key][0].defn())
    rows = []
    for k in range(4):
        mats = []
        for i in range(4):
            vals = []
            for j in range(4):
                e = chris_at(k, i, j)
                vals.append(e[0].call() if e else '0')
            mats.append('![' + ', '.join(vals) + ']')
        rows.append('![' + ', '.join(mats) + ']')
    body = '![' + ',\n'.join(rows) + ']'
    out.append('''/-- **The Christoffel symbols of the Kerr metric** as functions of `r` and `χ`:
`christoffelTable M a r χ k i j` is `Γ^k_{ij}`, symmetric in the lower indices, with the twenty
independent nonzero symbols `chris…` and the others zero. -/
def christoffelTable (M a r c : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=''')
    tl = []
    for k in range(4):
        for i in range(4):
            vals = []
            for j in range(4):
                e = chris_at(k, i, j)
                vals.append(e[0].call() if e else '0')
            pre = ('![![![' if (k == 0 and i == 0) else ('![![' if i == 0 else '!['))
            suf = (']]]' if (k == 3 and i == 3) else (']],' if i == 3 else '],'))
            ind = 2 if (k == 0 and i == 0) else (4 if i == 0 else 6)
            if k == 0 and i == 0:
                ind = 2
            tl.append(wrap(pre + ', '.join(vals) + suf, ind if not (k == 0 and i == 0) else 2))
    out.append('\n'.join(tl) + '\n')
    del body
    return '\n'.join(out)


def table_text(name, doc, cells, sig):
    """cells: function (k, i, j) -> text."""
    lines = []
    if doc:
        lines.append(wrap(f'/-- {doc} -/', 0))
    lines.append(f'private def {name} {sig} : Fin 4 → Fin 4 → Fin 4 → ℝ :=')
    for k in range(4):
        for i in range(4):
            vals = [cells(k, i, j) for j in range(4)]
            pre = ('![![![' if (k == 0 and i == 0) else ('![![' if i == 0 else '!['))
            suf = (']]]' if (k == 3 and i == 3) else (']],' if i == 3 else '],'))
            ind = 2 if (k == 0 and i == 0) else (4 if i == 0 else 6)
            lines.append(wrap(pre + ', '.join(vals) + suf, ind))
    return '\n'.join(lines) + '\n'


def all_hyps():
    return set(HORDER)


def gen_chris_derivs():
    out = []
    used = {'r': {}, 'c': {}}
    for key in sorted(chris):
        f, ex, dr, dc = chris[key]
        for var, dfn in (('r', dr), ('c', dc)):
            if dfn is None:
                continue
            out.append(dfn.defn())
            txt, hyps = deriv_lemma(f, dfn, var)
            out.append(txt)
            used[var][key] = hyps
    for var, idx in (('r', 2), ('c', 3)):
        def cell(k, i, j, var=var, idx=idx):
            e = chris_at(k, i, j)
            if e is None or e[idx] is None:
                return '0'
            return e[idx].call()
        out.append(table_text(f'christoffel{var.upper()}', None, cell, '(M a r c : ℝ)'))
    # dispatch lemmas
    for var in ('r', 'c'):
        idx = 2 if var == 'r' else 3
        hs = set()
        for key, h in used[var].items():
            hs |= h
        lam = 'christoffelTable M a s c q i j' if var == 'r' else 'christoffelTable M a r s q i j'
        lines = [wrap(f'private theorem hasDerivAt_christoffelTable_{var} (M a r c : ℝ) '
                      f'{hyp_binders(hs)} (q i j : Fin 4) :', 0)]
        lines.append(wrap(f'HasDerivAt (fun s => {lam}) (christoffel{var.upper()} M a r c q i j)'
                          f' {var} := by', 4))
        lines.append('  fin_cases q <;> fin_cases i <;> fin_cases j')
        for k in range(4):
            for i in range(4):
                for j in range(4):
                    e = chris_at(k, i, j)
                    if e is None:
                        lines.append(f'  · exact hasDerivAt_const {var} (0 : ℝ)')
                    else:
                        f = e[0]
                        dfn = e[idx]
                        if dfn is None:
                            lines.append(f'  · exact hasDerivAt_const {var} ({f.call()} : ℝ)')
                        else:
                            key = (k, min(i, j), max(i, j))
                            h = used[var][key]
                            vs = f.vars | dfn.vars | {var}
                            lines.append(wrap(f'· exact hasDerivAt_{f.name}_{var} '
                                              f'{args_str(vs)} {hyp_args(h)}', 2))
        out.append('\n'.join(lines) + '\n')
    return '\n'.join(out), used


def gen_coef_derivs():
    out = []
    used = {'r': {}, 'c': {}}
    for nm in ['gtt', 'gtp', 'grr', 'gcc', 'gpp']:
        f, ex, dr, dc = coef[nm]
        for var, dfn in (('r', dr), ('c', dc)):
            if dfn is None:
                continue
            out.append(dfn.defn())
            txt, hyps = deriv_lemma(f, dfn, var)
            out.append(txt)
            used[var][nm] = hyps
    return '\n'.join(out), used


COEF_POS = {(0, 0): 'gtt', (0, 3): 'gtp', (3, 0): 'gtp', (1, 1): 'grr', (2, 2): 'gcc',
            (3, 3): 'gpp'}


def gen_coef_tables(used):
    out = []
    for var, idx in (('r', 2), ('c', 3)):
        rows = []
        for i in range(4):
            vals = []
            for j in range(4):
                nm = COEF_POS.get((i, j))
                if nm is None or coef[nm][idx] is None:
                    vals.append('0')
                else:
                    vals.append(coef[nm][idx].call())
            rows.append('![' + ', '.join(vals) + ']')
        out.append(f'private def metric{var.upper()} (M a r c : ℝ) : Fin 4 → Fin 4 → ℝ :=')
        txt = '![' + ',\n    '.join(rows) + ']'
        out.append('\n'.join(wrap(t, 2 if n == 0 else 4) for n, t in enumerate(txt.split('\n    '))))
        out.append('')
    for var, idx in (('r', 2), ('c', 3)):
        hs = set()
        for h in used[var].values():
            hs |= h
        lam = 'metricTable M a s c i j' if var == 'r' else 'metricTable M a r s i j'
        lines = [wrap(f'private theorem hasDerivAt_metricTable_{var} (M a r c : ℝ) '
                      f'{hyp_binders(hs)} (i j : Fin 4) :', 0)]
        lines.append(wrap(f'HasDerivAt (fun s => {lam}) (metric{var.upper()} M a r c i j) {var}'
                          ' := by', 4))
        lines.append('  fin_cases i <;> fin_cases j')
        for i in range(4):
            for j in range(4):
                nm = COEF_POS.get((i, j))
                if nm is None:
                    lines.append(f'  · exact hasDerivAt_const {var} (0 : ℝ)')
                else:
                    f, ex, dr, dc = coef[nm]
                    dfn = coef[nm][idx]
                    if dfn is None:
                        lines.append(f'  · exact hasDerivAt_const {var} ({f.call()} : ℝ)')
                    else:
                        vs = f.vars | dfn.vars | {var}
                        lines.append(wrap(f'· exact hasDerivAt_{nm}_{var} {args_str(vs)} '
                                          f'{hyp_args(used[var][nm])}', 2))
        out.append('\n'.join(lines) + '\n')
    return '\n'.join(out)


# ---------------------------------------------------------------- symbolic tables
def metric_fn(i, j):
    nm = COEF_POS.get((i, j))
    return coef[nm][0] if nm else None


def metric_dfn(var, i, j):
    nm = COEF_POS.get((i, j))
    if nm is None:
        return None
    return coef[nm][2 if var == 'r' else 3]


def partial_metric(l, j, k):
    """metricPartial M a l r c j k: the function names involved (or None)."""
    if l == 1:
        return metric_dfn('r', j, k)
    if l == 2:
        return metric_dfn('c', j, k)
    return None


def chris_fn(k, i, j):
    e = chris_at(k, i, j)
    return e[0] if e else None


def partial_chris(l, k, i, j):
    e = chris_at(k, i, j)
    if e is None:
        return None
    if l == 1:
        return e[2]
    if l == 2:
        return e[3]
    return None


def fn_hyps(fn):
    return den_hyps(fn.node)


def gen_lowered():
    out = []
    used = {}
    for l in range(4):
        for i in range(4):
            for j in range(4):
                fns = []
                nonzero = False
                for q in range(4):
                    g = metric_fn(l, q)
                    G_ = chris_fn(q, i, j)
                    if g is not None:
                        fns.append(g)
                    if G_ is not None:
                        fns.append(G_)
                    if g is not None and G_ is not None:
                        nonzero = True
                ps = [partial_metric(i, j, l), partial_metric(j, l, i), partial_metric(l, i, j)]
                for p in ps:
                    if p is not None:
                        fns.append(p)
                        nonzero = True
                tabs = ['Fin.sum_univ_four', 'metricTable', 'christoffelTable', 'metricPartial']
                if 1 in (i, j, l):
                    tabs.append('metricR')
                if 2 in (i, j, l):
                    tabs.append('metricC')
                tabs.append('Matrix.cons_val')
                hs = set()
                names = []
                vs = set()
                for fn in fns:
                    if fn.name not in names:
                        names.append(fn.name)
                    hs |= fn_hyps(fn)
                    vs |= fn.vars
                lines = [wrap(f'private theorem lowered_{l}_{i}{j} (M a r c : ℝ)'
                              + (' ' + hyp_binders(hs) if nonzero else '') + ' :', 0)]
                lines.append(wrap(f'∑ q, metricTable M a r c {l} q * christoffelTable M a r c q '
                                  f'{i} {j} = (metricPartial M a {i} r c {j} {l} + metricPartial '
                                  f'M a {j} r c {l} {i} - metricPartial M a {l} r c {i} {j}) / 2 '
                                  ':= by', 4))
                if nonzero:
                    lines.append(wrap('simp only [' + ', '.join(tabs + names) + ']', 2))
                    lines += tail(hs, vs | {'M', 'a', 'r', 'c'})
                    used[(l, i, j)] = hs
                else:
                    lines.append(wrap('simp only [' + ', '.join(tabs + names) + ']', 2))
                    lines.append('  ring')
                    used[(l, i, j)] = set()
                out.append('\n'.join(lines) + '\n')
    hs = set()
    for h in used.values():
        hs |= h
    lines = [wrap(f'private theorem lowered (M a r c : ℝ) {hyp_binders(hs)} (l i j : Fin 4) :', 0)]
    lines.append(wrap('∑ q, metricTable M a r c l q * christoffelTable M a r c q i j = '
                      '(metricPartial M a i r c j l + metricPartial M a j r c l i - '
                      'metricPartial M a l r c i j) / 2 := by', 4))
    lines.append('  fin_cases l <;> fin_cases i <;> fin_cases j')
    for l in range(4):
        for i in range(4):
            for j in range(4):
                h = used[(l, i, j)]
                lines.append(wrap(f'· exact lowered_{l}_{i}{j} M a r c {hyp_args(h)}'.rstrip(), 2))
    out.append('\n'.join(lines) + '\n')
    return '\n'.join(out), hs


def gen_ricci():
    out = []
    used = {}
    for j in range(4):
        for k in range(4):
            fns = []
            nonzero = False
            for i in range(4):
                for p in (partial_chris(i, i, j, k),):
                    if p is not None:
                        fns.append(p)
                        nonzero = True
                p = partial_chris(j, i, i, k)
                if p is not None:
                    fns.append(p)
                    nonzero = True
                for b in range(4):
                    for (x, y) in (((i, i, b), (b, j, k)), ((i, j, b), (b, i, k))):
                        fx, fy = chris_fn(*x), chris_fn(*y)
                        if fx is not None:
                            fns.append(fx)
                        if fy is not None:
                            fns.append(fy)
                        if fx is not None and fy is not None:
                            nonzero = True
            names = []
            hs = set()
            vs = set()
            for fn in fns:
                if fn.name not in names:
                    names.append(fn.name)
                hs |= fn_hyps(fn)
                vs |= fn.vars
            tabs = ['ricciTab', 'Fin.sum_univ_four', 'christoffelTable', 'christoffelPartial',
                    'christoffelR', 'christoffelC', 'Matrix.cons_val']
            lines = [wrap(f'private theorem ricciTab_{j}{k} (M a r c : ℝ)'
                          + (' ' + hyp_binders(hs) if nonzero else '') + ' :', 0)]
            lines.append(f'    ricciTab M a r c {j} {k} = 0 := by')
            if nonzero:
                lines.append(wrap('simp only [' + ', '.join(tabs + names) + ']', 2))
                lines += tail(hs, vs | {'M', 'a', 'r', 'c'})
                used[(j, k)] = hs
            else:
                lines.append(wrap('simp only [' + ', '.join(tabs) + ']', 2))
                lines.append('  ring')
                used[(j, k)] = set()
            out.append('\n'.join(lines) + '\n')
    hs = set()
    for h in used.values():
        hs |= h
    lines = [wrap(f'private theorem ricciTab_eq_zero (M a r c : ℝ) {hyp_binders(hs)} '
                  '(j k : Fin 4) :', 0)]
    lines.append('    ricciTab M a r c j k = 0 := by')
    lines.append('  fin_cases j <;> fin_cases k')
    for j in range(4):
        for k in range(4):
            lines.append(wrap(f'· exact ricciTab_{j}{k} M a r c {hyp_args(used[(j, k)])}'.rstrip(),
                              2))
    out.append('\n'.join(lines) + '\n')
    return '\n'.join(out), hs


def main():
    tpl = open(os.path.join(HERE, 'template.lean')).read()
    parts = {}
    parts['COEFDEFS'] = '\n'.join(coef[nm][0].defn() for nm in ['gtt', 'gtp', 'grr', 'gcc', 'gpp'])
    cd, cused = gen_coef_derivs()
    parts['COEFDERIVS'] = cd
    parts['COEFTABLES'] = gen_coef_tables(cused)
    parts['ENTRIES'] = gen_entries()
    chd, _ = gen_chris_derivs()
    parts['CHRISDERIVS'] = chd
    lo, lhs = gen_lowered()
    parts['LOWERED'] = lo
    ri, rhs = gen_ricci()
    parts['RICCI'] = ri
    for key, val in parts.items():
        tpl = tpl.replace(f'-- GEN:{key}\n', val)
    def union(d):
        u = set()
        for h in d.values():
            u |= h
        return u
    _, chused = gen_chris_derivs()
    sets = {'HMR': union(cused['r']), 'HMC': union(cused['c']), 'HCR': union(chused['r']),
            'HCC': union(chused['c']), 'HLO': lhs, 'HRI': rhs}
    TERM = {'hS': '(sig_ne hM h{p})', 'hD': '(del_ne ha h{p})', 'hc1': '(sub_one_ne h{p})',
            'hc2': '(add_one_ne h{p})', 'h1c': '(one_sub_sq_ne h{p})'}
    import re
    def rep(m):
        key, p = m.group(1), m.group(2)
        return ' '.join(TERM[h].format(p=p) for h in HORDER if h in sets[key])
    tpl = re.sub(r'@@(\w+):(\w+)@@', rep, tpl)
    fixed = []
    for ln in tpl.split('\n'):
        if len(ln) > 100:
            ind = len(ln) - len(ln.lstrip(' '))
            ln = wrap(ln.strip(), ind)
        fixed.append(ln)
    tpl = '\n'.join(fixed)
    assert '-- GEN:' not in tpl
    target = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'Kerr.lean')
    open(target, 'w').write(tpl)
    print('lowered hyps', sorted(lhs), 'ricci hyps', sorted(rhs))
    for n, ln in enumerate(tpl.split('\n')):
        if len(ln) > 100:
            print('LONG', n + 1, len(ln))


if __name__ == '__main__':
    main()
