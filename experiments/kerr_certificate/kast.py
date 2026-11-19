"""A small AST mirroring Lean's binary operators, a printer, and a HasDerivAt generator.

Nodes: ('num', n) | ('var', name) | ('atom', 'S'|'D') | ('add', x, y) | ('sub', x, y)
     | ('mul', x, y) | ('div', x, y) | ('neg', x) | ('pow', x, n)
"""
import sympy as sp

r, c, M, a = sp.symbols('r c M a', real=True)
S, D = sp.symbols('S D', real=True)
VARS = {r: 'r', c: 'c', M: 'M', a: 'a'}

PREC = {'add': 65, 'sub': 65, 'mul': 70, 'div': 70, 'neg': 75, 'pow': 75}


def from_sympy(e):
    """Convert a SymPy expression (integers, r c M a S D) to the AST."""
    if e.is_Integer:
        n = int(e)
        if n < 0:
            return ('neg', ('num', -n))
        return ('num', n)
    if e.is_Rational:
        raise ValueError('rational ' + str(e))
    if e in VARS:
        return ('var', VARS[e])
    if e == S:
        return ('atom', 'S')
    if e == D:
        return ('atom', 'D')
    if e.is_Add:
        terms = e.as_ordered_terms()
        acc = None
        for t in terms:
            co, rest = t.as_coeff_Mul()
            if co < 0:
                node = from_sympy(-t)
                acc = ('neg', node) if acc is None else ('sub', acc, node)
            else:
                node = from_sympy(t)
                acc = node if acc is None else ('add', acc, node)
        return acc
    if e.is_Mul:
        co, rest = e.as_coeff_Mul()
        if co < 0:
            return ('neg', from_sympy(-e))
        facs = sp.Mul.make_args(e)
        num = [f for f in facs if not (f.is_Pow and f.exp.is_negative)]
        den = [f.base ** (-f.exp) for f in facs if f.is_Pow and f.exp.is_negative]
        num = sorted(num, key=lambda f: (0 if f.is_Number else 1))

        def fold(fs):
            acc = None
            for f in fs:
                node = from_sympy(f)
                acc = node if acc is None else ('mul', acc, node)
            return acc if acc is not None else ('num', 1)
        if den:
            return ('div', fold(num), fold(den))
        return fold(num)
    if e.is_Pow:
        n = e.exp
        if n.is_Integer and n > 0:
            return ('pow', from_sympy(e.base), int(n))
        if n.is_Integer and n < 0:
            return ('div', ('num', 1), from_sympy(e.base ** (-n)))
        raise ValueError('pow ' + str(e))
    raise ValueError('unknown ' + str(e))


def atom_str(name, ctx):
    """ctx: dict with the Lean names of r and c (for the lambda variable)."""
    if name == 'S':
        return f"sig a {ctx['r']} {ctx['c']}"
    return f"del M a {ctx['r']}"


def pr(node, ctx=None, nat_exp=False):
    """Print with Lean precedence. Returns (string, prec)."""
    if ctx is None:
        ctx = {'r': 'r', 'c': 'c'}
    k = node[0]
    if k == 'num':
        return str(node[1]), 1024
    if k == 'var':
        return ctx.get(node[1], node[1]), 1024
    if k == 'atom':
        return atom_str(node[1], ctx), 1024
    if k in ('add', 'sub', 'mul', 'div'):
        op = {'add': '+', 'sub': '-', 'mul': '*', 'div': '/'}[k]
        p = PREC[k]
        ls, lp = pr(node[1], ctx, nat_exp)
        rs, rp = pr(node[2], ctx, nat_exp)
        if lp < p:
            ls = '(' + ls + ')'
        if rp <= p:
            rs = '(' + rs + ')'
        return f'{ls} {op} {rs}', p
    if k == 'neg':
        s, p = pr(node[1], ctx, nat_exp)
        if p < 1024:
            s = '(' + s + ')'
        return '-' + s, 75
    if k == 'pow':
        s, p = pr(node[1], ctx, nat_exp)
        if p < 1024:
            s = '(' + s + ')'
        e = f'({node[2]} : ℕ)' if nat_exp else str(node[2])
        return f'{s} ^ {e}', 75
    raise ValueError(k)


def lean(node, ctx=None, nat_exp=False):
    return pr(node, ctx, nat_exp)[0]


def dep(node, var):
    k = node[0]
    if k == 'num':
        return False
    if k == 'var':
        return node[1] == var
    if k == 'atom':
        return node[1] == 'S' or (node[1] == 'D' and var == 'r')
    if k in ('neg', 'pow'):
        return dep(node[1], var)
    return dep(node[1], var) or dep(node[2], var)


NE = {'S': 'hS', 'D': 'hD'}


def ne_proof(node):
    """A proof that the (denominator) node is nonzero."""
    k = node[0]
    if k == 'atom':
        return NE[node[1]]
    if k == 'mul':
        return f'(mul_ne_zero {ne_proof(node[1])} {ne_proof(node[2])})'
    if k == 'pow':
        return f'(pow_ne_zero {node[2]} {ne_proof(node[1])})'
    if k == 'sub' and node == ('sub', ('var', 'c'), ('num', 1)):
        return 'hc1'
    if k == 'add' and node == ('add', ('var', 'c'), ('num', 1)):
        return 'hc2'
    if k == 'sub' and node == ('sub', ('num', 1), ('pow', ('var', 'c'), 2)):
        return 'h1c'
    raise ValueError('ne ' + str(node))


def ne_hyps(node, acc=None):
    if acc is None:
        acc = set()
    k = node[0]
    if k == 'atom':
        acc.add(NE[node[1]])
    elif k in ('mul',):
        ne_hyps(node[1], acc)
        ne_hyps(node[2], acc)
    elif k == 'pow':
        ne_hyps(node[1], acc)
    else:
        acc.add(ne_proof(node))
    return acc


def deriv_term(node, var, hyps):
    """A HasDerivAt term for the node as a function of `var` at the point `var`.
    Collect the nonzero hypotheses used in `hyps`."""
    pt = var
    if not dep(node, var):
        return f'(hasDerivAt_const {pt} ({lean(node)} : ℝ))'
    k = node[0]
    if k == 'var':
        return f'(hasDerivAt_id\' {pt})'
    if k == 'atom':
        if node[1] == 'S':
            return f'(hasDerivAt_sig_{var} a r c)'
        return '(hasDerivAt_del_r M a r)'
    if k == 'neg':
        return f'{deriv_term(node[1], var, hyps)}.fun_neg'
    if k == 'pow':
        return f'({deriv_term(node[1], var, hyps)}.fun_pow {node[2]})'
    if k in ('add', 'sub'):
        f = 'fun_add' if k == 'add' else 'fun_sub'
        return f'({deriv_term(node[1], var, hyps)}.{f} {deriv_term(node[2], var, hyps)})'
    if k == 'mul':
        l, rr = node[1], node[2]
        if not dep(l, var):
            return f'(HasDerivAt.const_mul ({lean(l)} : ℝ) {deriv_term(rr, var, hyps)})'
        if not dep(rr, var):
            return f'(HasDerivAt.mul_const {deriv_term(l, var, hyps)} ({lean(rr)} : ℝ))'
        return f'({deriv_term(l, var, hyps)}.fun_mul {deriv_term(rr, var, hyps)})'
    if k == 'div':
        l, rr = node[1], node[2]
        if not dep(rr, var):
            ne_hyps(rr, hyps)
            return f'(HasDerivAt.div_const {deriv_term(l, var, hyps)} ({lean(rr)} : ℝ))'
        ne_hyps(rr, hyps)
        return (f'({deriv_term(l, var, hyps)}.fun_div {deriv_term(rr, var, hyps)} '
                f'{ne_proof(rr)})')
    raise ValueError(k)
