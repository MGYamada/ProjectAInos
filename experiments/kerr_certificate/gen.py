"""Generate the Christoffel table of the Kerr metric and its derivative lemmas."""
import sympy as sp
import pickle
import os
import sys
sys.path.insert(0, os.path.dirname(__file__))
from kast import r, c, M, a, S, D, from_sympy, lean, deriv_term, ne_hyps

HERE = os.path.dirname(os.path.abspath(__file__))
t, ph = sp.symbols('t phi', real=True)
X = [t, r, c, ph]
Sx = r**2 + a**2*c**2
Dx = r**2 - 2*M*r + a**2
s2 = 1 - c**2


def compute():
    g = sp.zeros(4)
    g[0, 0] = -(1 - 2*M*r/Sx)
    g[0, 3] = g[3, 0] = -2*M*a*r*s2/Sx
    g[1, 1] = Sx/Dx
    g[2, 2] = Sx/s2
    g[3, 3] = (r**2 + a**2 + 2*M*a**2*r*s2/Sx)*s2
    gi = sp.simplify(g.inv())
    G = [[[sp.factor(sp.cancel(sum(gi[k, l]*(sp.diff(g[j, l], X[i]) + sp.diff(g[l, i], X[j])
                                             - sp.diff(g[i, j], X[l])) for l in range(4))/2))
           for j in range(4)] for i in range(4)] for k in range(4)]
    return g, G


cache = os.path.join(HERE, 'G.pkl')
if os.path.exists(cache):
    g, G = pickle.load(open(cache, 'rb'))
else:
    g, G = compute()
    pickle.dump((g, G), open(cache, 'wb'))


def to_atoms(e):
    e = sp.factor(e)
    e2 = e.subs({a**2*c**2 + r**2: S, -2*M*r + a**2 + r**2: D})
    back = e2.subs({S: Sx, D: Dx})
    assert sp.simplify(back - e) == 0, e
    den = sp.fraction(e2)[1]
    for f in sp.Mul.make_args(den):
        b = f.base if f.is_Pow else f
        assert b in (S, D, c - 1, c + 1) or b.is_Number, (b, e2)
    return e2


nz = [(k, i, j) for k in range(4) for i in range(4) for j in range(i, 4) if G[k][i][j] != 0]


def name(k, i, j):
    i, j = min(i, j), max(i, j)
    return f'chris{k}_{i}{j}'


if __name__ == '__main__':
    out = {}
    for (k, i, j) in nz:
        e = to_atoms(G[k][i][j])
        node = from_sympy(e)
        dr = to_atoms(sp.diff(G[k][i][j], r))
        dc = to_atoms(sp.diff(G[k][i][j], c))
        out[(k, i, j)] = (e, node, dr, dc)
    pickle.dump(out, open(os.path.join(HERE, 'entries.pkl'), 'wb'))
    for key, (e, node, dr, dc) in out.items():
        print(name(*key), ':', lean(node))
