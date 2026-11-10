#!/usr/bin/env python3
"""Symbolic and numerical evidence for the mechanics research plan.

Run all 47 checks with ``python -m ainos_experiments.verify_identities``;
append group names such as ``E9 E11`` to run only those groups. Importing this
module performs no experiments. Each ``run_eN()`` returns independent results
without printing; no group's symbolic state is reused by another group.

Every tag is documented in docs/mechanics-experiments.md. These checks are
computational evidence, not Lean proofs. Dependencies are pinned in pyproject.toml.

Conventions: omega = sum dq^i ^ dp_i, i_{X_H} omega = dH,
{f,g} = sum (df/dq dg/dp - df/dp dg/dq) = X_g(f), f' = {f,H}.
Landau-Lifshitz use [f,g]_LL = -{f,g}.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import math
from typing import Callable, Sequence

import sympy as sp
from sympy import symbols, Function, diff, Matrix, sqrt, LeviCivita


@dataclass(frozen=True)
class CheckResult:
    tag: str
    ok: bool
    description: str
    details: tuple[str, ...] = ()


def is_zero(expr):
    if isinstance(expr, sp.MatrixBase):
        return all(sp.simplify(x) == 0 for x in expr)
    return sp.simplify(expr) == 0


def _collector():
    results = []

    def check(tag, description, expr):
        ok = bool(expr) if isinstance(expr, bool) else is_zero(expr)
        results.append(CheckResult(tag, ok, description))

    return results, check


def PB(f, g, qs, ps):
    """Canonical bracket {f,g} in the convention above."""
    return sum(diff(f, q) * diff(g, p) - diff(f, p) * diff(g, q) for q, p in zip(qs, ps))


def jet_commutator_residuals(total_derivative, function, qs, vs):
    """Both commutators for every supplied jet coordinate, in index order."""
    if len(qs) != len(vs):
        raise ValueError("position and velocity coordinates must have equal lengths")
    return Matrix([
        residual
        for q, v in zip(qs, vs)
        for residual in (
            diff(total_derivative(function), v) - total_derivative(diff(function, v)) - diff(function, q),
            diff(total_derivative(function), q) - total_derivative(diff(function, q)),
        )
    ])


def run_e1() -> list[CheckResult]:
    results, check = _collector()
    # E1  Conventions: Hamilton's equations and [X_f, X_g] = -X_{{f,g}}
    # ----------------------------------------------------------------------------
    q, p = symbols('q p', real=True)
    f = Function('f')(q, p)
    g = Function('g')(q, p)
    h = Function('h')(q, p)
    H = Function('H')(q, p)
    check('E1a', "q' = {q,H} = dH/dp and p' = {p,H} = -dH/dq",
          Matrix([PB(q, H, [q], [p]) - diff(H, p), PB(p, H, [q], [p]) + diff(H, q)]))


    def X(fn):  # Hamiltonian vector field X_fn acting on a function: X_fn(u) = {u, fn}
        return lambda u: PB(u, fn, [q], [p])


    check('E1b', "[X_f, X_g] = -X_{{f,g}} (acting on a generic h)",
          X(f)(X(g)(h)) - X(g)(X(f)(h)) + X(PB(f, g, [q], [p]))(h))
    check('E1c', "Jacobi identity for the canonical bracket (generic f,g,h; uses symmetry of 2nd derivatives)",
          PB(PB(f, g, [q], [p]), h, [q], [p]) + PB(PB(g, h, [q], [p]), f, [q], [p]) + PB(PB(h, f, [q], [p]), g, [q], [p]))

    return results


def run_e2() -> list[CheckResult]:
    results, check = _collector()
    # E2  Prop. (closedness <-> Jacobi): d omega(X_f,X_g,X_h) = -Jac(f,g,h)
    #     tested on a NON-closed nondegenerate 2-form on R^4.
    # ----------------------------------------------------------------------------
    x1, x2, x3, x4 = xs = symbols('x1:5', real=True)
    W = Matrix([[0, 1, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 1 + x1**2], [0, 0, -(1 + x1**2), 0]])
    Winv = W.inv()


    def grad(u):
        return Matrix([diff(u, x) for x in xs])


    def Xw(u):  # i_X omega = du  <=>  X = -W^{-1} grad u
        return -Winv * grad(u)


    def brw(u, v):  # {u,v} := omega(X_u, X_v)
        return sp.expand((Xw(u).T * W * Xw(v))[0, 0])


    def domega(Xv, Yv, Zv):
        tot = 0
        for i in range(4):
            for j in range(4):
                for k in range(4):
                    c = diff(W[j, k], xs[i]) + diff(W[k, i], xs[j]) + diff(W[i, j], xs[k])
                    if c != 0:
                        tot += c * Xv[i] * Yv[j] * Zv[k]
        return tot


    ff = x1 * x3 + x2**2 + x4
    gg = x1 * x4 + x3 + x2 * x3
    hh = x2 * x4 + x1**2 * x3 + x1
    check('E2a', "{f,g} = omega(X_f,X_g) = X_g(f) for a general nondegenerate omega",
          brw(ff, gg) - (grad(ff).T * Xw(gg))[0, 0])
    jac = brw(brw(ff, gg), hh) + brw(brw(gg, hh), ff) + brw(brw(hh, ff), gg)
    check('E2b', "d omega(X_f,X_g,X_h) = -({{f,g},h} + cyclic) with d omega != 0",
          domega(Xw(ff), Xw(gg), Xw(hh)) + jac)
    check('E2c', "sanity: the Jacobiator in E2b is not identically zero", bool(sp.simplify(jac) != 0))

    return results


def run_e3() -> list[CheckResult]:
    results, check = _collector()
    # E3  Cotangent bundle: {f,P_X} = X(f),  {P_X,P_Y} = -P_{[X,Y]}   (Q = R^2)
    # ----------------------------------------------------------------------------
    q1, q2, p1, p2 = symbols('q1 q2 p1 p2', real=True)
    Q2, P2 = [q1, q2], [p1, p2]
    Xc = [Function('X1')(q1, q2), Function('X2')(q1, q2)]
    Yc = [Function('Y1')(q1, q2), Function('Y2')(q1, q2)]
    fQ = Function('f')(q1, q2)
    PX = Xc[0] * p1 + Xc[1] * p2
    PY = Yc[0] * p1 + Yc[1] * p2
    brXY = [sum(Xc[j] * diff(Yc[i], Q2[j]) - Yc[j] * diff(Xc[i], Q2[j]) for j in range(2)) for i in range(2)]
    check('E3a', "{f, P_X} = X(f)", PB(fQ, PX, Q2, P2) - sum(Xc[i] * diff(fQ, Q2[i]) for i in range(2)))
    check('E3b', "{P_X, P_Y} = -P_{[X,Y]}", PB(PX, PY, Q2, P2) + brXY[0] * p1 + brXY[1] * p2)

    return results


def run_e4() -> list[CheckResult]:
    results, check = _collector()
    # E4  Angular momentum, Galilei boosts, virial
    # ----------------------------------------------------------------------------
    qx, qy, qz, px, py, pz, t, m = symbols('q_x q_y q_z p_x p_y p_z t m', real=True)
    QQ, PP = [qx, qy, qz], [px, py, pz]
    qv, pv = Matrix(QQ), Matrix(PP)
    Mv = qv.cross(pv)
    eps = lambda i, j, k: LeviCivita(i, j, k)
    check('E4a', "{M_i, M_j} = eps_ijk M_k  (L&L: [M_i,M_j] = -eps_ijk M_k)",
          Matrix(3, 3, lambda i, j: PB(Mv[i], Mv[j], QQ, PP) - sum(eps(i, j, k) * Mv[k] for k in range(3))))
    Kv = m * qv - t * pv
    H0 = (pv.dot(pv)) / (2 * m)
    check('E4b', "boost momenta K = m q - t p:  {K_i, P_j} = m delta_ij",
          Matrix(3, 3, lambda i, j: PB(Kv[i], PP[j], QQ, PP) - (m if i == j else 0)))
    check('E4c', "dK/dt + {K, H_0} = 0 for H_0 = |p|^2/2m (centre-of-mass integral)",
          Matrix([diff(Kv[i], t) + PB(Kv[i], H0, QQ, PP) for i in range(3)]))
    check('E4d', "{K_i, K_j} = 0", Matrix(3, 3, lambda i, j: PB(Kv[i], Kv[j], QQ, PP)))
    kk = symbols('k', real=True)
    for name, U in [('r^k', (qx**2 + qy**2 + qz**2)**(kk / 2)), ('x^2 y^(k-2)', qx**2 * qy**(kk - 2))]:
        Hk = pv.dot(pv) / (2 * m) + U
        check(f'E4e-{name.replace(" ", "")}', f"virial: {{q.p, H}} = 2T - kU for U = {name}",
              PB(qv.dot(pv), Hk, QQ, PP) - (pv.dot(pv) / m - kk * U))
    u1, u2, u3 = symbols('u1:4', real=True)
    uv = Matrix([u1, u2, u3])
    vv = Matrix(symbols('v1:4', real=True))
    check('E4f', "free particle: L(v+u) - L(v) = D_t(m q.u + m|u|^2 t/2) with q' = v",
          m * ((vv + uv).dot(vv + uv) - vv.dot(vv)) / 2 - (m * vv.dot(uv) + m * uv.dot(uv) / 2))

    return results


def run_e5() -> list[CheckResult]:
    results, check = _collector()
    qx, qy, qz, px, py, pz, m, al = symbols('q_x q_y q_z p_x p_y p_z m alpha', real=True)
    QQ, PP = [qx, qy, qz], [px, py, pz]
    qv, pv = Matrix(QQ), Matrix(PP)
    Mv = qv.cross(pv)
    eps = lambda i, j, k: LeviCivita(i, j, k)
    # E5  Kepler problem: Laplace-Runge-Lenz vector (r adjoined with r^2 = q.q)
    # ----------------------------------------------------------------------------
    r = sqrt(qv.dot(qv))
    HK = pv.dot(pv) / (2 * m) - al / r
    Av = pv.cross(Mv) - m * al * qv / r
    check('E5a', "{A_i, H} = 0 for H = |p|^2/2m - alpha/r, A = p x M - m alpha q/r",
          Matrix([PB(Av[i], HK, QQ, PP) for i in range(3)]))
    check('E5b', "{M_i, A_j} = eps_ijk A_k",
          Matrix(3, 3, lambda i, j: PB(Mv[i], Av[j], QQ, PP) - sum(eps(i, j, k) * Av[k] for k in range(3))))
    check('E5c', "{A_i, A_j} = -2 m H eps_ijk M_k",
          Matrix(3, 3, lambda i, j: PB(Av[i], Av[j], QQ, PP) + 2 * m * HK * sum(eps(i, j, k) * Mv[k] for k in range(3))))
    check('E5d', "A . M = 0", Av.dot(Mv))
    check('E5e', "|A|^2 = m^2 alpha^2 + 2 m H |M|^2", Av.dot(Av) - (m**2 * al**2 + 2 * m * HK * Mv.dot(Mv)))
    check('E5f', "orbit equation: A . q = |M|^2 - m alpha r", Av.dot(qv) - (Mv.dot(Mv) - m * al * r))
    # Rutherford: e^2 = 1 + 2 E M^2/(m alpha^2), E = m v^2/2, M = m rho v, sin(chi/2) = 1/e
    vinf, rho = symbols('v_inf rho', positive=True)
    e2 = 1 + 2 * (m * vinf**2 / 2) * (m * rho * vinf)**2 / (m * al**2)
    check('E5g', "Rutherford: cot^2(chi/2) = e^2 - 1 = (m v^2 rho/alpha)^2", (e2 - 1) - (m * vinf**2 * rho / al)**2)

    return results


def run_e6() -> list[CheckResult]:
    results, check = _collector()
    # E6  Rigid body: Lie-Poisson bracket {L_i,L_j} = -eps_ijk L_k on R^3
    # ----------------------------------------------------------------------------
    L1, L2, L3, I1, I2, I3 = symbols('L1 L2 L3 I1 I2 I3', positive=True)
    Ls, Is = [L1, L2, L3], [I1, I2, I3]


    def LP(u, v):  # {u,v} = -L . (grad u x grad v)
        gu = Matrix([diff(u, a) for a in Ls])
        gv = Matrix([diff(v, a) for a in Ls])
        return -Matrix(Ls).dot(gu.cross(gv))


    HR = sum(Ls[i]**2 / (2 * Is[i]) for i in range(3))
    check('E6a', "generators: {L_1,L_2} = -L_3 (and cyclic)",
          Matrix([LP(L1, L2) + L3, LP(L2, L3) + L1, LP(L3, L1) + L2]))
    check('E6b', "Euler equations: L_1' = {L_1,H} = (1/I_3 - 1/I_2) L_2 L_3 (and cyclic)",
          Matrix([LP(L1, HR) - (1 / I3 - 1 / I2) * L2 * L3,
                  LP(L2, HR) - (1 / I1 - 1 / I3) * L3 * L1,
                  LP(L3, HR) - (1 / I2 - 1 / I1) * L1 * L2]))
    check('E6c', "|L|^2 is a Casimir", Matrix([LP(sum(a**2 for a in Ls), b) for b in Ls]))
    FF, GG, HH = [Function(n)(L1, L2, L3) for n in 'FGH']
    check('E6d', "Jacobi identity for the Lie-Poisson bracket (generic F,G,H)",
          LP(LP(FF, GG), HH) + LP(LP(GG, HH), FF) + LP(LP(HH, FF), GG))
    # linearised stability about the principal axes: L_i' = c_i L_j L_k
    c1, c2, c3 = (1 / I3 - 1 / I2), (1 / I1 - 1 / I3), (1 / I2 - 1 / I1)
    vals = {I1: 1, I2: 2, I3: 3}
    check('E6e', "for I_1<I_2<I_3: rotation about axis 2 unstable (c_1 c_3 > 0), about axes 1 and 3 stable",
          bool((c1 * c3).subs(vals) > 0 and (c2 * c3).subs(vals) < 0 and (c1 * c2).subs(vals) < 0))

    # heavy top: bracket on R^3_L x R^3_Gamma (minus Lie-Poisson of e(3))
    G1, G2, G3, mug = symbols('Gamma1 Gamma2 Gamma3 mu_g', real=True)
    c1x, c2x, c3x = symbols('chi1 chi2 chi3', real=True)
    Gs = [G1, G2, G3]


    def HT(u, v):
        guL = Matrix([diff(u, a) for a in Ls]); gvL = Matrix([diff(v, a) for a in Ls])
        guG = Matrix([diff(u, a) for a in Gs]); gvG = Matrix([diff(v, a) for a in Gs])
        return -Matrix(Ls).dot(guL.cross(gvL)) - Matrix(Gs).dot(guL.cross(gvG) + guG.cross(gvL))


    Hht = HR + mug * (G1 * c1x + G2 * c2x + G3 * c3x)
    Lm, Gm, Omm, chim = Matrix(Ls), Matrix(Gs), Matrix([Ls[i] / Is[i] for i in range(3)]), Matrix([c1x, c2x, c3x])
    ok_gen = all(sp.simplify(HT(Ls[i], Gs[j]) + sum(LeviCivita(i, j, k) * Gs[k] for k in range(3))) == 0
                 for i in range(3) for j in range(3))
    eom = Matrix([HT(Ls[i], Hht) for i in range(3)]) - (Lm.cross(Omm) + mug * Gm.cross(chim))
    eom2 = Matrix([HT(Gs[i], Hht) for i in range(3)]) - Gm.cross(Omm)
    cas = Matrix([HT(Gm.dot(Gm), w) for w in Ls + Gs] + [HT(Lm.dot(Gm), w) for w in Ls + Gs])
    t1 = L1 * G2 + L3**2 + G1 * G3
    t2 = L2 * G1 + G2**2 * L1 + L3
    t3 = L1 * L2 + G3 * L3 + G1
    jac_ht = HT(HT(t1, t2), t3) + HT(HT(t2, t3), t1) + HT(HT(t3, t1), t2)
    check('E6f', "heavy top: {L_i,Gamma_j} = -eps_ijk Gamma_k; L' = L x Omega + mu g Gamma x chi; Gamma' = Gamma x Omega; "
                 "Casimirs |Gamma|^2, L.Gamma; Jacobi on polynomial test functions",
          bool(ok_gen and is_zero(eom) and is_zero(eom2) and is_zero(cas) and is_zero(sp.expand(jac_ht))))

    return results


def run_e7() -> list[CheckResult]:
    results, check = _collector()
    qx, qy, qz, px, py, pz = symbols('q_x q_y q_z p_x p_y p_z', real=True)
    QQ, PP = [qx, qy, qz], [px, py, pz]
    qv, pv = Matrix(QQ), Matrix(PP)
    Mv = qv.cross(pv)
    q, p = symbols('q p', real=True)
    f = Function('f')(q, p)
    # E7  Singular reduction examples
    # ----------------------------------------------------------------------------
    s1, s2, s3 = qv.dot(qv), pv.dot(pv), qv.dot(pv)
    check('E7a', "sl(2,R) relations: {s1,s2}=4 s3, {s1,s3}=2 s1, {s2,s3}=-2 s2",
          Matrix([PB(s1, s2, QQ, PP) - 4 * s3, PB(s1, s3, QQ, PP) - 2 * s1, PB(s2, s3, QQ, PP) + 2 * s2]))
    check('E7b', "|q x p|^2 = s1 s2 - s3^2", Mv.dot(Mv) - (s1 * s2 - s3**2))
    check('E7c', "s1 s2 - s3^2 Poisson-commutes with s1, s2, s3",
          Matrix([PB(s1 * s2 - s3**2, s, QQ, PP) for s in (s1, s2, s3)]))
    b = Function('b')(q)
    c = Function('c')(q)
    check('E7d', "{p b, p c} = p (b' c - b c')", PB(p * b, p * c, [q], [p]) - p * (diff(b, q) * c - b * diff(c, q)))
    check('E7e', "{f, p^2} = 2 p df/dq", PB(f, p**2, [q], [p]) - 2 * p * diff(f, q))

    return results


def run_e8() -> list[CheckResult]:
    results, check = _collector()
    q1, q2, p1, p2 = symbols('q1 q2 p1 p2', real=True)
    Q2, P2 = [q1, q2], [p1, p2]
    # E8  Dirac bracket for the second-class pair phi1 = |q|^2 - 1, phi2 = q.p  (R^4)
    # ----------------------------------------------------------------------------
    phi = [q1**2 + q2**2 - 1, q1 * p1 + q2 * p2]
    C = Matrix(2, 2, lambda a, bb: PB(phi[a], phi[bb], Q2, P2))
    Cinv = C.inv()
    F4 = Function('F')(q1, q2, p1, p2)


    def dirac(u, v):
        return PB(u, v, Q2, P2) - sum(PB(u, phi[a], Q2, P2) * Cinv[a, bb] * PB(phi[bb], v, Q2, P2)
                                        for a in range(2) for bb in range(2))


    check('E8a', "Dirac bracket: {F, phi_a}_D = 0 for generic F (constraint to the circle)",
          Matrix([dirac(F4, phi[0]), dirac(F4, phi[1])]))

    d1 = q1 * p2 + q2**2
    d2 = p1**2 + q1 * q2
    d3 = q2 * p1 + p2
    check('E8b', "Dirac bracket satisfies the Jacobi identity (polynomial test functions, where C is invertible)",
          dirac(dirac(d1, d2), d3) + dirac(dirac(d2, d3), d1) + dirac(dirac(d3, d1), d2))

    return results


def run_e9() -> list[CheckResult]:
    results, check = _collector()
    # E9  Jet identities (n = 2 degrees of freedom): Euler operator, energy, Noether
    # ----------------------------------------------------------------------------
    tt = symbols('t', real=True)
    Q = symbols('q1 q2', real=True)
    V = symbols('v1 v2', real=True)
    A = symbols('a1 a2', real=True)
    J = symbols('j1 j2', real=True)
    K4 = symbols('k1 k2', real=True)


    def D(u):  # total time derivative on jets of order <= 3
        return (diff(u, tt) + sum(V[i] * diff(u, Q[i]) + A[i] * diff(u, V[i]) + J[i] * diff(u, A[i])
                                  + K4[i] * diff(u, J[i]) for i in range(2)))


    def Euler(u, i):  # E_i = d/dq - D d/dv + D^2 d/da   (order <= 2)
        return diff(u, Q[i]) - D(diff(u, V[i])) + D(D(diff(u, A[i])))


    Lg = Function('L')(tt, *Q, *V)
    F0 = Function('F')(tt, *Q)
    F1 = Function('G')(tt, *Q, *V)
    xi = [Function('xi1')(tt, *Q), Function('xi2')(tt, *Q)]
    check('E9a', "E_i(D_t F) = 0 for F = F(t,q)", Matrix([Euler(D(F0), i) for i in range(2)]))
    check('E9b', "E_i(D_t G) = 0 for G = G(t,q,v) (second-order Euler operator)",
          Matrix([Euler(D(F1), i) for i in range(2)]))
    EL = [diff(Lg, Q[i]) - D(diff(Lg, V[i])) for i in range(2)]
    En = sum(V[i] * diff(Lg, V[i]) for i in range(2)) - Lg
    check('E9c', "energy identity: D_t(E_L) = -v^i E_i(L) - dL/dt",
          D(En) + sum(V[i] * EL[i] for i in range(2)) + diff(Lg, tt))
    prxi = sum(xi[i] * diff(Lg, Q[i]) + D(xi[i]) * diff(Lg, V[i]) for i in range(2))
    check('E9d', "Noether identity: pr(xi)(L) = xi^i E_i(L) + D_t(xi^i dL/dv^i)",
          prxi - sum(xi[i] * EL[i] for i in range(2)) - D(sum(xi[i] * diff(Lg, V[i]) for i in range(2))))
    check('E9e', "[d/dv^i, D_t] = d/dq^i and [d/dq^i, D_t] = 0 on jets",
          jet_commutator_residuals(D, F1, Q, V))

    return results


def run_e10() -> list[CheckResult]:
    results, check = _collector()
    qx, qy, qz, px, py, pz, m = symbols('q_x q_y q_z p_x p_y p_z m', real=True)
    QQ, PP = [qx, qy, qz], [px, py, pz]
    qv, pv = Matrix(QQ), Matrix(PP)
    Mv = qv.cross(pv)
    q, p = symbols('q p', real=True)
    f = Function('f')(q, p)
    g = Function('g')(q, p)
    H = Function('H')(q, p)
    # E10  Elementary canonical changes of variables
    # ----------------------------------------------------------------------------
    x, y, pxx, pyy = symbols('x y p_x p_y', real=True)
    XY, PXY = [x, y], [pxx, pyy]
    rr = sqrt(x**2 + y**2)
    ph = sp.atan2(y, x)
    pr = (x * pxx + y * pyy) / rr
    pph = x * pyy - y * pxx
    check('E10a', "polar coordinates are canonical: {r,p_r}=1, {phi,p_phi}=1, others 0",
          Matrix([PB(rr, pr, XY, PXY) - 1, PB(ph, pph, XY, PXY) - 1, PB(rr, pph, XY, PXY),
                  PB(ph, pr, XY, PXY), PB(rr, ph, XY, PXY), PB(pr, pph, XY, PXY)]))
    check('E10b', "|p|^2 = p_r^2 + p_phi^2/r^2", pxx**2 + pyy**2 - (pr**2 + pph**2 / rr**2))
    m1, m2 = symbols('m1 m2', positive=True)
    w1, w2 = symbols('w1 w2', real=True)
    mu = m1 * m2 / (m1 + m2)
    Vc = (m1 * w1 + m2 * w2) / (m1 + m2)
    check('E10c', "two-body: m1 w1^2/2 + m2 w2^2/2 = (m1+m2) V^2/2 + mu (w1-w2)^2/2",
          m1 * w1**2 / 2 + m2 * w2**2 / 2 - ((m1 + m2) * Vc**2 / 2 + mu * (w1 - w2)**2 / 2))
    # rotating frame: H = |p|^2/2m - Omega.(q x p) + U
    O1, O2, O3 = symbols('Omega1:4', real=True)
    Om = Matrix([O1, O2, O3])
    Uf = Function('U')(qx, qy, qz)
    Hrot = pv.dot(pv) / (2 * m) - Om.dot(Mv) + Uf
    qdot = Matrix([PB(a, Hrot, QQ, PP) for a in QQ])
    pdot = Matrix([PB(a, Hrot, QQ, PP) for a in PP])
    check('E10d', "rotating frame: q' = p/m - Omega x q", qdot - (pv / m - Om.cross(qv)))
    vel = qdot
    # m v' = p' - m Omega x v  (from p = m(v + Omega x q), Omega constant)
    acc_force = pdot - m * Om.cross(vel)
    gradU = Matrix([diff(Uf, a) for a in QQ])
    check('E10e', "rotating frame: m v' = -grad U + 2 m v x Omega + m Omega x (q x Omega)",
          acc_force - (-gradU + 2 * m * vel.cross(Om) + m * Om.cross(qv.cross(Om))))
    # Maupertuis reparametrisation: {g, f (H - E)} = f {g, H}  mod (H - E)
    ee = symbols('E', real=True)
    check('E10f', "Maupertuis: {g, f (H-E)} - f {g,H} = (H-E) {g,f}",
          PB(g, f * (H - ee), [q], [p]) - f * PB(g, H, [q], [p]) - (H - ee) * PB(g, f, [q], [p]))

    return results


class PeriodSearchError(RuntimeError):
    """A bounded integration failed to resolve a trustworthy oscillation."""


@dataclass(frozen=True)
class TurningPoint:
    time: float
    position: float
    direction: int  # +1: negative-to-positive velocity; -1: positive-to-negative


@dataclass(frozen=True)
class PeriodEstimate:
    period: float
    crossings: tuple[TurningPoint, TurningPoint]
    steps: int
    max_relative_energy_drift: float


def estimate_period(a_: float, b_: float, amp: float, dt: float = 2.0e-4, *,
                    max_time: float = 20.0, max_steps: int = 200_000,
                    energy_tolerance: float = 1.0e-6) -> PeriodEstimate:
    """Integrate x'' = -x-a*x^2-b*x^3 from the positive turning point (amp, 0).

    Fixed-step RK4 must find a negative-position minimum (+ velocity crossing)
    followed by a positive-position maximum (- crossing). The second crossing
    measures one period from the initial maximum. Crossing times and positions
    use linear interpolation in velocity across their bracketing step, including
    an exact zero at the right endpoint once. Both time and step budgets apply.

    Invalid inputs raise ValueError. Nonfinite evolution, excessive relative
    drift in E=v^2/2+x^2/2+a*x^3/3+b*x^4/4, unexpected turning points, or budget
    exhaustion raise PeriodSearchError. This estimates oscillations about zero;
    it does not assign a period to stationary or escaping trajectories.
    """
    values = (a_, b_, amp, dt, max_time, energy_tolerance)
    if not all(math.isfinite(value) for value in values):
        raise ValueError("period parameters must be finite")
    if amp <= 0 or dt <= 0 or max_time <= 0 or energy_tolerance <= 0:
        raise ValueError("amplitude, dt, max_time, and energy_tolerance must be positive")
    if isinstance(max_steps, bool) or not isinstance(max_steps, int) or max_steps <= 0:
        raise ValueError("max_steps must be a positive integer")

    def acc(x):
        return -x - a_ * x * x - b_ * x**3

    def energy(x, v):
        return v * v / 2 + x * x / 2 + a_ * x**3 / 3 + b_ * x**4 / 4

    try:
        initial_acc = acc(amp)
        initial_energy = energy(amp, 0.0)
    except OverflowError as exc:
        raise ValueError("initial acceleration or energy is not finite") from exc
    if not math.isfinite(initial_acc) or not math.isfinite(initial_energy):
        raise ValueError("initial acceleration or energy is not finite")
    if initial_acc >= 0:
        raise ValueError("initial turning point must accelerate toward zero; stationary/outward data supplied")
    energy_scale = max(abs(initial_energy), amp * amp / 2)
    if energy_scale == 0:
        raise ValueError("amplitude is too small to resolve its energy")

    x, v = amp, 0.0
    crossings = []
    max_drift = 0.0
    for step in range(max_steps):
        time = step * dt
        if (step + 1) * dt > max_time:
            break
        try:
            k1x, k1v = v, acc(x)
            k2x, k2v = v + 0.5 * dt * k1v, acc(x + 0.5 * dt * k1x)
            k3x, k3v = v + 0.5 * dt * k2v, acc(x + 0.5 * dt * k2x)
            k4x, k4v = v + dt * k3v, acc(x + dt * k3x)
            xn = x + dt * (k1x + 2 * k2x + 2 * k3x + k4x) / 6
            vn = v + dt * (k1v + 2 * k2v + 2 * k3v + k4v) / 6
            current_energy = energy(xn, vn)
        except OverflowError as exc:
            raise PeriodSearchError(f"nonfinite evolution near t={time:.6g}") from exc
        if not all(math.isfinite(value) for value in
                   (k1x, k1v, k2x, k2v, k3x, k3v, k4x, k4v, xn, vn, current_energy)):
            raise PeriodSearchError(f"nonfinite evolution near t={time:.6g}")
        drift = abs(current_energy - initial_energy) / energy_scale
        max_drift = max(max_drift, drift)
        if drift > energy_tolerance:
            raise PeriodSearchError(
                f"relative energy drift {drift:.3g} exceeds {energy_tolerance:.3g} near t={time + dt:.6g}")

        direction = 1 if v < 0 <= vn else -1 if v > 0 >= vn else 0
        if direction:
            fraction = v / (v - vn)
            crossing = TurningPoint(time + dt * fraction, x + (xn - x) * fraction, direction)
            expected = 1 if not crossings else -1
            position_ok = crossing.position < 0 if direction == 1 else crossing.position > 0
            if (direction != expected or not position_ok or not 0 < fraction <= 1
                    or crossing.time <= (crossings[-1].time if crossings else 0)):
                raise PeriodSearchError(f"unexpected or repeated velocity crossing near t={time:.6g}")
            crossings.append(crossing)
            if len(crossings) == 2:
                return PeriodEstimate(crossing.time, (crossings[0], crossings[1]), step + 1, max_drift)
        x, v = xn, vn
    raise PeriodSearchError(
        f"period search exhausted max_time={max_time:g} or max_steps={max_steps}; "
        f"found {len(crossings)}/2 directed velocity crossings")


def period(a_: float, b_: float, amp: float, dt: float = 2.0e-4, **limits) -> float:
    """Return the validated period; see estimate_period for limits and diagnostics."""
    return estimate_period(a_, b_, amp, dt, **limits).period


def run_e11() -> list[CheckResult]:
    """Anharmonic frequency shift, with RK4 energy control and amplitude extrapolation."""
    ok_all = True
    details = []
    for a_, b_ in [(1.0, 1.0), (0.7, -0.4), (0.0, 1.0)]:
        kappa = 3 * b_ / 8 - 5 * a_**2 / 12
        estimates = []
        try:
            for amp in (0.04, 0.02, 0.01):
                omega = 2 * math.pi / period(a_, b_, amp)
                estimates.append((omega - 1) / amp**2)
        except (ValueError, PeriodSearchError) as exc:
            ok_all = False
            details.append(f"      a={a_}, b={b_}: integration failed: {exc}")
            continue
        # The error is O(amp): Richardson-extrapolate the last two amplitudes.
        extrapolated = 2 * estimates[2] - estimates[1]
        ok_all = ok_all and abs(extrapolated - kappa) < 2e-4
        details.append(
            f"      a={a_}, b={b_}: (omega-1)/A^2 at A=0.04,0.02,0.01 = "
            f"{estimates[0]:+.5f}, {estimates[1]:+.5f}, {estimates[2]:+.5f}; "
            f"extrapolated {extrapolated:+.5f}; predicted {kappa:+.5f}")
    return [CheckResult('E11', ok_all,
                        "anharmonic frequency shift (3 beta/8 - 5 alpha^2/12) A^2 for omega_0 = 1 (numerical)",
                        tuple(details))]


GROUPS: dict[str, Callable[[], list[CheckResult]]] = {
    'E1': run_e1, 'E2': run_e2, 'E3': run_e3, 'E4': run_e4, 'E5': run_e5,
    'E6': run_e6, 'E7': run_e7, 'E8': run_e8, 'E9': run_e9, 'E10': run_e10, 'E11': run_e11,
}


def run_groups(groups: Sequence[str] | None = None) -> list[CheckResult]:
    """Evaluate the requested groups in order, silently and without shared results."""
    names = list(GROUPS) if groups is None else list(groups)
    if len(names) != len(set(names)):
        raise ValueError("each experiment group may be requested only once")
    unknown = set(names) - GROUPS.keys()
    if unknown:
        raise ValueError(f"unknown experiment groups: {', '.join(sorted(unknown))}")
    results = [result for name in names for result in GROUPS[name]()]
    if len({result.tag for result in results}) != len(results):
        raise ValueError("experiment result tags must be unique")
    return results


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('groups', nargs='*', metavar='GROUP',
                        help='optional group names: ' + ', '.join(GROUPS))
    args = parser.parse_args(argv)
    try:
        results = run_groups(args.groups or None)
    except ValueError as exc:
        parser.error(str(exc))
    for result in results:
        for line in result.details:
            print(line)
        print(f"[{'PASS' if result.ok else 'FAIL'}] {result.tag}: {result.description}")
    n_ok = sum(result.ok for result in results)
    print(f"\n{n_ok}/{len(results)} checks passed")
    return 0 if n_ok == len(results) else 1


if __name__ == '__main__':
    raise SystemExit(main())
