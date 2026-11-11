"""Exact checks for GR 5.1's metric, connection and curvature examples.

Time first, c=1, signature (-+). The coordinate change is (T,X)=(t,x+t²).
All computations are symbolic over the reals; no tolerances or random seeds
are needed. Formal claims are established separately in Lean.
"""

import sympy as sp


def check_zero(name, expression):
    entries = (list(expression) if isinstance(expression, (sp.MatrixBase, list, tuple))
               else [expression])
    if any(sp.simplify(entry) != 0 for entry in entries):
        raise AssertionError(f"{name}: exact residual is nonzero: {expression}")


def christoffel(metric, coordinates):
    """Return Gamma^k_ij as one symmetric matrix per upper index k."""
    inverse = metric.inv()
    size = len(coordinates)
    return [sp.Matrix(size, size, lambda i, j: sp.simplify(sum(
        inverse[k, ell] * (
            sp.diff(metric[ell, j], coordinates[i])
            + sp.diff(metric[ell, i], coordinates[j])
            - sp.diff(metric[i, j], coordinates[ell])) / 2
        for ell in range(size)))) for k in range(size)]


def verify_connection(metric, coordinates):
    gamma = christoffel(metric, coordinates)
    opposite = christoffel(-metric, coordinates)
    size = len(coordinates)
    for k in range(size):
        check_zero("torsion-free", gamma[k] - gamma[k].T)
        check_zero("connection metric-sign reversal", gamma[k] - opposite[k])
        for i in range(size):
            for j in range(size):
                check_zero("metric compatibility", sp.diff(metric[i, j], coordinates[k])
                           - sum(gamma[ell][k, i] * metric[ell, j]
                                 + gamma[ell][k, j] * metric[i, ell]
                                 for ell in range(size)))
    return gamma


def curvature(gamma, coordinates):
    """Return R^a_bcd, with R(e_b,e_c)e_d as the vector being expanded."""
    size = len(coordinates)
    riemann = sp.MutableDenseNDimArray.zeros(size, size, size, size)
    for a in range(size):
        for b in range(size):
            for c in range(size):
                for d in range(size):
                    riemann[a, b, c, d] = sp.simplify(
                        sp.diff(gamma[a][c, d], coordinates[b])
                        - sp.diff(gamma[a][b, d], coordinates[c])
                        + sum(gamma[a][b, k] * gamma[k][c, d]
                              - gamma[a][c, k] * gamma[k][b, d]
                              for k in range(size)))
    return riemann


def verify_curvature(metric, coordinates, gamma):
    riemann = curvature(gamma, coordinates)
    size = len(coordinates)

    def lowered(b, c, d, e):
        return sum(metric[e, a] * riemann[a, b, c, d] for a in range(size))

    for a in range(size):
        for b in range(size):
            for c in range(size):
                for d in range(size):
                    check_zero("first-pair antisymmetry",
                               riemann[a, b, c, d] + riemann[a, c, b, d])
                    check_zero("algebraic first Bianchi",
                               riemann[a, b, c, d] + riemann[a, c, d, b]
                               + riemann[a, d, b, c])
                    check_zero("last-pair antisymmetry", lowered(a, b, c, d)
                               + lowered(a, b, d, c))
                    check_zero("pair interchange", lowered(a, b, c, d)
                               - lowered(c, d, a, b))
    # Ric(u,v) = tr(w -> R(w,u)v), matching the Lean contraction order.
    ricci = sp.Matrix(size, size, lambda b, c: sp.simplify(sum(
        riemann[a, a, b, c] for a in range(size))))
    check_zero("Ricci symmetry", ricci - ricci.T)
    scalar = sp.simplify(sp.trace(metric.inv() * ricci))
    return riemann, ricci, scalar


def verify():
    t, x, time, space = sp.symbols("t x T X", real=True)
    coordinates = sp.Matrix([t, x])
    inertial = sp.Matrix([time, space])
    shear = sp.Matrix([t, x + t**2])
    unshear = sp.Matrix([time, space - time**2])
    check_zero("inverse after shear", unshear.subs(
        dict(zip(inertial, shear)), simultaneous=True) - coordinates)
    check_zero("shear after inverse", shear.subs(
        dict(zip(coordinates, unshear)), simultaneous=True) - inertial)

    jacobian = shear.jacobian(coordinates)
    inverse_jacobian = unshear.jacobian(inertial).subs(
        dict(zip(inertial, shear)), simultaneous=True)
    check_zero("inverse Jacobian", inverse_jacobian * jacobian - sp.eye(2))
    eta = sp.diag(-1, 1)
    metric = jacobian.T * eta * jacobian
    check_zero("metric coefficients", metric - sp.Matrix([
        [-1 + 4*t**2, 2*t], [2*t, 1]]))
    check_zero("determinant", metric.det() + 1)
    check_zero("inertial coefficients", inverse_jacobian.T * metric * inverse_jacobian - eta)

    v = sp.Matrix(sp.symbols("v_t v_x", real=True))
    w = sp.Matrix(sp.symbols("w_t w_x", real=True))
    alpha = sp.Matrix(sp.symbols("alpha_t alpha_x", real=True))
    inverse_metric = metric.inv()
    check_zero("raise after lower", inverse_metric * metric * v - v)
    check_zero("lower after raise", metric * inverse_metric * alpha - alpha)
    check_zero("metric covariance", (v.T * metric * w)[0]
               - ((jacobian*v).T * eta * (jacobian*w))[0])
    check_zero("covector pairing", (inverse_metric * alpha).T * metric * v - alpha.T * v)
    check_zero("inverse metric covariance", inverse_metric
               - inverse_jacobian * eta.inv() * inverse_jacobian.T)
    check_zero("opposite metric", jacobian.T * (-eta) * jacobian + metric)
    check_zero("opposite sharp", (-metric).inv() + inverse_metric)

    # An arbitrary two-tensor, without assuming symmetry, tests all slots.
    tensor = sp.Matrix(2, 2, sp.symbols("B_tt B_tx B_xt B_xx", real=True))
    pulled_tensor = jacobian.T * tensor * jacobian
    check_zero("metric contraction covariance", sp.trace(inverse_metric * pulled_tensor)
               - sp.trace(eta.inv() * tensor))
    spatial_tensor = jacobian.T * sp.diag(0, 1) * jacobian
    check_zero("nonconstant spatial tensor", spatial_tensor
               - sp.Matrix([[4*t**2, 2*t], [2*t, 1]]))
    check_zero("spatial tensor contraction", sp.trace(inverse_metric * spatial_tensor) - 1)
    check_zero("metric self contraction", sp.trace(inverse_metric * metric) - 2)

    # T^i_jk transforms in all three indices; contracting i with k leaves j.
    mixed = sp.MutableDenseNDimArray(sp.symbols("R:8", real=True), (2, 2, 2))
    transformed = sp.MutableDenseNDimArray.zeros(2, 2, 2)
    for i in range(2):
        for j in range(2):
            for k in range(2):
                transformed[i, j, k] = sum(
                    jacobian[i, a] * inverse_jacobian[b, j] * inverse_jacobian[c, k]
                    * mixed[a, b, c]
                    for a in range(2) for b in range(2) for c in range(2))
    contracted = sp.Matrix([sum(mixed[i, j, i] for i in range(2)) for j in range(2)])
    transformed_contraction = sp.Matrix([
        sum(transformed[i, j, i] for i in range(2)) for j in range(2)])
    check_zero("partial tensor contraction covariance",
               transformed_contraction - inverse_jacobian.T * contracted)

    # The nonlinear Christoffel term is the second derivative of the chart.
    flat_gamma = verify_connection(eta, inertial)
    for component in flat_gamma:
        check_zero("inertial connection", component)
    gamma = verify_connection(metric, coordinates)
    check_zero("nonlinear time connection", gamma[0])
    check_zero("nonlinear spatial connection", gamma[1] - sp.Matrix([[2, 0], [0, 0]]))
    for k in range(2):
        transformed_gamma = sum((
            inverse_jacobian[k, a] * sp.hessian(shear[a], coordinates)
            for a in range(2)), sp.zeros(2))
        check_zero("connection Hessian transformation", gamma[k] - transformed_gamma)

    curved_metric = sp.exp(2*x**2) * eta
    curved_gamma = verify_connection(curved_metric, coordinates)
    check_zero("conformal time connection", curved_gamma[0] - sp.Matrix([[0, 2*x], [2*x, 0]]))
    check_zero("conformal spatial connection", curved_gamma[1] - sp.diag(2*x, 2*x))

    for name, flat_metric, flat_coords, coefficients in [
            ("standard Minkowski", eta, inertial, flat_gamma),
            ("nonlinear Minkowski", metric, coordinates, gamma)]:
        riemann, ricci, scalar = verify_curvature(flat_metric, flat_coords, coefficients)
        check_zero(name + " Riemann", list(sp.flatten(riemann.tolist())))
        check_zero(name + " Ricci", ricci)
        check_zero(name + " scalar curvature", scalar)

    riemann, ricci, scalar = verify_curvature(curved_metric, coordinates, curved_gamma)
    check_zero("conformal Ricci", ricci - sp.diag(2, -2))
    check_zero("conformal scalar curvature", scalar + 4*sp.exp(-2*x**2))
    for component in curved_gamma:
        check_zero("connection vanishes at origin", component.subs({t: 0, x: 0}))
    check_zero("curvature at origin is nonzero", scalar.subs({t: 0, x: 0}) + 4)
    opposite_riemann, opposite_ricci, opposite_scalar = verify_curvature(
        -curved_metric, coordinates, christoffel(-curved_metric, coordinates))
    check_zero("curvature metric-sign reversal", list(sp.flatten(
        (opposite_riemann - riemann).tolist())))
    check_zero("Ricci metric-sign reversal", opposite_ricci - ricci)
    check_zero("scalar curvature metric-sign reversal", opposite_scalar + scalar)

    # Check a nonzero curvature tensor in both nonlinear charts as well.
    substitution = {t: shear[0], x: shear[1]}
    pulled_metric = sp.exp(2*shear[1]**2) * metric
    pulled_riemann, pulled_ricci, pulled_scalar = verify_curvature(
        pulled_metric, coordinates, christoffel(pulled_metric, coordinates))
    for a in range(2):
        for b in range(2):
            for c in range(2):
                for d in range(2):
                    expected = sum(
                        inverse_jacobian[a, k] * jacobian[ell, b] * jacobian[m, c]
                        * jacobian[n, d] * riemann[k, ell, m, n].subs(
                            substitution, simultaneous=True)
                        for k in range(2) for ell in range(2)
                        for m in range(2) for n in range(2))
                    check_zero("nonzero curvature coordinate covariance",
                               pulled_riemann[a, b, c, d] - expected)
    check_zero("Ricci coordinate covariance", pulled_ricci
               - jacobian.T * ricci.subs(substitution, simultaneous=True) * jacobian)
    check_zero("scalar curvature coordinate covariance",
               pulled_scalar - scalar.subs(substitution, simultaneous=True))

    if metric.subs(t, 0) == metric.subs(t, 1):
        raise AssertionError("metric regression must have nonconstant coefficients")
    if jacobian.subs(t, 0) == jacobian.subs(t, 1):
        raise AssertionError("chart regression must have nonconstant Jacobian")
    print("Lorentz geometry exact checks passed: nonlinear charts, metric covariance, "
          "inverse metric, raising/lowering, full/partial tensor contraction, "
          "Levi-Civita coefficients, Hessian transformation, curvature/Bianchi, "
          "Ricci/scalar contractions, nonzero curvature covariance, and both signatures.")


def main():
    verify()


if __name__ == "__main__":
    main()
