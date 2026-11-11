"""Exact checks for GR 5.1's metric, connection and nonlinear-chart examples.

Time first, c=1, signature (-+). The coordinate change is (T,X)=(t,x+t²).
All computations are symbolic over the reals; no tolerances or random seeds
are needed. Formal claims are established separately in Lean.
"""

import sympy as sp


def check_zero(name, expression):
    entries = list(expression) if isinstance(expression, sp.MatrixBase) else [expression]
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

    curved_gamma = verify_connection(sp.exp(2*x**2) * eta, coordinates)
    check_zero("conformal time connection", curved_gamma[0] - sp.Matrix([[0, 2*x], [2*x, 0]]))
    check_zero("conformal spatial connection", curved_gamma[1] - sp.diag(2*x, 2*x))

    if metric.subs(t, 0) == metric.subs(t, 1):
        raise AssertionError("metric regression must have nonconstant coefficients")
    if jacobian.subs(t, 0) == jacobian.subs(t, 1):
        raise AssertionError("chart regression must have nonconstant Jacobian")
    print("Lorentz geometry exact checks passed: nonlinear charts, metric covariance, "
          "inverse metric, raising/lowering, full/partial tensor contraction, "
          "Levi-Civita coefficients, Hessian transformation, and both signature conventions.")


def main():
    verify()


if __name__ == "__main__":
    main()
