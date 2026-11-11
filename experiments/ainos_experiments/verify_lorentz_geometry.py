"""Exact checks for GR 5.1's metric and nonlinear-chart foundation.

Time first, c=1, signature (-+). The coordinate change is (T,X)=(t,x+t²).
All computations are symbolic over the reals; no tolerances or random seeds
are needed. Formal claims are established separately in Lean.
"""

import sympy as sp


def check_zero(name, expression):
    entries = list(expression) if isinstance(expression, sp.MatrixBase) else [expression]
    if any(sp.simplify(entry) != 0 for entry in entries):
        raise AssertionError(f"{name}: exact residual is nonzero: {expression}")


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

    if metric.subs(t, 0) == metric.subs(t, 1):
        raise AssertionError("metric regression must have nonconstant coefficients")
    if jacobian.subs(t, 0) == jacobian.subs(t, 1):
        raise AssertionError("chart regression must have nonconstant Jacobian")
    print("Lorentz geometry exact checks passed: nonlinear charts, metric covariance, "
          "inverse metric, raising/lowering, full/partial tensor contraction, "
          "and both signature conventions.")


def main():
    verify()


if __name__ == "__main__":
    main()
