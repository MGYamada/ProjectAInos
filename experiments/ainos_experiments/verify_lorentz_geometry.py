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

    if metric.subs(t, 0) == metric.subs(t, 1):
        raise AssertionError("metric regression must have nonconstant coefficients")
    if jacobian.subs(t, 0) == jacobian.subs(t, 1):
        raise AssertionError("chart regression must have nonconstant Jacobian")
    print("Lorentz geometry exact checks passed: nonlinear charts, metric covariance, "
          "inverse metric, raising/lowering, and both signature conventions.")


def main():
    verify()


if __name__ == "__main__":
    main()
