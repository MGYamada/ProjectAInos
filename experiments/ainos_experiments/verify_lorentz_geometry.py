"""Exact checks for GR 5.1's metric, curvature and motion examples.

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


def covariant_along(gamma, coordinates, curve, field, parameter):
    """Differentiate coordinate components of a field along a curve."""
    evaluated = [component.subs(dict(zip(coordinates, curve)), simultaneous=True)
                 for component in gamma]
    velocity = sp.diff(curve, parameter)
    return sp.diff(field, parameter) + sp.Matrix([
        (velocity.T * component * field)[0] for component in evaluated])


def verify_motion(metric, coordinates, gamma, jacobian):
    s, a, b, c, d = sp.symbols("s a b c d", real=True)
    curve = sp.Matrix([s, -s**2])
    velocity = sp.diff(curve, s)
    substitution = dict(zip(coordinates, curve))
    along_metric = metric.subs(substitution, simultaneous=True)
    check_zero("nonlinear affine geodesic", covariant_along(
        gamma, coordinates, curve, velocity, s))
    check_zero("timelike velocity norm", (velocity.T * along_metric * velocity)[0] + 1)
    field = sp.Matrix([a, b - 2*s*a])
    other = sp.Matrix([c, d - 2*s*c])
    check_zero("nonlinear parallel field", covariant_along(
        gamma, coordinates, curve, field, s))
    check_zero("parallel metric pairing", (field.T * along_metric * other)[0] + a*c - b*d)
    check_zero("inertial parallel components",
               jacobian.subs(substitution, simultaneous=True) * field - sp.Matrix([a, b]))
    s0, s1, s2 = sp.symbols("s0 s1 s2", real=True)

    def transport(start, end):
        return sp.Matrix([[1, 0], [-2*(end-start), 1]])

    check_zero("endpoint transport", transport(s0, s1) * field.subs(s, s0)
               - field.subs(s, s1))
    check_zero("transport metric preservation", transport(s0, s1).T
               * along_metric.subs(s, s1) * transport(s0, s1) - along_metric.subs(s, s0))
    check_zero("transport subdivision", transport(s1, s2) * transport(s0, s1)
               - transport(s0, s2))
    check_zero("transport reversal", transport(s1, s0) * transport(s0, s1) - sp.eye(2))
    null_field = sp.Matrix([1, 1 - 2*s])
    check_zero("nonzero null parallel field", covariant_along(
        gamma, coordinates, curve, null_field, s))
    check_zero("null field norm", (null_field.T * along_metric * null_field)[0])
    if null_field[0] != 1:
        raise AssertionError("null regression must have a nowhere-zero time component")
    # Include a change with zero speed at the origin; no division by r' is used.
    for reparam in [s**2, s + s**3, -s + 1]:
        reparam_curve = curve.subs(s, reparam)
        reparam_velocity = sp.diff(reparam_curve, s)
        check_zero("acceleration parameter-change term", covariant_along(
            gamma, coordinates, reparam_curve, reparam_velocity, s)
                   - sp.diff(reparam, s, 2) * velocity.subs(s, reparam))
        check_zero("parallel field parameter change", covariant_along(
            gamma, coordinates, reparam_curve, field.subs(s, reparam), s))
    # A nongeodesic curve checks the full r'' v + (r')² Dv formula.
    curve = sp.Matrix([s, s**3])
    velocity = sp.diff(curve, s)
    acceleration = covariant_along(gamma, coordinates, curve, velocity, s)
    reparam = s + s**2
    check_zero("full covariant acceleration transformation", covariant_along(
        gamma, coordinates, curve.subs(s, reparam), sp.diff(curve.subs(s, reparam), s), s)
               - sp.diff(reparam, s, 2) * velocity.subs(s, reparam)
               - sp.diff(reparam, s)**2 * acceleration.subs(s, reparam))


def verify_piecewise_transport(metric, coordinates, gamma):
    """Exact segment equations and corner composition in the curved example.

    The rectangle holonomy here is a symbolic check, not a Lean holonomy theorem.
    """
    s, t0, x0, duration, distance = sp.symbols("s t0 x0 T X", real=True)
    horizontal = sp.Matrix([t0 + duration*s, x0])
    angle = 2*x0*duration*s
    horizontal_map = sp.Matrix([[sp.cosh(angle), -sp.sinh(angle)],
                                [-sp.sinh(angle), sp.cosh(angle)]])
    vertical = sp.Matrix([t0, x0 + distance*s])
    vertical_map = sp.exp(x0**2 - (x0 + distance*s)**2) * sp.eye(2)
    for curve, fundamental in [(horizontal, horizontal_map), (vertical, vertical_map)]:
        check_zero("segment initial transport", fundamental.subs(s, 0) - sp.eye(2))
        for column in range(2):
            check_zero("curved segment parallel equation", covariant_along(
                gamma, coordinates, curve, fundamental[:, column], s))
        along_metric = metric.subs(dict(zip(coordinates, curve)), simultaneous=True)
        check_zero("curved segment metric preservation", fundamental.T * along_metric
                   * fundamental - along_metric.subs(s, 0))
    # (0,0) -> (T,0) -> (T,X) -> (0,X) -> (0,0), with genuine corners.
    horizontal_end = horizontal_map.subs(s, 1)
    vertical_end = vertical_map.subs(s, 1)
    legs = [horizontal_end.subs(x0, 0), vertical_end.subs(x0, 0),
            horizontal_end.subs({x0: distance, duration: -duration}, simultaneous=True),
            vertical_end.subs({x0: distance, distance: -distance}, simultaneous=True)]
    forward = sp.eye(2)
    backward = sp.eye(2)
    for leg in legs:
        forward = leg * forward
    for leg in reversed(legs):
        backward = leg.inv() * backward
    boost = sp.Matrix([[sp.cosh(2*duration*distance), sp.sinh(2*duration*distance)],
                       [sp.sinh(2*duration*distance), sp.cosh(2*duration*distance)]])
    check_zero("curved rectangle composition", forward - boost)
    check_zero("curved rectangle reversal", backward * forward - sp.eye(2))
    check_zero("curved rectangle metric preservation", forward.T * sp.diag(-1, 1)
               * forward - sp.diag(-1, 1))


def verify_inertial_correction(metric, coordinates, gamma, point, linear, normal_metric):
    """Check the quadratic chart's first and second jets at a chosen point.

    The inverse function theorem and the actual chart construction are proved
    in Lean. Here the transformed metric is evaluated along the forward map,
    so no symbolic inversion of the quadratic polynomial is required.
    """
    substitution = dict(zip(coordinates, point))
    displacement = coordinates - point
    size = len(coordinates)
    hessians = [sum((linear[k, ell] * gamma[ell].subs(substitution, simultaneous=True)
                    for ell in range(size)), sp.zeros(size)) for k in range(size)]
    correction = linear * displacement + sp.Rational(1, 2) * sp.Matrix([
        (displacement.T * hessian * displacement)[0] for hessian in hessians])
    jacobian = correction.jacobian(coordinates)
    check_zero("inertial chart center", correction.subs(substitution, simultaneous=True))
    check_zero("inertial chart prescribed Jacobian",
               jacobian.subs(substitution, simultaneous=True) - linear)
    inverse_at_point = linear.inv()
    for k in range(size):
        actual_hessian = sp.hessian(correction[k], coordinates)
        transformed_connection = inverse_at_point.T * (
            hessians[k] - actual_hessian) * inverse_at_point
        check_zero("inertial chart zero connection", transformed_connection)

    inverse_jacobian = jacobian.inv()
    transformed_metric = inverse_jacobian.T * metric * inverse_jacobian
    check_zero("inertial chart metric normalization",
               transformed_metric.subs(substitution, simultaneous=True) - normal_metric)
    for coordinate in coordinates:
        check_zero("inertial chart first metric derivatives",
                   transformed_metric.diff(coordinate).subs(substitution, simultaneous=True))


def verify_parallel_coframe(coordinates, gamma, coframe, primitive):
    """Check a nonconstant parallel coframe and its Poincaré primitive."""
    size = len(coordinates)
    for i in range(size):
        connection = sp.Matrix(size, size, lambda k, j: gamma[k][i, j])
        check_zero("parallel coframe equation",
                   coframe.diff(coordinates[i]) - coframe * connection)
        for j in range(size):
            check_zero("parallel coframe closedness",
                       coframe[:, j].diff(coordinates[i])
                       - coframe[:, i].diff(coordinates[j]))
    s = sp.symbols("s", real=True)
    base = sp.Matrix(sp.symbols(f"a:{size}", real=True))
    segment = base + s * (coordinates - base)
    integrand = coframe.subs(dict(zip(coordinates, segment)), simultaneous=True) * (coordinates - base)
    integrated = integrand.applyfunc(lambda entry: sp.integrate(entry, (s, 0, 1)))
    check_zero("Poincare primitive of the shear coframe", integrated - primitive
               + primitive.subs(dict(zip(coordinates, base)), simultaneous=True))
    check_zero("integrated coframe Jacobian", integrated.jacobian(coordinates) - coframe)


def verify_volterra_solution():
    """Exact nonconstant-coefficient ODE and parameter-variation checks."""
    t, a, y0, b, z = sp.symbols("t a y0 b z", real=True)
    # At a=1 this is the Lean rampCoefficient example, with sup norm <= 1/2.
    coefficient = a * t / 2
    solution = sp.exp(a * t**2 / 4) * y0
    check_zero("Volterra ramp initial value", solution.subs(t, 0) - y0)
    check_zero("Volterra ramp differential equation", sp.diff(solution, t) - coefficient * solution)
    variation = b * sp.diff(solution, a) + z * sp.diff(solution, y0)
    check_zero("Volterra ramp variation initial value", variation.subs(t, 0) - z)
    check_zero("Volterra ramp variational equation",
               sp.diff(variation, t) - coefficient * variation - b * t * solution / 2)


def verify_radial_family():
    """Exact radial rescaling, endpoint derivative, and coframe checks."""
    t, x, s, v = sp.symbols("t x s v", real=True)
    connection = -x / 2
    radial_coefficient = -connection.subs(x, t*x) * x
    radial_solution = sp.exp(t**2 * x**2 / 4) * v
    endpoint = sp.exp(x**2 / 4)
    coframe = sp.exp(-x**2 / 4)
    check_zero("radial family ODE", sp.diff(radial_solution, t)
               - radial_coefficient * radial_solution)
    check_zero("radial family reparametrization", radial_solution.subs(t, s)
               - endpoint.subs(x, s*x) * v)
    check_zero("radial endpoint derivative", x * sp.diff(endpoint, x)
               + connection * x * endpoint)
    check_zero("radial frame/coframe inverse", endpoint * coframe - 1)
    check_zero("one-dimensional parallel coframe", sp.diff(coframe, x) - coframe * connection)


def verify_flat_frame_defect():
    """Check both coordinate directions and the curvature term's sign."""
    t, x = sp.symbols("t x", real=True)
    coords = (t, x)
    shear_connection = (sp.Matrix([[0, 0], [2, 0]]), sp.zeros(2))
    frame = sp.Matrix([[1, 0], [-2*t, 1]])
    coframe = sp.Matrix([[1, 0], [2*t, 1]])
    check_zero("shear radial frame inverse", coframe * frame - sp.eye(2))
    for i, coord in enumerate(coords):
        check_zero(f"shear full parallel frame direction {i}",
                   frame.diff(coord) + shear_connection[i] * frame)
        check_zero(f"shear full parallel coframe direction {i}",
                   coframe.diff(coord) - coframe * shear_connection[i])

    # The conformal metric exp(2*x**2) * diag(-1, 1) is curved. Its
    # curvature term must remain in the defect identity for arbitrary P.
    curved_connection = (sp.Matrix([[0, 2*x], [2*x, 0]]), 2*x*sp.eye(2))
    trial_frame = sp.Matrix([[1+t*x, t], [x, 1]])
    defect = tuple(trial_frame.diff(coord) + gamma * trial_frame
                   for coord, gamma in zip(coords, curved_connection))
    curvature = (curved_connection[1].diff(t) - curved_connection[0].diff(x)
                 + curved_connection[0] * curved_connection[1]
                 - curved_connection[1] * curved_connection[0])
    check_zero("curved defect compatibility sign",
               defect[1].diff(t) - defect[0].diff(x)
               - curved_connection[1] * defect[0] + curved_connection[0] * defect[1]
               - curvature * trial_frame)
    if curvature == sp.zeros(2):
        raise AssertionError("curved defect regression requires nonzero curvature")


def verify():
    verify_volterra_solution()
    verify_radial_family()
    verify_flat_frame_defect()
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

    verify_motion(metric, coordinates, gamma, jacobian)
    verify_parallel_coframe(coordinates, gamma, jacobian, shear)

    curved_metric = sp.exp(2*x**2) * eta
    curved_gamma = verify_connection(curved_metric, coordinates)
    verify_piecewise_transport(curved_metric, coordinates, curved_gamma)
    check_zero("conformal time connection", curved_gamma[0] - sp.Matrix([[0, 2*x], [2*x, 0]]))
    check_zero("conformal spatial connection", curved_gamma[1] - sp.diag(2*x, 2*x))

    # A nontrivial Lorentz basis and a nonzero-curvature point exercise the
    # general correction, in both metric-sign conventions.
    boost = sp.Matrix([[sp.Rational(5, 4), sp.Rational(3, 4)],
                       [sp.Rational(3, 4), sp.Rational(5, 4)]])
    for local_metric, coefficients, point, linear in [
            (eta, flat_gamma, sp.Matrix([1, 2]), boost),
            (metric, gamma, sp.Matrix([1, 2]), boost * jacobian.subs(t, 1)),
            (curved_metric, curved_gamma, sp.Matrix([1, 1]), sp.exp(1) * boost)]:
        for sign in [1, -1]:
            verify_inertial_correction(sign * local_metric, coordinates, coefficients,
                                       point, linear, sign * eta)

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
    # Mixed derivatives of a parallel coframe require theta * R = 0. The
    # conformal origin has a nonzero curvature matrix, despite Gamma = 0.
    connection = [sp.Matrix(2, 2, lambda k, j: curved_gamma[k][i, j]) for i in range(2)]
    obstruction = (connection[1].diff(t) - connection[0].diff(x)
                   + connection[0] * connection[1] - connection[1] * connection[0])
    check_zero("curved parallel-coframe integrability obstruction",
               obstruction.subs({t: 0, x: 0}) - sp.Matrix([[0, -2], [-2, 0]]))
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
          "Ricci/scalar contractions, nonzero curvature covariance, both signatures, "
          "parallel fields, geodesics, metric preservation, endpoint transport, "
          "subdivision/reversal, curved piecewise-path composition, "
          "nonzero null fields, reparametrization, quadratic local inertial charts, "
          "parallel coframe integration, the curved integrability obstruction, "
          "a nonconstant Volterra solution/parameter variation, "
          "a smooth radial family with rescaling and endpoint derivative, "
          "and full flat-frame/coframe equations with the curved defect sign.")


def main():
    verify()


if __name__ == "__main__":
    main()
