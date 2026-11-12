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


def verify_covariant_pullback(metric, coordinates):
    """Dimension-changing maps, singular maps, and nonlinear composition."""
    t, x = coordinates
    s = sp.symbols("s", real=True)
    axis = sp.Matrix([s, 0])
    derivative = axis.jacobian([s])
    along = metric.subs({t: s, x: 0}, simultaneous=True)
    induced = derivative.T * along * derivative
    check_zero("dimension-changing metric pullback", induced - sp.Matrix([[-1 + 4*s**2]]))
    check_zero("Minkowski time-axis pullback", derivative.T * sp.diag(-1, 1) * derivative
               + sp.ones(1))
    check_zero("degenerate induced tensor", induced.subs(s, sp.Rational(1, 2)))
    projection = sp.Matrix([t, 0])
    projection_derivative = projection.jacobian(coordinates)
    check_zero("singular nonconstant pullback", projection_derivative.T
               * metric.subs(x, 0) * projection_derivative - sp.diag(-1 + 4*t**2, 0))
    zero_derivative = sp.zeros(2)
    check_zero("constant-map pullback", zero_derivative.T * metric * zero_derivative)

    # A nonlinear noninvertible map has zero derivative at the origin.
    # The nonsymmetric tensor tests the two input slots independently.
    f = sp.Matrix([s**2, s**3])
    g = sp.Matrix([t, t*x])
    tensor = sp.Matrix([[1 + t, x], [t - x, 2 + x**2]])
    g_pullback = g.jacobian(coordinates).T * tensor.subs(
        dict(zip(coordinates, g)), simultaneous=True) * g.jacobian(coordinates)
    iterated = f.diff(s).T * g_pullback.subs(
        dict(zip(coordinates, f)), simultaneous=True) * f.diff(s)
    composite = g.subs(dict(zip(coordinates, f)), simultaneous=True)
    direct = composite.diff(s).T * tensor.subs(
        dict(zip(coordinates, composite)), simultaneous=True) * composite.diff(s)
    check_zero("nonlinear noninvertible pullback composition", direct - iterated)
    check_zero("vanishing derivative at origin", direct.subs(s, 0))


def verify_native_forms():
    """Alternating pullback: nonlinear charts, changed dimension and singular maps."""
    t, x, s, r = sp.symbols("t x s r", real=True)
    coordinates = sp.Matrix([t, x])
    shear = sp.Matrix([t, x + t**2])
    jacobian = shear.jacobian(coordinates)
    spatial = sp.Matrix([[0, 1]])
    area = sp.Matrix([[0, 1], [-1, 0]])
    pulled_spatial = spatial * jacobian
    check_zero("native spatial shear form", pulled_spatial - sp.Matrix([[2*t, 1]]))
    check_zero("native normalized shear area", jacobian.T * area * jacobian - area)
    axis = sp.Matrix([s, 0])
    check_zero("native dimension-changing one-form", pulled_spatial.subs(
        {t: s, x: 0}, simultaneous=True) * axis.diff(s) - sp.Matrix([[2*s]]))
    check_zero("native dimension-changing two-form", axis.diff(s).T * area * axis.diff(s))
    projection = sp.Matrix([t, 0]).jacobian(coordinates)
    check_zero("native singular projection area", projection.T * area * projection)

    def pull_two(mapping, source, target, field):
        derivative = mapping.jacobian(source)
        return derivative.T * field.subs(
            dict(zip(target, mapping)), simultaneous=True) * derivative

    def d_one(form, coords):
        return sp.Matrix(len(coords), len(coords), lambda i, j:
                         sp.diff(form[j], coords[i]) - sp.diff(form[i], coords[j]))

    potential = sp.Matrix([[0, t]])
    check_zero("native nonzero exterior derivative normalization", d_one(potential, coordinates) - area)
    shear_potential = potential.subs(dict(zip(coordinates, shear)), simultaneous=True) * jacobian
    check_zero("native nonlinear potential coefficients", shear_potential - sp.Matrix([[2*t**2, t]]))
    check_zero("native nonlinear exterior derivative", d_one(shear_potential, coordinates) - area)
    inverse = sp.Matrix([t, x - t**2])
    inverse_potential = potential.subs(dict(zip(coordinates, inverse)), simultaneous=True) * inverse.jacobian(coordinates)
    check_zero("native inverse-chart exterior derivative", d_one(inverse_potential, coordinates) - area)

    # A nonlinear map from a plane into three dimensions tests naturality without invertibility.
    u, v, w = sp.symbols("u v w", real=True)
    target = sp.Matrix([u, v, w])
    target_potential = sp.Matrix([[u*v, w*u**2, sp.exp(v)*w]])
    target_field = d_one(target_potential, target)
    check_zero("native d-squared mixed-derivative cancellation",
               sp.diff(target_field[1, 2], u) + sp.diff(target_field[2, 0], v)
               + sp.diff(target_field[0, 1], w))
    immersion = sp.Matrix([t, x, t*x])
    immersion_jacobian = immersion.jacobian(coordinates)
    substitution = dict(zip(target, immersion))
    source_potential = target_potential.subs(substitution, simultaneous=True) * immersion_jacobian
    check_zero("native dimension-changing d-pullback naturality",
               d_one(source_potential, coordinates) - immersion_jacobian.T
               * target_field.subs(substitution, simultaneous=True) * immersion_jacobian)

    def wedge_one(a, b):
        return a.T * b - b.T * a

    def d_two_three(form):
        return sp.diff(form[1, 2], u) + sp.diff(form[2, 0], v) + sp.diff(form[0, 1], w)

    def wedge_two_one(two, one):
        return two[0, 1]*one[2] - two[0, 2]*one[1] + two[1, 2]*one[0]

    alpha = sp.Matrix([[u*v, w, u]])
    beta = sp.Matrix([[v, w*u, v**2]])
    product = wedge_one(alpha, beta)
    check_zero("native wedge graded commutation", product + wedge_one(beta, alpha))
    check_zero("native wedge graded Leibniz",
               d_two_three(product) - wedge_two_one(d_one(alpha, target), beta)
               + wedge_two_one(d_one(beta, target), alpha))
    check_zero("native wedge negative Leibniz example",
               d_two_three(wedge_one(sp.Matrix([[1, 0, 0]]), sp.Matrix([[0, 0, v]]))) + 1)
    pulled_alpha = alpha.subs(substitution, simultaneous=True) * immersion_jacobian
    pulled_beta = beta.subs(substitution, simultaneous=True) * immersion_jacobian
    check_zero("native wedge dimension-changing naturality",
               wedge_one(pulled_alpha, pulled_beta) - immersion_jacobian.T
               * product.subs(substitution, simultaneous=True) * immersion_jacobian)
    check_zero("native wedge nonlinear-chart normalization",
               wedge_one(sp.Matrix([[1, 0]]) * jacobian, spatial * jacobian) - area)

    # Variable form and nonlinear maps test both evaluation and all covariant slots.
    f = sp.Matrix([s, r + s**2])
    g = sp.Matrix([t**2, t*x])
    variable_area = (1 + t + x**2) * area
    composite = g.subs({t: f[0], x: f[1]}, simultaneous=True)
    direct = pull_two(composite, sp.Matrix([s, r]), coordinates, variable_area)
    iterated = pull_two(f, sp.Matrix([s, r]), coordinates,
                       pull_two(g, coordinates, coordinates, variable_area))
    check_zero("native variable two-form composition", direct - iterated)
    check_zero("native composition at singular point", direct.subs(s, 0))


def verify_quadratic_variation(metric, coordinates, gamma):
    """Differentiate the density independently, using force minus d(momentum)/ds."""
    size = len(coordinates)
    velocity = sp.Matrix(sp.symbols(f"v0:{size}", real=True))
    acceleration = sp.Matrix(sp.symbols(f"a0:{size}", real=True))
    density = (velocity.T * metric * velocity)[0] / 2
    force = sp.Matrix([sp.diff(density, q) for q in coordinates])
    momentum = sp.Matrix([sp.diff(density, v) for v in velocity])
    residual = (force - momentum.jacobian(coordinates) * velocity
                - momentum.jacobian(velocity) * acceleration)
    covariant_acceleration = acceleration + sp.Matrix([
        (velocity.T * component * velocity)[0] for component in gamma])
    check_zero("quadratic EL equals minus lowered acceleration",
               residual + metric * covariant_acceleration)

    # On the open timelike cone the speed is positive. Differentiate the
    # square-root density itself, retaining the full speed derivative.
    mass = sp.symbols("m", positive=True)
    speed = sp.sqrt(-(velocity.T * metric * velocity)[0])
    free_density = -mass * speed
    free_force = sp.Matrix([sp.diff(free_density, q) for q in coordinates])
    free_momentum = sp.Matrix([sp.diff(free_density, v) for v in velocity])
    free_residual = (free_force - free_momentum.jacobian(coordinates) * velocity
                     - free_momentum.jacobian(velocity) * acceleration)
    speed_derivative = (sp.Matrix([speed]).jacobian(coordinates) * velocity
                        + sp.Matrix([speed]).jacobian(velocity) * acceleration)[0]
    check_zero("massive EL includes the non-affine speed term",
               free_residual + mass/speed * metric *
               (covariant_acceleration - speed_derivative/speed * velocity))

    # Nonzero endpoint variations exercise the boundary term. A stationary
    # coordinate clock in the conformal metric need not be a geodesic.
    s, x0, epsilon = sp.symbols("s x0 epsilon", real=True)
    curve = sp.Matrix([s, x0])
    variation = sp.Matrix([s**2, 1+s])
    perturbed = curve + epsilon * variation
    perturbed_metric = metric.subs(dict(zip(coordinates, perturbed)), simultaneous=True)
    perturbed_velocity = sp.diff(perturbed, s)
    action_density = (perturbed_velocity.T * perturbed_metric * perturbed_velocity)[0] / 2
    variation_density = sp.diff(action_density, epsilon).subs(epsilon, 0)
    along_metric = metric.subs(dict(zip(coordinates, curve)), simultaneous=True)
    boundary = (sp.diff(curve, s).T * along_metric * variation)[0]
    along_acceleration = covariant_along(gamma, coordinates, curve, sp.diff(curve, s), s)
    interior = -(along_acceleration.T * along_metric * variation)[0]
    check_zero("first variation with endpoint term",
               sp.integrate(variation_density, (s, 0, 1))
               - (boundary.subs(s, 1) - boundary.subs(s, 0))
               - sp.integrate(interior, (s, 0, 1)))


def verify_clocks(metric, curved_metric, coordinates):
    """Exact native-clock examples and a causal-type check of the quadratic density."""
    s, x0, a, b = sp.symbols("s x0 a b", real=True)
    curve = sp.Matrix([s, -s**2])
    velocity = sp.diff(curve, s)
    along_metric = metric.subs(dict(zip(coordinates, curve)), simultaneous=True)
    check_zero("shear proper-speed square", (velocity.T * along_metric * velocity)[0] + 1)
    check_zero("shear proper time", sp.integrate(sp.Integer(1), (s, a, b)) - (b-a))
    clock_metric = curved_metric.subs(coordinates[1], x0)
    speed = sp.sqrt(-clock_metric[0, 0])
    check_zero("curved stationary-clock rate", speed - sp.exp(x0**2))
    check_zero("curved stationary-clock proper time",
               sp.integrate(speed, (s, a, b)) - (b-a) * sp.exp(x0**2))
    check_zero("curved stationary-clock quadratic action",
               sp.integrate(clock_metric[0, 0]/2, (s, a, b)) + (b-a)*sp.exp(2*x0**2)/2)
    null = sp.Matrix([1, 1])
    check_zero("null quadratic density", (null.T * curved_metric * null)[0])
    # A null reference velocity still admits arbitrary variation directions.
    epsilon = sp.symbols("epsilon", real=True)
    varied = null + epsilon * sp.Matrix([0, 1])
    check_zero("unconstrained variation at a null velocity",
               sp.diff((varied.T * curved_metric * varied)[0]/2, epsilon).subs(epsilon, 0)
               - sp.exp(2*coordinates[1]**2))

    # The exponential clock is a stationary massive worldline with nonzero
    # native acceleration. The proper-time inverse is log(tau + exp(s0)).
    exponential_curve = sp.Matrix([sp.exp(s), -sp.exp(2*s)])
    exponential_velocity = sp.diff(exponential_curve, s)
    gamma = christoffel(metric, coordinates)
    native_acceleration = covariant_along(gamma, coordinates, exponential_curve,
                                        exponential_velocity, s)
    check_zero("exponential-clock tangential acceleration",
               native_acceleration - exponential_velocity)
    along_exponential = metric.subs(dict(zip(coordinates, exponential_curve)), simultaneous=True)
    exponential_speed = sp.sqrt(-(exponential_velocity.T * along_exponential * exponential_velocity)[0])
    check_zero("exponential-clock proper speed", exponential_speed - sp.exp(s))
    check_zero("exponential-clock massive residual",
               native_acceleration - sp.diff(exponential_speed, s)/exponential_speed
               * exponential_velocity)
    if sp.simplify((along_exponential * native_acceleration)[0]) == 0:
        raise AssertionError("non-affine clock must have a nonzero quadratic residual")
    check_zero("exponential-clock proper time",
               sp.integrate(exponential_speed, (s, a, b)) - sp.exp(b) + sp.exp(a))
    p = sp.symbols("p", positive=True)  # p = tau + exp(s0)
    inverse = sp.log(p)
    inverse_curve = exponential_curve.subs(s, inverse)
    check_zero("proper-time inverse derivative", sp.diff(inverse, p) - 1/sp.exp(inverse))
    check_zero("proper-time inverse yields affine motion",
               covariant_along(gamma, coordinates, inverse_curve, sp.diff(inverse_curve, p), p))
    inverse_metric = metric.subs(dict(zip(coordinates, inverse_curve)), simultaneous=True)
    check_zero("proper-time inverse gives unit speed",
               (sp.diff(inverse_curve, p).T * inverse_metric * sp.diff(inverse_curve, p))[0] + 1)
    tau = sp.symbols("tau", nonnegative=True)
    finite_inverse = sp.log(tau + sp.exp(a))
    check_zero("finite clock inverse composition", sp.exp(finite_inverse) - sp.exp(a) - tau)
    check_zero("finite clock left endpoint", finite_inverse.subs(tau, 0) - a)
    check_zero("finite clock right endpoint",
               finite_inverse.subs(tau, sp.exp(b) - sp.exp(a)) - b)


def verify_family_variations(metric, coordinates, gamma, *, shear=False):
    """Differentiate genuine two-parameter families and their scalar densities."""
    epsilon, s, x0, mass = sp.symbols("epsilon s x0 mass", real=True)
    family = sp.Matrix([s + epsilon*s**2, epsilon + s**2])
    variation = sp.diff(family, epsilon)
    velocity = sp.diff(family, s)
    mixed_et = covariant_along(gamma, coordinates, family, velocity, epsilon)
    mixed_te = covariant_along(gamma, coordinates, family, variation, s)
    check_zero("native family mixed covariant derivatives", mixed_et - mixed_te)
    along_metric = metric.subs(dict(zip(coordinates, family)), simultaneous=True)
    density = (velocity.T * along_metric * velocity)[0]/2
    check_zero("native quadratic family density derivative",
               sp.diff(density, epsilon) - (mixed_te.T * along_metric * velocity)[0])

    # At epsilon=0 this is a timelike clock for every s and x0. The shear
    # case uses the actual inverse coordinate map, including its second derivative.
    timelike_family = sp.Matrix([s + epsilon*s**2, x0 + epsilon*(1+s)])
    if shear:
        timelike_family[1] -= timelike_family[0]**2
    field = sp.diff(timelike_family, epsilon)
    velocity = sp.diff(timelike_family, s)
    along_metric = metric.subs(dict(zip(coordinates, timelike_family)), simultaneous=True)
    q = sp.simplify((velocity.T * along_metric * velocity)[0])
    speed = sp.sqrt(-q)
    mixed = covariant_along(gamma, coordinates, timelike_family, field, s)
    actual = sp.diff(-mass*speed, epsilon).subs(epsilon, 0)
    expected = (mass/speed * (mixed.T * along_metric * velocity)[0]).subs(epsilon, 0)
    check_zero("native massive family density derivative", actual - expected)
    base_curve = timelike_family.subs(epsilon, 0)
    base_velocity = velocity.subs(epsilon, 0)
    base_field = field.subs(epsilon, 0)
    base_metric = along_metric.subs(epsilon, 0)
    base_speed = sp.simplify(speed.subs(epsilon, 0))
    acceleration = covariant_along(gamma, coordinates, base_curve, base_velocity, s)
    pairing = (base_field.T * base_metric * base_velocity)[0]
    quadratic_actual = sp.diff(q/2, epsilon).subs(epsilon, 0)
    quadratic_residual = -(base_field.T * base_metric * acceleration)[0]
    massive_boundary = mass/base_speed * pairing
    massive_residual = -mass/base_speed * (base_field.T * base_metric * (
        acceleration - sp.diff(base_speed, s)/base_speed * base_velocity))[0]
    for label, derivative, boundary, residual in [
        ("quadratic", quadratic_actual, pairing, quadratic_residual),
        ("massive", actual, massive_boundary, massive_residual),
    ]:
        derivative, boundary, residual = map(sp.simplify, (derivative, boundary, residual))
        check_zero(f"native {label} endpoint formula", derivative - sp.diff(boundary, s) - residual)
        integral = sp.integrate(derivative, (s, 0, 1))
        middle = sp.Rational(1, 2)
        left = boundary.subs(s, middle) - boundary.subs(s, 0) + sp.integrate(residual, (s, 0, middle))
        right = boundary.subs(s, 1) - boundary.subs(s, middle) + sp.integrate(residual, (s, middle, 1))
        check_zero(f"native {label} first-variation subdivision", integral - left - right)

    if shear:
        # Same genuinely nonlinear fixed-endpoint family proved in Lean.
        bump = s*(1-s)
        time = s + epsilon*bump
        nonlinear = sp.Matrix([time, epsilon**2*bump - time**2])
        nonlinear_metric = metric.subs(dict(zip(coordinates, nonlinear)), simultaneous=True)
        nonlinear_v = sp.diff(nonlinear, s)
        nonlinear_q = sp.simplify((nonlinear_v.T * nonlinear_metric * nonlinear_v)[0])
        check_zero("nonlinear family endpoint fixing",
                   [entry for endpoint in (0, 1)
                    for entry in nonlinear.subs(s, endpoint) - nonlinear.subs({s: endpoint, epsilon: 0})])
        check_zero("nonlinear family quadratic stationarity",
                   sp.integrate(sp.diff(nonlinear_q/2, epsilon).subs(epsilon, 0), (s, 0, 1)))
        check_zero("nonlinear family massive stationarity",
                   sp.integrate(sp.diff(-mass*sp.sqrt(-nonlinear_q), epsilon).subs(epsilon, 0), (s, 0, 1)))


def verify_localized_variations(metric, coordinates):
    """C² compact chart tests and a nonstationary curved clock, all exact."""
    s, epsilon, u, v = sp.symbols("s epsilon u v", real=True)
    left, right = sp.Rational(1, 4), sp.Rational(3, 4)
    cutoff = 4096*(s-left)**3*(right-s)**3
    # Extending by zero has matching derivatives through order two.
    check_zero("localized cutoff C2 gluing",
               [sp.diff(cutoff, s, k).subs(s, end)
                for k in range(3) for end in (left, right)])
    check_zero("localized cutoff midpoint", cutoff.subs(s, sp.Rational(1, 2))-1)
    time, space = s + epsilon*cutoff*u, epsilon*cutoff*v
    family = sp.Matrix([time, space-time**2])
    reference = sp.Matrix([s, -s**2])
    check_zero("localized chart reference", family.subs(epsilon, 0)-reference)
    check_zero("localized chart native test velocity",
               sp.diff(family, epsilon).subs(epsilon, 0)
               - cutoff*sp.Matrix([u, v-2*s*u]))
    along_metric = metric.subs(dict(zip(coordinates, family)), simultaneous=True)
    velocity = sp.diff(family, s)
    density = sp.simplify((velocity.T*along_metric*velocity)[0]/2)
    check_zero("localized chart quadratic stationarity",
               sp.integrate(sp.diff(density, epsilon).subs(epsilon, 0), (s, left, right)))

    # At x=1, a supported spatial test detects the conformal clock's acceleration.
    curved_family = sp.Matrix([s, 1+epsilon*cutoff])
    curved_metric = sp.exp(2*curved_family[1]**2)*sp.diag(-1, 1)
    curved_velocity = sp.diff(curved_family, s)
    norm = (curved_velocity.T*curved_metric*curved_velocity)[0]
    total = sp.integrate(cutoff, (s, left, right))
    assert total > 0
    quadratic = sp.integrate(sp.diff(norm/2, epsilon).subs(epsilon, 0), (s, left, right))
    massive = sp.integrate(sp.diff(-sp.sqrt(-norm), epsilon).subs(epsilon, 0), (s, left, right))
    check_zero("curved clock localized quadratic variation", quadratic+2*sp.exp(2)*total)
    check_zero("curved clock localized massive variation", massive+2*sp.E*total)
    assert quadratic < 0 and massive < 0


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

    verify_covariant_pullback(metric, coordinates)
    verify_native_forms()
    verify_motion(metric, coordinates, gamma, jacobian)
    verify_parallel_coframe(coordinates, gamma, jacobian, shear)

    curved_metric = sp.exp(2*x**2) * eta
    curved_gamma = verify_connection(curved_metric, coordinates)
    verify_piecewise_transport(curved_metric, coordinates, curved_gamma)
    verify_quadratic_variation(eta, inertial, flat_gamma)
    verify_quadratic_variation(metric, coordinates, gamma)
    verify_quadratic_variation(curved_metric, coordinates, curved_gamma)
    verify_clocks(metric, curved_metric, coordinates)
    verify_family_variations(eta, inertial, flat_gamma)
    verify_family_variations(metric, coordinates, gamma, shear=True)
    verify_localized_variations(metric, coordinates)
    verify_family_variations(curved_metric, coordinates, curved_gamma)
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
          "full flat-frame/coframe equations with the curved defect sign, "
          "curved proper-time clocks, quadratic Euler–Lagrange/native acceleration, "
          "endpoint variations, unconstrained null-velocity variations, "
          "massive non-affine Euler–Lagrange equations, the finite proper-time inverse, "
          "mixed covariant derivatives and densities of curve families, "
          "and native alternating-form pullback examples.")


def main():
    verify()


if __name__ == "__main__":
    main()
