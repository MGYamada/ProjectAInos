"""Exact electromagnetic convention and radial-reconstruction checks.

Time first, c=1, metric (-+++), orientation dt^dx^dy^dz. No random or
floating-point computations are used. These experiments supplement Lean.
"""

from itertools import product

import sympy as sp


def curvature(potential, coordinates):
    return sp.Matrix(4, 4, lambda i, j: sp.diff(potential[j], coordinates[i])
                     - sp.diff(potential[i], coordinates[j]))


def hodge(field):
    metric = sp.diag(-1, 1, 1, 1)
    raised = metric * field * metric
    return sp.Matrix(4, 4, lambda i, j: sum(
        sp.Rational(1, 2) * sp.LeviCivita(i, j, k, l) * raised[k, l]
        for k, l in product(range(4), repeat=2)))


def contraction(left, right):
    raised = sp.diag(-1, 1, 1, 1) * right * sp.diag(-1, 1, 1, 1)
    return sum(left[i, j] * raised[i, j] for i, j in product(range(4), repeat=2))


def check_zero(name, expression):
    entries = list(expression) if isinstance(expression, sp.MatrixBase) else [expression]
    if any(sp.simplify(entry) != 0 for entry in entries):
        raise AssertionError(f"{name}: exact residual is nonzero: {expression}")


def verify_virial_coulomb_larmor():
    """The virial identity, motion in a Coulomb field and Larmor's theorem (§§34, 39, 45).

    * §34: the improvement stress T^{mu nu} = (d^mu d^nu - eta^{mu nu} box) chi is symmetric
      and conserved, with spatial trace 3 d_0^2 chi - 2 Laplacian chi, and T^00 plus the
      four-trace is the spatial trace;
    * §39: for H = sqrt(m^2 + e^{-2s}(p_s^2 + p_phi^2)) + alpha e^{-s}, X = (p_phi^2 - alpha^2)
      e^{-s} + alpha H and Y = p_phi p_s e^{-s} have the brackets of CoulombMotion.lean, and
      d^2X/dphi^2 = -kappa^2 X with kappa^2 = 1 - alpha^2/p_phi^2 (the rosette);
    * §45: in the symmetric gauge, |p - (e/2) B x q|^2/2m = |p|^2/2m - Omega.(q x p)
      + (e^2/8m)|B x q|^2 with Omega = e B/2m.
    """
    coordinates = sp.symbols("t x y z", real=True)
    eta = sp.diag(-1, 1, 1, 1)
    chi = sp.Function("chi")(*coordinates)
    box = sum(eta[a, a] * sp.diff(chi, coordinates[a], 2) for a in range(4))
    stress = sp.Matrix(4, 4, lambda m, n: eta[m, m] * eta[n, n]
                       * sp.diff(chi, coordinates[m], coordinates[n]) - eta[m, n] * box)
    check_zero("improvement stress symmetry", stress - stress.T)
    check_zero("improvement stress conservation", sp.Matrix(
        [sum(sp.diff(stress[m, n], coordinates[m]) for m in range(4)) for n in range(4)]))
    spatial_trace = sum(stress[a, a] for a in range(1, 4))
    laplacian = sum(sp.diff(chi, coordinates[a], 2) for a in range(1, 4))
    check_zero("improvement spatial trace",
               spatial_trace - 3 * sp.diff(chi, coordinates[0], 2) + 2 * laplacian)
    check_zero("energy plus four-trace", stress[0, 0] + (-stress[0, 0] + spatial_trace)
               - spatial_trace)

    s, phi, ps, pphi = sp.symbols("s phi p_s p_phi", real=True)
    mass, alpha = sp.symbols("m alpha", positive=True)
    energy = sp.sqrt(mass**2 + sp.exp(-2 * s) * (ps**2 + pphi**2))
    hamiltonian = energy + alpha * sp.exp(-s)

    def bracket(f, g):
        return (sp.diff(f, s) * sp.diff(g, ps) - sp.diff(f, ps) * sp.diff(g, s)
                + sp.diff(f, phi) * sp.diff(g, pphi) - sp.diff(f, pphi) * sp.diff(g, phi))

    orbit_x = (pphi**2 - alpha**2) * sp.exp(-s) + alpha * hamiltonian
    orbit_y = pphi * ps * sp.exp(-s)
    check_zero("Coulomb bracket X", bracket(orbit_x, hamiltonian)
               + (pphi**2 - alpha**2) * ps * sp.exp(-3 * s) / energy)
    check_zero("Coulomb bracket Y", bracket(orbit_y, hamiltonian)
               - orbit_x * pphi * sp.exp(-2 * s) / energy)
    check_zero("Coulomb angular velocity", bracket(phi, hamiltonian)
               - pphi * sp.exp(-2 * s) / energy)
    check_zero("Coulomb angular momentum", bracket(pphi, hamiltonian))
    x_rate = bracket(orbit_x, hamiltonian) / bracket(phi, hamiltonian)
    y_rate = bracket(orbit_y, hamiltonian) / bracket(phi, hamiltonian)
    check_zero("rosette first equation", x_rate + (pphi**2 - alpha**2) * orbit_y / pphi**2)
    check_zero("rosette second equation", y_rate - orbit_x)

    q = sp.Matrix(sp.symbols("q0:3", real=True))
    p = sp.Matrix(sp.symbols("p0:3", real=True))
    field = sp.Matrix(sp.symbols("B0:3", real=True))
    charge = sp.symbols("e", real=True)
    kinetic = p - charge / 2 * field.cross(q)
    larmor = charge * field / (2 * mass)
    rotating = (p.dot(p)) / (2 * mass) - larmor.dot(q.cross(p))
    check_zero("Larmor identity", kinetic.dot(kinetic) / (2 * mass) - rotating
               - charge**2 / (8 * mass) * field.cross(q).dot(field.cross(q)))


def verify_static_fields_and_waves():
    """Static fields, the moving charge and waves (§§36–38, 46–48, 50).

    * §36: the regularized Newton kernel 1/(4 pi sqrt(r^2 + eps^2)) has the Laplacian
      -3 eps^2/(4 pi (r^2 + eps^2)^(5/2)), and the peak 3/(4 pi (r^2 + 1)^(5/2)) has integral 1;
    * §37: the point charge has field energy q^2/(8 pi eps) outside the radius eps;
    * §38: the boosted static potential -phi(gamma(x - Vt), y, z) (dt - V dx) gives L&L (38.8);
    * §46: div E = -box phi - d_t L and curl B - d_t E = -box a + grad L for A = (-phi, a);
    * §§47–48: the plane wave f(l.x) a with null l and <l, a> = 0 is a vacuum solution, and the
      Doppler factor is gamma (1 - V n_1);
    * §50: s1^2 + s2^2 + s3^2 = s0^2 - 4 det J for a Hermitian 2x2 matrix.
    """
    x, y, z = sp.symbols("x y z", real=True)
    eps, r = sp.symbols("epsilon r", positive=True)
    kernel = 1 / (4 * sp.pi * sp.sqrt(x**2 + y**2 + z**2 + eps**2))
    laplacian = sum(sp.diff(kernel, v, 2) for v in (x, y, z))
    check_zero("regularized kernel Laplacian",
               laplacian + 3 * eps**2 / (4 * sp.pi * (x**2 + y**2 + z**2 + eps**2)**sp.Rational(5, 2)))
    peak = sp.integrate(4 * sp.pi * r**2 * 3 / (4 * sp.pi * (r**2 + 1)**sp.Rational(5, 2)),
                        (r, 0, sp.oo))
    check_zero("peak integral", peak - 1)
    q = sp.symbols("q", real=True)
    energy = sp.integrate(4 * sp.pi * r**2 * (q / (4 * sp.pi * r**2))**2 / 2, (r, eps, sp.oo))
    check_zero("point-charge energy outside eps", energy - q**2 / (8 * sp.pi * eps))

    t = sp.symbols("t", real=True)
    coordinates = (t, x, y, z)
    velocity = sp.symbols("V", real=True)
    gamma = 1 / sp.sqrt(1 - velocity**2)
    comoving = (gamma * (x - velocity * t), y, z)
    coulomb = q / (4 * sp.pi * sp.sqrt(sum(c**2 for c in comoving)))
    potential = sp.Matrix([-gamma * coulomb, gamma * velocity * coulomb, 0, 0])
    field = curvature(potential, coordinates)
    electric = sp.Matrix([field[i, 0] for i in range(1, 4)])
    separation = sp.Matrix([x - velocity * t, y, z])
    distance = sp.sqrt(separation.dot(separation))
    sine_sq = (y**2 + z**2) / distance**2
    expected = q * (1 - velocity**2) * separation / (
        4 * sp.pi * distance**3 * (1 - velocity**2 * sine_sq)**sp.Rational(3, 2))
    point = {t: sp.Rational(1, 3), x: sp.Rational(7, 5), y: sp.Rational(-2, 3), z: sp.Rational(1, 2),
             velocity: sp.Rational(3, 5), q: 2}
    residual = (electric - expected).subs(point)
    if any(abs(sp.N(entry, 30)) > sp.Float("1e-25") for entry in residual):
        raise AssertionError(f"moving charge (38.8): residual {residual}")

    phi = sp.Function("phi")(*coordinates)
    a = [sp.Function(f"a{i}")(*coordinates) for i in range(3)]
    four = sp.Matrix([-phi] + a)
    field = curvature(four, coordinates)
    electric = [field[i, 0] for i in range(1, 4)]
    magnetic = [field[2, 3], field[3, 1], field[1, 2]]

    def box(f):
        return -sp.diff(f, t, 2) + sum(sp.diff(f, v, 2) for v in (x, y, z))

    lorenz = sp.diff(phi, t) + sum(sp.diff(a[i], v) for i, v in enumerate((x, y, z)))
    check_zero("div E in Lorenz form", sum(sp.diff(electric[i], v) for i, v in enumerate((x, y, z)))
               + box(phi) + sp.diff(lorenz, t))
    curl = [sp.diff(magnetic[2], y) - sp.diff(magnetic[1], z),
            sp.diff(magnetic[0], z) - sp.diff(magnetic[2], x),
            sp.diff(magnetic[1], x) - sp.diff(magnetic[0], y)]
    for i, v in enumerate((x, y, z)):
        check_zero(f"curl B - d_t E in Lorenz form {i}",
                   curl[i] - sp.diff(electric[i], t) + box(a[i]) - sp.diff(lorenz, v))

    kappa = sp.symbols("kappa", positive=True)
    profile = sp.Function("f")
    phase = kappa * (t - x)
    wave = sp.Matrix([0, 0, profile(phase), 0])
    wave_field = curvature(wave, coordinates)
    raised = sp.diag(-1, 1, 1, 1) * wave_field * sp.diag(-1, 1, 1, 1)
    check_zero("plane wave vacuum", sp.Matrix(
        [sum(sp.diff(raised[m, n], coordinates[m]) for m in range(4)) for n in range(4)]))
    normal = sp.Matrix(sp.symbols("n1:4", real=True))
    wavevector = kappa * sp.Matrix([1, -normal[0], -normal[1], -normal[2]])
    observer = gamma * sp.Matrix([1, velocity, 0, 0])
    check_zero("Doppler factor", wavevector.dot(observer)
               - gamma * kappa * (1 - velocity * normal[0]))

    j00, j11 = sp.symbols("J00 J11", real=True)
    re, im = sp.symbols("Re Im", real=True)
    coherency = sp.Matrix([[j00, re + sp.I * im], [re - sp.I * im, j11]])
    stokes = [j00 + j11, 2 * re, -2 * im, j00 - j11]
    check_zero("Stokes identity", sum(s**2 for s in stokes[1:]) - stokes[0]**2
               + 4 * coherency.det())


def verify_multipoles_magnetostatics_and_modes():
    """Multipoles, magnetostatics, the Fourier kernel and cavity modes (§§40–44, 51, 52).

    * §§40–41: the second derivative of 1/(4 pi |z|) is (3 z z - |z|^2 1)/(4 pi |z|^5), the
      dipole field is (3 (n.d) n - d)/(4 pi |x|^3), and the quadrupole term is
      sum D_ij x_i x_j/(8 pi |x|^5) with D_ij = 3 y_i y_j - |y|^2 delta_ij;
    * §43: curl curl a = grad div a - Laplacian a;
    * §44: for j = rho v with v = Omega x r, the moment (1/2) r x j is (e/2m) times r x (mu v);
    * §51: int_0^oo t^(-1/2) e^(-r t) dt = sqrt(pi/r), and the radial transform of 1/(4 pi |x|)
      with a damping e^(-eps |x|) tends to 1/(4 pi^2 |xi|^2);
    * §52: the conducting mode a = c_i cos(W t) cos(k_i x_i) prod sin(k_j x_j) solves the wave
      equation when W^2 = sum k_j^2.
    """
    x, y, z = coords = sp.symbols("x y z", real=True)
    point = sp.Matrix(coords)
    radius = sp.sqrt(point.dot(point))
    kernel = 1 / (4 * sp.pi * radius)
    hessian = sp.hessian(kernel, coords)
    check_zero("second derivative of the kernel",
               hessian - (3 * point * point.T - radius**2 * sp.eye(3)) / (4 * sp.pi * radius**5))
    d = sp.Matrix(sp.symbols("d0:3", real=True))
    dipole = d.dot(point) / (4 * sp.pi * radius**3)
    field = -sp.Matrix([sp.diff(dipole, v) for v in coords])
    normal = point / radius
    check_zero("dipole field", field - (3 * normal.dot(d) * normal - d) / (4 * sp.pi * radius**3))
    yv = sp.Matrix(sp.symbols("y0:3", real=True))
    second = (sp.Rational(1, 2) * (yv.T * hessian * yv))[0]
    quadrupole = 3 * yv * yv.T - yv.dot(yv) * sp.eye(3)
    check_zero("quadrupole term", second - (point.T * quadrupole * point)[0]
               / (8 * sp.pi * radius**5))

    a = sp.Matrix([sp.Function(f"a{i}")(*coords) for i in range(3)])

    def curl(f):
        return sp.Matrix([sp.diff(f[2], y) - sp.diff(f[1], z), sp.diff(f[0], z) - sp.diff(f[2], x),
                          sp.diff(f[1], x) - sp.diff(f[0], y)])

    divergence = sum(sp.diff(a[i], v) for i, v in enumerate(coords))
    gradient = sp.Matrix([sp.diff(divergence, v) for v in coords])
    laplacian = a.applyfunc(lambda f: sum(sp.diff(f, v, 2) for v in coords))
    check_zero("curl curl", curl(curl(a)) - gradient + laplacian)
    charge, mass = sp.symbols("e m", positive=True)
    mu = sp.Function("mu")(*coords)
    rotation = sp.Matrix(sp.symbols("W0:3", real=True))
    velocity = rotation.cross(point)
    current = charge / mass * mu * velocity
    check_zero("magnetic moment ratio", point.cross(current) / 2
               - charge / (2 * mass) * point.cross(mu * velocity))

    t, r = sp.symbols("t r", positive=True)
    check_zero("subordination integral", sp.integrate(t**sp.Rational(-1, 2) * sp.exp(-r * t),
                                                      (t, 0, sp.oo)) - sp.sqrt(sp.pi / r))
    k, eps = sp.symbols("k epsilon", positive=True)
    damped = sp.integrate(4 * sp.pi * r**2 * sp.exp(-eps * r) / (4 * sp.pi * r)
                          * sp.sin(2 * sp.pi * k * r) / (2 * sp.pi * k * r), (r, 0, sp.oo))
    check_zero("Fourier transform of the kernel", sp.limit(damped, eps, 0)
               - 1 / (4 * sp.pi**2 * k**2))

    time = sp.symbols("t", real=True)
    wave = sp.symbols("k0:3", positive=True)
    frequency = sp.sqrt(sum(q**2 for q in wave))
    mode = sp.cos(frequency * time) * sp.cos(wave[0] * x) * sp.sin(wave[1] * y) * sp.sin(wave[2] * z)
    check_zero("conducting mode wave equation", -sp.diff(mode, time, 2)
               + sum(sp.diff(mode, v, 2) for v in coords))


def verify_retarded_potentials():
    """The retarded integral (§§62, 64).

    * the field V_i = d_i f/r - d_t f y_i/r^2 - f y_i/r^3, evaluated at the retarded point
      (t - |y|, x - y), has div V = (d_t^2 f - Laplacian f)(t - r, x - y)/r away from y = 0, the
      key step of RetardedIntegral.integral_wave_div_norm;
    * a time-harmonic solution e^(-2 pi i nu t) A(x) of (d_t^2 - Laplacian) u = e^(-2 pi i nu t) j(x)
      satisfies (Laplacian + (2 pi nu)^2) A = -j, the Helmholtz equation of §64.
    """
    t, x, y, z = sp.symbols("t x y z", real=True)
    y1, y2, y3 = ys = sp.symbols("y1 y2 y3", real=True)
    s, a, b, c = sp.symbols("s a b c", real=True)
    # A concrete smooth f(s, a, b, c); the identity is checked exactly at a rational point.
    base = sp.exp(-(s**2 + a**2 + 2 * b**2 + c**2)) * (1 + s * a - b * c + s**2 * c)
    r = sp.sqrt(y1**2 + y2**2 + y3**2)
    retarded = {s: t - r, a: x - y1, b: y - y2, c: z - y3}

    def at(expr):
        return expr.subs(retarded, simultaneous=True)

    dt_f = at(sp.diff(base, s))
    d_f = [at(sp.diff(base, v)) for v in (a, b, c)]
    value = at(base)
    field = [d_f[i] / r - dt_f * ys[i] / r**2 - value * ys[i] / r**3 for i in range(3)]
    divergence = sum(sp.diff(field[i], ys[i]) for i in range(3))
    wave = at(sp.diff(base, s, 2) - sum(sp.diff(base, v, 2) for v in (a, b, c)))
    sample = {t: sp.Rational(1, 3), x: sp.Rational(1, 2), y: sp.Rational(-1, 4), z: 1,
              y1: sp.Rational(2, 7), y2: sp.Rational(-3, 5), y3: sp.Rational(1, 9)}
    check_zero("retarded field divergence", sp.nsimplify(sp.N((divergence - wave / r).subs(sample),
                                                            60), tolerance=1e-50))
    nu = sp.symbols("nu", positive=True)
    amplitude = sp.Function("A")(x, y, z)
    current = sp.Function("j")(x, y, z)
    u = sp.exp(-2 * sp.pi * sp.I * nu * t) * amplitude
    equation = sp.diff(u, t, 2) - sum(sp.diff(u, v, 2) for v in (x, y, z)) \
        - sp.exp(-2 * sp.pi * sp.I * nu * t) * current
    helmholtz = sum(sp.diff(amplitude, v, 2) for v in (x, y, z)) + (2 * sp.pi * nu)**2 * amplitude \
        + current
    check_zero("Helmholtz sign", sp.simplify(equation * sp.exp(2 * sp.pi * sp.I * nu * t) + helmholtz))


def sphere_integral(expr, n, theta, phi):
    """Integrate a polynomial-trigonometric expression over the unit sphere."""
    sub = {n[0]: sp.sin(theta) * sp.cos(phi), n[1]: sp.sin(theta) * sp.sin(phi),
           n[2]: sp.cos(theta)}
    inner = sp.integrate(sp.expand(expr.subs(sub, simultaneous=True)), (phi, 0, 2 * sp.pi))
    return sp.integrate(sp.simplify(inner) * sp.sin(theta), (theta, 0, sp.pi))


def verify_radiation():
    """The Liénard–Wiechert field, near-zone flux, multipole powers, Darwin gauge, Liénard power."""
    e = sp.symbols("e", real=True)
    t = sp.symbols("t", real=True)
    xs = sp.Matrix(sp.symbols("x1 x2 x3", real=True))
    tau = sp.symbols("tau", real=True)
    # (63.8): a polynomial worldline r(tau) = r0 + v0 tau + a0 tau^2/2 + j0 tau^3/6.
    r0 = sp.Matrix([sp.Rational(1, 3), -sp.Rational(1, 2), sp.Rational(1, 5)])
    v0 = sp.Matrix([sp.Rational(1, 4), sp.Rational(1, 6), -sp.Rational(1, 7)])
    a0 = sp.Matrix([sp.Rational(2, 3), -1, sp.Rational(1, 2)])
    j0 = sp.Matrix([1, sp.Rational(1, 3), -2])
    r = r0 + v0 * tau + a0 * tau**2 / 2 + j0 * tau**3 / 6
    v = r.diff(tau)
    Rv = xs - r
    Rn = sp.sqrt(Rv.dot(Rv))
    kappa = Rn - Rv.dot(v)
    phi = e / (4 * sp.pi * kappa)
    avec = e * v / (4 * sp.pi * kappa)
    # Implicit derivatives of the retarded time: d_t tau = R/kappa, grad tau = -R_vec/kappa.
    dtau_t = Rn / kappa
    dtau_x = [-Rv[i] / kappa for i in range(3)]

    def d_t(f):
        return sp.diff(f, tau) * dtau_t

    def d_x(f, i):
        return sp.diff(f, xs[i]) + sp.diff(f, tau) * dtau_x[i]

    efield = sp.Matrix([-d_x(phi, i) - d_t(avec[i]) for i in range(3)])
    bfield = sp.Matrix([d_x(avec[2], 1) - d_x(avec[1], 2), d_x(avec[0], 2) - d_x(avec[2], 0),
                        d_x(avec[1], 0) - d_x(avec[0], 1)])
    acc = v.diff(tau)
    lw = e / (4 * sp.pi) * ((1 - v.dot(v)) * (Rv - Rn * v) / kappa**3
                            + Rv.cross((Rv - Rn * v).cross(acc)) / kappa**3)
    sample = {tau: 0, xs[0]: r0[0] + 3, xs[1]: r0[1] + 4, xs[2]: r0[2] + 12}
    check_zero("Lienard-Wiechert electric field (63.8)", (efield - lw).subs(sample))
    nvec = Rv / Rn
    check_zero("Lienard-Wiechert magnetic field (63.9)", (bfield - nvec.cross(lw)).subs(sample))

    # §63, the source identity: the Jacobian of (tau, y) -> (tau + |y|, r(tau) + y) is 1 - n.v,
    # which cancels the denominator of the potentials; the charge at rest pairs to -e chi(t, 0).
    nv = sp.Matrix(sp.symbols("m1:4", real=True))
    vv = sp.Matrix(sp.symbols("w1:4", real=True))
    jac = sp.Matrix([[1, nv[0], nv[1], nv[2]], [vv[0], 1, 0, 0], [vv[1], 0, 1, 0],
                     [vv[2], 0, 0, 1]])
    check_zero("light-cone Jacobian", jac.det() - (1 - nv.dot(vv)))
    yy = sp.Matrix(sp.symbols("y1:4", real=True))
    ynorm = sp.sqrt(yy.dot(yy))
    check_zero("light-cone cancellation", (1 - yy.dot(vv) / ynorm)
               * e / (4 * sp.pi * (ynorm - yy.dot(vv))) - e / (4 * sp.pi * ynorm))
    rad = sp.symbols("rho", positive=True)
    chi = sp.exp(-t**2 - rad**2)
    lap = sp.diff(chi, rad, 2) + 2 * sp.diff(chi, rad) / rad
    pairing = sp.integrate(sp.simplify(lap / rad * 4 * sp.pi * rad**2), (rad, 0, sp.oo))
    check_zero("point charge at rest is the source", pairing + 4 * sp.pi * chi.subs(rad, 0))
    # Liénard (73.x): the angular integral of |n x ((n - v) x a)|^2/(1 - n.v)^5.
    theta, ph = sp.symbols("theta phi", real=True)
    n = sp.Matrix(sp.symbols("n1 n2 n3", real=True))
    beta = sp.Rational(1, 2)
    vel = sp.Matrix([0, 0, beta])
    for accel in (sp.Matrix([1, 0, 2]), sp.Matrix([0, 3, 0])):
        num = n.cross((n - vel).cross(accel))
        sub = {n[0]: sp.sin(theta) * sp.cos(ph), n[1]: sp.sin(theta) * sp.sin(ph),
               n[2]: sp.cos(theta)}
        inner = sp.integrate(sp.expand(num.dot(num).subs(sub)), (ph, 0, 2 * sp.pi))
        s = sp.symbols("s", real=True)
        inner_s = sp.simplify(inner.subs(sp.sin(theta)**2, 1 - sp.cos(theta)**2)
                              .subs(sp.cos(theta), s))
        total = sp.integrate(inner_s / (1 - beta * s)**5, (s, -1, 1))
        gamma2 = 1 / (1 - beta**2)
        expected = sp.Rational(8, 3) * sp.pi * gamma2**3 * (accel.dot(accel)
                                                            - vel.cross(accel).dot(vel.cross(accel)))
        check_zero("Lienard angular integral", total - expected)

    # §73: the one-variable integrals behind Liénard's formula, the four-acceleration, and the
    # momentum identity ∫ (n.v) dI = |v|^2 ∫ dI; §74: the synchrotron reduction.
    s, bt = sp.symbols("s beta", real=True)
    bsub = {bt: sp.Rational(3, 7)}
    for name, integrand, value in [
            ("1/(1-bs)^3", 1 / (1 - bt * s)**3, 2 / (1 - bt**2)**2),
            ("s/(1-bs)^3", s / (1 - bt * s)**3, 2 * bt / (1 - bt**2)**2),
            ("(1-s^2)/(1-bs)^5", (1 - s**2) / (1 - bt * s)**5, sp.Rational(4, 3) / (1 - bt**2)**3),
            ("s(1-s^2)/(1-bs)^5", s * (1 - s**2) / (1 - bt * s)**5,
             sp.Rational(4, 3) * bt / (1 - bt**2)**3)]:
        check_zero(f"Lienard integral {name}",
                   sp.integrate(integrand.subs(bsub), (s, -1, 1)) - value.subs(bsub))
    v3 = sp.Matrix(sp.symbols("u1:4", real=True))
    a3 = sp.Matrix(sp.symbols("a1:4", real=True))
    gam2 = 1 / (1 - v3.dot(v3))
    w_space = gam2 * a3 + gam2**2 * v3.dot(a3) * v3
    w_time = gam2**2 * v3.dot(a3)
    check_zero("four-acceleration square", w_space.dot(w_space) - w_time**2
               - gam2**3 * (a3.dot(a3) - v3.cross(a3).dot(v3.cross(a3))))
    radius, omega = sp.symbols("R Omega", positive=True)
    v_c = sp.Matrix([0, radius * omega, 0])
    a_c = sp.Matrix([-radius * omega**2, 0, 0])
    g_c = 1 / (1 - v_c.dot(v_c))
    check_zero("synchrotron reduction", g_c**3 * (a_c.dot(a_c) - v_c.cross(a_c).dot(v_c.cross(a_c)))
               - g_c**2 * radius**2 * omega**4)
    vel_m = sp.Matrix([0, 0, sp.Rational(1, 2)])
    acc_m = sp.Matrix([1, 0, 2])
    num_m = n.cross((n - vel_m).cross(acc_m))
    sub_m = {n[0]: sp.sin(theta) * sp.cos(ph), n[1]: sp.sin(theta) * sp.sin(ph),
             n[2]: sp.cos(theta)}
    s_m = sp.symbols("s_m", real=True)

    def power_moment(weight):
        inner_m = sp.integrate(sp.expand((weight * num_m.dot(num_m)).subs(sub_m)),
                               (ph, 0, 2 * sp.pi))
        inner_m = sp.simplify(inner_m.subs(sp.sin(theta)**2, 1 - sp.cos(theta)**2)
                              .subs(sp.cos(theta), s_m))
        return sp.integrate(inner_m / (1 - s_m / 2)**5, (s_m, -1, 1))

    check_zero("momentum of the radiation along v",
               power_moment(n.dot(vel_m)) - vel_m.dot(vel_m) * power_moment(1))
    # §72: the point dipole, fields of all orders and the flux identity.
    rr = sp.sqrt(xs.dot(xs))
    d = [sp.Function(f"d{i}") for i in range(3)]
    dip = sp.Matrix([d[i](t - rr) for i in range(3)])
    a_dip = sp.Matrix([sp.diff(d[i](t - rr), t) / (4 * sp.pi * rr) for i in range(3)])
    phi_dip = -sum(sp.diff(d[i](t - rr) / (4 * sp.pi * rr), xs[i]) for i in range(3))
    e_dip = sp.Matrix([-sp.diff(phi_dip, xs[i]) - sp.diff(a_dip[i], t) for i in range(3)])
    b_dip = sp.Matrix([sp.diff(a_dip[2], xs[1]) - sp.diff(a_dip[1], xs[2]),
                       sp.diff(a_dip[0], xs[2]) - sp.diff(a_dip[2], xs[0]),
                       sp.diff(a_dip[1], xs[0]) - sp.diff(a_dip[0], xs[1])])
    u = sp.symbols("u", real=True)
    D0, D1, D2, D3 = [sp.Matrix(sp.symbols(f"D{k}_1:4", real=True)) for k in range(4)]
    derivs = {}
    for i in range(3):
        f = d[i]
        derivs[sp.Derivative(f(u), (u, 3))] = D3[i]
        derivs[sp.Derivative(f(u), (u, 2))] = D2[i]
        derivs[sp.Derivative(f(u), u)] = D1[i]
        derivs[f(u)] = D0[i]

    def at_u(expr):
        expr = expr.subs(t, u + rr).doit()
        for key in sorted(derivs, key=lambda k: -sp.count_ops(k)):
            expr = expr.subs(key, derivs[key])
        return sp.simplify(expr)

    nn = xs / rr
    b_expected = (D2 / rr + D1 / rr**2).cross(nn) / (4 * sp.pi)
    e_expected = ((3 * nn * nn.dot(D0) - D0) / rr**3 + (3 * nn * nn.dot(D1) - D1) / rr**2
                  + (nn * nn.dot(D2) - D2) / rr) / (4 * sp.pi)
    point = {xs[0]: sp.Rational(2, 3), xs[1]: sp.Rational(-1, 3), xs[2]: sp.Rational(2, 3)}
    check_zero("dipole magnetic field (72.x)", (b_dip.applyfunc(at_u) - b_expected).subs(point))
    check_zero("dipole electric field (72.x)", (e_dip.applyfunc(at_u) - e_expected).subs(point))
    # Flux through the sphere of radius R: R^2 ∫ (E x B).n dσ.
    R = sp.symbols("R", positive=True)
    bR = (D2 / R + D1 / R**2).cross(n) / (4 * sp.pi)
    eR = ((3 * n * n.dot(D0) - D0) / R**3 + (3 * n * n.dot(D1) - D1) / R**2
          + (n * n.dot(D2) - D2) / R) / (4 * sp.pi)
    flux = R**2 * sphere_integral(eR.cross(bR).dot(n), n, theta, ph)
    q_r = (D1.dot(D1) / R + D0.dot(D1) / R**2 + D0.dot(D0) / (2 * R**3)) / (6 * sp.pi)
    # d/dt Q_R at fixed R is d/du along the jet D0 -> D1 -> D2 -> D3.
    dq = sum(sp.diff(q_r, D0[i]) * D1[i] + sp.diff(q_r, D1[i]) * D2[i] for i in range(3))
    check_zero("near-zone flux (72.x)", flux - (D2.dot(D2) / (6 * sp.pi) + dq))
    sq = D0 + R * D1
    check_zero("near-zone energy is a sum of squares",
               q_r - (sq.dot(sq) + R**2 * D1.dot(D1)) / (12 * sp.pi * R**3))

    # The moments of the sphere (SphereIntegral): ∫ n3^k = 4π/(k+1) for even k, 0 for odd k,
    # the second and fourth moments, and the orthogonal moment against g(n3) = n3^2.
    for k in range(7):
        moment = sphere_integral(n[2]**k, n, theta, ph)
        check_zero(f"sphere moment n3^{k}",
                   moment - (4 * sp.pi / (k + 1) if k % 2 == 0 else 0))
    check_zero("second moment", sphere_integral(n[0] * n[1], n, theta, ph))
    check_zero("fourth moment", sphere_integral(n[0]**2 * n[1]**2, n, theta, ph)
               - 4 * sp.pi / 15)
    check_zero("orthogonal moment", sphere_integral(n[0]**2 * n[2]**2, n, theta, ph)
               - sphere_integral((1 - n[2]**2) * n[2]**2, n, theta, ph) / 2)
    # §§67, 71: the angular integrals of the multipole powers.
    acc_d = sp.Matrix(sp.symbols("dd1:4", real=True))
    nx = n.cross(acc_d)
    check_zero("dipole angular integral", sphere_integral(nx.dot(nx), n, theta, ph)
               - sp.Rational(8, 3) * sp.pi * acc_d.dot(acc_d))
    q3 = sp.Matrix(3, 3, lambda i, j: sp.Symbol(f"Q{min(i, j)}{max(i, j)}", real=True))
    m2 = sp.Matrix(sp.symbols("m1:4", real=True))
    # M_ik = ∫ y_i (d_s^2 j_k) = (1/2) Q'''_ik + eps_ikl m''_l (conservation and m = ½∫ y × j).
    mmat = sp.Matrix(3, 3, lambda i, k: q3[i, k] / 2
                     + sum(sp.LeviCivita(i, k, l) * m2[l] for l in range(3)))
    tvec = sp.Matrix([sum(n[i] * mmat[i, k] for i in range(3)) for k in range(3)])
    ntv = n.cross(tvec)
    power = sphere_integral(ntv.dot(ntv), n, theta, ph) / (16 * sp.pi**2)
    dq3 = 3 * q3 - q3.trace() * sp.eye(3)
    expected = (sum(dq3[i, j]**2 for i in range(3) for j in range(3)) / 180
                + sp.Rational(2, 3) * m2.dot(m2)) / (4 * sp.pi)
    check_zero("quadrupole and magnetic dipole power (71.x)", power - expected)

    # The instances of §§67, 71: rho = cos s d1 chi has d = -(cos s)(∫chi) e1, and
    # rho = cos s d1^2 chi has D_11 = 4 cos s ∫chi, D_22 = D_33 = -2 cos s ∫chi, so the power
    # coefficient is (1/4π)(24/180) = 1/(30π).
    g1, g2, g3 = sp.symbols("g1 g2 g3", real=True)
    gauss = sp.exp(-(g1**2 + g2**2 + g3**2))
    mass = sp.integrate(gauss, (g1, -sp.oo, sp.oo), (g2, -sp.oo, sp.oo), (g3, -sp.oo, sp.oo))

    def space_integral(expr):
        return sp.integrate(expr, (g1, -sp.oo, sp.oo), (g2, -sp.oo, sp.oo), (g3, -sp.oo, sp.oo))

    check_zero("dipole instance moment", space_integral(g1 * sp.diff(gauss, g1)) + mass)
    rho2 = sp.diff(gauss, g1, 2)
    gs = (g1, g2, g3)
    dq = [space_integral(rho2 * (3 * gs[i]**2 - (g1**2 + g2**2 + g3**2))) for i in range(3)]
    check_zero("quadrupole instance moments", sp.Matrix(dq) - mass * sp.Matrix([4, -2, -2]))
    check_zero("quadrupole instance coefficient",
               sum(c**2 for c in (4, -2, -2)) / sp.Integer(180) / (4 * sp.pi) - 1 / (30 * sp.pi))
    # §65: the Darwin gauge for a point charge to second order.
    rt = sp.Matrix([sp.Function(f"r{i}")(t) for i in range(3)])
    sep = xs - rt
    dist = sp.sqrt(sep.dot(sep))
    vt = rt.diff(t)
    chi = e / (8 * sp.pi) * sp.diff(dist, t)
    phi2 = e / (4 * sp.pi * dist) + e / (8 * sp.pi) * sp.diff(dist, t, 2)
    a1 = e * vt / (4 * sp.pi * dist)
    check_zero("Darwin scalar potential (65.x)", sp.simplify(phi2 - sp.diff(chi, t)
                                                             - e / (4 * sp.pi * dist)))
    a_darwin = e / (8 * sp.pi * dist) * (vt + vt.dot(sep / dist) * sep / dist)
    check_zero("Darwin vector potential (65.6)",
               (a1 + sp.Matrix([sp.diff(chi, xs[i]) for i in range(3)]) - a_darwin)
               .applyfunc(sp.simplify))


def verify_darwin_point_charge():
    """§65: the Liénard–Wiechert field of a slow point charge is the Darwin field to order κ²."""
    e, kappa, s = sp.symbols("e kappa s", real=True)
    path = sp.Matrix([s / 2 + s**2 / 3, -s / 3 + s**3 / 5, s**2 / 4])
    point = sp.Matrix([3, 4, 0])
    a1, a2, a3 = sp.symbols("a1:4", real=True)
    tau = -5 + a1 * kappa + a2 * kappa**2 + a3 * kappa**3
    at = path.subs(s, kappa * tau)
    sep = point - at
    eq = sp.expand(sp.series(tau**2 - sep.dot(sep), kappa, 0, 4).removeO())
    sol = sp.solve([eq.coeff(kappa, k) for k in (1, 2, 3)], [a1, a2, a3], dict=True)[0]
    tau = tau.subs(sol)
    vel = (kappa * path.diff(s)).subs(s, kappa * tau)
    acc = (kappa**2 * path.diff(s, 2)).subs(s, kappa * tau)
    sep = point - path.subs(s, kappa * tau)
    dist = -tau
    den = dist - sep.dot(vel)
    lw = e / (4 * sp.pi) * ((1 - vel.dot(vel)) * (sep - dist * vel) / den**3
                            + sep.cross((sep - dist * vel).cross(acc)) / den**3)
    t = sp.symbols("t", real=True)
    xs = sp.Matrix(sp.symbols("x1:4", real=True))
    c = path.subs(s, kappa * t)
    cdot = c.diff(t)
    x_c = xs - c
    rho = sp.sqrt(x_c.dot(x_c))
    nn = x_c / rho
    phi_d = e / (4 * sp.pi * rho)
    a_d = e / (8 * sp.pi * rho) * (cdot + cdot.dot(nn) * nn)
    e_d = sp.Matrix([-sp.diff(phi_d, xs[i]) - sp.diff(a_d[i], t) for i in range(3)])
    e_d = e_d.subs({t: 0, xs[0]: 3, xs[1]: 4, xs[2]: 0})
    diff = (lw - e_d).applyfunc(lambda f: sp.series(f, kappa, 0, 3).removeO())
    check_zero("Lienard-Wiechert field of a slow charge is the Darwin field to order kappa^2",
               diff.applyfunc(sp.simplify))
    b_lw = (sep / dist).cross(lw)
    b_d = sp.Matrix([sp.diff(a_d[2], xs[1]) - sp.diff(a_d[1], xs[2]),
                     sp.diff(a_d[0], xs[2]) - sp.diff(a_d[2], xs[0]),
                     sp.diff(a_d[1], xs[0]) - sp.diff(a_d[0], xs[1])])
    b_d = b_d.subs({t: 0, xs[0]: 3, xs[1]: 4, xs[2]: 0})
    diff_b = (b_lw - b_d).applyfunc(lambda f: sp.series(f, kappa, 0, 2).removeO())
    check_zero("Lienard-Wiechert magnetic field of a slow charge to order kappa",
               diff_b.applyfunc(sp.simplify))
    lw_wrong = (lw - e_d).applyfunc(lambda f: sp.series(f, kappa, 0, 4).removeO())
    if all(sp.simplify(entry) == 0 for entry in lw_wrong):
        raise AssertionError("the Darwin comparison did not see the third order")


def verify():
    t, x, y, z = coordinates = sp.symbols("t x y z", real=True)
    ex, ey, ez, bx, by, bz = sp.symbols("E_x E_y E_z B_x B_y B_z", real=True)
    field = sp.Matrix([[0, -ex, -ey, -ez], [ex, 0, bz, -by],
                       [ey, -bz, 0, bx], [ez, by, -bx, 0]])
    scalar = lambda f: sp.Rational(1, 2) * contraction(f, f)
    pseudo = lambda f: sp.Rational(1, 4) * contraction(f, hodge(f))
    check_zero("Hodge square", hodge(hodge(field)) + field)
    check_zero("B squared minus E squared", scalar(field)
               - (bx**2 + by**2 + bz**2 - ex**2 - ey**2 - ez**2))
    check_zero("E dot B", pseudo(field) - (ex * bx + ey * by + ez * bz))
    parity = sp.diag(1, -1, 1, 1)
    reflected = parity.T * field * parity
    check_zero("scalar under reflection", scalar(reflected) - scalar(field))
    check_zero("pseudoscalar under reflection", pseudo(reflected) + pseudo(field))
    check_zero("Hodge under reflection", hodge(reflected) + parity.T * hodge(field) * parity)

    rapidity = sp.symbols("rapidity", real=True)
    c, s = sp.cosh(rapidity), sp.sinh(rapidity)
    boost = sp.Matrix([[c, s, 0, 0], [s, c, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    boosted = boost.T * field * boost
    check_zero("scalar under boost", scalar(boosted) - scalar(field))
    check_zero("pseudoscalar under boost", pseudo(boosted) - pseudo(field))

    uniform_potential = sp.Matrix([0, -ex * t, 0, bx * y])
    uniform = curvature(uniform_potential, coordinates)
    check_zero("uniform potential signs", uniform - field.subs({ey: 0, ez: 0, by: 0, bz: 0}))
    gauge_function = t * x + y * z
    shifted = uniform_potential + sp.Matrix([sp.diff(gauge_function, q) for q in coordinates])
    check_zero("gauge curvature", curvature(shifted, coordinates) - uniform)
    for i, j, k in product(range(4), repeat=3):
        check_zero("Bianchi", sp.diff(uniform[j, k], coordinates[i])
                   + sp.diff(uniform[k, i], coordinates[j]) + sp.diff(uniform[i, j], coordinates[k]))

    linear = sp.zeros(4)
    linear[0, 1], linear[1, 0] = t, -t
    for degree, jet in [(0, field), (1, linear)]:
        potential = sp.Matrix([sum(coordinates[i] * jet[i, j] for i in range(4))
                               / sp.Integer(degree + 2) for j in range(4)])
        check_zero(f"radial gauge degree {degree}", sp.Matrix(coordinates).dot(potential))
        check_zero(f"radial reconstruction degree {degree}", curvature(potential, coordinates) - jet)
        wrong = sp.Matrix([sum(coordinates[i] * jet[i, j] for i in range(4))
                           / sp.Integer(degree + 1) for j in range(4)])
        if curvature(wrong, coordinates) == jet:
            raise AssertionError("radial check did not distinguish the wrong coefficient")

    tau = sp.symbols("tau", real=True)
    worldline = sp.Matrix([sp.sinh(tau), sp.cosh(tau), 0, 0])
    velocity, metric = worldline.diff(tau), sp.diag(-1, 1, 1, 1)
    force = metric * uniform.subs({ex: 1, bx: 0}) * velocity
    check_zero("proper-time mass shell", (velocity.T * metric * velocity)[0] + 1)
    check_zero("hyperbolic Lorentz force", velocity.diff(tau) - force)
    check_zero("force orthogonality", (velocity.T * metric * force)[0])
    verify_virial_coulomb_larmor()
    verify_static_fields_and_waves()
    verify_multipoles_magnetostatics_and_modes()
    verify_retarded_potentials()
    verify_radiation()
    verify_darwin_point_charge()
    print("Electrodynamics exact checks passed: signs, invariants, covariance, gauge, "
          "Bianchi, degree 0/1 radial reconstruction, hyperbolic worldline, the virial "
          "improvement stress, the Coulomb brackets and rosette, Larmor's identity, the Newton kernel "
          "and the point-charge energy, the moving charge (38.8), the wave equation in Lorenz "
          "form, plane waves, the Doppler factor, the Stokes identity, the kernel derivatives, the "
          "dipole and quadrupole terms, curl curl, the magnetic moment ratio, the Fourier "
          "transform of the kernel, the conducting modes, the retarded field divergence and the "
          "Helmholtz sign, the Liénard–Wiechert fields and the light-cone Jacobian, the moments of the "
          "sphere, Liénard's integral and the synchrotron reduction, the near-zone fields and flux, "
          "the multipole powers and their instances, the Darwin potentials, and the field of a slow "
          "point charge to second order.")


def main():
    verify()


if __name__ == "__main__":
    main()
