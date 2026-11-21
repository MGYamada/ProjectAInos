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


def verify_geometrical_optics():
    """The eikonal expansion, the intensity of a spherical wave, the Riccati law of the curvature
    and the amplitude at a focal point (§§53–58)."""
    t, x, y, z, eps = sp.symbols("t x y z epsilon", real=True)
    coords = (t, x, y, z)
    a, b, psi = [sp.Function(name)(*coords) for name in ("a", "b", "psi")]

    def wave(f):
        return sp.diff(f, t, 2) - sum(sp.diff(f, v, 2) for v in (x, y, z))

    def pair(f, g):
        return sp.diff(f, t) * sp.diff(g, t) - sum(sp.diff(f, v) * sp.diff(g, v) for v in (x, y, z))

    c, s = sp.cos(psi / eps), sp.sin(psi / eps)
    check_zero("high-frequency expansion of a cos", wave(a * c)
               - (-(pair(psi, psi) * a * c) / eps**2
                  - (2 * pair(a, psi) + a * wave(psi)) * s / eps + wave(a) * c))
    check_zero("high-frequency expansion of b sin", wave(b * s)
               - (-(pair(psi, psi) * b * s) / eps**2
                  + (2 * pair(b, psi) + b * wave(psi)) * c / eps + wave(b) * s))
    # §§53, 58: the outgoing spherical phase t - r is null with box (t - r) = 2/r, the shell
    # g(t - r)/r is exact and transported; the quarter shift exchanges the pair of waves, whose
    # gradient energies add without oscillating terms; a localized plane wave has box a = -Δ⊥ f.
    g = sp.Function("g")
    rr = sp.sqrt(x**2 + y**2 + z**2)
    phase = t - rr
    shell = g(t - rr) / rr
    check_zero("null spherical phase", sp.simplify(pair(phase, phase)))
    check_zero("box of the spherical phase", sp.simplify(wave(phase) - 2 / rr))
    check_zero("exact spherical shell", sp.simplify(wave(shell)))
    check_zero("transport of the spherical shell",
               sp.simplify(2 * pair(shell, phase) + shell * wave(phase)))
    check_zero("quarter shift of the phase",
               sp.simplify(a * sp.cos((psi + eps * sp.pi / 2) / eps)
                           + b * sp.sin((psi + eps * sp.pi / 2) / eps) - (b * c - a * s)))
    w1 = a * c + b * s
    w2 = b * c - a * s
    for v in coords:
        lhs = sp.diff(w1, v)**2 + sp.diff(w2, v)**2
        rhs = ((a**2 + b**2) * sp.diff(psi, v)**2 / eps**2
               + 2 * (b * sp.diff(a, v) - a * sp.diff(b, v)) * sp.diff(psi, v) / eps
               + sp.diff(a, v)**2 + sp.diff(b, v)**2)
        check_zero(f"pair energy along {v}", sp.simplify(sp.expand(lhs - rhs)))
    f3 = sp.Function("f")
    plane = f3(x - t, y, z)
    check_zero("transport of a plane wave", sp.simplify(sp.diff(plane, t) + sp.diff(plane, x)))
    check_zero("diffraction source of a plane wave",
               sp.simplify(wave(plane) + sp.diff(plane, y, 2) + sp.diff(plane, z, 2)))
    # §53: the complete integral of the linear-gradient medium n^2 = n0^2 + 2 g z solves
    # S_sigma + (|grad S|^2 - n^2)/2 = 0, with rays q = beta + alpha sigma + g sigma^2 e3/2.
    al = sp.Matrix(sp.symbols("alpha1:4", real=True))
    sg, n0s, gg = sp.symbols("sigma n0sq g", real=True)
    qv = sp.Matrix([x, y, z])
    action = (al.dot(qv) + gg * sg * z - (al.dot(al) - n0s) * sg / 2 - gg * al[2] * sg**2 / 2
              - gg**2 * sg**3 / 6)
    grad_s = sp.Matrix([sp.diff(action, v) for v in (x, y, z)])
    check_zero("Hamilton-Jacobi equation of the linear-gradient medium",
               sp.expand(sp.diff(action, sg) + (grad_s.dot(grad_s) - n0s - 2 * gg * z) / 2))
    # §54: a spherical wave psi = |x| (static eikonal |grad psi| = 1) has intensity 1/|x|^2,
    # and transport 2 grad a . grad psi + a Laplacian psi = 0 holds for a = 1/|x|.
    r = sp.sqrt(x**2 + y**2 + z**2)
    grad = lambda f: sp.Matrix([sp.diff(f, v) for v in (x, y, z)])
    lap = lambda f: sum(sp.diff(f, v, 2) for v in (x, y, z))
    check_zero("static eikonal of a spherical wave", grad(r).dot(grad(r)) - 1)
    flux = grad(r) / r**2
    check_zero("intensity of a spherical wave", sum(sp.diff(flux[i], v)
                                                    for i, v in enumerate((x, y, z))))
    check_zero("transport of a spherical wave", 2 * grad(1 / r).dot(grad(r)) + lap(r) / r)
    # §56: the curvature of the front obeys H' = -H^2 with H(l) = H0 (1 + l H0)^(-1), and the
    # Hessian of |x| along the ray x0 + l n is that law with H0 the Hessian at x0.
    l = sp.symbols("l", positive=True)
    h0 = sp.Matrix(3, 3, lambda i, j: sp.Symbol(f"h{min(i, j)}{max(i, j)}", real=True))
    hl = h0 * (sp.eye(3) + l * h0).inv()
    check_zero("Riccati law of the curvature", sp.simplify(hl.diff(l) + hl * hl))
    hess = sp.Matrix(3, 3, lambda i, j: sp.diff(r, (x, y, z)[i], (x, y, z)[j]))
    x0 = sp.Matrix([sp.Rational(3, 13), sp.Rational(4, 13), sp.Rational(12, 13)])
    ray = {x: x0[0] * (1 + l), y: x0[1] * (1 + l), z: x0[2] * (1 + l)}
    h_at = hess.subs({x: x0[0], y: x0[1], z: x0[2]})
    check_zero("Hessian of the eikonal along a ray",
               (hess.subs(ray) - h_at * (sp.eye(3) + l * h_at).inv()).applyfunc(sp.simplify))
    # The amplitude a(l) = det(1 + l H0)^(-1/2) solves 2 a' + tr(H) a = 0, and for a converging
    # spherical front (H0 = -(1/R) on the transverse plane) it diverges at l = R.
    rad = sp.symbols("R", positive=True)
    h_conv = sp.diag(-1 / rad, -1 / rad, 0)
    det = (sp.eye(3) + l * h_conv).det()
    amp = det**sp.Rational(-1, 2)
    h_l = h_conv * (sp.eye(3) + l * h_conv).inv()
    check_zero("transport of the amplitude along a ray", sp.simplify(2 * amp.diff(l)
                                                                      + h_l.trace() * amp))
    check_zero("amplitude of a converging front", sp.simplify(amp**2 * (1 - l / rad)**2 - 1))
    if sp.limit(1 / (1 - l / rad)**2, l, rad, dir="-") != sp.oo:
        raise AssertionError("the amplitude should diverge at the focal point")

    # §56: Jacobi's formula d/dl log det(1 + l H0) = tr(H0 (1 + l H0)^(-1)), and the cylinder
    # psi = -|P(x - c)| (P the projection across the axis e3) has det(1 + l H0) = 1 - l/rho.
    hq = sp.Matrix([[sp.Rational(1, 2), sp.Rational(1, 3), 0], [sp.Rational(1, 3), -1, 2],
                    [0, 2, sp.Rational(1, 5)]])
    check_zero("Jacobi's formula", sp.simplify(sp.diff(sp.log((sp.eye(3) + l * hq).det()), l)
                                               - (hq * (sp.eye(3) + l * hq).inv()).trace()))
    cyl = -sp.sqrt(x**2 + y**2)
    hess_c = sp.Matrix(3, 3, lambda i, j: sp.diff(cyl, (x, y, z)[i], (x, y, z)[j]))
    pt = {x: sp.Rational(3, 5), y: sp.Rational(4, 5), z: 7}
    check_zero("focal line of a cylindrical front",
               sp.simplify((sp.eye(3) + l * hess_c.subs(pt)).det() - (1 - l)))
    check_zero("Laplacian of a cylindrical front", sp.simplify(lap(cyl).subs(pt) + 1))
    # §55: the paraxial point eikonal psi = (a r^2 - 2b r r' + c r'^2)/2 has the momenta
    # p = b r' - a r, p' = c r' - b r; its angular eikonal f = (c p^2 - 2b p p' + a p'^2)/(2D),
    # D = b^2 - ac, has df/dp = r and df/dp' = -r'; the ray-transfer matrix has determinant 1;
    # and the exact free propagation (r, p) -> (r + L p/sqrt(1 - p^2), p) is symplectic.
    pa, pb, pc = sp.symbols("a_p b_p c_p", real=True)
    r1, r2 = sp.symbols("r r'", real=True)
    p1, p2 = sp.symbols("p p'", real=True)
    dd = pb**2 - pa * pc
    sol = sp.solve([sp.Eq(p1, pb * r2 - pa * r1), sp.Eq(p2, pc * r2 - pb * r1)], [r1, r2],
                   dict=True)[0]
    f_ang = (pc * p1**2 - 2 * pb * p1 * p2 + pa * p2**2) / (2 * dd)
    check_zero("angular eikonal, entry", sp.simplify(sp.diff(f_ang, p1) - sol[r1]))
    check_zero("angular eikonal, exit", sp.simplify(sp.diff(f_ang, p2) + sol[r2]))
    psi_pt = (pa * r1**2 - 2 * pb * r1 * r2 + pc * r2**2) / 2
    check_zero("angular eikonal is the Legendre transform",
               sp.simplify((psi_pt - p2 * r2 + p1 * r1).subs(sol) - f_ang))
    abcd = sp.Matrix([[pa / pb, 1 / pb], [(pa * pc - pb**2) / pb, pc / pb]])
    check_zero("ray-transfer matrix is unimodular", sp.simplify(abcd.det() - 1))
    big_l = sp.symbols("L", positive=True)
    q1, q2, m1, m2 = sp.symbols("q1 q2 m1 m2", real=True)
    root = sp.sqrt(1 - m1**2 - m2**2)
    image = sp.Matrix([q1 + big_l * m1 / root, q2 + big_l * m2 / root, m1, m2])
    jfree = image.jacobian([q1, q2, m1, m2])
    omega = sp.Matrix([[0, 0, -1, 0], [0, 0, 0, -1], [1, 0, 0, 0], [0, 1, 0, 0]])
    check_zero("free propagation is symplectic", (jfree.T * omega * jfree - omega)
               .applyfunc(sp.simplify))
    # §57: the optical Lagrangian n|v| has momentum n v/|v| and vanishing energy p.v - L; the
    # reparametrized segments have a constant unit tangent and the length n0 |P' - P|; a
    # similarity x -> k R x + c has |D phi v| = k |v|, and an inversion does not.
    vs = sp.Matrix(sp.symbols("v1:4", real=True))
    n0 = sp.symbols("n0", positive=True)
    speed = sp.sqrt(vs.dot(vs))
    lag = n0 * speed
    mom = sp.Matrix([sp.diff(lag, v) for v in vs])
    check_zero("optical momentum", mom - n0 * vs / speed)
    check_zero("optical energy", sp.simplify(mom.dot(vs) - lag))
    ep, tt = sp.symbols("varepsilon tau", real=True)
    pp = sp.Matrix([1, 2, 2])
    seg = (tt + ep * tt * (1 - tt)) * pp
    vel = seg.diff(tt)
    check_zero("segment unit tangent", (vel / (1 + ep * (1 - 2 * tt)) - pp))
    length = sp.integrate(n0 * 3 * (1 + ep * (1 - 2 * tt)), (tt, 0, 1))
    check_zero("segment optical length", length - 3 * n0)
    k = sp.symbols("k", positive=True)
    th = sp.symbols("theta", real=True)
    rot = sp.Matrix([[sp.cos(th), -sp.sin(th), 0], [sp.sin(th), sp.cos(th), 0], [0, 0, 1]])
    xs3 = sp.Matrix(sp.symbols("q1:4", real=True))
    sim = k * rot * xs3 + sp.Matrix([1, 2, 3])
    jac = sim.jacobian(xs3)
    check_zero("similarity scales lengths", sp.simplify((jac * vs).dot(jac * vs)
                                                        - k**2 * vs.dot(vs)))
    inv = xs3 / xs3.dot(xs3)
    jinv = inv.jacobian(xs3)
    ratio = sp.simplify((jinv * vs).dot(jinv * vs) / vs.dot(vs))
    if sp.simplify(sp.diff(ratio, xs3[0])) == 0:
        raise AssertionError("an inversion should have a varying ratio")


def verify_diffraction_scattering_and_gravitational_radiation():
    """Diffraction (§§59-61), scattering (§§78-80), focusing (§119), the charges at infinity
    (§105) and the quadrupole formula (§110)."""
    x, y, z, k = sp.symbols("x y z k", real=True)
    rr = sp.sqrt(x**2 + y**2 + z**2)
    green = sp.exp(sp.I * k * rr) / (4 * sp.pi * rr)
    kernel = z * sp.exp(sp.I * k * rr) * (1 - sp.I * k * rr) / (2 * sp.pi * rr**3)
    check_zero("Rayleigh-Sommerfeld kernel", sp.simplify(-2 * sp.diff(green, z) - kernel))
    lap = sum(sp.diff(kernel, v, 2) for v in (x, y, z))
    check_zero("Helmholtz equation of the kernel", sp.simplify(lap + k**2 * kernel))
    r = sp.symbols("r", positive=True)
    check_zero("Poisson kernel mass", sp.integrate(r * (r**2 + 1)**sp.Rational(-3, 2),
                                                   (r, 0, sp.oo)) - 1)
    s, zp, big_d = sp.symbols("s z_p D", positive=True)
    radius = sp.sqrt(s**2 + zp**2)
    primitive = -zp * sp.exp(sp.I * k * radius) / (2 * sp.pi * radius)
    check_zero("primitive of the kernel on the plane",
               sp.simplify(sp.diff(primitive, s)
                           - s * zp * sp.exp(sp.I * k * radius) * (1 - sp.I * k * radius)
                           / (2 * sp.pi * radius**3)))
    nz = sp.symbols("n_z", positive=True)
    point = big_d * sp.exp(-sp.I * k * big_d) * (big_d * nz) * sp.exp(sp.I * k * big_d) * (
        1 - sp.I * k * big_d) / (2 * sp.pi * big_d**3)
    check_zero("Fraunhofer field of a point aperture",
               sp.simplify(point - nz * (1 - sp.I * k * big_d) / (2 * sp.pi * big_d)))
    # §78: Thomson's cross section and its angular distribution.
    e, m, e0, w, t = sp.symbols("e m E_0 omega t", positive=True)
    accel = e / m * e0 * sp.cos(w * t)
    mean = lambda f: w / (2 * sp.pi) * sp.integrate(f, (t, 0, 2 * sp.pi / w))
    power = mean(sp.Rational(2, 3) * e**2 / (4 * sp.pi) * accel**2)
    sigma_t = sp.Rational(8, 3) * sp.pi * (e**2 / (4 * sp.pi * m))**2
    check_zero("Thomson cross section", sp.simplify(power / (e0**2 / 2) - sigma_t))
    th, ph = sp.symbols("theta phi", real=True)
    check_zero("angular distribution of Thomson scattering",
               sp.integrate(sp.sin(th)**2 * sp.sin(th), (th, 0, sp.pi), (ph, 0, 2 * sp.pi))
               - sp.Rational(8, 3) * sp.pi)
    # §79: the steady response of the damped bound charge.
    g, w0 = sp.symbols("gamma omega_0", positive=True)
    amp_c, amp_s = sp.symbols("A B", real=True)
    xs = amp_c * sp.cos(w * t) + amp_s * sp.sin(w * t)
    eq = sp.expand(sp.diff(xs, t, 2) + 2 * g * sp.diff(xs, t) + w0**2 * xs - sp.cos(w * t))
    sol = sp.solve([eq.coeff(sp.cos(w * t)), eq.coeff(sp.sin(w * t))], [amp_c, amp_s])
    check_zero("bound-charge response", sp.simplify(sol[amp_c]**2 + sol[amp_s]**2
                                                    - 1 / ((w0**2 - w**2)**2 + 4 * g**2 * w**2)))
    # §§75, 76: the runaway solution, the damping of the reduced oscillator, the work of the
    # damping force, and the Lorentz-Dirac force along u = (cosh f, sinh f, 0, 0).
    kk = sp.Rational(2, 3) * e**2 / (4 * sp.pi)
    vel_run = kk / m * (sp.exp(m / kk * t) - 1)
    check_zero("runaway solution", sp.simplify(m * sp.diff(vel_run, t) - kk * sp.diff(vel_run, t, 2)))
    check_zero("damping of the reduced oscillator",
               sp.simplify(kk / m * w0**2 / 2 - e**2 * w0**2 / (12 * sp.pi * m)))
    vt = t**3 - 2 * t + sp.sin(t)
    lhs = sp.integrate(kk * sp.diff(vt, t, 2) * vt, (t, 0, 1))
    rhs = (-kk * sp.integrate(sp.diff(vt, t)**2, (t, 0, 1))
           + kk * (sp.diff(vt, t) * vt).subs(t, 1) - kk * (sp.diff(vt, t) * vt).subs(t, 0))
    check_zero("work of the damping force", sp.simplify(lhs - rhs))
    tau = sp.symbols("tau", real=True)
    rap = sp.Function("f")(tau)
    four_u = sp.Matrix([sp.cosh(rap), sp.sinh(rap), 0, 0])
    eta = sp.diag(-1, 1, 1, 1)
    acc2 = four_u.diff(tau, 2)
    ld = kk * (acc2 + (acc2.T * eta * four_u)[0] * four_u)
    check_zero("Lorentz-Dirac force is orthogonal", sp.simplify((ld.T * eta * four_u)[0]))
    check_zero("Lorentz-Dirac force of a hyperbola", sp.simplify(ld.subs(rap, 3 * tau)))
    # §119: Raychaudhuri for a diagonal Bianchi I metric, theta = sum H, shear = sum H^2 - theta^2/3.
    tt = sp.symbols("t", real=True)
    scales = [sp.Function(f"a{i}")(tt) for i in range(3)]
    hub = [sp.diff(a, tt) / a for a in scales]
    theta = sum(hub)
    shear = sum(hh**2 for hh in hub) - theta**2 / 3
    r00 = -sum(sp.diff(a, tt, 2) / a for a in scales)
    check_zero("Raychaudhuri for Bianchi I", sp.simplify(sp.diff(theta, tt) + theta**2 / 3
                                                         + shear + r00))
    gam = sp.Matrix([[2, 1, 0], [1, 2, 1], [0, 1, 3]])
    sym = sp.Matrix([[1, -2, 3], [-2, 0, 1], [3, 1, -1]])
    kap = gam.inv() * sym
    if (kap * kap).trace() - kap.trace()**2 / 3 < 0:
        raise AssertionError("trace inequality failed")
    # §105: the isotropic far metric diag(-(1 - 2M/r), (1 + 2M/r) δ) has
    # lambda^{00ab} = -(1 + 2M/r)^2 δ_ab, h^{00a} = 4M(1 + 2M/r) x_a/r^3 and the surface charge
    # (1/2) ∮ h^{00a} n_a dA = 8π M (1 + 2M/R).
    mass, rad = sp.symbols("M R", positive=True)
    cs = (x, y, z)
    lam = -(1 + 2 * mass / rr)**2
    h00 = [sp.diff(lam, v) for v in cs]
    check_zero("superpotential of the isotropic metric",
               (sp.Matrix(h00) - 4 * mass * (1 + 2 * mass / rr) * sp.Matrix(cs) / rr**3)
               .applyfunc(sp.simplify))
    flux_density = sp.simplify(sum(h00[i] * cs[i] / rr for i in range(3))).subs(
        {x: rad, y: 0, z: 0})
    check_zero("charge of the isotropic metric",
               sp.simplify(flux_density * 4 * sp.pi * rad**2 / 2
                           - 8 * sp.pi * mass * (1 + 2 * mass / rad)))
    # §110: the sphere integral of the transverse-traceless square and the binary.
    n = sp.Matrix(sp.symbols("n1:4", real=True))
    smat = sp.Matrix(3, 3, lambda i, j: sp.Symbol(f"S{min(i, j)}{max(i, j)}", real=True))
    proj = sp.eye(3) - n * n.T
    tt_part = proj * smat * proj - proj * (proj * smat).trace() / 2
    tt_sq = sum(tt_part[i, j]**2 for i in range(3) for j in range(3))
    quad = 3 * smat - smat.trace() * sp.eye(3)
    check_zero("sphere integral of the TT square",
               sp.simplify(sphere_integral(tt_sq, n, th, ph)
                           - sp.Rational(8, 45) * sp.pi * sum(quad[i, j]**2 for i in range(3)
                                                              for j in range(3))))
    mu, a_orb, om = sp.symbols("mu a Omega", positive=True)
    orbit = sp.Matrix([a_orb * sp.cos(om * tt), a_orb * sp.sin(om * tt), 0])
    moment = mu * orbit * orbit.T
    third = moment.diff(tt, 3)
    dq3 = 3 * third - third.trace() * sp.eye(3)
    check_zero("binary quadrupole", sp.simplify(sum(dq3[i, j]**2 for i in range(3)
                                                    for j in range(3))
                                                - 288 * mu**2 * a_orb**4 * om**6))
    kap_g = sp.symbols("kappa", positive=True)
    check_zero("binary power", kap_g / (360 * sp.pi) * 288 - sp.Rational(32, 5)
               * kap_g / (8 * sp.pi))


def verify_collisions_collapse_and_post_newtonian():
    """Collision radiation (§§68, 70), Tolman's collapse (§103), the 1PN Lagrangian (§106), the
    scalar modes of the flat dust universe (§115) and the Bianchi II bounce (§118)."""
    # §70: the period average of |a|^2 = k^2/r^4 on the Kepler ellipse r = p/(1 + e cos φ),
    # p = ℓ^2/k, with dt = r^2 dφ/ℓ and T = 2πℓ^3/(k^2 (1 - e^2)^(3/2)).
    k, ell, ecc, phi = sp.symbols("k ell epsilon phi", positive=True)
    semi = ell**2 / k
    radius = semi / (1 + ecc * sp.cos(phi))
    period = 2 * sp.pi * ell**3 / (k**2 * (1 - ecc**2)**sp.Rational(3, 2))
    average = sp.integrate(sp.expand((k**2 / radius**4) * radius**2 / ell), (phi, 0, 2 * sp.pi))
    check_zero("Kepler average of the squared acceleration",
               sp.simplify(average / period
                           - k**6 * (2 + ecc**2) * (1 - ecc**2)**sp.Rational(3, 2) / (2 * ell**8)))
    # §68: the effective radiation for repulsion, (2/9) e^2 v^3 a: with ρ = a s the integrand of
    # ∫ ΔE 2πρ dρ is e^2 v^3 a (−s + (s^2 + 3) arctan(s)/3)/s^4, whose primitive is
    # e^2 v^3 a (1/(3 s^2) − arctan(s)(1/(3s) + 1/(3 s^3))), from −(2/9) e^2 v^3 a at 0 to 0 at ∞.
    e, a, v, s = sp.symbols("e a v s", positive=True)
    check_zero("arccos form of the asymptotic angle",
               sp.simplify(sp.diff(sp.acos(1 / sp.sqrt(1 + s**2)), s) - sp.diff(sp.atan(s), s)))
    energy_s = (sp.Rational(2, 3) / (4 * sp.pi) * e**2 * v**3 * a**2
                * ((3 * a**2 + a**2 * s**2) * sp.atan(s) - 3 * a**2 * s) / (a * s)**5)
    integrand = energy_s * 2 * sp.pi * (a * s) * a
    primitive = e**2 * v**3 * a * (1 / (3 * s**2) - sp.atan(s) * (1 / (3 * s) + 1 / (3 * s**3)))
    check_zero("primitive of the effective radiation", sp.simplify(sp.diff(primitive, s) - integrand))
    eff = sp.limit(primitive, s, sp.oo) - sp.limit(primitive, s, 0, dir="+")
    check_zero("effective radiation for repulsion", sp.simplify(eff - sp.Rational(2, 9) * e**2
                                                                * v**3 * a))
    # §103: the parabolic solution r = (9F/4)^(1/3) (τ0 - τ)^(2/3) has ṙ^2 = F/r, r̈ = -F/(2r^2),
    # and the Lemaître radius has r'^2 = r_g/r.
    tau, tau0, big_f = sp.symbols("tau tau_0 F", positive=True)
    r_par = (sp.Rational(9, 4) * big_f)**sp.Rational(1, 3) * (tau0 - tau)**sp.Rational(2, 3)
    check_zero("parabolic first integral", sp.simplify(sp.diff(r_par, tau)**2 - big_f / r_par))
    check_zero("parabolic acceleration", sp.simplify(sp.diff(r_par, tau, 2) + big_f / (2 * r_par**2)))
    rg, big_r = sp.symbols("r_g R", positive=True)
    r_lem = (sp.Rational(9, 4) * rg)**sp.Rational(1, 3) * (big_r - tau)**sp.Rational(2, 3)
    check_zero("Lemaitre radius", sp.simplify(sp.diff(r_lem, big_r)**2 - rg / r_lem))
    # §106: -m c^2 sqrt(1 + X/c^2) for the 1PN metric is the test-body Lagrangian to order c^-2.
    m, c, pot, psi, bv, v2 = sp.symbols("m c Phi psi Bv v2", real=True)
    eps = sp.symbols("varepsilon", positive=True)
    radicand = 2 * pot - v2 + eps * (2 * pot**2 + 2 * psi - 2 * bv + 2 * pot * v2)
    lag = -m * sp.sqrt(1 + eps * radicand) / eps
    series = sp.series(lag, eps, 0, 2).removeO()
    target = (-m / eps + m * v2 / 2 - m * pot
              + eps * (m * v2**2 / 8 - sp.Rational(3, 2) * m * pot * v2 - m * pot**2 / 2 - m * psi
                       + m * bv))
    check_zero("post-Newtonian test-body Lagrangian", sp.expand(series - target))
    # §115: on the flat dust universe a = t^(2/3), κρ = 4/(3t^2), the scalar-mode equations
    # λ'' + 3(a'/a)λ' + n²(μ − λ)/(3a²) = 0 = μ'' + 3(a'/a)μ' + n²(μ − λ)/(3a²) hold for the growing
    # mode (δ ∝ t^(2/3)) and the decaying mode (δ ∝ 1/t), with κρδ = −(μ'' + 2(a'/a)μ').
    tt_, cc, nn2 = sp.symbols("t c n2", positive=True)
    scale = tt_**sp.Rational(2, 3)
    hub = sp.diff(scale, tt_) / scale
    kap_rho = 4 / (3 * tt_**2)
    check_zero("flat dust Friedmann equation", sp.simplify(hub**2 - kap_rho / 3))
    for name, lam, mu, delta in [
            ("growing", -2 * cc * scale - 20 * cc / (3 * nn2), -2 * cc * scale, cc * scale),
            ("decaying", -2 * cc / tt_, -2 * cc / tt_, cc / tt_)]:
        for f in (lam, mu):
            check_zero(f"{name} scalar mode",
                       sp.simplify(sp.diff(f, tt_, 2) + 3 * hub * sp.diff(f, tt_)
                                   + nn2 * (mu - lam) / (3 * scale**2)))
        check_zero(f"{name} density contrast",
                   sp.simplify(kap_rho * delta + sp.diff(mu, tt_, 2) + 2 * hub * sp.diff(mu, tt_)))
    # §118: the Taub solution solves the one-wall system and its rates tend to p(u) and p(u - 1).
    u = sp.symbols("u", positive=True)
    t = sp.symbols("t", real=True)
    alpha = (sp.log(2 * u) - sp.log(sp.cosh(2 * u * t))) / 2
    beta = sp.log(sp.cosh(2 * u * t)) / 2 + t
    gamma = sp.log(sp.cosh(2 * u * t)) / 2 + u**2 * t
    a4 = sp.exp(4 * alpha)
    check_zero("one-wall equation for alpha", sp.simplify(sp.diff(alpha, t, 2) + a4 / 2))
    check_zero("one-wall equation for beta", sp.simplify(sp.diff(beta, t, 2) - a4 / 2))
    check_zero("one-wall equation for gamma", sp.simplify(sp.diff(gamma, t, 2) - a4 / 2))
    da, db, dg = sp.diff(alpha, t), sp.diff(beta, t), sp.diff(gamma, t)
    check_zero("one-wall constraint", sp.simplify(da * db + da * dg + db * dg - a4 / 4))
    vol = da + db + dg
    kasner = [-u / (1 + u + u**2), (1 + u) / (1 + u + u**2), u * (1 + u) / (1 + u + u**2)]
    limits = [sp.limit(w / vol, t, sp.oo) for w in (da, db, dg)]
    check_zero("Kasner exponents as the time tends to infinity", sp.Matrix(limits)
               - sp.Matrix(kasner))


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
    verify_geometrical_optics()
    verify_diffraction_scattering_and_gravitational_radiation()
    verify_collisions_collapse_and_post_newtonian()
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
          "point charge to second order, and geometrical optics: the eikonal expansion, rays, intensity, "
          "the angular eikonal, the Riccati law, focal points, imaging and the error energy, and the "
          "diffraction kernel, Thomson and bound-charge scattering, radiation damping, Raychaudhuri, the "
          "charge of the isotropic metric and the quadrupole formula, and the Kepler and collision "
          "radiation, Tolman's collapse, the post-Newtonian Lagrangian, the modes of a dust universe "
          "and the Bianchi II bounce.")


def main():
    verify()


if __name__ == "__main__":
    main()
